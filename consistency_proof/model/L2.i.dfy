include "types.s.dfy"
include "network.i.dfy"
include "program.i.dfy"
include "MSI.i.dfy"

module L2 {
  import opened Types
  import opened CacheTypes
  import opened EngineTypes
  import opened Program


  import opened MessageType
  import Network

  import MSI.Controller
  import MSI.Directory

  datatype Constants = Constants(
    working_set: set<Address>, // set of addresses accessed by cache
    cache_size: nat,
    loc: Location,
    addr_map: Address -> CoreId
  ) {
    ghost predicate WF(i: CoreId, p: Program, f: Address -> CoreId) {
      && cache_size > 0
      && loc == Cache(i, L2)
      && addr_map == f
      && working_set == p.WorkingSet()
    }
  }

  // L2 is directory for L1 eL1D, and child for L3
  datatype L2Entry =
    | PendingCB(addr: Address)
    | L2Entry(addr: Address, dirty: bool, coh: Controller.Variables, dir: Directory.Variables)

  datatype Variables = Variables(
    cache: seq<L2Entry>,
    next_coh_msg_t1: seq<Option<Message>>, // [0]: Get's/Put's from Tier 1 [1]: Data from Tier 1 
    next_coh_msg_t2: seq<Option<Message>>  // [0]: Inv/FwdGet's/Data/PutAck from L2/L3s, [1]: InvAck from L2/L3s
  ) {
    ghost predicate WF(c: Constants) {
      && c.loc.Cache?
      && |cache| == c.cache_size
      && |next_coh_msg_t1| == 2 // 2 virtual channels
      && |next_coh_msg_t2| == 2 // 2 virtual channels
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && (forall i: nat | i < |v.cache| :: v.cache[i].L2Entry? && v.cache[i].coh.I?)
    && v.next_coh_msg_t1 == [None, None]
    && v.next_coh_msg_t2 == [None, None]
  }

  datatype Step =
    | ReceiveCoherenceMessageStep()
    | CacheCommunicationStep(c_step: Controller.Step, idx: nat, addr: Address, msg: Message) // perform a cache communication step (to the L3)
    | DirectoryStep(d_step: Directory.Step, opt_idx: Option<nat>, msg: Message) // perform a step
    | ScheduleCallbackStep(eng_req: EngineRequest, addr: Address, idx: nat)  // Environmental transition
    | ReceiveOnMissDataStep(eng_resp: EngineResponse)

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: Network.MessageOps)
  {
    match step {
      case ReceiveCoherenceMessageStep() => ReceiveCoherenceMessage(c, v, v', msgOps)
      case CacheCommunicationStep(c_step, idx, addr, msg) => CacheCommunication(c, v, v', msgOps, c_step, idx, addr, msg)
      case DirectoryStep(d_step, idx, msg) => DirectoryCommunication(c, v, v', msgOps, d_step, idx, msg)
      case ScheduleCallbackStep(eng_req, addr, idx) => ScheduleCallback(c, v, v', msgOps, eng_req, addr, idx)
      case ReceiveOnMissDataStep(eng_resp) => ReceiveOnMissData(c, v, v', msgOps, eng_resp)
    }
  }

  /////////////////////
  // UTILITY FUNCTIONS
  /////////////////////

  ghost predicate AddrNotInCache(c: Constants, v: Variables, addr: Address)
  {
    && (forall i: nat | i < |v.cache| && v.cache[i].L2Entry? && !v.cache[i].coh.I? :: v.cache[i].addr != addr)
  }

  ghost predicate AddrNotPendingCallback(c: Constants, v: Variables, addr: Address)
  {
    && (forall i: nat | i < |v.cache| && v.cache[i].PendingCB? :: v.cache[i].addr != addr)
  }

  // all L2 entries aren't this addr
  ghost predicate AddrHasNoActiveCacheEntry(c: Constants, v: Variables, addr: Address)
  {
    && AddrNotInCache(c, v, addr)
    && AddrNotPendingCallback(c, v, addr)
  }

  ghost predicate NeedsCallback(addr: Address)
  {
    && addr.Morph?
    && addr.morphType.Private?
  }

  /////////////////////
  // STEP PREDICATES
  /////////////////////
  ghost predicate ReceiveCoherenceMessage(c: Constants, v: Variables, v': Variables, msgOps: Network.MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && msgOps.send == multiset{}
    && msgOps.recv.Some?
    && msgOps.recv.val.CoherenceMsg?
    && msgOps.recv.val.meta.dst == c.loc // intended for this cache
    && var msg := msgOps.recv.val;
    // section 8.2.3 primer for classification
    && match msg.coh_msg {
      case GetM | GetS | PutM(_) | PutS  => (
        // lower pri channel msg for t1
        && v.next_coh_msg_t1[0].None?
        && v'.next_coh_msg_t1[0] == Some(msg)
        && v'.next_coh_msg_t1[1] == v.next_coh_msg_t1[1]
        && v'.next_coh_msg_t2 == v.next_coh_msg_t2
      )
      case PutAck | PutAckStale | FwdGetM | FwdGetS | Inv  => (
        // lower pri channel msg for t2
        && v.next_coh_msg_t2[0].None?
        && v'.next_coh_msg_t2[0] == Some(msg)
        && v'.next_coh_msg_t2[1] == v.next_coh_msg_t2[1]
        && v'.next_coh_msg_t1 == v.next_coh_msg_t1
      )
      case Data(_, _)  => (
        if msg.meta.src.Cache? && msg.meta.src.level.Tier1() then (
          // data from L1, higher pri channel for t1
          && v.next_coh_msg_t1[1].None?
          && v'.next_coh_msg_t1[1] == Some(msg)
          && v'.next_coh_msg_t1[0] == v.next_coh_msg_t1[0]
          && v'.next_coh_msg_t2 == v.next_coh_msg_t2
        ) else (
          // data from L2 or L3, higher pri channel for t2
          && v.next_coh_msg_t2[1].None?
          && v'.next_coh_msg_t2[1] == Some(msg)
          && v'.next_coh_msg_t2[0] == v.next_coh_msg_t2[0]
          && v'.next_coh_msg_t1 == v.next_coh_msg_t1
        )
      )
      case InvAck => (
        // higher pri channel msg for t2
        && v.next_coh_msg_t2[1].None?
        && v'.next_coh_msg_t2[1] == Some(msg)
        && v'.next_coh_msg_t2[0] == v.next_coh_msg_t2[0]
        && v'.next_coh_msg_t1 == v.next_coh_msg_t1
      )
    }
    && v'.cache == v.cache
  }

  // guard our behavior as a child cache (of the L3)
  ghost predicate CacheCommunication(c: Constants, v: Variables, v': Variables, msgOps: Network.MessageOps, step: Controller.Step, idx: nat, addr: Address, msg: Message)
  {
    && v.WF(c)
    && v'.WF(c)
    && idx < |v.cache|
    // don't do cache coms for something waiting for a callback
    && v.cache[idx].L2Entry?
    && v'.cache[idx].L2Entry?
    // index validation
    // fix addr in all cases here, even if going to I to overguard
    // against edge cases where we might transition to IIA etc
    // for GetS/M, this entry needs to be updated with addr
    && v'.cache[idx].addr == addr
    && !NeedsCallback(addr)
    && msgOps.recv.None? // sleight of hand. We don't receive anything here...
    && var fakeMsgOps := msgOps.(
      recv := if step.RecvMsgStep? then Some(msg) else None
    ); // and create a fake msgOps to use in the MSI protocol
    && (match step
      case GetSStep() => (
        // addr is not in the cache
        && AddrHasNoActiveCacheEntry(c, v, addr)
        // predata, dir shouldn't matter
        && addr in c.working_set
        && !v'.cache[idx].dirty // mark it not dirty
        && v'.cache[idx].dir == Directory.I(Just(0)) // mark dir in I state so we process Puts correctly
        // if we don't specify, we can transition to M w/ owner and can process a stray PutM by changing coh to M
        && v'.next_coh_msg_t2 == v.next_coh_msg_t2
      )
      case GetMStep() => (
        // only send out a request if there is a requested GetM from above (L1 or eL1D)
        // by WF of program, the addr will thus respect private morph core
        // index is empty or shared
        && v.next_coh_msg_t1[0].Some?
        && var msg := v.next_coh_msg_t1[0].val;
        && msg.CoherenceMsg?
        && msg.coh_msg.GetM?
        && msg.meta.addr == addr
        && (match v.cache[idx].coh
          case S(_) => (
            && v.cache[idx].addr == addr
            // dir might be in S, but we are elevating to M
            // so preserve sharers
            && v'.cache[idx].dir == v.cache[idx].dir
          )
          case I => (
            && AddrHasNoActiveCacheEntry(c, v, addr)
            && v'.cache[idx].dir == Directory.I(Just(0)) // mark dir in I state so we process Puts correctly
            // if we don't specify, we can transition to M w/ owner and can process a stray PutM by changing coh to M
          )
          case _ => false
        )
        && !v'.cache[idx].dirty // mark it not dirty
        && v'.next_coh_msg_t2 == v.next_coh_msg_t2
      )
      case EvictStep() => (
        && v.cache[idx].addr == addr
        // can't evict something that's directory state is not I (children are borrowing)
        && v.cache[idx].dir.I?
        && v.cache[idx].dir == v'.cache[idx].dir // keep this stable due to IIA transient state
        // if evicting data in M state, it must be dirty
        && (v.cache[idx].coh.M? ==> v.cache[idx].dirty)
        && v'.cache[idx].dirty == v.cache[idx].dirty // preserve dirty state in case someone needs it
        && v'.next_coh_msg_t2 == v.next_coh_msg_t2
      )
      case RecvMsgStep() => (
        // match addr going to recvmessage step with index
        // addr matching the msg is handled by NextStep
        && v.cache[idx].addr == addr
        && v'.cache[idx].dirty == v.cache[idx].dirty
        // additional guards to allow for hierarchical coherence
        && msg.CoherenceMsg?
        && match msg.coh_msg {
          case FwdGetS => (
            // if the message is a FwdGetS, the directory must be in I or S
            && (v.cache[idx].dir.I? || v.cache[idx].dir.S?)
            && v.cache[idx].dir == v'.cache[idx].dir
            && v.cache[idx].dirty // stall FwdGetS till write is done
            // msg needs to be next in queue (virtual channel 0)
            && v.next_coh_msg_t2[0] == Some(msg)
            && v'.next_coh_msg_t2[0].None? // remove entry
            && v'.next_coh_msg_t2[1] == v.next_coh_msg_t2[1] // virtual 1 unchanged
          )
          case Inv | FwdGetM => (
            // if the message is a FwdGetM or Inv, the directory must be in I (directory owns it)
            && v.cache[idx].dir.I?
            && v'.cache[idx].dir == v.cache[idx].dir // keep this stable due to IIA transient state
            && (msg.coh_msg.FwdGetM? ==> v.cache[idx].dirty) // stall FwdGetM till write is done
            // msg needs to be next in queue (virtual channel 0)
            && v.next_coh_msg_t2[0] == Some(msg)
            && v'.next_coh_msg_t2[0].None? // remove entry
            && v'.next_coh_msg_t2[1] == v.next_coh_msg_t2[1] // virtual 1 unchanged
          )
          case Data(val, _) => (
            // shouldn't be receiving other messages, except Data
            // msg needs to be next in queue (virtual channel 1)
            && v.next_coh_msg_t2[1] == Some(msg)
            && v'.next_coh_msg_t2[1].None? // remove entry
            && v'.next_coh_msg_t2[0] == v.next_coh_msg_t2[0] // virtual 0 unchanged
            // the reading of this data is guarded until acks come in by guard expecting coh being M or S
            // TODO: can the value change? i.e. when receiving Data in SMAD, can it be different? (I think no)
            // how about IMAD?, can't lend to proxy in IMAD.. so necessarily will be in I
            && v'.cache[idx].dir == if !v.cache[idx].dir.I? then v.cache[idx].dir else Directory.I(val)
          )
          case InvAck => (
            // TODO: Any guard on invack?
            && v'.cache[idx].dir == v.cache[idx].dir
            // msg needs to be next in queue (virtual channel 1)
            && v.next_coh_msg_t2[1] == Some(msg)
            && v'.next_coh_msg_t2[1].None? // remove entry
            && v'.next_coh_msg_t2[0] == v.next_coh_msg_t2[0]
          )
          case PutAck | PutAckStale => (
            // PutAck doesn't have guard requiring entry is I (should be in I because we can only evict from I)
            && v'.cache[idx].dir == v.cache[idx].dir
            // msg needs to be next in queue (virtual channel 0)
            && v.next_coh_msg_t2[0] == Some(msg)
            && v'.next_coh_msg_t2[0].None? // remove entry
            && v'.next_coh_msg_t2[1] == v.next_coh_msg_t2[1]
          )
          case _ => false
        }
      )
    )
    // all other entries are the same
    && (forall i: nat | i < |v.cache| && i != idx :: v.cache[i] == v'.cache[i])
    // no messages changing for upper protocol
    && v'.next_coh_msg_t1 == v.next_coh_msg_t1
    // no change to directory here.
    && Controller.NextStep(Controller.Constants(c.loc, Cache(c.addr_map(addr), L3)), v.cache[idx].coh, v'.cache[idx].coh, fakeMsgOps, step, addr)
  }

  // guard our behavior as a directory (for L1 eL1D)
  ghost predicate DirectoryCommunication(c: Constants, v: Variables, v': Variables, msgOps: Network.MessageOps, step: Directory.Step, idx: Option<nat>, msg: Message)
  {
    && v.WF(c)
    && v'.WF(c)
    && msgOps.recv.None?
    && msg.CoherenceMsg?
    && var fakeMsgOps := msgOps.(
      recv := Some(msg)
    ); // create a fake msgOps to use in the MSI protocol
    && (idx.Some? ==> (
      && idx.val < |v.cache|
      && v.cache[idx.val].L2Entry?
      && !v.cache[idx.val].coh.I? // nonempty entry
      // dir coms not for callback entries
      && v'.cache[idx.val].L2Entry?
      // all other entries are the same
      && (forall i: nat | i < |v.cache| && i != idx.val :: v.cache[i] == v'.cache[i])
      && v.cache[idx.val].addr == msg.meta.addr
      && v'.cache[idx.val].addr == msg.meta.addr
    ))
    && (idx.None? ==> (
      // all entries are the same
      && v'.cache == v.cache
      // allow evictions for PendingCB entries here as well
      && AddrNotInCache(c, v, msg.meta.addr)
    ))
    // validation for messages we receive as directory
    && (match msg.coh_msg {
      case GetM => (
        // msg needs to be next in queue (virtual channel 0)
        && v.next_coh_msg_t1[0] == Some(msg)
        && v'.next_coh_msg_t1[0].None? // remove entry
        && v'.next_coh_msg_t1[1] == v.next_coh_msg_t1[1] // virtual 1 unchanged
        && idx.Some?
        // if we receive a GetM, then we must have the data in M as a child
        && (if msg.meta.src == Cache(c.loc.core, Proxy) then
            // todo: is this chill?
            v.cache[idx.val].coh.Loadable()
          else
            v.cache[idx.val].coh.M?
        )
        && v'.cache[idx.val].coh == v.cache[idx.val].coh
        && v'.cache[idx.val].dirty == if 
          v.cache[idx.val].dir.M? && msg.meta.src == Cache(c.loc.core, Proxy) then
            true // if doing a FwdGetM to the proxy, ensure that we preemptively mark the data dirty
          else
            v.cache[idx.val].dirty
      )
      case GetS => (
        // msg needs to be next in queue (virtual channel 0)
        && v.next_coh_msg_t1[0] == Some(msg)
        && v'.next_coh_msg_t1[0].None? // remove entry
        && v'.next_coh_msg_t1[1] == v.next_coh_msg_t1[1] // virtual 1 unchanged
        && idx.Some?
        // if we receive a GetS, then we must have the data in readable format
        && v.cache[idx.val].coh.Loadable()
        && v'.cache[idx.val].coh == v.cache[idx.val].coh
        && v'.cache[idx.val].dirty == if 
          v.cache[idx.val].dir.M? && msg.meta.src == Cache(c.loc.core, Proxy) then
            true // if doing a FwdGetS to the proxy, ensure that we preemptively mark the data dirty
          else    // this isn't strictly necessary as subsequent Data will mark it dirty,
            v.cache[idx.val].dirty // but this ensures when Data is sent from L1/eL1 to Proxy, already dirty
      )
      case PutM(data) => (
        // msg needs to be next in queue (virtual channel 0)
        && v.next_coh_msg_t1[0] == Some(msg)
        && v'.next_coh_msg_t1[0].None? // remove entry
        && v'.next_coh_msg_t1[1] == v.next_coh_msg_t1[1] // virtual 1 unchanged
        // don't enforce idx here, can be None, in which case we use the I case to send a PutAck
        && (idx.Some? ==> (if v.cache[idx.val].dir.M?
              && msg.meta.src == v.cache[idx.val].dir.owner
              && v.cache[idx.val].dir.owner != Cache(c.loc.core, Proxy) then
          (
            // should already have it in M state (won't enforce explicitly, should be provable)
            && v'.cache[idx.val].coh == Controller.M(data)
            && v'.cache[idx.val].dirty // data coming back via PutM is ALWAYS dirty (from L1 or eL1D)
          ) else (
            // includes the proxy returning the data (should be S -> S in this case)
            // otherwise the data is just swallowed, no change.
            && v'.cache[idx.val].coh == v.cache[idx.val].coh
            && v'.cache[idx.val].dirty == v.cache[idx.val].dirty
          )
        ))
      )
      case Data(data,_) => (
        // msg needs to be next in queue (virtual channel 1)
        && v.next_coh_msg_t1[1] == Some(msg)
        && v'.next_coh_msg_t1[1].None? // remove entry
        && v'.next_coh_msg_t1[0] == v.next_coh_msg_t1[0] // virtual 0 unchanged
        && msg.meta.src.Cache? // should be provable
        && idx.Some?
        && (if !msg.meta.src.level.Proxy? then
          (
            // should already have it in M state (won't enforce explicitly, should be provable)
            && v'.cache[idx.val].coh == Controller.M(data)
            && v'.cache[idx.val].dirty // data coming back via PutM is ALWAYS dirty (from L1 or eL1D)
          ) else (
            // if the proxy returning the data, it is just swallowed, no change.
            && v'.cache[idx.val].coh == v.cache[idx.val].coh
            && v'.cache[idx.val].dirty == v.cache[idx.val].dirty
          )
        )
      )
      case PutS => (
        // msg needs to be next in queue (virtual channel 0)
        && v.next_coh_msg_t1[0] == Some(msg)
        && v'.next_coh_msg_t1[0].None? // remove entry
        && v'.next_coh_msg_t1[1] == v.next_coh_msg_t1[1] // virtual 1 unchanged
        // don't enforce idx here, can be None, in which case we use the I case to send a PutAck
        && (idx.Some? ==> (
          && v'.cache[idx.val].coh == v.cache[idx.val].coh
          && v'.cache[idx.val].dirty == v.cache[idx.val].dirty
        ))
      )
      // these are the only directory messages
      case _ => false
    })
    // no messages changing for lower protocol
    && v'.next_coh_msg_t2 == v.next_coh_msg_t2
    // value doesn't matter
    && var dir := if idx.Some? then v.cache[idx.val].dir else Directory.I(Just(0));
    && var dir' := if idx.Some? then v'.cache[idx.val].dir else Directory.I(Just(0));
    && Directory.NextStep(Directory.Constants(c.loc), dir, dir', fakeMsgOps, step)
  }

  ghost predicate ScheduleCallback(c: Constants, v: Variables, v': Variables, msgOps: Network.MessageOps, eng_req: EngineRequest, addr: Address, idx: nat)
  {
    // can't schedule callback for something in WB
    && v.WF(c)
    && v'.WF(c)
    && msgOps.recv.None?
    // send the cb request to engine
    && msgOps.send == multiset{ EngineRequest(eng_req, Metadata(addr, c.loc, Engine(c.loc.core))) }
    && NeedsCallback(addr)
    && (match eng_req
        case OnMiss(miss_idx) => (
          && miss_idx == idx
          && idx < |v.cache|
          && v.cache[idx].L2Entry?
          && v.cache[idx].coh.I? // must be empty
          && AddrHasNoActiveCacheEntry(c, v, addr)
          && addr.morphType.idx == c.loc.core // only schedule callbacks for addresses from this core
          && addr in c.working_set // only schedule callbacks for addresses in working set
          && v'.cache[idx] == PendingCB(addr)
          // TODO: one free entry invariant for deadlock prevention
        )
        case OnEvict(val) => (
          && idx < |v.cache|
          && v.cache[idx].L2Entry?
          && !v.cache[idx].coh.I? // nonempty entry
          && v.cache[idx].addr == addr
          && v.cache[idx].dir.I? // we must own this addr as a directory (eL1d or L1 don't have it)
          && v.cache[idx].dir.val == val
          && !v.cache[idx].dirty
          && v'.cache[idx].L2Entry?
          && v'.cache[idx].coh.I? // clear entry
        )
        case OnWriteBack(val) => (
          && idx < |v.cache|
          && v.cache[idx].L2Entry?
          && !v.cache[idx].coh.I? // nonempty entry
          && v.cache[idx].addr == addr
          && v.cache[idx].dir.I? // we must own this addr as a directory (eL1d or L1 don't have it)
          && v.cache[idx].dir.val == val
          && v.cache[idx].dirty
          && v'.cache[idx].L2Entry?
          && v'.cache[idx].coh.I? // clear entry
        )
    )
    && v'.next_coh_msg_t1 == v.next_coh_msg_t1
    && v'.next_coh_msg_t2 == v.next_coh_msg_t2
    // all other entries are the same
    && (forall i: nat | i < |v.cache| && i != idx :: v.cache[i] == v'.cache[i])
  }

  // TODO: data moves around/changes between put and putack?
  // think we are safe because: put can only happen on dir I and gets/m require coh in M or S

  ghost predicate ReceiveOnMissData(c: Constants, v: Variables, v': Variables, msgOps: Network.MessageOps, eng_resp: EngineResponse)
  {
    // can't receive data for something in WB
    && v.WF(c)
    && v'.WF(c)
    && msgOps.send == multiset{}
    && msgOps.recv.Some?
    && var resp := msgOps.recv.val;
    && resp.EngineResponse?
    && resp.engine_resp == eng_resp
    && resp.meta.dst == c.loc
    && eng_resp.idx < |v.cache|
    && v.cache[eng_resp.idx].PendingCB?
    && v.cache[eng_resp.idx].addr == resp.meta.addr
    && (forall i: nat | i < |v.cache| && i != eng_resp.idx :: v.cache[i] == v'.cache[i])
    && v'.next_coh_msg_t1 == v.next_coh_msg_t1
    && v'.next_coh_msg_t2 == v.next_coh_msg_t2
    && v'.cache[eng_resp.idx] == L2Entry(resp.meta.addr, false, Controller.M(eng_resp.val), Directory.I(eng_resp.val))
  }



}