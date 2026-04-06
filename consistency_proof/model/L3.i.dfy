include "types.s.dfy"
include "program.i.dfy"
include "network.i.dfy"
include "MSI.i.dfy"

module L3 {
  import opened Types
  import opened CacheTypes
  import opened EngineTypes
  import opened Program


  import opened MessageType
  import Network

  import MSI.Controller
  import MSI.Directory

  datatype Constants = Constants(
    working_set: set<Address>,
    cache_size: nat,
    loc: Location,
    addr_map: Address -> CoreId
  ) {
    ghost predicate WF(i: CoreId, p: Program, f: Address -> CoreId) {
      && cache_size > 0
      && loc == Cache(i, L3)
      && f == addr_map
      && working_set == p.WorkingSet()
    }
  }

  datatype L3Entry =
    | Empty()
    | PendingCB(addr: Address)
    | PendingMem(addr: Address)
    | L3Entry(addr: Address, dirty: bool, dir: Directory.Variables)

  datatype Variables = Variables(
    cache: seq<L3Entry>,
    next_coh_msg: seq<Option<Message>> // [0]: Get's/Put's from L2s [1]: Data from L2s
  ) {
    ghost predicate WF(c: Constants) {
      && c.loc.Cache?
      && |cache| == c.cache_size
      && |next_coh_msg| == 2
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && (forall i: nat | i < |v.cache| :: v.cache[i].Empty?)
    && v.next_coh_msg == [None, None]
  }

  datatype Step =
    | ReceiveCoherenceMessageStep()
    | DirectoryStep(d_step: Directory.Step, opt_idx: Option<nat>, msg: Message) // perform a step
    | ScheduleCallbackStep(eng_req: EngineRequest, addr: Address, idx: nat)  // Environmental transition
    | ReceiveOnMissDataStep(eng_resp: EngineResponse)
    | ReqMemoryStep(addr: Address, idx: nat)
    | RespMemoryStep(idx: nat)

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: Network.MessageOps)
  {
    match step
      case ReceiveCoherenceMessageStep() => ReceiveCoherenceMessage(c, v, v', msgOps)
      case DirectoryStep(d_step, idx, msg) => DirectoryCommunication(c, v, v', msgOps, d_step, idx, msg)
      case ScheduleCallbackStep(eng_req, addr, idx) => ScheduleCallback(c, v, v', msgOps, eng_req, addr, idx)
      case ReceiveOnMissDataStep(eng_resp) => ReceiveOnMissData(c, v, v', msgOps, eng_resp)
      case ReqMemoryStep(addr, idx) => ReqMemory(c, v, v', msgOps, addr, idx)
      case RespMemoryStep(idx) => RespMemory(c, v, v', msgOps, idx)
  }
  // Utility

  ghost predicate NeedsCallback(addr: Address)
  {
    && addr.Morph?
    && addr.morphType.Shared?
  }

  ghost predicate AddrNotInCache(c: Constants, v: Variables, addr: Address)
  {
    && (forall i: nat | i < |v.cache| && v.cache[i].L3Entry? :: v.cache[i].addr != addr)
  }

  ghost predicate AddrHasNoActiveCacheEntry(c: Constants, v: Variables, addr: Address)
  {
    && (forall i: nat | i < |v.cache| && !v.cache[i].Empty? :: v.cache[i].addr != addr)
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
    && msgOps.recv.val.meta.src.Cache? // sent by cache, so we don't consume Mem() messages
    && var msg := msgOps.recv.val;
    // section 8.2.3 primer for classification
    && match msg.coh_msg {
      case GetM | GetS | PutM(_) | PutS  => (
        // lower pri channel msg
        && v.next_coh_msg[0].None?
        && v'.next_coh_msg[0] == Some(msg)
        && v'.next_coh_msg[1] == v.next_coh_msg[1]
      )
      case Data(_, _)  => (
        // higher pri channel msg
        && v.next_coh_msg[1].None?
        && v'.next_coh_msg[1] == Some(msg)
        && v'.next_coh_msg[0] == v.next_coh_msg[0]
      )
      case _ => false // nothing else should be sent to L3 (directory only)
    }
    && v'.cache == v.cache
  }

  // guard our behavior as a directory (for L2s)
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
      && v.cache[idx.val].L3Entry?
      // dir coms not for callback entries
      && v'.cache[idx.val].L3Entry?
      // all other entries are the same
      && (forall i: nat | i < |v.cache| && i != idx.val :: v.cache[i] == v'.cache[i])
      // validation for messages we receive as directory
      && v.cache[idx.val].addr == msg.meta.addr
      && v'.cache[idx.val].addr == msg.meta.addr
    ))
    && (idx.None? ==> (
      // all entries are the same
      && v'.cache == v.cache
      // allow evictions for PendingCB/PendingMem entries here as well
      && AddrNotInCache(c, v, msg.meta.addr)
    ))
    && (match msg.coh_msg {
      case PutM(data) => (
        && v.next_coh_msg[0] == Some(msg)
        && v'.next_coh_msg[0].None? // remove entry
        && v'.next_coh_msg[1] == v.next_coh_msg[1] // virtual 1 unchanged
        && (idx.Some? ==> 
          (if v.cache[idx.val].dir.M?
            && msg.meta.src == v.cache[idx.val].dir.owner then
            v'.cache[idx.val].dirty // current data coming back via PutM is ALWAYS dirty
          else
            // in theory this is a no-op, as someone would have told us it was dirty already
            v'.cache[idx.val].dirty == v.cache[idx.val].dirty
          )
        )
      )
      case PutS => (
        && v.next_coh_msg[0] == Some(msg)
        && v'.next_coh_msg[0].None? // remove entry
        && v'.next_coh_msg[1] == v.next_coh_msg[1] // virtual 1 unchanged
        && (idx.Some? ==> v'.cache[idx.val].dirty == v.cache[idx.val].dirty)
      )
      case Data(data,_) => (
        && v.next_coh_msg[1] == Some(msg)
        && v'.next_coh_msg[1].None? // remove entry
        && v'.next_coh_msg[0] == v.next_coh_msg[0] // virtual 0 unchanged
        && idx.Some?
        && v'.cache[idx.val].dirty // data coming back from L2 is ALWAYS dirty
      )
      case _ => ( // GetS, GetM
        && v.next_coh_msg[0] == Some(msg)
        && v'.next_coh_msg[0].None? // remove entry
        && v'.next_coh_msg[1] == v.next_coh_msg[1] // virtual 1 unchanged
        && idx.Some?
        && v'.cache[idx.val].dirty == v.cache[idx.val].dirty
      )
    })
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
          && AddrHasNoActiveCacheEntry(c, v, addr)
          && c.addr_map(addr) == c.loc.core // only schedule callbacks for addrs we own
          && addr in c.working_set
          && v.cache[idx].Empty? // must be empty
          // all other entries are the same
          && v'.cache[idx] == PendingCB(addr)
          // TODO: one free entry invariant for deadlock prevention
        )
        case OnEvict(val) => (
          && idx < |v.cache|
          && v.cache[idx].L3Entry?
          && v.cache[idx].addr == addr
          && v.cache[idx].dir.I? // we must own this addr as a directory (no L2 has it)
          && v.cache[idx].dir.val == val
          && !v.cache[idx].dirty
          && v'.cache[idx].Empty? // clear entry
        )
        case OnWriteBack(val) => (
          && idx < |v.cache|
          && v.cache[idx].L3Entry?
          && v.cache[idx].addr == addr
          && v.cache[idx].dir.I? // we must own this addr as a directory (no L2 has it)
          && v.cache[idx].dir.val == val
          && v.cache[idx].dirty
          && v'.cache[idx].Empty? // clear entry
        )
    )
    && (forall i: nat | i < |v.cache| && i != idx :: v.cache[i] == v'.cache[i])
    && v'.next_coh_msg == v.next_coh_msg // no change to next_coh_msg
  }


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
    && v'.cache[eng_resp.idx] == L3Entry(resp.meta.addr, false, Directory.I(eng_resp.val))
    && v'.next_coh_msg == v.next_coh_msg // no change to next_coh_msg
  }

  ghost predicate ReqMemory(c: Constants, v: Variables, v': Variables, msgOps: Network.MessageOps, addr: Address, idx: nat)
  {
    && v.WF(c)
    && v'.WF(c)
    && msgOps.recv.None?
    && idx < |v.cache|
    && addr.Regular? // should be just Regular Addrs at this point
    && (match v.cache[idx]
      case Empty => (
        && AddrHasNoActiveCacheEntry(c, v, addr)
        && c.addr_map(addr) == c.loc.core // only fetch addrs we own
        && addr in c.working_set
        // cant be in cache already
        && msgOps.send == multiset{
          CoherenceMsg(GetM, Metadata(addr, c.loc, Mem()))
        }
      )
      case L3Entry(entry_addr,dirty,dir) => (
        && entry_addr == addr
        && dir.I? // should be evictable
        // TODO: dirty?
        && msgOps.send == multiset{
          CoherenceMsg(PutM(dir.val), Metadata(addr, c.loc, Mem()))
        }
      )
      case _ => false
    )
    && v'.cache[idx] == PendingMem(addr)
    && (forall i: nat | i < |v.cache| && i != idx :: v.cache[i] == v'.cache[i])
    && v'.next_coh_msg == v.next_coh_msg // no change to next_coh_msg
  }

  ghost predicate RespMemory(c: Constants, v: Variables, v': Variables, msgOps: Network.MessageOps, idx: nat)
  {
    && v.WF(c)
    && v'.WF(c)
    && msgOps.send == multiset{}
    && msgOps.recv.Some?
    && var resp := msgOps.recv.val;
    && resp.CoherenceMsg?
    && resp.meta.dst == c.loc
    && idx < |v.cache|
    && v.cache[idx].PendingMem?
    && v.cache[idx].addr == resp.meta.addr
    && (match resp.coh_msg
      case Data(val,_) => (
        && resp.meta.src == Mem()
        && v'.cache[idx] == L3Entry(resp.meta.addr, false, Directory.I(val))
      )
      case PutAck => (
        && v'.cache[idx] == L3Entry.Empty()
      )
      case _ => false
    )
    && (forall i: nat | i < |v.cache| && i != idx :: v.cache[i] == v'.cache[i])
    && v'.next_coh_msg == v.next_coh_msg // no change to next_coh_msg
  }


}