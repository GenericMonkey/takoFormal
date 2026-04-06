include "types.s.dfy"
include "program.i.dfy"
include "MSI.i.dfy"

module Engine {
  import opened Types
  import opened CacheTypes
  import opened Program
  import opened EngineTypes

  import Network
  import opened MessageType

  import MSI.Controller

  datatype Constants = Constants(
    working_set: set<Address>, // set of addresses accessed by cache
    locs: Controller.Constants,
    onMissCBs: map<Address, Thread>,
    onEvictCBs: map<Address, Thread>,
    onWBCBs: map<Address, Thread>,
    cache_size: nat,
    buffer_size: nat
  ) {
    ghost predicate WF(i: CoreId, p: Program) {
      // grab program callbacks
      && onMissCBs == p.onMissCBs
      && onEvictCBs == p.onEvictCBs
      && onWBCBs == p.onWBCBs
      && cache_size > 0
      && buffer_size > 0
      && locs.loc == Cache(i, eL1)
      && locs.dir_loc == Cache(i, L2)
      && working_set == p.WorkingSet()
    }
  }

  datatype BufferEntry =
    | Empty()
    | BufferEntry(
      addr: Address,
      req_loc: Location,
      started: bool,
      pc: nat,
      count: nat,
      regs: map<Register, Value>,
      cb_type: EngineRequest,
      // TODO: seq might be too weak here
      values: seq<Value>
    )

  datatype EL1Entry = EL1Entry(addr: Address, coh: Controller.Variables, dirty: bool)

  datatype Variables = Variables(
    buffer: seq<BufferEntry>,
    cache: seq<EL1Entry>,
    cb_order: map<Address, seq<nat>>
  ) {
    ghost predicate WF(c: Constants) {
      && c.locs.loc.Cache?
      && |buffer| == c.buffer_size
      && |cache| == c.cache_size
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    // initialize buffers and cache
    && (forall i: nat | i < |v.buffer| :: v.buffer[i].Empty?)
    && v.cb_order == map[]
    && (forall i: nat | i < |v.cache| :: v.cache[i].coh.I?)
  }

  datatype Step =
    // TODO: flush in callback?
    | NextInstStep(idx: nat, inst: Instruction, c_idx: nat) //advances PC and does the action at that cb slot. action guarded by 1) for ld/st: data in cache, 2) for flush: all data being gone
    | CacheCommunicationStep(step: Controller.Step, c_idx: nat, b_idx: nat, addr: Address) // perform a cache communication step
    | ReceiveCallbackReqStep(idx: nat) // receive a callback from the L2/L3
    | StartCallbackStep(idx: nat) // start a callback
    | FinishCallbackStep(idx: nat) // send a response to the L2/L3

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: Network.MessageOps) {
    match step {
      case NextInstStep(idx, inst, c_idx) => NextInst(c, v, v', idx, inst, msgOps, c_idx)
      case CacheCommunicationStep(step, c_idx, b_idx, addr) => CacheCommunication(c, v, v', msgOps, step, c_idx, b_idx, addr)
      case ReceiveCallbackReqStep(idx) => ReceiveCallbackReq(c, v, v', idx, msgOps)
      case StartCallbackStep(idx) => StartCallback(c, v, v', idx, msgOps)
      case FinishCallbackStep(idx) => FinishCallback(c, v, v', idx, msgOps)
    }
  }

  // Utility Functions

  ghost predicate EntryHasNextInst(c: Constants, entry: BufferEntry)
  {
    && entry.BufferEntry?
    && match entry.cb_type {
      case OnMiss(_) => (
        && entry.addr in c.onMissCBs
        && entry.pc < |c.onMissCBs[entry.addr]|
      )
      case OnEvict(_) => (
        && entry.addr in c.onEvictCBs
        && entry.pc < |c.onEvictCBs[entry.addr]|
      )
      case OnWriteBack(_) => (
        && entry.addr in c.onWBCBs
        && entry.pc < |c.onWBCBs[entry.addr]|
      )
    }
  }

  // bind inst to looking up the next instruction in the buffer
  ghost function NextInstForEntry(c: Constants, entry: BufferEntry) : Instruction
    requires EntryHasNextInst(c, entry)
  {
    match entry.cb_type {
      case OnMiss(_) => c.onMissCBs[entry.addr][entry.pc]
      case OnEvict(_) => c.onEvictCBs[entry.addr][entry.pc]
      case OnWriteBack(_) => c.onWBCBs[entry.addr][entry.pc]
    }
  }

  ghost predicate CallbackFinished(c: Constants, entry: BufferEntry)
  {
    && entry.BufferEntry?
    && entry.started // needs to have started to be allowed to finish
    && match entry.cb_type {
      case OnMiss(_) => (
        && entry.addr in c.onMissCBs
        && entry.pc == |c.onMissCBs[entry.addr]|
      )
      case OnEvict(_) => (
        && entry.addr in c.onEvictCBs
        && entry.pc == |c.onEvictCBs[entry.addr]|
      )
      case OnWriteBack(_) => (
        && entry.addr in c.onWBCBs
        && entry.pc == |c.onWBCBs[entry.addr]|
      )
    }
  }

  ghost predicate AddrNotInCache(c: Constants, v: Variables, addr: Address)
  {
    && (forall i: nat | i < |v.cache| && !v.cache[i].coh.I? :: v.cache[i].addr != addr)
  }

  ghost predicate AddrNotPendingCallback(c: Constants, v: Variables, addr: Address)
  {
    && (forall i: nat | i < |v.buffer| && v.buffer[i].BufferEntry? :: v.buffer[i].addr != addr)
  }

  ghost predicate PrivateCallbackInBuffer(c: Constants, v: Variables)
  {
    && (exists i: nat :: (
      && i < |v.buffer|
      && v.buffer[i].BufferEntry?
      && v.buffer[i].addr.Morph?
      && v.buffer[i].addr.morphType.Private?
    ))
  }

  ghost predicate IsNextCallback(c: Constants, v: Variables, idx: nat)
    requires idx < |v.buffer|
    requires v.buffer[idx].BufferEntry?
  {
    && v.buffer[idx].addr in v.cb_order
    && |v.cb_order[v.buffer[idx].addr]| > 0
    && v.cb_order[v.buffer[idx].addr][0] == idx
  }

  // Step Predicates


  ghost predicate NextInst(c: Constants, v: Variables, v': Variables, buf_idx: nat, inst: Instruction, msgOps: Network.MessageOps, c_idx: nat)
  {
    && msgOps.send == multiset{}
    && msgOps.recv.None?
    && v.WF(c)
    && buf_idx < |v.buffer|
    && EntryHasNextInst(c, v.buffer[buf_idx])
    && inst == NextInstForEntry(c, v.buffer[buf_idx])
    && v.buffer[buf_idx].started
    && msgOps.send == multiset{}
    && msgOps.recv.None?
    && match inst {
      case Load(addr, reg) => (
        && c_idx < |v.cache|
        && v.cache[c_idx].addr == addr
        && (v.cache[c_idx].coh.M? || v.cache[c_idx].coh.S?)
        && DoLoad(c, v, v', inst, buf_idx, c_idx)
      )
      case Store(addr, val) => (
        && c_idx < |v.cache|
        && v.cache[c_idx].addr == addr
        && v.cache[c_idx].coh.M?
        && (val.Reg? ==> val.reg in v.buffer[buf_idx].regs)
        && DoStore(c, v, v', inst, buf_idx, c_idx)
      )
      case RMW(addr, wval, reg) => (
        && c_idx < |v.cache|
        && v.cache[c_idx].addr == addr
        && v.cache[c_idx].coh.M?
        && (wval.Reg? ==> wval.reg in v.buffer[buf_idx].regs)
        && DoRMW(c, v, v', inst, buf_idx, c_idx)
      )
      // TODO: Double check flushes can't happen here
      case Flush(_) => false
      case Branch(reg, compval, target) => (
        && reg in v.buffer[buf_idx].regs
        && DoBranch(c, v, v', inst, buf_idx)
      )
    }
  }

  ghost predicate DoLoad(c: Constants, v: Variables, v': Variables, inst: Instruction, buf_idx: nat, idx: nat)
    requires inst.Load?
    requires buf_idx < |v.buffer|
    requires v.buffer[buf_idx].BufferEntry?
    requires idx < |v.cache|
    requires (v.cache[idx].coh.M? || v.cache[idx].coh.S?)
  {
    && v' == v.(
      buffer := v.buffer[buf_idx := v.buffer[buf_idx].(
        // increment PC and add the result to the list
        pc := v.buffer[buf_idx].pc + 1,
        regs := v.buffer[buf_idx].regs[inst.reg := v.cache[idx].coh.val],
        // add value to list of computed results
        values := v.buffer[buf_idx].values + [v.cache[idx].coh.val]
      )]
    )
  }

  ghost predicate DoStore(c: Constants, v: Variables, v': Variables, inst: Instruction, buf_idx: nat, idx: nat)
    requires v.WF(c)
    requires inst.Store?
    requires buf_idx < |v.buffer|
    requires v.buffer[buf_idx].BufferEntry?
    requires inst.val.Reg? ==> inst.val.reg in v.buffer[buf_idx].regs
    requires idx < |v.cache|
    requires v.cache[idx].coh.M?
  {
    var val := if inst.val.Reg? then v.buffer[buf_idx].regs[inst.val.reg] else Just(inst.val.val/*, Some(Core(c.locs.loc.core, v.buffer[buf_idx].pc))*/);
    && v' == v.(
      buffer := v.buffer[buf_idx := v.buffer[buf_idx].(
        // increment PC
        pc := v.buffer[buf_idx].pc + 1
      )],
      cache := v.cache[idx := v.cache[idx].(
        coh := Controller.Variables.M(val),
        dirty := true // mark as dirty
      )]
    )
  }

  ghost predicate DoRMW(c: Constants, v: Variables, v': Variables, inst: Instruction, buf_idx: nat, idx: nat)
    requires v.WF(c)
    requires inst.RMW?
    requires buf_idx < |v.buffer|
    requires v.buffer[buf_idx].BufferEntry?
    requires inst.wval.Reg? ==> inst.wval.reg in v.buffer[buf_idx].regs
    requires idx < |v.cache|
    requires v.cache[idx].coh.M?
  {
    var val := if inst.wval.Reg? then v.buffer[buf_idx].regs[inst.wval.reg] else Just(inst.wval.val/*, Some(Core(c.locs.loc.core, v.buffer[buf_idx].pc))*/);
    && v' == v.(
      buffer := v.buffer[buf_idx := v.buffer[buf_idx].(
        // increment PC
        pc := v.buffer[buf_idx].pc + 1,
        regs := v.buffer[buf_idx].regs[inst.reg := v.cache[idx].coh.val],
        // add value to list of computed results
        values := v.buffer[buf_idx].values + [v.cache[idx].coh.val]
      )],
      // also update cache with write value
      cache := v.cache[idx := v.cache[idx].(
        coh := Controller.Variables.M(val),
        dirty := true // mark as dirty
      )]
    )
  }

  ghost predicate DoBranch(c: Constants, v: Variables, v': Variables, inst: Instruction, buf_idx: nat)
    requires inst.Branch?
    requires buf_idx < |v.buffer|
    requires v.buffer[buf_idx].BufferEntry?
    requires inst.reg in v.buffer[buf_idx].regs
  {
    var target := if v.buffer[buf_idx].regs[inst.reg] == inst.compval then v.buffer[buf_idx].pc + 1 else inst.target;
    var new_count := if v.buffer[buf_idx].pc >= target then v.buffer[buf_idx].count + 1 else v.buffer[buf_idx].count;
    && v' == v.(
      buffer := v.buffer[buf_idx := v.buffer[buf_idx].(
        // increment PC
        pc := target,
        count := new_count
      )]
    )
  }

  ghost predicate CacheCommunication(c: Constants, v: Variables, v': Variables, msgOps: Network.MessageOps, step: Controller.Step, c_idx: nat, b_idx: nat, addr: Address)
  {
    && v.WF(c)
    && v'.WF(c)
    && c_idx < |v.cache|
    // all other entries are the same
    && (forall i: nat | i < |v.cache| && i != c_idx :: v.cache[i] == v'.cache[i])
    && v.buffer == v'.buffer
    && v.cb_order == v'.cb_order
    // index validation
    // for GetS/M, this entry needs to be updated with addr
    // need it even if evicting for transient states like IIA etc
    // fine because we'll be marked invalid by nextstep
    && v'.cache[c_idx].addr == addr
    && (match step
      case GetSStep() => (
        // addr is not in the cache
        && AddrNotInCache(c, v, addr)
        && (addr.Morph? ==> addr.morphType.Shared? && PrivateCallbackInBuffer(c, v))
        && addr in c.working_set
        && !v'.cache[c_idx].dirty
      )
      case GetMStep() => (
        // only send out a request if the next instruction is a store or RMW
        // by WF of program, the addr will thus respect private morph core
        && b_idx < |v.buffer|
        && EntryHasNextInst(c, v.buffer[b_idx])
        && v.buffer[b_idx].started
        && var inst := NextInstForEntry(c, v.buffer[b_idx]);
        && (inst.Store? || inst.RMW?)
        && addr == inst.addr
        // index is empty or shared
        && (match v.cache[c_idx].coh
          case S(_) => (v.cache[c_idx].addr == addr)
          case I => (AddrNotInCache(c, v, addr))
          case _ => false
        )
        && !v'.cache[c_idx].dirty
      )
      case EvictStep() => (
        && v.cache[c_idx].addr == addr
        // if evicting data in M state, it must be dirty
        && (v.cache[c_idx].coh.M? ==> v.cache[c_idx].dirty)
        && v'.cache[c_idx].dirty == v.cache[c_idx].dirty // preserve dirty state in case someone needs it
        // S M enforcement handled by NextStep
      )
      case RecvMsgStep() => (
        // match addr going to recvmessage step with index
        && v.cache[c_idx].addr == addr
        && v'.cache[c_idx].dirty == v.cache[c_idx].dirty // preserve dirty
        && msgOps.recv.Some?
        && msgOps.recv.val.CoherenceMsg?
        && var msg := msgOps.recv.val;
        // stall till we actually do the write
        && ((msg.coh_msg.FwdGetM? || msg.coh_msg.FwdGetS?) ==> v.cache[c_idx].dirty)
        // all other messages aren't concerned with dirty
        // - PutAck/Stale is after enforcement
        // - Inv only happens in S state
        // - InvAck happens before data is received in M
        // - Data happens pre-data
        // addr matching the msg is handled by NextStep
      )
    )
    && Controller.NextStep(c.locs, v.cache[c_idx].coh, v'.cache[c_idx].coh, msgOps, step, addr)
  }

  ghost predicate ReceiveCallbackReq(c: Constants, v: Variables, v': Variables, idx: nat, msgOps: Network.MessageOps)
  {
    && v.WF(c)
    && idx < |v.buffer|
    && v.buffer[idx].Empty?
    // TODO: how to enforce the deadlock avoidance property?
    // TODO: enforcement that dedicated slot for shared cbs
    && msgOps.send == multiset{}
    && msgOps.recv.Some?
    && var msg := msgOps.recv.val;
    && msg.EngineRequest?
    && msg.meta.dst == Engine(c.locs.loc.core)
    && var regs := if msg.engine_req.OnMiss? then map[] else map[EvictReg() := msg.engine_req.val];
    && v' == v.(
      buffer := v.buffer[idx := BufferEntry(msg.meta.addr, msg.meta.src, false, 0, 0, regs, msg.engine_req, [])],
      cb_order := v.cb_order[ msg.meta.addr := (if msg.meta.addr in v.cb_order then v.cb_order[msg.meta.addr] + [idx] else [idx]) ]
    )
  }


  ghost predicate StartCallback(c: Constants, v: Variables, v': Variables, idx: nat, msgOps: Network.MessageOps)
  {
    && v.WF(c)
    && idx < |v.buffer|
    && v.buffer[idx].BufferEntry?
    // can only start the callback at head of queue
    && IsNextCallback(c, v, idx)
    // hasn't started yet
    && !v.buffer[idx].started
    // send if onmiss
    && msgOps.send == multiset{}
    && msgOps.recv.None?
    && v' == v.(
      // flip started bit to true
      buffer := v.buffer[idx := v.buffer[idx].(started := true)]
    )
  }

  ghost predicate FinishCallback(c: Constants, v: Variables, v': Variables, idx: nat, msgOps: Network.MessageOps)
  {
    && v.WF(c)
    && idx < |v.buffer|
    && v.buffer[idx].BufferEntry?
    // can only finish the callback at head of queue
    && IsNextCallback(c, v, idx)
    && CallbackFinished(c, v.buffer[idx])
    // send if onmiss
    && msgOps.send == (if v.buffer[idx].cb_type.OnMiss? then
        multiset{
          EngineResponse(
            OnMissData(v.buffer[idx].cb_type.idx, Transform(v.buffer[idx].values)),
            Metadata(v.buffer[idx].addr, Engine(c.locs.loc.core), v.buffer[idx].req_loc)
          )
        }
      else
        multiset{}
    )
    && msgOps.recv.None?
    && v' == v.(
      // clear out entry
      buffer := v.buffer[idx := BufferEntry.Empty()],
      // remove head of cb_order to allow next cb for same addr to run
      cb_order := v.cb_order[ v.buffer[idx].addr := v.cb_order[v.buffer[idx].addr][1..] ]
    )
  }

}