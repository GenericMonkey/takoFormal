include "types.s.dfy"
include "program.i.dfy"
include "network.i.dfy"
include "MSI.i.dfy"

module Core {
  import opened Types
  import opened CacheTypes
  import opened Program

  import opened MessageType
  import Network

  import MSI.Controller

  datatype Constants = Constants(
    working_set: set<Address>, // set of addresses accessed by cache
    cache_size: nat,
    insts: Thread,
    locs: Controller.Constants
  ) {
    ghost predicate WF(i: CoreId, p : Program) {
      && insts == (if i < |p.threads| then p.threads[i] else [])
      && cache_size > 0
      && locs.loc == Cache(i, L1)
      && locs.dir_loc == Cache(i, L2)
      && working_set == p.WorkingSet()
    }
  }

  datatype L1Entry = L1Entry(addr : Address, coh: Controller.Variables, dirty: bool)


  datatype Variables = Variables(
    pc: nat,
    count: nat,
    regs: map<Register, Value>,
    cache: seq<L1Entry>,
    results: seq<(Address, Value)>
  ) {
    ghost predicate WF(c: Constants) {
      && c.locs.loc.Cache?
      && |cache| == c.cache_size
    }
  }
  // Invariant (enforced or assumed)
  // entries in cache are either empty or data (no Allocated or CallbackRunning)

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && v.pc == 0 // start at first instruction
    && v.count == 0
    && v.results == [] // no results yet
    && (forall i: nat | i < |v.cache| :: v.cache[i].coh.I?)
    && v.regs == map[]
  }

  datatype Step =
    | NextInstStep(inst: Instruction, idx: nat) //advances PC and does the action. action guarded by 1) for ld/st: data in cache, 2) for flush: all data being gone
    | CacheCommunicationStep(step: Controller.Step, idx: nat, addr: Address) // perform a cache communication step



  ghost predicate NextStep(c : Constants, v: Variables, v': Variables, step : Step, msgOps: Network.MessageOps, addrFlushed: bool)
  {
    match step
      case NextInstStep(inst, idx) => NextInst(c, v, v', inst, msgOps, addrFlushed, idx)
      case CacheCommunicationStep(step, idx, addr) => CacheCommunication(c, v, v', msgOps, step, idx, addr)
  }


  /////////////////////
  // UTILITY FUNCTIONS
  /////////////////////
  ghost predicate AddrNotInCache(c: Constants, v: Variables, addr: Address)
  {
    && (forall i: nat | i < |v.cache| && !v.cache[i].coh.I? :: v.cache[i].addr != addr)
  }


  // NEXT INSTRUCTION

  ghost predicate NextInst(c: Constants, v: Variables, v': Variables, inst: Instruction, msgOps: Network.MessageOps, addrFlushed: bool, idx: nat)
  {
    && v.WF(c)
    && v.pc < |c.insts|
    && c.insts[v.pc] == inst
    && msgOps.send == multiset{}
    && msgOps.recv.None?
    && match inst {
      case Load(addr, reg) =>
        && idx < |v.cache|
        && v.cache[idx].addr == addr
        && (v.cache[idx].coh.M? || v.cache[idx].coh.S?)
        && DoLoad(c, v, v', inst, idx)
      case Store(addr, val) =>
        && idx < |v.cache|
        && v.cache[idx].addr == addr
        && v.cache[idx].coh.M?
        && (val.Reg? ==> val.reg in v.regs)
        && DoStore(c, v, v', inst, idx)
      case Flush(addr) => (
        // no restrictions on idx in flush case, unused
        && addrFlushed
        && v' == v.(
          // increment PC
          pc := v.pc + 1
        )
      )
      case RMW(addr, wval, reg) => (
        && idx < |v.cache|
        && v.cache[idx].addr == addr
        && v.cache[idx].coh.M?
        && (wval.Reg? ==> wval.reg in v.regs)
        && DoRMW(c, v, v', inst, idx)
      )
      case Branch(reg, compval, target) => (
        && reg in v.regs
        && DoBranch(c, v, v', inst)
      )
    }
  }

  ghost predicate DoLoad(c: Constants, v: Variables, v': Variables, inst: Instruction, idx: nat)
    requires inst.Load?
    requires idx < |v.cache|
    requires (v.cache[idx].coh.M? || v.cache[idx].coh.S?)
  {
    v' == v.(
      // increment PC and add the result to the list
      pc := v.pc + 1,
      regs := v.regs[inst.reg := v.cache[idx].coh.val],
      results := v.results + [(inst.addr, v.cache[idx].coh.val)]
    )
  }

  ghost predicate DoStore(c: Constants, v: Variables, v': Variables, inst: Instruction, idx: nat)
    requires v.WF(c)
    requires inst.Store?
    requires inst.val.Reg? ==> inst.val.reg in v.regs
    requires idx < |v.cache|
    requires v.cache[idx].coh.M?
  {
    var val := if inst.val.Reg? then v.regs[inst.val.reg] else Just(inst.val.val/*, Some(Core(c.locs.loc.core, v.pc))*/);
    v' == v.(
      // increment PC and write the value into the entry
      pc := v.pc + 1,
      cache := v.cache[idx := v.cache[idx].(
        coh := Controller.Variables.M(val),
        dirty := true // mark as dirty
      )]
    )
  }

  ghost predicate DoRMW(c: Constants, v: Variables, v': Variables, inst: Instruction, idx: nat)
    requires v.WF(c)
    requires inst.RMW?
    requires inst.wval.Reg? ==> inst.wval.reg in v.regs
    requires idx < |v.cache|
    requires v.cache[idx].coh.M?
  {
    var val := if inst.wval.Reg? then v.regs[inst.wval.reg] else Just(inst.wval.val/*, Some(Core(c.locs.loc.core, v.pc))*/);
    v' == v.(
      // increment PC and write the value into the entry
      pc := v.pc + 1,
      regs := v.regs[inst.reg := v.cache[idx].coh.val],
      results := v.results + [(inst.addr, v.cache[idx].coh.val)],
      cache := v.cache[idx := v.cache[idx].(
        coh := Controller.Variables.M(val),
        dirty := true // mark as dirty
      )]
    )
  }

  ghost predicate DoBranch(c: Constants, v: Variables, v': Variables, inst: Instruction)
    requires inst.Branch?
    requires inst.reg in v.regs
  {
    var target := if v.regs[inst.reg] == inst.compval then v.pc + 1 else inst.target;
    // var target := if v.regs[inst.reg].MatchingVal(inst.compval) then v.pc + 1 else inst.target;
    var new_count := if v.pc >= target then v.count + 1 else v.count;
    // if equal, go to next instruction. else, jump past the branch
    v' == v.(
      pc := target,
      count := new_count
    )
  }


  ghost predicate CacheCommunication(c: Constants, v: Variables, v': Variables, msgOps: Network.MessageOps, step: Controller.Step, idx: nat, addr: Address)
  {
    && v.WF(c)
    && v'.WF(c)
    && idx < |v.cache|
    // all other entries are the same
    && (forall i: nat | i < |v.cache| && i != idx :: v.cache[i] == v'.cache[i])
    && v.results == v'.results
    && v.pc == v'.pc
    && v.count == v'.count
    && v.regs == v'.regs
    // update address afterwards to keep same address
    // need it even if evicting for transient states like IIA etc
    && v'.cache[idx].addr == addr
    // index validation
    && (match step
      case GetSStep() => (
        // addr is not in the cache
        && AddrNotInCache(c, v, addr)
        && addr in c.working_set
        && (addr.Morph? && addr.morphType.Private? ==> (addr.morphType.idx == c.locs.loc.core))
        && !v'.cache[idx].dirty
      )
      case GetMStep() => (
        // only send out a request if the next instruction is a store or RMW
        // by WF of program, the addr will thus respect private morph core
        && v.pc < |c.insts|
        && var inst := c.insts[v.pc];
        && (inst.Store? || inst.RMW?)
        && addr == inst.addr
        // index is empty or shared
        && (match v.cache[idx].coh
          case S(_) => (v.cache[idx].addr == addr)
          case I => (AddrNotInCache(c, v, addr))
          case _ => false
        )
        && !v'.cache[idx].dirty // mark it not dirty
      )
      case EvictStep() => (
        && v.cache[idx].addr == addr
        // if evicting data in M state, it must be dirty
        && (v.cache[idx].coh.M? ==> v.cache[idx].dirty)
        && v'.cache[idx].dirty == v.cache[idx].dirty // preserve dirty state in case someone needs it
        // S M enforcement handled by NextStep
      )
      case RecvMsgStep() => (
        // match addr going to recvmessage step with index
        && v.cache[idx].addr == addr
        && v'.cache[idx].dirty == v.cache[idx].dirty // preserve dirty
        && msgOps.recv.Some?
        && msgOps.recv.val.CoherenceMsg?
        && var msg := msgOps.recv.val;
        // stall till we actually do the write
        && ((msg.coh_msg.FwdGetM? || msg.coh_msg.FwdGetS?) ==> v.cache[idx].dirty)
        // all other messages aren't concerned with dirty
        // - PutAck/Stale is after enforcement
        // - Inv only happens in S state
        // - InvAck happens before data is received in M
        // - Data happens pre-data
        // addr matching the msg is handled by NextStep
      )
    )
    && Controller.NextStep(c.locs, v.cache[idx].coh, v'.cache[idx].coh, msgOps, step, addr)
  }
}