include "execution.i.dfy"
include "program.i.dfy"
include "types.s.dfy"

module TakoSpec {
  import opened Execution
  import opened Program
  import opened Types
  import opened RefinementTypes

  datatype Constants = Constants(
    p: Program
  ) {
    ghost predicate WF() {
      && p.WF()
    }
  }

  ////////////////////////////////////////////////////////////////////////
  // Expectations
  // CBO: Ms <nothing> Me <Wcbs/Rcbs> Es <nothing> Ee <Flush> Ms
  // Es must have Me preceding

  datatype Variables = Variables(
    epochs:map<Address, Epoch>,
    pcs:imap<ThreadId, RuntimeData>,
    execution: Execution
  ) {
    ghost predicate WF(c: Constants) {
      && c.WF()
    }
  }

  // can we build preexec + witness at same time?
  ghost predicate Init(c: Constants, v: Variables) {
    && v.WF(c)
    // all thread ids are initialized to 0, no CBs are added yet
    && v.pcs == (imap id : ThreadId | id.CoreId? && id.id < |c.p.threads| :: RuntimeData(PC(0, 0), map[], []))
    && v.execution.Init(c.p)
    && v.epochs == (map addr: Address | addr in c.p.WorkingSet() && addr.Morph? :: Out(0))
  }


  datatype Step =
    | PerformRegularLoadStep(e: Event, w: Event, reg: Register)
    | PerformRegularStoreStep(e: Event)
    | PerformRegularRMWStep(e: Event, w: Event, reg: Register)
    | PerformMorphLoadStep(e: Event, reg: Register)
    | PerformMorphStoreStep(e: Event)
    | PerformMorphRMWStep(e: Event, reg: Register)
    | PerformFlushStep(e: Event)
    | StartOnMissCBStep(e: Event)
    | EndOnMissCBStep(e: Event)
    | StartOnEvictCBStep(e: Event)
    | EndOnEvictCBStep(e: Event)
    | PerformBranchStep(id: ThreadId)

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  {
    match step {
      case PerformRegularLoadStep(e, w, reg) => PerformRegularLoad(c, v, v', e, w, reg)
      case PerformRegularStoreStep(e) => PerformRegularStore(c, v, v', e)
      case PerformRegularRMWStep(e, w, reg) => PerformRegularRMW(c, v, v', e, w, reg)
      case PerformMorphLoadStep(e, reg) => PerformMorphLoad(c, v, v', e, reg)
      case PerformMorphStoreStep(e) => PerformMorphStore(c, v, v', e)
      case PerformMorphRMWStep(e, reg) => PerformMorphRMW(c, v, v', e, reg)
      case PerformFlushStep(e) => PerformFlush(c, v, v', e)
      case StartOnMissCBStep(e) => StartOnMissCB(c, v, v', e)
      case EndOnMissCBStep(e) => EndOnMissCB(c, v, v', e)
      case StartOnEvictCBStep(e) => StartOnEvictCB(c, v, v', e)
      case EndOnEvictCBStep(e) => EndOnEvictCB(c, v, v', e)
      case PerformBranchStep(id) => PerformBranch(c, v, v', id)
    }
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables)
  {
    exists step: Step :: NextStep(c, v, v', step)
  }

  ghost predicate NextStepRefined(c: Constants, v: Variables, v': Variables, step: Step, re: RefinementEvent)
  {
    && match re {
      case PerformLoad => (
        || (step.PerformRegularLoadStep? && step.e.addr.Regular?)
        || (step.PerformMorphLoadStep? && step.e.addr.Morph?)
      )
      case PerformStore => (
        || (step.PerformRegularStoreStep? && step.e.addr.Regular?)
        || (step.PerformMorphStoreStep? && step.e.addr.Morph?)
      )
      case PerformRMW => (
        || (step.PerformRegularRMWStep? && step.e.addr.Regular?)
        || (step.PerformMorphRMWStep? && step.e.addr.Morph?)
      )
      case PerformFlush => step.PerformFlushStep?
      case PerformBranch => step.PerformBranchStep?
      case StartOnMiss => step.StartOnMissCBStep?
      case StartOnEvict => step.StartOnEvictCBStep? && step.e.Es? && !step.e.dirty
      case StartOnWriteback => step.StartOnEvictCBStep? && step.e.Es? && step.e.dirty
      case EndOnMiss => step.EndOnMissCBStep?
      case EndOnEvict => step.EndOnEvictCBStep? && step.e.Ee? && !step.e.dirty
      case EndOnWriteback => step.EndOnEvictCBStep? && step.e.Ee? && step.e.dirty
      case NoOp => false // Noop handled by Refinement Obligation Theorem
    }
    && NextStep(c, v, v', step)
  }

  ghost predicate NextRefine(c: Constants, v: Variables, v': Variables, re: RefinementEvent)
  {
    exists step: Step :: NextStepRefined(c, v, v', step, re)
  }

  // Utility Functions

  /* Check if the instruction at the ThreadInfo location in program matches the given instruction */
  ghost predicate ValidThreadInfo(c: Constants, info: ThreadInfo)
  {
    && info.pc.PC?
    && match info.id {
      case Initial() => false
      case CoreId(id) => (
        && id < |c.p.threads|
        && info.pc.pc < |c.p.threads[id]|
      )
      case CallbackId(addr, cb, _) => (
        match cb {
          case OnMiss() => (
            && addr in c.p.onMissCBs
            && info.pc.pc < |c.p.onMissCBs[addr]|
          )
          case OnEvict() => (
            && addr in c.p.onEvictCBs
            && info.pc.pc < |c.p.onEvictCBs[addr]|
          )
          case OnWriteBack() => (
            && addr in c.p.onWBCBs
            && info.pc.pc < |c.p.onWBCBs[addr]|
          )
        }
      )
    }
  }

  ghost function ProgramInstruction(c: Constants, info: ThreadInfo) : Instruction
    requires ValidThreadInfo(c, info)
  {
    match info.id {
      case Initial() => Load(Regular(0, false), Register(0))
      case CoreId(id) => c.p.threads[id][info.pc.pc]
      case CallbackId(addr, cb, _) => (
        match cb {
          case OnMiss() => c.p.onMissCBs[addr][info.pc.pc]
          case OnEvict() => c.p.onEvictCBs[addr][info.pc.pc]
          case OnWriteBack() => c.p.onWBCBs[addr][info.pc.pc]
        }
      )
    }
  }

  ghost predicate UpdateCboCommon(c: Constants, v: Variables, v': Variables, e: Event)
    requires e.info.id in v.pcs
    requires v.pcs[e.info.id].pc == e.info.pc
    requires e.info.pc.PC?
  {
    && v'.execution == v.execution.(
        pre := v.execution.pre.(events := v.execution.pre.events + {e}), // and event to pre_exec
        wit := v.execution.wit.(
          cbo := v.execution.wit.cbo
            + (set e_o: Event | e_o in v.execution.CBEventsToAddr(e.addr) :: (e_o, e))
        )
    )
  }

  ghost predicate UpdateEcoCommon(c: Constants, v: Variables, v': Variables, e: Event)
  {
    && v'.epochs == v.epochs // no change to epochs
    && v'.execution.pre.events == v.execution.pre.events + {e} // and event to pre_exec
  }

  ghost predicate UpdatePCWithVal(c: Constants, v: Variables, v': Variables, e: Event, reg: Register)
    requires e.R? || e.Rcb? || e.RMW? || e.RMWcb?
    requires e.info.id in v.pcs
    requires v.pcs[e.info.id].pc == e.info.pc
    requires e.info.pc.PC?
  {
    && var rval := if (e.RMW? || e.RMWcb?) then e.rval else e.val;
    && v'.pcs == v.pcs[e.info.id := v.pcs[e.info.id].(
      pc := v.pcs[e.info.id].pc.(pc := e.info.pc.pc + 1),
      regs := v.pcs[e.info.id].regs[ reg := rval ],
      vals := v.pcs[e.info.id].vals + [rval]
    )]
  }

  ghost predicate UpdatePCOnly(c: Constants, v: Variables, v': Variables, e: Event)
    requires e.W? || e.Wcb? || e.F?
    requires e.info.id in v.pcs
    requires v.pcs[e.info.id].pc == e.info.pc
    requires e.info.pc.PC?
  {
    && v'.pcs == v.pcs[e.info.id := v.pcs[e.info.id].(
      pc := v.pcs[e.info.id].pc.(pc := e.info.pc.pc + 1)
    )] // increment pc only
  }



  // Transition Steps

  ghost predicate PerformRegularLoad(c: Constants, v: Variables, v': Variables, r: Event, w: Event, reg: Register)
  {
    && r.R? // is a read event
    && r.addr.Regular? // is a regular address
    // bookkeeping in thread is correct
    && var info := r.info;
    && info.id in v.pcs
    && v.pcs[info.id].pc == info.pc // pc is correct for this event
    && ValidThreadInfo(c, info) // thread info is valid
    && var i := ProgramInstruction(c, info);
    && i == Load(r.addr, reg) // match a load in program
    // this index is a write
    && w.W?
    && w in v.execution.WritesToAddr(r.addr)
    // all indices after are not writes
    && (forall w' : Event | w' in v.execution.WritesToAddr(r.addr) :: !((w, w') in v.execution.wit.mo))
    // val of event matches last write to location
    && w.val == r.val
    // update
    && UpdateEcoCommon(c, v, v', r)                 // epochs, pre_exec
    && v'.execution.wit == v.execution.wit.(        // exec wit
      rf := v.execution.wit.rf + {(w, r)}
    )
    && UpdatePCWithVal(c, v, v', r, reg)            // pcs
  }

  ghost predicate PerformRegularStore(c: Constants, v: Variables, v': Variables, w: Event)
  {
    && w.W? // is a write event
    && w.addr.Regular? // is a regular address
    // bookkeeping in thread is correct
    && var info := w.info;
    && info.id in v.pcs
    && v.pcs[info.id].pc == info.pc // pc is correct for this event
    && ValidThreadInfo(c, info) // thread info is valid
    && var i := ProgramInstruction(c, info);
    && i.Store? // is a store instruction
    && i.addr == w.addr // address matches
    && (i.val.Reg? ==> i.val.reg in v.pcs[info.id].regs) // register is valid
    && var wval := if i.val.Reg? then v.pcs[info.id].regs[i.val.reg] else Just(i.val.val);
    && w.val == wval // value matches
    && w.addr in c.p.WorkingSet()
    // update
    && UpdateEcoCommon(c, v, v', w)               // epochs, pre_exec
    // mo to all previous writes
    && v'.execution.wit == v.execution.wit.(      // exec wit
      mo := v.execution.wit.mo
        + (set w_o: Event | w_o in v.execution.WritesToAddr(w.addr) :: (w_o, w))
    )
    && UpdatePCOnly(c, v, v', w)                  // pcs
  }

  ghost predicate PerformRegularRMW(c: Constants, v: Variables, v': Variables, rmw: Event, w: Event, reg: Register)
  {
    && rmw.RMW? // is a write event
    && rmw.addr.Regular? // is a regular address
    // bookkeeping in thread is correct
    && var info := rmw.info;
    && info.id in v.pcs
    && v.pcs[info.id].pc == info.pc // pc is correct for this event
    && ValidThreadInfo(c, info) // thread info is valid
    && var i := ProgramInstruction(c, info);
    && i.RMW? // is a store instruction
    && i.addr == rmw.addr // address matches
    && i.reg == reg // register matches
    && (i.wval.Reg? ==> i.wval.reg in v.pcs[info.id].regs) // register is valid
    && var wval := if i.wval.Reg? then v.pcs[info.id].regs[i.wval.reg] else Just(i.wval.val);
    && rmw.wval == wval // value matches
    // this index is a w or rmw (technically we know it is either the initial write of 0 or rmw)
    && (w.RMW? || (w.W? && w.info.id.Initial?))
    && w in v.execution.WritesToAddr(rmw.addr)
    // all indices after are not writes
    && (forall w' : Event | w' in v.execution.WritesToAddr(rmw.addr) :: !((w, w') in v.execution.wit.mo))
    // val of event matches last write to location
    && var wval := if w.RMW? then w.wval else w.val;
    && wval == rmw.rval
    && rmw.addr in c.p.WorkingSet()
    // update
    && UpdateEcoCommon(c, v, v', rmw)               // epochs, pre_exec
    // mo to all previous writes, rf to most recent write
    && v'.execution.wit == v.execution.wit.(      // exec wit
      rf := v.execution.wit.rf + {(w, rmw)},
      mo := v.execution.wit.mo
        + (set w_o: Event | w_o in v.execution.WritesToAddr(w.addr) :: (w_o, rmw))
    )
    && UpdatePCWithVal(c, v, v', rmw, reg)        // pcs
  }

  ghost predicate PerformMorphLoad(c: Constants, v: Variables, v': Variables, r: Event, reg: Register)
  {
    && r.Rcb? // is a read event
    && r.addr.Morph? // is a morph address
    && r.addr in v.epochs
    // bookkeeping in thread is correct
    && var info := r.info;
    && info.id in v.pcs
    && v.pcs[info.id].pc == info.pc // pc is correct for this event
    && ValidThreadInfo(c, info) // thread info is valid
    && var i := ProgramInstruction(c, info);
    && i == Load(r.addr, reg) // match a load in program
    // this event is a value producer
    && v.epochs[r.addr].In?
    && var val := if v.epochs[r.addr].wcb.Some? then v.epochs[r.addr].wcb.val else v.epochs[r.addr].me;
    && (val.Wcb? || val.Me?) // should be provable in theory
    // val of event matches last write to location
    && val.val == r.val
    // update
    && UpdateCboCommon(c, v, v', r)       // pre_exec, wit
    && v'.epochs == v.epochs              // epochs
    && UpdatePCWithVal(c, v, v', r, reg)  // pcs
  }

  ghost predicate PerformMorphStore(c: Constants, v: Variables, v': Variables, w: Event)
  {
    && w.Wcb? // is a write event
    && w.addr.Morph? // is a morph address
    && w.addr in v.epochs
    // bookkeeping in thread is correct
    && var info := w.info;
    && info.id in v.pcs
    && v.pcs[info.id].pc == info.pc // pc is correct for this event
    && ValidThreadInfo(c, info) // thread info is valid
    && var i := ProgramInstruction(c, info);
    && i.Store? // is a store instruction
    && i.addr == w.addr // address matches
    && (i.val.Reg? ==> i.val.reg in v.pcs[info.id].regs) // register is valid
    && var wval := if i.val.Reg? then v.pcs[info.id].regs[i.val.reg] else Just(i.val.val);
    && w.val == wval // value matches
    // this event is a value producer
    && v.epochs[w.addr].In?
    // update
    && UpdateCboCommon(c, v, v', w)
    && v'.epochs == v.epochs[w.addr := v.epochs[w.addr].(wcb := Some(w))]
    && UpdatePCOnly(c, v, v', w)
  }

  ghost predicate PerformMorphRMW(c: Constants, v: Variables, v': Variables, rmw: Event, reg: Register)
  {
    && rmw.RMWcb? // is a write event
    && rmw.addr.Morph? // is a morph address
    && rmw.addr in v.epochs
    // bookkeeping in thread is correct
    && var info := rmw.info;
    && info.id in v.pcs
    && v.pcs[info.id].pc == info.pc // pc is correct for this event
    && ValidThreadInfo(c, info) // thread info is valid
    && var i := ProgramInstruction(c, info);
    && i.RMW? // is a store instruction
    && i.addr == rmw.addr // address matches
    && i.reg == reg // register matches
    && (i.wval.Reg? ==> i.wval.reg in v.pcs[info.id].regs) // register is valid
    && var wval := if i.wval.Reg? then v.pcs[info.id].regs[i.wval.reg] else Just(i.wval.val);
    && rmw.wval == wval // value matches
    // this event is a value producer
    && v.epochs[rmw.addr].In?
    && var prev := if v.epochs[rmw.addr].wcb.Some? then v.epochs[rmw.addr].wcb.val else v.epochs[rmw.addr].me;
    && (prev.RMWcb? || prev.Me?) // should be provable in theory
    // val of event matches last write to location
    && var wval := if prev.RMWcb? then prev.wval else prev.val;
    && wval == rmw.rval
    // update
    && UpdateCboCommon(c, v, v', rmw)
    && v'.epochs == v.epochs[rmw.addr := v.epochs[rmw.addr].(wcb := Some(rmw))]
    && UpdatePCWithVal(c, v, v', rmw, reg)
  }

  ghost predicate PerformFlush(c: Constants, v: Variables, v': Variables, f: Event)
  {
    && f.F? // is a flush event
    && f.addr.Morph? // is a morph address
    && f.addr in v.epochs
    // bookkeeping in thread is correct
    && var info := f.info;
    && info.id in v.pcs
    && v.pcs[info.id].pc == info.pc // pc is correct for this event
    && ValidThreadInfo(c, info) // thread info is valid
    && var i := ProgramInstruction(c, info);
    && i == Flush(f.addr) // match a flush in program
    && v.epochs[f.addr].Out?
    // update
    && UpdateCboCommon(c, v, v', f)
    && v'.epochs == v.epochs
    && UpdatePCOnly(c, v, v', f)
  }

  ghost predicate StartOnMissCB(c: Constants, v: Variables, v': Variables, cb: Event)
  {
    && cb.Ms?
    && cb.addr in v.epochs
    && cb.addr in c.p.onMissCBs // address has a callback
    // bookkeeping in thread is correct
    && cb.WF()
    && var info := cb.info;
    && v.epochs[cb.addr].Out?
    && info.id.count == v.epochs[cb.addr].epoch
    // we can't have this one in the tracker already
    && !(info.id in v.pcs)
    // update
    && v' == v.(
      epochs := v.epochs[cb.addr := Miss(v.epochs[cb.addr].epoch)], // set epoch to miss
      pcs := v.pcs[info.id := RuntimeData(PC(0, 0), map[], [])], // set pc to 0
      execution := v.execution.(
        pre := v.execution.pre.(events := v.execution.pre.events + {cb}), // and event to pre_exec
        wit := v.execution.wit.(
          cbo := v.execution.wit.cbo
            + (set e_o: Event | e_o in v.execution.CBEventsToAddr(cb.addr) :: (e_o, cb))
        )
      )
    )
  }

  ghost predicate EndOnMissCB(c: Constants, v: Variables, v': Variables, cb: Event)
  {
    && cb.Me?
    && cb.addr in v.epochs
    && cb.addr in c.p.onMissCBs // address has a callback
    // bookkeeping in thread is correct
    && cb.WF()
    && var info := cb.info;
    // have this one in the tracker with pc full
    && info.id in v.pcs
    && v.pcs[info.id].pc.PC?
    && v.pcs[info.id].pc.pc == |c.p.onMissCBs[cb.addr]| // pc is at end
    && cb.val == Transform(v.pcs[info.id].vals) // val is the transformed value
    // update
    && v' == v.(
      epochs := v.epochs[cb.addr := In(v.epochs[cb.addr].epoch, cb, None)], // set epoch to In, Me is value producer
      pcs := v.pcs[info.id := v.pcs[info.id].(pc := End())], // set pc to end
      execution := v.execution.(
        pre := v.execution.pre.(events := v.execution.pre.events + {cb}), // and event to pre_exec
        wit := v.execution.wit.(
          cbo := v.execution.wit.cbo
            + (set e_o: Event | e_o in v.execution.CBEventsToAddr(cb.addr) :: (e_o, cb))
        )
      )
    )
  }

  ghost predicate StartOnEvictCB(c: Constants, v: Variables, v': Variables, cb: Event)
  {
    && cb.Es?
    && cb.addr in v.epochs
    && cb.addr in (if cb.dirty then c.p.onWBCBs else c.p.onEvictCBs)
    // bookkeeping in thread is correct
    && cb.WF()
    && var info := cb.info;
    && v.epochs[cb.addr].In?
    && info.id.count == v.epochs[cb.addr].epoch
    // no intervening evictions should allow us to prove we don't need to check for opposite dirty polarity
    && !(info.id in v.pcs)
    && (
      if cb.dirty then (
        && v.epochs[cb.addr].wcb.Some?
        && v.epochs[cb.addr].wcb.val.CBWrite()
        && cb.val == if v.epochs[cb.addr].wcb.val.Wcb? then 
          v.epochs[cb.addr].wcb.val.val
        else 
          v.epochs[cb.addr].wcb.val.wval 
      ) else (
        && v.epochs[cb.addr].wcb.None?
        && v.epochs[cb.addr].me.Me?
        && cb.val == v.epochs[cb.addr].me.val
      )
    )
    // update
    && v' == v.(
      epochs := v.epochs[cb.addr := Evict(v.epochs[cb.addr].epoch, cb.val, cb.dirty)], // set epoch to evict
      pcs := v.pcs[info.id := RuntimeData(PC(0, 0), map[EvictReg() := cb.val], [])], // set pc to 0
      execution := v.execution.(
        pre := v.execution.pre.(events := v.execution.pre.events + {cb}), // and event to pre_exec
        wit := v.execution.wit.(
          cbo := v.execution.wit.cbo
            + (set e_o: Event | e_o in v.execution.CBEventsToAddr(cb.addr) :: (e_o, cb))
        )
      )
    )
  }

  ghost predicate EndOnEvictCB(c: Constants, v: Variables, v': Variables, cb: Event)
  {
    && cb.Ee?
    && cb.addr in (if cb.dirty then c.p.onWBCBs else c.p.onEvictCBs) // address has a callback
    && cb.addr in v.epochs
    // bookkeeping in thread is correct
    && cb.WF()
    && var info := cb.info;
    // have this one in the tracker with pc full
    && info.id in v.pcs
    && var inst_count := if cb.dirty then |c.p.onWBCBs[cb.addr]| else |c.p.onEvictCBs[cb.addr]|;
    && v.pcs[info.id].pc.PC?
    && v.pcs[info.id].pc.pc == inst_count // pc is at end
    // update
    && v' == v.(
      pcs := v.pcs[info.id := v.pcs[info.id].(pc := End())], // set pc to end
      epochs := v.epochs[cb.addr := Out(v.epochs[cb.addr].epoch + 1)], // increment epoch
      execution := v.execution.(
        pre := v.execution.pre.(events := v.execution.pre.events + {cb}), // and event to pre_exec
        wit := v.execution.wit.(
          cbo := v.execution.wit.cbo
            + (set e_o: Event | e_o in v.execution.CBEventsToAddr(cb.addr) :: (e_o, cb))
        )
      )
    )
  }

  ghost predicate PerformBranch(c: Constants, v: Variables, v': Variables, id: ThreadId)
  {
    && id in v.pcs
    && v.pcs[id].pc.PC?
    && ValidThreadInfo(c, ThreadInfo(id, v.pcs[id].pc)) // thread info is valid
    && var i := ProgramInstruction(c, ThreadInfo(id, v.pcs[id].pc));
    && i.Branch?
    && i.reg in v.pcs[id].regs
    && var val := if i.reg in v.pcs[id].regs then v.pcs[id].regs[i.reg] else Just(0);
    && var target := if val == i.compval then v.pcs[id].pc.pc + 1 else i.target;
    && var count := if v.pcs[id].pc.pc >= target then v.pcs[id].pc.count + 1 else v.pcs[id].pc.count;
    && v' == v.(
      pcs := v.pcs[id := v.pcs[id].(pc := PC(target, count))]
    )
  }
}