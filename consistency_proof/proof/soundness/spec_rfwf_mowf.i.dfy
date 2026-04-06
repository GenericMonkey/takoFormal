include "../../model/execution.i.dfy"
include "../../model/program.i.dfy"
include "../../model/tako_spec.i.dfy"
include "../../model/types.s.dfy"
include "invariants.i.dfy"

module RfWfMoWfProof {
  import opened Execution
  import opened Program
  import opened Types
  import opened RefinementTypes
  import opened TakoSpec
  import opened SpecConsistencyInvariants


  ghost predicate Safety(c: Constants, v: Variables) {
    && v.execution.WF()
    && v.execution.RfWf()
    && v.execution.MoWf()
  }

  ghost predicate Inv(c: Constants, v: Variables) {
    // properties
    && Safety(c, v)

    // additional invariants
    && InfoInPCTrackerMeansEventInExecution(c, v)
    && PCTrackerEnsuresUniqueEvents(c, v)
  }

  lemma InitImpliesInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
  {}


  lemma RegularLoadPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularLoadStep?
    ensures Inv(c, v')
  {

    // rf
    forall r: Event | r in v'.execution.pre.events && r.RegRead()
      ensures exists w: Event :: (
          && w in v'.execution.pre.events
          && w.RegWrite()
          && var rval := if r.R? then r.val else r.rval;
          && var wval := if w.W? then w.val else w.wval;
          && wval == rval
          && SameAddr(w.addr, r.addr)
          && (w, r) in v'.execution.wit.rf
      )
    {
      if r == step.e {
        // var w := v.eco_tracker[r.addr][step.w_idx];
        var w := step.w;
      } else {
        var w :| w in v.execution.pre.events
          && w.RegWrite()
          && var rval := if r.R? then r.val else r.rval;
          && var wval := if w.W? then w.val else w.wval;
          && SameAddr(w.addr, r.addr)
          && (w, r) in v.execution.wit.rf;
      }
    }
    assert v'.execution.RfWf();

    // mo
    assert v'.execution.wit.mo == v.execution.wit.mo;
    assert forall addr: Address :: v'.execution.WritesToAddr(addr) == v.execution.WritesToAddr(addr);
    assert v'.execution.MoWf();
  }

  lemma RegularStorePreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularStoreStep?
    ensures Inv(c, v')
  {
    // total order on mo
    forall addr: Address
      ensures Library.stricttotalorder(v'.execution.wit.mo, v'.execution.WritesToAddr(addr))
    {
      if addr == step.e.addr {
        assert v'.execution.WritesToAddr(addr) == v.execution.WritesToAddr(addr) + {step.e};
      } else {
        assert v'.execution.WritesToAddr(addr) == v.execution.WritesToAddr(addr);
      }
    }
    assert v'.execution.MoWf();
  }
  
  lemma RegularRMWPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularRMWStep?
    ensures Inv(c, v')
  {
    // rf
    forall r: Event | r in v'.execution.pre.events && r.RegRead()
      ensures exists w: Event :: (
          && w in v'.execution.pre.events
          && w.RegWrite()
          && var rval := if r.R? then r.val else r.rval;
          && var wval := if w.W? then w.val else w.wval;
          && wval == rval
          && SameAddr(w.addr, r.addr)
          && (w, r) in v'.execution.wit.rf
      )
    {
      if r == step.e {
        // var w := v.eco_tracker[r.addr][step.w_idx];
        var w := step.w;
      } else {
        var w :| w in v.execution.pre.events
          && w.RegWrite()
          && var rval := if r.R? then r.val else r.rval;
          && var wval := if w.W? then w.val else w.wval;
          && SameAddr(w.addr, r.addr)
          && (w, r) in v.execution.wit.rf;
      }
    }
    assert v'.execution.RfWf();

    // mo
    RegularRMWPreservesMoWf(c, v, v', step);
  }

  
  lemma RegularRMWPreservesMoWf(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularRMWStep?
    ensures v'.execution.MoWf()
  {
    forall addr: Address
      ensures Library.stricttotalorder(v'.execution.wit.mo, v'.execution.WritesToAddr(addr))
    {
      if addr == step.e.addr {
        assert v'.execution.WritesToAddr(addr) == v.execution.WritesToAddr(addr) + {step.e};
      } else {
        assert v'.execution.WritesToAddr(addr) == v.execution.WritesToAddr(addr);
      }
    }
    assert v'.execution.MoWf();
  }

  lemma MorphLoadPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphLoadStep?
    ensures Inv(c, v')
  {
    assert v'.execution.wit.mo == v.execution.wit.mo;
    assert forall addr: Address :: v'.execution.WritesToAddr(addr) == v.execution.WritesToAddr(addr);
    assert v'.execution.MoWf();
  }

  lemma MorphStorePreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphStoreStep?
    ensures Inv(c, v')
  {
    assert v'.execution.wit.mo == v.execution.wit.mo;
    assert forall addr: Address :: v'.execution.WritesToAddr(addr) == v.execution.WritesToAddr(addr);
    assert v'.execution.MoWf();
  }

  lemma MorphRMWPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphRMWStep?
    ensures Inv(c, v')
  {
    assert v'.execution.wit.mo == v.execution.wit.mo;
    assert forall addr: Address :: v'.execution.WritesToAddr(addr) == v.execution.WritesToAddr(addr);
    assert v'.execution.MoWf();
  }

  lemma FlushPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformFlushStep?
    ensures Inv(c, v')
  {
    assert v'.execution.wit.mo == v.execution.wit.mo;
    assert forall addr: Address :: v'.execution.WritesToAddr(addr) == v.execution.WritesToAddr(addr);
    assert v'.execution.MoWf();
  }

  lemma StartOnMissCBPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnMissCBStep?
    ensures Inv(c, v')
  {
    assert v'.execution.wit.mo == v.execution.wit.mo;
    assert forall addr: Address :: v'.execution.WritesToAddr(addr) == v.execution.WritesToAddr(addr);
    assert v'.execution.MoWf();
    assert step.e in v'.execution.pre.events;
    assert v'.pcs[step.e.info.id].pc.PC?;
    forall id : ThreadId, e : Event | (
      && id in v'.pcs
      && !v'.pcs[id].pc.End?
      && e in v'.execution.pre.events
      && e.info.id == id
    )
      ensures e.info.pc.less_than(v'.pcs[id].pc)
    {
      if id == step.e.info.id {
        if e == step.e {
          assert e.info.pc.less_than(v'.pcs[id].pc);
        } else {
          assert e.info.pc.less_than(v.pcs[id].pc);
        }
      }

    }

    assert PCTrackerEnsuresUniqueEvents(c, v');
  }

  lemma EndOnMissCBPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnMissCBStep?
    ensures Inv(c, v')
  {
    assert v'.execution.wit.mo == v.execution.wit.mo;
    assert forall addr: Address :: v'.execution.WritesToAddr(addr) == v.execution.WritesToAddr(addr);
    assert v'.execution.MoWf();
  }

  lemma StartOnEvictCBPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnEvictCBStep?
    ensures Inv(c, v')
  {
    assert v'.execution.wit.mo == v.execution.wit.mo;
    assert forall addr: Address :: v'.execution.WritesToAddr(addr) == v.execution.WritesToAddr(addr);
    assert v'.execution.MoWf();
  }

  lemma EndOnEvictCBPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures Inv(c, v')
  {
    assert v'.execution.wit.mo == v.execution.wit.mo;
    assert forall addr: Address :: v'.execution.WritesToAddr(addr) == v.execution.WritesToAddr(addr);
    assert v'.execution.MoWf();
  }

  lemma PerformBranchPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformBranchStep?
    ensures Inv(c, v')
  {
    assert v'.execution.wit.mo == v.execution.wit.mo;
    assert forall addr: Address :: v'.execution.WritesToAddr(addr) == v.execution.WritesToAddr(addr);
    assert v'.execution.MoWf();
  }

  lemma NextPreservesInv(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    var step :| NextStep(c, v, v', step);
    match step {
      case PerformRegularLoadStep(_, _, _) => {
        RegularLoadPreservesInv(c, v, v', step);
      }
      case PerformRegularStoreStep(e) => {
        RegularStorePreservesInv(c, v, v', step);
      }
      case PerformRegularRMWStep(_, _, _) => {
        RegularRMWPreservesInv(c, v, v', step);
      }
      case PerformMorphLoadStep(_, _) => {
        MorphLoadPreservesInv(c, v, v', step);
      }
      case PerformMorphStoreStep(e) => {
        MorphStorePreservesInv(c, v, v', step);
      }
      case PerformMorphRMWStep(_, _) => {
        MorphRMWPreservesInv(c, v, v', step);
      }
      case PerformFlushStep(e) => {
        FlushPreservesInv(c, v, v', step);
      }
      case StartOnMissCBStep(e) => {
        StartOnMissCBPreservesInv(c, v, v', step);
      }
      case EndOnMissCBStep(e) => {
        EndOnMissCBPreservesInv(c, v, v', step);
      }
      case StartOnEvictCBStep(e) => {
        StartOnEvictCBPreservesInv(c, v, v', step);
      }
      case EndOnEvictCBStep(e) => {
        EndOnEvictCBPreservesInv(c, v, v', step);
      }
      case PerformBranchStep(_) => {
        PerformBranchPreservesInv(c, v, v', step);
      }
    }
  }
}