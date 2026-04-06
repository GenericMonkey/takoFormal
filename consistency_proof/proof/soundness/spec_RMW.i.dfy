include "../../model/execution.i.dfy"
include "../../model/program.i.dfy"
include "../../model/tako_spec.i.dfy"
include "../../model/types.s.dfy"
include "invariants.i.dfy"

module RMWProof {
  import opened Execution
  import opened Program
  import opened Types
  import opened TakoSpec
  import opened SpecConsistencyInvariants
  import opened Library

  ghost predicate Safety(c: Constants, v: Variables) {
    && v.execution.WF()
    && v.execution.RMW()
  }

  ghost predicate Inv(c: Constants, v: Variables) {
    && Safety(c, v)

    && InfoInPCTrackerMeansEventInExecution(c, v)
    && PCTrackerEnsuresUniqueEvents(c, v)
    && InitialWriteExistsForallAddr(c, v)
  }

  lemma InitImpliesInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
  {
    reveal Execution.rmwloops;
    reveal trans_closure;
  }

  lemma ExtensionIrreflexiveRf(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires !step.PerformBranchStep?
    ensures irreflexive(v'.execution.wit.rf - v.execution.wit.rf)
  {}

  
  lemma ExtensionIrreflexiveMoRf(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires !step.PerformBranchStep?
    ensures irreflexive(
      compose(
        v'.execution.wit.mo,
        v'.execution.wit.rf
      ) - 
      compose(
        v.execution.wit.mo,
        v.execution.wit.rf
      )
    )
  {}
  
  lemma ExtensionIrreflexiveMoMoRf(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires !step.PerformBranchStep?
    ensures irreflexive(
      compose(
        v'.execution.wit.mo,
        compose(
          v'.execution.wit.mo,
          inverse(v'.execution.wit.rf)
        )
      ) - 
      compose(
        v.execution.wit.mo,
        compose(
          v.execution.wit.mo,
          inverse(v.execution.wit.rf)
        )
      )
    )
  {}

  lemma ExtensionIrreflexive(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires !step.PerformBranchStep?
    ensures irreflexive(v'.execution.rmwloops() - v.execution.rmwloops())
  {
    reveal Execution.rmwloops;
    ExtensionIrreflexiveRf(c, v, v', step);
    ExtensionIrreflexiveMoRf(c, v, v', step);
    ExtensionIrreflexiveMoMoRf(c, v, v', step);
  }
  
  lemma RfMonotonic(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures v.execution.wit.rf <= v'.execution.wit.rf
  {}

  
  lemma MoRfMonotonic(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures
      compose(
        v.execution.wit.mo,
        v.execution.wit.rf
      ) <= 
      compose(
        v'.execution.wit.mo,
        v'.execution.wit.rf
      )
  {}
  
  lemma MoMoRfMonotonic(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures
      compose(
        v.execution.wit.mo,
        compose(
          v.execution.wit.mo,
          inverse(v.execution.wit.rf)
        )
      ) <=
      compose(
        v'.execution.wit.mo,
        compose(
          v'.execution.wit.mo,
          inverse(v'.execution.wit.rf)
        )
      )
  {}

  lemma RMWLoopsMonotonic(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures v.execution.rmwloops() <= v'.execution.rmwloops()
  {
    reveal Execution.rmwloops;
    RfMonotonic(c, v, v');
    MoRfMonotonic(c, v, v');
    MoMoRfMonotonic(c, v, v');
  }
  
  lemma NextPreservesInv(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    var step :| NextStep(c, v, v', step);
    if step.PerformBranchStep? {
      assert v'.execution == v.execution;
      assert v'.execution.RMW();
    } else {
      var rel := v.execution.rmwloops();
      var ext := v'.execution.rmwloops() - v.execution.rmwloops();
      ExtensionIrreflexive(c, v, v', step);
      IrreflexivePreservedUnderUnion(rel, ext);
      // irr(rel + ext)
      RMWLoopsMonotonic(c, v, v');
      UnionWithDifferenceIsSameAsUnion(rel, v'.execution.rmwloops());
      assert rel + ext == v'.execution.rmwloops();
      assert v'.execution.RMW();
    }
  }
}
  