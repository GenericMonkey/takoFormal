include "../../model/execution.i.dfy"
include "../../model/program.i.dfy"
include "../../model/tako_spec.i.dfy"
include "../../model/types.s.dfy"
include "invariants.i.dfy"

module CboWf8Proof {
  import opened Execution
  import opened Program
  import opened Types
  import opened TakoSpec
  import opened SpecConsistencyInvariants


  ghost predicate Safety(c: Constants, v: Variables) {
    && v.execution.WF()
    && v.execution.CboWf8()
  }

  ghost predicate Inv0(c: Constants, v: Variables)
  {
    // additional invariants
    && v.WF(c)

    && InfoInPCTrackerMeansEventInExecution(c, v)
    && PCTrackerEnsuresUniqueEvents(c, v)


    && AllEventsWellFormed(c, v)
    && IncompleteOnMissMeansMissEpoch(c, v)
    && IncompleteOnEvictMeansEvictEpoch(c, v)
  }

  ghost predicate Inv(c: Constants, v: Variables) {
    && Safety(c, v)

    && Inv0(c, v)
  }

  ////////////////////////////////////////////////
  // Inv0 lemmas
  ////////////////////////////////////////////////
  lemma RegularLoadPreservesInv0(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularLoadStep?
    ensures Inv0(c, v')
  {
    reveal Program.WF;
  }

  lemma RegularStorePreservesInv0(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularStoreStep?
    ensures Inv0(c, v')
  {}

  lemma MorphLoadPreservesInv0(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphLoadStep?
    ensures Inv0(c, v')
  {
    reveal Program.WF;
  }

  lemma MorphStorePreservesInv0(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphStoreStep?
    ensures Inv0(c, v')
  {}

  lemma FlushPreservesInv0(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformFlushStep?
    ensures Inv0(c, v')
  {}

  lemma StartOnMissCBPreservesInv0(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnMissCBStep?
    ensures Inv0(c, v')
  {}

  lemma EndOnMissCBPreservesInv0(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnMissCBStep?
    ensures Inv0(c, v')
  {}

  lemma StartOnEvictCBPreservesInv0(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnEvictCBStep?
    ensures Inv0(c, v')
  {}

  lemma EndOnEvictCBPreservesInv0(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures Inv0(c, v')
  {}

  lemma RegularRMWPreservesInv0(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularRMWStep?
    ensures Inv0(c, v')
  {
    reveal Program.WF;
  }

  lemma MorphRMWPreservesInv0(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphRMWStep?
    ensures Inv0(c, v')
  {
    reveal Program.WF;
  }

  lemma BranchPreservesInv0(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformBranchStep?
    ensures Inv0(c, v')
  {}

  ////////////////////////////////////////////////
  // Safety lemmas
  ////////////////////////////////////////////////
  lemma RegularLoadPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularLoadStep?
    ensures Safety(c, v')
  {}

  lemma RegularStorePreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularStoreStep?
    ensures Safety(c, v')
  {}

  lemma RegularRMWPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularRMWStep?
    ensures Safety(c, v')
  {}

  lemma MorphLoadPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphLoadStep?
    ensures Safety(c, v')
  {}

  lemma MorphStorePreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphStoreStep?
    ensures Safety(c, v')
  {}

  lemma MorphRMWPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphRMWStep?
    ensures Safety(c, v')
  {}

  lemma FlushPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformFlushStep?
    ensures Safety(c, v')
  {}

  lemma StartOnMissCBPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnMissCBStep?
    ensures Safety(c, v')
  {}

  lemma EndOnMissCBPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnMissCBStep?
    ensures Safety(c, v')
  {}

  lemma StartOnEvictCBPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnEvictCBStep?
    ensures Safety(c, v')
  {}

  lemma EndOnEvictCBPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures Safety(c, v')
  {}

  lemma BranchPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformBranchStep?
    ensures Safety(c, v')
  {}

  lemma NextPreservesInv(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    var step :| NextStep(c, v, v', step);
    match step {
      case PerformRegularLoadStep(_, _, _) => {
        RegularLoadPreservesInv0(c, v, v', step);
        RegularLoadPreservesSafety(c, v, v', step);
      }
      case PerformRegularStoreStep(e) => {
        RegularStorePreservesInv0(c, v, v', step);
        RegularStorePreservesSafety(c, v, v', step);
      }
      case PerformRegularRMWStep(_, _, _) => {
        RegularRMWPreservesInv0(c, v, v', step);
        RegularRMWPreservesSafety(c, v, v', step);
      }
      case PerformMorphLoadStep(_, _) => {
        MorphLoadPreservesInv0(c, v, v', step);
        MorphLoadPreservesSafety(c, v, v', step);
      }
      case PerformMorphStoreStep(e) => {
        MorphStorePreservesInv0(c, v, v', step);
        MorphStorePreservesSafety(c, v, v', step);
      }
      case PerformMorphRMWStep(e, _) => {
        MorphRMWPreservesInv0(c, v, v', step);
        MorphRMWPreservesSafety(c, v, v', step);
      }
      case PerformFlushStep(e) => {
        FlushPreservesInv0(c, v, v', step);
        FlushPreservesSafety(c, v, v', step);
      }
      case StartOnMissCBStep(e) => {
        StartOnMissCBPreservesInv0(c, v, v', step);
        StartOnMissCBPreservesSafety(c, v, v', step);
      }
      case EndOnMissCBStep(e) => {
        EndOnMissCBPreservesInv0(c, v, v', step);
        EndOnMissCBPreservesSafety(c, v, v', step);
      }
      case StartOnEvictCBStep(e) => {
        StartOnEvictCBPreservesInv0(c, v, v', step);
        StartOnEvictCBPreservesSafety(c, v, v', step);
      }
      case EndOnEvictCBStep(e) => {
        EndOnEvictCBPreservesInv0(c, v, v', step);
        EndOnEvictCBPreservesSafety(c, v, v', step);
      }
      case PerformBranchStep(id) => {
        BranchPreservesInv0(c, v, v', step);
        BranchPreservesSafety(c, v, v', step);
      }
    }
  }

  lemma InitImpliesInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
  {}

}