include "../../model/execution.i.dfy"
include "../../model/program.i.dfy"
include "../../model/tako_spec.i.dfy"
include "../../model/types.s.dfy"
include "invariants.i.dfy"

module CboWf2_2Proof {
  import opened Execution
  import opened Program
  import opened Types
  import opened TakoSpec
  import opened SpecConsistencyInvariants


  ghost predicate Safety(c: Constants, v: Variables) {
    && v.execution.WF()
    && v.execution.CboWf2_2()
  }

  ghost predicate Inv(c: Constants, v: Variables) {
    && v.WF(c)
    // properties
    && Safety(c, v)

    // additional invariants
    && InfoInPCTrackerMeansEventInExecution(c, v)
    && PCTrackerEnsuresUniqueEvents(c, v)


    && AllEventsWellFormed(c, v)
    && OneIncompletePerAddress(c, v)
    && InOutEpochMeansNoIncomplete(c, v)

    && IncompleteOnEvictMeansEvictEpoch(c, v)
    && EvictEpochExistingEvents(c, v)
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
    reveal Program.WF;
  }

  lemma RegularStorePreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularStoreStep?
    ensures Inv(c, v')
  {}

  lemma MorphLoadPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphLoadStep?
    ensures Inv(c, v')
  {
    reveal Program.WF;
  }

  lemma MorphStorePreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphStoreStep?
    ensures Inv(c, v')
  {}

  lemma FlushPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformFlushStep?
    ensures Inv(c, v')
  {}

  lemma StartOnMissCBPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnMissCBStep?
    ensures Inv(c, v')
  {}

  lemma EndOnMissCBPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnMissCBStep?
    ensures Inv(c, v')
  {}

  lemma StartOnEvictCBPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnEvictCBStep?
    ensures Inv(c, v')
  {}

  lemma EndOnEvictCBPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures Inv(c, v')
  {}

  lemma RegularRMWPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularRMWStep?
    ensures Inv(c, v')
  {
    reveal Program.WF;
  }

  lemma MorphRMWPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphRMWStep?
    ensures Inv(c, v')
  {
    reveal Program.WF;
  }

  lemma BranchPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformBranchStep?
    ensures Inv(c, v')
  {}

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
      case PerformRegularStoreStep(_) => {
        RegularStorePreservesInv(c, v, v', step);
      }
      case PerformRegularRMWStep(_, _, _) => {
        RegularRMWPreservesInv(c, v, v', step);
      }
      case PerformMorphLoadStep(_, _) => {
        MorphLoadPreservesInv(c, v, v', step);
      }
      case PerformMorphStoreStep(_) => {
        MorphStorePreservesInv(c, v, v', step);
      }
      case PerformMorphRMWStep(_, _) => {
        MorphRMWPreservesInv(c, v, v', step);
      }
      case PerformFlushStep(_) => {
        FlushPreservesInv(c, v, v', step);
      }
      case StartOnMissCBStep(_) => {
        StartOnMissCBPreservesInv(c, v, v', step);
      }
      case EndOnMissCBStep(_) => {
        EndOnMissCBPreservesInv(c, v, v', step);
      }
      case StartOnEvictCBStep(_) => {
        StartOnEvictCBPreservesInv(c, v, v', step);
      }
      case EndOnEvictCBStep(_) => {
        EndOnEvictCBPreservesInv(c, v, v', step);
      }
      case PerformBranchStep(_) => {
        BranchPreservesInv(c, v, v', step);
      }
    }
  }
}