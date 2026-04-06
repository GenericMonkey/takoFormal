include "../../model/execution.i.dfy"
include "../../model/program.i.dfy"
include "../../model/tako_spec.i.dfy"
include "../../model/types.s.dfy"
include "invariants.i.dfy"

module CboWf2_1Proof {
  import opened Execution
  import opened Program
  import opened Types
  import opened TakoSpec
  import opened SpecConsistencyInvariants


  ghost predicate Safety(c: Constants, v: Variables) {
    && v.execution.WF()
    && v.execution.CboWf2_1()

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

    && IncompleteOnMissMeansMissEpoch(c, v)
    && MissEpochExistingEvents(c, v)
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
  {}

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
  {}

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
  {}

  lemma MorphRMWPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphRMWStep?
    ensures Inv(c, v')
  {}

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
      case PerformRegularLoadStep(e, w_idx, _) => {
        RegularLoadPreservesInv(c, v, v', step);
      }
      case PerformRegularStoreStep(e) => {
        RegularStorePreservesInv(c, v, v', step);
      }
      case PerformRegularRMWStep(e, w, _) => {
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
      case PerformBranchStep(id) => {
        BranchPreservesInv(c, v, v', step);
      }
    }
  }
}