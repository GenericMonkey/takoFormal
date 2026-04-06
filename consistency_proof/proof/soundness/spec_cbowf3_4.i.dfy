include "../../model/execution.i.dfy"
include "../../model/program.i.dfy"
include "../../model/tako_spec.i.dfy"
include "../../model/types.s.dfy"
include "invariants.i.dfy"

module CboWf3_4Proof {
  import opened Execution
  import opened Program
  import opened Types
  import opened TakoSpec
  import opened SpecConsistencyInvariants

  ghost predicate Alt(c: Constants, v: Variables) {
    forall es1: Event, es2: Event | WFEvictStart(c, v, es1) && WFEvictStart(c, v, es2) && (es1, es2) in v.execution.wit.cbo ::
      exists ee: Event :: (
        && WFEvictEnd(c, v, ee)
        && (es1, ee) in v.execution.pre.thd()
        && (ee, es2) in v.execution.wit.cbo
      )
  }



  ghost predicate Safety(c: Constants, v: Variables) {
    && v.execution.WF()
    && Alt(c, v)
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

  ghost predicate Inv1(c: Constants, v: Variables)
  {
    && BookEndsOutEpoch(c, v)
    && BookEndsMissEpoch(c, v)
    && BookEndsInEpoch(c, v)
    && BookEndsEvictEpoch(c, v)
  }

  ghost predicate Inv2(c: Constants, v: Variables)
  {
    && EvictEpochExistingEventsN(c, v)
    && LowerEpochExistingEventsN(c, v)
    && InEpochExistingEventsN(c, v)
    && MissEpochExistingEventsN(c, v)
  }

  ghost predicate Inv3(c: Constants, v: Variables)
  {
    && LowerEpochImpliesCbo(c, v)
    && SameEpochImpliesCbo(c, v)
  }

  ghost predicate Inv(c: Constants, v: Variables) {
    && Safety(c, v)

    && Inv0(c, v)

    && Inv1(c, v)

    && Inv2(c, v)

    && Inv3(c, v)
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
  // Inv1 lemmas
  ////////////////////////////////////////////////
  lemma RegularLoadPreservesInv1(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularLoadStep?
    ensures Inv1(c, v')
  {}

  lemma RegularStorePreservesInv1(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularStoreStep?
    ensures Inv1(c, v')
  {}

  lemma MorphLoadPreservesInv1(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphLoadStep?
    ensures Inv1(c, v')
  {}

  lemma MorphStorePreservesInv1(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphStoreStep?
    ensures Inv1(c, v')
  {}

  lemma FlushPreservesInv1(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformFlushStep?
    ensures Inv1(c, v')
  {}

  lemma StartOnMissCBPreservesInv1(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnMissCBStep?
    ensures Inv1(c, v')
  {}

  lemma EndOnMissCBPreservesInv1(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnMissCBStep?
    ensures Inv1(c, v')
  {}

  lemma StartOnEvictCBPreservesInv1(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnEvictCBStep?
    ensures Inv1(c, v')
  {}

  lemma EndOnEvictCBPreservesInv1(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures Inv1(c, v')
  {}

  lemma RegularRMWPreservesInv1(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularRMWStep?
    ensures Inv1(c, v')
  {}

  lemma MorphRMWPreservesInv1(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphRMWStep?
    ensures Inv1(c, v')
  {}

  lemma BranchPreservesInv1(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformBranchStep?
    ensures Inv1(c, v')
  {}

  ////////////////////////////////////////////////
  // Inv2 lemmas
  ////////////////////////////////////////////////

  lemma RegularLoadPreservesInv2(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularLoadStep?
    ensures Inv2(c, v')
  {}

  lemma RegularStorePreservesInv2(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularStoreStep?
    ensures Inv2(c, v')
  {}

  lemma MorphLoadPreservesInv2(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphLoadStep?
    ensures Inv2(c, v')
  {}

  lemma MorphStorePreservesInv2(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphStoreStep?
    ensures Inv2(c, v')
  {}

  lemma FlushPreservesInv2(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformFlushStep?
    ensures Inv2(c, v')
  {}

  lemma StartOnMissCBPreservesInv2(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnMissCBStep?
    ensures Inv2(c, v')
  {}

  lemma EndOnMissCBPreservesInv2(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnMissCBStep?
    ensures Inv2(c, v')
  {}

  lemma StartOnEvictCBPreservesInv2(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnEvictCBStep?
    ensures Inv2(c, v')
  {}

  lemma EndOnEvictCBPreservesInv2(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures Inv2(c, v')
  {}

  lemma RegularRMWPreservesInv2(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularRMWStep?
    ensures Inv2(c, v')
  {}

  lemma MorphRMWPreservesInv2(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphRMWStep?
    ensures Inv2(c, v')
  {}

  lemma BranchPreservesInv2(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformBranchStep?
    ensures Inv2(c, v')
  {}


  ////////////////////////////////////////////////
  // Inv3 lemmas
  ////////////////////////////////////////////////

  lemma RegularLoadPreservesInv3(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularLoadStep?
    ensures Inv3(c, v')
  {
    // assert v'.execution.CboWf3_1();
  }

  lemma RegularStorePreservesInv3(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularStoreStep?
    ensures Inv3(c, v')
  {
    // assert v'.execution.CboWf3_1();
  }

  lemma MorphLoadPreservesInv3(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphLoadStep?
    ensures Inv3(c, v')
  {
    // assert v'.execution.CboWf3_1();
  }

  lemma MorphStorePreservesInv3(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphStoreStep?
    ensures Inv3(c, v')
  {
    // assert v'.execution.CboWf3_1();
  }

  lemma FlushPreservesInv3(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformFlushStep?
    ensures Inv3(c, v')
  {
    // assert v'.execution.CboWf3_1();
  }

  lemma StartOnMissCBPreservesInv3(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnMissCBStep?
    ensures Inv3(c, v')
  {
  }

  lemma EndOnMissCBPreservesInv3(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnMissCBStep?
    ensures Inv3(c, v')
  {}

  lemma StartOnEvictCBPreservesInv3(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnEvictCBStep?
    ensures Inv3(c, v')
  {
  }

  lemma EndOnEvictCBPreservesInv3(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures Inv3(c, v')
  {
  }

  lemma RegularRMWPreservesInv3(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularRMWStep?
    ensures Inv3(c, v')
  {}

  lemma MorphRMWPreservesInv3(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphRMWStep?
    ensures Inv3(c, v')
  {}

  lemma BranchPreservesInv3(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformBranchStep?
    ensures Inv3(c, v')
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
  {
    forall es1: Event | WFEvictStart(c, v', es1) && WFEvictStart(c, v', step.e) && (es1, step.e) in v'.execution.wit.cbo
      ensures exists ee: Event :: (
        && WFEvictEnd(c, v', ee)
        && (es1, ee) in v'.execution.pre.thd()
        && (ee, step.e) in v'.execution.wit.cbo
      )
    {
      assert es1.info.id.count < v.epochs[es1.addr].epoch;
      if es1.dirty {
        assert es1.info.id == CallbackId(es1.addr, OnWriteBack(), es1.info.id.count);
      } else {
        assert es1.info.id == CallbackId(es1.addr, OnEvict(), es1.info.id.count);
      }
    }
  }

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
        RegularLoadPreservesInv1(c, v, v', step);
        RegularLoadPreservesInv2(c, v, v', step);
        RegularLoadPreservesInv3(c, v, v', step);
        RegularLoadPreservesSafety(c, v, v', step);
      }
      case PerformRegularStoreStep(e) => {
        RegularStorePreservesInv0(c, v, v', step);
        RegularStorePreservesInv1(c, v, v', step);
        RegularStorePreservesInv2(c, v, v', step);
        RegularStorePreservesInv3(c, v, v', step);
        RegularStorePreservesSafety(c, v, v', step);
      }
      case PerformRegularRMWStep(_, _, _) => {
        RegularRMWPreservesInv0(c, v, v', step);
        RegularRMWPreservesInv1(c, v, v', step);
        RegularRMWPreservesInv2(c, v, v', step);
        RegularRMWPreservesInv3(c, v, v', step);
        RegularRMWPreservesSafety(c, v, v', step);
      }
      case PerformMorphLoadStep(_, _) => {
        MorphLoadPreservesInv0(c, v, v', step);
        MorphLoadPreservesInv1(c, v, v', step);
        MorphLoadPreservesInv2(c, v, v', step);
        MorphLoadPreservesInv3(c, v, v', step);
        MorphLoadPreservesSafety(c, v, v', step);
      }
      case PerformMorphStoreStep(e) => {
        MorphStorePreservesInv0(c, v, v', step);
        MorphStorePreservesInv1(c, v, v', step);
        MorphStorePreservesInv2(c, v, v', step);
        MorphStorePreservesInv3(c, v, v', step);
        MorphStorePreservesSafety(c, v, v', step);
      }
      case PerformMorphRMWStep(e, _) => {
        MorphRMWPreservesInv0(c, v, v', step);
        MorphRMWPreservesInv1(c, v, v', step);
        MorphRMWPreservesInv2(c, v, v', step);
        MorphRMWPreservesInv3(c, v, v', step);
        MorphRMWPreservesSafety(c, v, v', step);
      }
      case PerformFlushStep(e) => {
        FlushPreservesInv0(c, v, v', step);
        FlushPreservesInv1(c, v, v', step);
        FlushPreservesInv2(c, v, v', step);
        FlushPreservesInv3(c, v, v', step);
        FlushPreservesSafety(c, v, v', step);
      }
      case StartOnMissCBStep(e) => {
        StartOnMissCBPreservesInv0(c, v, v', step);
        StartOnMissCBPreservesInv1(c, v, v', step);
        StartOnMissCBPreservesInv2(c, v, v', step);
        StartOnMissCBPreservesInv3(c, v, v', step);
        StartOnMissCBPreservesSafety(c, v, v', step);
      }
      case EndOnMissCBStep(e) => {
        EndOnMissCBPreservesInv0(c, v, v', step);
        EndOnMissCBPreservesInv1(c, v, v', step);
        EndOnMissCBPreservesInv2(c, v, v', step);
        EndOnMissCBPreservesInv3(c, v, v', step);
        EndOnMissCBPreservesSafety(c, v, v', step);
      }
      case StartOnEvictCBStep(e) => {
        StartOnEvictCBPreservesInv0(c, v, v', step);
        StartOnEvictCBPreservesInv1(c, v, v', step);
        StartOnEvictCBPreservesInv2(c, v, v', step);
        StartOnEvictCBPreservesInv3(c, v, v', step);
        StartOnEvictCBPreservesSafety(c, v, v', step);
      }
      case EndOnEvictCBStep(e) => {
        EndOnEvictCBPreservesInv0(c, v, v', step);
        EndOnEvictCBPreservesInv1(c, v, v', step);
        EndOnEvictCBPreservesInv2(c, v, v', step);
        EndOnEvictCBPreservesInv3(c, v, v', step);
        EndOnEvictCBPreservesSafety(c, v, v', step);
      }
      case PerformBranchStep(id) => {
        BranchPreservesInv0(c, v, v', step);
        BranchPreservesInv1(c, v, v', step);
        BranchPreservesInv2(c, v, v', step);
        BranchPreservesInv3(c, v, v', step);
        BranchPreservesSafety(c, v, v', step);
      }
    }
  }


  lemma AltImpliesCboWf3_4(c: Constants, v: Variables)
    requires Alt(c, v)
    requires AllEventsWellFormed(c, v)
    ensures v.execution.CboWf3_4()
  {
    forall x : (Event, Event) | (x in Library.compose(
        Library.iden(v.execution.EvictStarts()),
        Library.compose(
          v.execution.wit.cbo,
          Library.iden(v.execution.EvictStarts())
        )
      ))
      ensures x in
      Library.compose(
        Library.iden(v.execution.EvictStarts()),
        Library.compose(
          Library.intersection(
            v.execution.pre.thd(),
            Library.prod(
              (v.execution.EvictStarts()),
              (v.execution.EvictEnds())
            )
          ),
          Library.compose(
            v.execution.wit.cbo,
            Library.iden(v.execution.EvictStarts())
          )
        )
      )
    {
      var es1 := x.0;
      var es2 := x.1;
      assert WFEvictStart(c, v, es1);
      assert WFEvictStart(c, v, es2);
      var ee :| (
        && WFEvictEnd(c, v, ee)
        && (es1, ee) in v.execution.pre.thd()
        && (ee, es2) in v.execution.wit.cbo
      );
    }
  }

  lemma InitImpliesInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
  {}

  lemma InvImpliesSafety(c: Constants, v: Variables)
    requires Inv(c, v)
    ensures v.execution.CboWf3_4()
  {
    AltImpliesCboWf3_4(c, v);
  }
}