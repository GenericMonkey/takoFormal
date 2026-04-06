include "../../model/execution.i.dfy"
include "../../model/program.i.dfy"
include "../../model/tako_spec.i.dfy"
include "../../model/types.s.dfy"
include "invariants.i.dfy"

module CboWf5_1Proof {
  import opened Execution
  import opened Program
  import opened Types
  import opened TakoSpec
  import opened SpecConsistencyInvariants


  ghost predicate Safety(c: Constants, v: Variables) {
    && v.execution.WF()
    && v.execution.CboWf5_1()

  }

  ghost predicate Inv0(c: Constants, v: Variables) {
    && v.WF(c)

    && InfoInPCTrackerMeansEventInExecution(c, v)
    && PCTrackerEnsuresUniqueEvents(c, v)
    && AllEventsWellFormed(c, v)
    && IrreflexiveCbo(c, v)
    && IncompleteOnMissMeansMissEpoch(c, v)
    && IncompleteOnEvictMeansEvictEpoch(c, v)
    && MeEventsUniquePerEpoch(c, v)
  }

  ghost predicate Inv1(c: Constants, v: Variables) {
    && BookEndsOutEpoch(c, v)
    && BookEndsMissEpoch(c, v)
    && BookEndsInEpoch(c, v)
    && BookEndsEvictEpoch(c, v)

  }

  ghost predicate Inv2(c: Constants, v: Variables) {
    && LowerEpochImpliesCbo(c, v)
    && InEpochMeIsMissEnd(c, v)
    && SameEpochImpliesCbo(c, v)
    && InEpochWcbIsWriteCBorRMWCB(c, v)
    && InEpochNoWcbMeansMeIsLast(c, v)
  }

  ghost predicate Inv(c: Constants, v: Variables) {
    && Safety(c, v)

    // additional invariants
    && Inv0(c, v)

    && Inv1(c, v)
    && Inv2(c, v)
  }

  lemma InitImpliesInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
  {}

  ////////////////////////////////////////////////
  // Safety lemmas
  ////////////////////////////////////////////////

  lemma RegularLoadPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularLoadStep?
    ensures Safety(c, v')
  {
    assert v'.execution.WriteCBs() == v.execution.WriteCBs();
    assert v'.execution.ReadCBs() == v.execution.ReadCBs();
    assert v'.execution.MissEnds() == v.execution.MissEnds();
    assert v'.execution.CallbackTimeEvents() == v.execution.CallbackTimeEvents();
  }

  lemma RegularStorePreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularStoreStep?
    ensures Safety(c, v')
  {
    assert v'.execution.WriteCBs() == v.execution.WriteCBs();
    assert v'.execution.ReadCBs() == v.execution.ReadCBs();
    assert v'.execution.MissEnds() == v.execution.MissEnds();
    assert v'.execution.CallbackTimeEvents() == v.execution.CallbackTimeEvents();
  }

  lemma MorphLoadPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphLoadStep?
    ensures Safety(c, v')
  {
    assert v'.execution.WriteCBs() == v.execution.WriteCBs();
    assert v'.execution.ReadCBs() == v.execution.ReadCBs() + {step.e};
    assert v'.execution.MissEnds() == v.execution.MissEnds();
    assert v'.execution.CallbackTimeEvents() == v.execution.CallbackTimeEvents();
    var v_e := if v.epochs[step.e.addr].wcb.Some? then v.epochs[step.e.addr].wcb.val else v.epochs[step.e.addr].me;
    assert (v_e, step.e) in v'.execution.viscb() by {
      assert (v_e, step.e) in v'.execution.wit.cbo -
        Library.compose(
          v'.execution.wit.cbo,
          Library.compose(
            Library.iden(v'.execution.WriteCBs() + v'.execution.CallbackTimeEvents()),
            v'.execution.wit.cbo
          )
        );
    }

    forall x | x in v'.execution.viscb() - {(v_e, step.e)}
      ensures x in v.execution.viscb()
    {
      var v_e' := x.0;
      var rcb := x.1;
      if rcb == step.e {
        assert v_e' != v_e;
        assert v_e'.addr == rcb.addr;
        if v_e.Wcb? {
          assert (v_e', v_e) in v.execution.wit.cbo;
          assert false;
        } else {
          assert v_e.Me?;
          if v_e'.Me? {
            assert false;
          } else {
            assert v_e'.Wcb?; // ve is a M_e (none)
            assert false;
          }
        }
        // assert (v_e', v_e) in v.execution.wit.cbo;
      }
      assert (v_e', rcb) in v.execution.wit.cbo -
        Library.compose(
          v.execution.wit.cbo,
          Library.compose(
            Library.iden(v.execution.WriteCBs() + v.execution.CallbackTimeEvents()),
            v.execution.wit.cbo
          )
        );
    }
    forall x | x in v.execution.viscb()
      ensures x in v'.execution.viscb()
    {
      var v_e' := x.0;
      var rcb := x.1;
      forall e: Event | e in (v'.execution.WriteCBs() + v'.execution.CallbackTimeEvents())
        ensures !((v_e', e) in v'.execution.wit.cbo && (e, rcb) in v'.execution.wit.cbo)
      {}
      assert (v_e', rcb) in v'.execution.wit.cbo -
        Library.compose(
          v'.execution.wit.cbo,
          Library.compose(
            Library.iden(v'.execution.WriteCBs() + v'.execution.CallbackTimeEvents()),
            v'.execution.wit.cbo
          )
        );
    }
  }

  lemma MorphStorePreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphStoreStep?
    ensures Safety(c, v')
  {
    assert v'.execution.WriteCBs() == v.execution.WriteCBs() + {step.e};
    assert v'.execution.ReadCBs() == v.execution.ReadCBs();
    assert v'.execution.MissEnds() == v.execution.MissEnds();
    assert v'.execution.CallbackTimeEvents() == v.execution.CallbackTimeEvents();
    forall x | x in v'.execution.viscb()
      ensures x in v.execution.viscb()
    {
      var v_e := x.0;
      var rcb := x.1;
      assert step.e != v_e;
      assert (v_e, rcb) in v.execution.wit.cbo -
        Library.compose(
          v.execution.wit.cbo,
          Library.compose(
            Library.iden(v.execution.WriteCBs() + v.execution.CallbackTimeEvents()),
            v.execution.wit.cbo
          )
        );

    }
    forall x | x in v.execution.viscb()
      ensures x in v'.execution.viscb()
    {
      var v_e := x.0;
      var rcb := x.1;
      forall e: Event | e in (v'.execution.WriteCBs() + v'.execution.CallbackTimeEvents())
        ensures !((v_e, e) in v'.execution.wit.cbo && (e, rcb) in v'.execution.wit.cbo)
      {}
      assert (v_e, rcb) in v'.execution.wit.cbo -
        Library.compose(
          v'.execution.wit.cbo,
          Library.compose(
            Library.iden(v'.execution.WriteCBs() + v'.execution.CallbackTimeEvents()),
            v'.execution.wit.cbo
          )
        );
    }
  }

  lemma FlushPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformFlushStep?
    ensures Safety(c, v')
  {
    assert v'.execution.WriteCBs() == v.execution.WriteCBs();
    assert v'.execution.ReadCBs() == v.execution.ReadCBs();
    assert v'.execution.MissEnds() == v.execution.MissEnds();
    assert v'.execution.EvictStarts() == v.execution.EvictStarts();
    assert v'.execution.CallbackTimeEvents() == v.execution.CallbackTimeEvents();
  }

  lemma StartOnMissCBPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnMissCBStep?
    ensures Safety(c, v')
  {
    assert v'.execution.WriteCBs() == v.execution.WriteCBs();
    assert v'.execution.ReadCBs() == v.execution.ReadCBs();
    assert v'.execution.MissEnds() == v.execution.MissEnds();
    assert v'.execution.EvictStarts() == v.execution.EvictStarts();
    assert v'.execution.CallbackTimeEvents() == v.execution.CallbackTimeEvents() + {step.e};
  }

  lemma EndOnMissCBPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnMissCBStep?
    ensures Safety(c, v')
  {
    assert v'.execution.WriteCBs() == v.execution.WriteCBs();
    assert v'.execution.ReadCBs() == v.execution.ReadCBs();
    assert v'.execution.MissEnds() == v.execution.MissEnds() + {step.e};
    assert v'.execution.EvictStarts() == v.execution.EvictStarts();
    assert v'.execution.CallbackTimeEvents() == v.execution.CallbackTimeEvents() + {step.e};
    forall x | x in v'.execution.viscb()
      ensures x in v.execution.viscb()
    {
      var v_e := x.0;
      var rcb := x.1;
      assert step.e != v_e;
      assert (v_e, rcb) in v.execution.wit.cbo -
        Library.compose(
          v.execution.wit.cbo,
          Library.compose(
            Library.iden(v.execution.WriteCBs() + v.execution.CallbackTimeEvents()),
            v.execution.wit.cbo
          )
        );

    }
    forall x | x in v.execution.viscb()
      ensures x in v'.execution.viscb()
    {
      var v_e := x.0;
      var rcb := x.1;
      forall e: Event | e in (v'.execution.WriteCBs() + v'.execution.CallbackTimeEvents())
        ensures !((v_e, e) in v'.execution.wit.cbo && (e, rcb) in v'.execution.wit.cbo)
      {}
      assert (v_e, rcb) in v'.execution.wit.cbo -
        Library.compose(
          v'.execution.wit.cbo,
          Library.compose(
            Library.iden(v'.execution.WriteCBs() + v'.execution.CallbackTimeEvents()),
            v'.execution.wit.cbo
          )
        );
    }
  }

  lemma StartOnEvictCBPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnEvictCBStep?
    ensures Safety(c, v')
  {
    assert v'.execution.WriteCBs() == v.execution.WriteCBs();
    assert v'.execution.ReadCBs() == v.execution.ReadCBs();
    assert v'.execution.MissEnds() == v.execution.MissEnds();
    assert v'.execution.EvictStarts() == v.execution.EvictStarts() + {step.e};
    assert v'.execution.CallbackTimeEvents() == v.execution.CallbackTimeEvents() + {step.e};
    forall x | x in v'.execution.viscb() && x.1.CBRead()
      ensures x in v.execution.viscb()
    {
      var v_e := x.0;
      var rcb := x.1;
      assert step.e != v_e;
      assert (v_e, rcb) in v.execution.wit.cbo -
        Library.compose(
          v.execution.wit.cbo,
          Library.compose(
            Library.iden(v.execution.WriteCBs() + v.execution.CallbackTimeEvents()),
            v.execution.wit.cbo
          )
        );

    }
    forall x | x in v.execution.viscb() && x.1.CBRead()
      ensures x in v'.execution.viscb()
    {
      var v_e := x.0;
      var rcb := x.1;
      forall e: Event | e in (v'.execution.WriteCBs() + v'.execution.CallbackTimeEvents())
        ensures !((v_e, e) in v'.execution.wit.cbo && (e, rcb) in v'.execution.wit.cbo)
      {}
      assert (v_e, rcb) in v'.execution.wit.cbo -
        Library.compose(
          v'.execution.wit.cbo,
          Library.compose(
            Library.iden(v'.execution.WriteCBs() + v'.execution.CallbackTimeEvents()),
            v'.execution.wit.cbo
          )
        );
    }
  }

  lemma EndOnEvictCBPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures Safety(c, v')
  {
    assert v'.execution.WriteCBs() == v.execution.WriteCBs();
    assert v'.execution.ReadCBs() == v.execution.ReadCBs();
    assert v'.execution.MissEnds() == v.execution.MissEnds();
    assert v'.execution.EvictStarts() == v.execution.EvictStarts();
    assert v'.execution.CallbackTimeEvents() == v.execution.CallbackTimeEvents() + {step.e};
  }

  lemma RegularRMWPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularRMWStep?
    ensures Safety(c, v')
  {
    assert v'.execution.WriteCBs() == v.execution.WriteCBs();
    assert v'.execution.ReadCBs() == v.execution.ReadCBs();
    assert v'.execution.MissEnds() == v.execution.MissEnds();
    assert v'.execution.CallbackTimeEvents() == v.execution.CallbackTimeEvents();
  }

  lemma MorphRMWPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphRMWStep?
    ensures Safety(c, v')
  {
    assert v'.execution.WriteCBs() == v.execution.WriteCBs() + {step.e};
    assert v'.execution.ReadCBs() == v.execution.ReadCBs() + {step.e};
    assert v'.execution.MissEnds() == v.execution.MissEnds();
    assert v'.execution.CallbackTimeEvents() == v.execution.CallbackTimeEvents();
    var v_e := if v.epochs[step.e.addr].wcb.Some? then v.epochs[step.e.addr].wcb.val else v.epochs[step.e.addr].me;
    assert (v_e, step.e) in v'.execution.viscb() by {
      assert (v_e, step.e) in v'.execution.wit.cbo -
        Library.compose(
          v'.execution.wit.cbo,
          Library.compose(
            Library.iden(v'.execution.WriteCBs() + v'.execution.CallbackTimeEvents()),
            v'.execution.wit.cbo
          )
        );
    }

    forall x | x in v'.execution.viscb() - {(v_e, step.e)}
      ensures x in v.execution.viscb()
    {
      var v_e' := x.0;
      var rcb := x.1;
      if rcb == step.e {
        assert v_e' != v_e;
        assert v_e'.addr == rcb.addr;
        if v_e.Wcb? {
          assert (v_e', v_e) in v.execution.wit.cbo;
          assert false;
        } else {
          assert v_e.Me?;
          if v_e'.Me? {
            assert false;
          } else {
            assert v_e'.Wcb?; // ve is a M_e (none)
            assert false;
          }
        }
        // assert (v_e', v_e) in v.execution.wit.cbo;
      }
      assert (v_e', rcb) in v.execution.wit.cbo -
        Library.compose(
          v.execution.wit.cbo,
          Library.compose(
            Library.iden(v.execution.WriteCBs() + v.execution.CallbackTimeEvents()),
            v.execution.wit.cbo
          )
        );
    }
    forall x | x in v.execution.viscb()
      ensures x in v'.execution.viscb()
    {
      var v_e' := x.0;
      var rcb := x.1;
      forall e: Event | e in (v'.execution.WriteCBs() + v'.execution.CallbackTimeEvents())
        ensures !((v_e', e) in v'.execution.wit.cbo && (e, rcb) in v'.execution.wit.cbo)
      {}
      assert (v_e', rcb) in v'.execution.wit.cbo -
        Library.compose(
          v'.execution.wit.cbo,
          Library.compose(
            Library.iden(v'.execution.WriteCBs() + v'.execution.CallbackTimeEvents()),
            v'.execution.wit.cbo
          )
        );
    }
  }

  lemma BranchPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformBranchStep?
    ensures Safety(c, v')
  {
    assert v'.execution.WriteCBs() == v.execution.WriteCBs();
    assert v'.execution.ReadCBs() == v.execution.ReadCBs();
    assert v'.execution.MissEnds() == v.execution.MissEnds();
    assert v'.execution.CallbackTimeEvents() == v.execution.CallbackTimeEvents();
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

  lemma NextPreservesInv(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    var step :| NextStep(c, v, v', step);
    match step {
      case PerformRegularLoadStep(_,_,_) => {
        RegularLoadPreservesInv0(c, v, v', step);
        RegularLoadPreservesInv1(c, v, v', step);
        RegularLoadPreservesInv2(c, v, v', step);
        RegularLoadPreservesSafety(c, v, v', step);
      }
      case PerformRegularStoreStep(e) => {
        RegularStorePreservesInv0(c, v, v', step);
        RegularStorePreservesInv1(c, v, v', step);
        RegularStorePreservesInv2(c, v, v', step);
        RegularStorePreservesSafety(c, v, v', step);
      }
      case PerformRegularRMWStep(_,_,_) => {
        RegularRMWPreservesInv0(c, v, v', step);
        RegularRMWPreservesInv1(c, v, v', step);
        RegularRMWPreservesInv2(c, v, v', step);
        RegularRMWPreservesSafety(c, v, v', step);
      }
      case PerformMorphLoadStep(_,_) => {
        MorphLoadPreservesInv0(c, v, v', step);
        MorphLoadPreservesInv1(c, v, v', step);
        MorphLoadPreservesInv2(c, v, v', step);
        MorphLoadPreservesSafety(c, v, v', step);
      }
      case PerformMorphStoreStep(e) => {
        MorphStorePreservesInv0(c, v, v', step);
        MorphStorePreservesInv1(c, v, v', step);
        MorphStorePreservesInv2(c, v, v', step);
        MorphStorePreservesSafety(c, v, v', step);
      }
      case PerformMorphRMWStep(_,_) => {
        MorphRMWPreservesInv0(c, v, v', step);
        MorphRMWPreservesInv1(c, v, v', step);
        MorphRMWPreservesInv2(c, v, v', step);
        MorphRMWPreservesSafety(c, v, v', step);
      }
      case PerformFlushStep(e) => {
        FlushPreservesInv0(c, v, v', step);
        FlushPreservesInv1(c, v, v', step);
        FlushPreservesInv2(c, v, v', step);
        FlushPreservesSafety(c, v, v', step);
      }
      case StartOnMissCBStep(e) => {
        StartOnMissCBPreservesInv0(c, v, v', step);
        StartOnMissCBPreservesInv1(c, v, v', step);
        StartOnMissCBPreservesInv2(c, v, v', step);
        StartOnMissCBPreservesSafety(c, v, v', step);
      }
      case EndOnMissCBStep(e) => {
        EndOnMissCBPreservesInv0(c, v, v', step);
        EndOnMissCBPreservesInv1(c, v, v', step);
        EndOnMissCBPreservesInv2(c, v, v', step);
        EndOnMissCBPreservesSafety(c, v, v', step);
      }
      case StartOnEvictCBStep(e) => {
        StartOnEvictCBPreservesInv0(c, v, v', step);
        StartOnEvictCBPreservesInv1(c, v, v', step);
        StartOnEvictCBPreservesInv2(c, v, v', step);
        StartOnEvictCBPreservesSafety(c, v, v', step);
      }
      case EndOnEvictCBStep(e) => {
        EndOnEvictCBPreservesInv0(c, v, v', step);
        EndOnEvictCBPreservesInv1(c, v, v', step);
        EndOnEvictCBPreservesInv2(c, v, v', step);
        EndOnEvictCBPreservesSafety(c, v, v', step);
      }
      case PerformBranchStep(_) => {
        BranchPreservesInv0(c, v, v', step);
        BranchPreservesInv1(c, v, v', step);
        BranchPreservesInv2(c, v, v', step);
        BranchPreservesSafety(c, v, v', step);
      }
    }
  }
}