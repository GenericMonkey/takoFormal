include "../../model/execution.i.dfy"
include "../../model/program.i.dfy"
include "../../model/tako_spec.i.dfy"
include "../../model/types.s.dfy"
include "invariants.i.dfy"

module CohProof {
  import opened Execution
  import opened Program
  import opened Types
  import opened TakoSpec
  import opened SpecConsistencyInvariants
  import opened Library

  ghost predicate Safety(c: Constants, v: Variables) {
    && v.execution.WF()
    && v.execution.Coh()
    && v.execution.MoWf2()
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
    reveal trans_closure;
    reveal compose_n;
  }

  ////////////////////////////////////////////
  // New Event Range for HB
  ////////////////////////////////////////////
  lemma SbEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires !step.PerformBranchStep?
    ensures range(v'.execution.pre.sb() - v.execution.pre.sb()) <= {step.e}
  {}

  lemma InitToNoninitEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires !step.PerformBranchStep?
    ensures range(v'.execution.init_to_noninit() - v.execution.init_to_noninit()) <= {step.e}
  {}

  lemma PerformRegularLoadStepVfEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularLoadStep?
    ensures range(v'.execution.vf() - v.execution.vf()) <= {step.e}
  {
    assert v.execution.MissEnds() == v'.execution.MissEnds();
    assert v.execution.CallbackMemEvents() == v'.execution.CallbackMemEvents();
    assert v.execution.CallbackTimeEvents() == v'.execution.CallbackTimeEvents();
  }

  lemma PerformRegularStoreStepVfEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularStoreStep?
    ensures range(v'.execution.vf() - v.execution.vf()) <= {step.e}
  {
    assert v.execution.MissEnds() == v'.execution.MissEnds();
    assert v.execution.CallbackMemEvents() == v'.execution.CallbackMemEvents();
    assert v.execution.CallbackTimeEvents() == v'.execution.CallbackTimeEvents();
  }

  lemma PerformRegularRMWStepVfEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularRMWStep?
    ensures range(v'.execution.vf() - v.execution.vf()) <= {step.e}
  {
    assert v.execution.MissEnds() == v'.execution.MissEnds();
    assert v.execution.CallbackMemEvents() == v'.execution.CallbackMemEvents();
    assert v.execution.CallbackTimeEvents() == v'.execution.CallbackTimeEvents();
  }

  lemma PerformMorphAccessVfEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphLoadStep? || step.PerformMorphStoreStep? || step.PerformMorphRMWStep?
    ensures range(v'.execution.vf() - v.execution.vf()) <= {step.e}
  {
    assert v'.execution.MissEnds() == v.execution.MissEnds();
    assert v'.execution.CallbackMemEvents() == v.execution.CallbackMemEvents() + {step.e};
    assert v'.execution.CallbackTimeEvents() == v.execution.CallbackTimeEvents();
    forall x | x in v'.execution.vf() - v.execution.vf()
      ensures x.1 == step.e
    {
      var me := x.0;
      var rw := x.1;
      if rw != step.e {
        assert (me, rw) in v'.execution.vf();
        assert !((me, rw) in v.execution.vf());
        assert (me, rw) in v'.execution.wit.cbo;
        if (me, rw) in v.execution.wit.cbo {
          assert (me, rw) in Library.prod(v.execution.MissEnds(), v.execution.CallbackMemEvents());
          assert (me, rw) in Library.compose(
            v.execution.wit.cbo,
            Library.compose(
              Library.iden(v.execution.CallbackTimeEvents()),
              v.execution.wit.cbo
            )
          );
          assert false;
        }
      }
    }
  }

  lemma PerformFlushStepVfEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformFlushStep?
    ensures range(v'.execution.vf() - v.execution.vf()) <= {step.e}
  {
    assert v.execution.MissEnds() == v'.execution.MissEnds();
    assert v.execution.CallbackMemEvents() == v'.execution.CallbackMemEvents();
    assert v.execution.CallbackTimeEvents() == v'.execution.CallbackTimeEvents();
  }

  lemma StartOnMissCBStepVfEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnMissCBStep?
    ensures range(v'.execution.vf() - v.execution.vf()) <= {step.e}
  {
    assert v'.execution.MissEnds() == v.execution.MissEnds();
    assert v'.execution.CallbackMemEvents() == v.execution.CallbackMemEvents();
    assert v'.execution.CallbackTimeEvents() == v.execution.CallbackTimeEvents() + {step.e};
  }

  lemma EndOnMissCBStepVfEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnMissCBStep?
    ensures range(v'.execution.vf() - v.execution.vf()) <= {step.e}
  {
    assert v'.execution.MissEnds() == v.execution.MissEnds() + {step.e};
    assert v'.execution.CallbackMemEvents() == v.execution.CallbackMemEvents();
    assert v'.execution.CallbackTimeEvents() == v.execution.CallbackTimeEvents() + {step.e};
    forall x | x in v'.execution.vf()
      ensures x in v.execution.vf()
    {
      var me := x.0;
      var rwcb := x.1;
      assert me != step.e;
      assert ((me, rwcb) in v.execution.wit.cbo - Library.compose(v.execution.wit.cbo, Library.compose(Library.iden(v.execution.CallbackTimeEvents()), v.execution.wit.cbo)));
    }

  }

  lemma StartOnEvictCBStepVfEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnEvictCBStep?
    ensures range(v'.execution.vf() - v.execution.vf()) <= {step.e}
  {
    assert v'.execution.MissEnds() == v.execution.MissEnds();
    assert v'.execution.CallbackMemEvents() == v.execution.CallbackMemEvents();
    assert v'.execution.CallbackTimeEvents() == v.execution.CallbackTimeEvents() + {step.e};
  }

  lemma EndOnEvictCBStepVfEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures range(v'.execution.vf() - v.execution.vf()) <= {step.e}
  {
    assert v'.execution.MissEnds() == v.execution.MissEnds();
    assert v'.execution.CallbackMemEvents() == v.execution.CallbackMemEvents();
    assert v'.execution.CallbackTimeEvents() == v.execution.CallbackTimeEvents() + {step.e};
  }

  lemma VfEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires !step.PerformBranchStep?
    ensures range(v'.execution.vf() - v.execution.vf()) <= {step.e}
  {
    match step {
      case PerformRegularLoadStep(_, _, _) => {
        PerformRegularLoadStepVfEdgesHaveNewEventRange(c, v, v', step);
      }
      case PerformRegularStoreStep(e) => {
        PerformRegularStoreStepVfEdgesHaveNewEventRange(c, v, v', step);
      }
      case PerformRegularRMWStep(_, _, _) => {
        PerformRegularRMWStepVfEdgesHaveNewEventRange(c, v, v', step);
      }
      case PerformMorphLoadStep(_, _) => {
        PerformMorphAccessVfEdgesHaveNewEventRange(c, v, v', step);
      }
      case PerformMorphStoreStep(e) => {
        PerformMorphAccessVfEdgesHaveNewEventRange(c, v, v', step);
      }
      case PerformMorphRMWStep(_, _) => {
        PerformMorphAccessVfEdgesHaveNewEventRange(c, v, v', step);
      }
      case PerformFlushStep(e) => {
        PerformFlushStepVfEdgesHaveNewEventRange(c, v, v', step);
      }
      case StartOnMissCBStep(e) => {
        StartOnMissCBStepVfEdgesHaveNewEventRange(c, v, v', step);
      }
      case EndOnMissCBStep(e) => {
        EndOnMissCBStepVfEdgesHaveNewEventRange(c, v, v', step);
      }
      case StartOnEvictCBStep(e) => {
        StartOnEvictCBStepVfEdgesHaveNewEventRange(c, v, v', step);
      }
      case EndOnEvictCBStep(e) => {
        EndOnEvictCBStepVfEdgesHaveNewEventRange(c, v, v', step);
      }
      case PerformBranchStep(_) => {
        assert false;
      }
    }
  }

  lemma MeEsEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires !step.PerformBranchStep?
    ensures range(v'.execution.me_es() - v.execution.me_es()) <= {step.e}
  {}

  lemma EeMsEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires !step.PerformBranchStep?
    ensures range(v'.execution.ee_ms() - v.execution.ee_ms()) <= {step.e}
  {}

  lemma PerformRegularLoadStepEbEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularLoadStep?
    ensures range(v'.execution.eb() - v.execution.eb()) <= {step.e}
  {
    assert v.execution.EvictEnds() == v'.execution.EvictEnds();
    assert v.execution.Flushes() == v'.execution.Flushes();
    assert v.execution.CallbackTimeEvents() == v'.execution.CallbackTimeEvents();
  }

  lemma PerformRegularStoreStepEbEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularStoreStep?
    ensures range(v'.execution.eb() - v.execution.eb()) <= {step.e}
  {
    assert v.execution.EvictEnds() == v'.execution.EvictEnds();
    assert v.execution.Flushes() == v'.execution.Flushes();
    assert v.execution.CallbackTimeEvents() == v'.execution.CallbackTimeEvents();
  }

  lemma PerformRegularRMWStepEbEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularRMWStep?
    ensures range(v'.execution.eb() - v.execution.eb()) <= {step.e}
  {
    assert v.execution.EvictEnds() == v'.execution.EvictEnds();
    assert v.execution.Flushes() == v'.execution.Flushes();
    assert v.execution.CallbackTimeEvents() == v'.execution.CallbackTimeEvents();
  }

  lemma PerformMorphLoadStepEbEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphLoadStep?
    ensures range(v'.execution.eb() - v.execution.eb()) <= {step.e}
  {
    assert v.execution.EvictEnds() == v'.execution.EvictEnds();
    assert v.execution.Flushes() == v'.execution.Flushes();
    assert v.execution.CallbackTimeEvents() == v'.execution.CallbackTimeEvents();
  }

  lemma PerformMorphStoreStepEbEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphStoreStep?
    ensures range(v'.execution.eb() - v.execution.eb()) <= {step.e}
  {
    assert v.execution.EvictEnds() == v'.execution.EvictEnds();
    assert v.execution.Flushes() == v'.execution.Flushes();
    assert v.execution.CallbackTimeEvents() == v'.execution.CallbackTimeEvents();
  }

  lemma PerformMorphRMWStepEbEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphRMWStep?
    ensures range(v'.execution.eb() - v.execution.eb()) <= {step.e}
  {
    assert v.execution.EvictEnds() == v'.execution.EvictEnds();
    assert v.execution.Flushes() == v'.execution.Flushes();
    assert v.execution.CallbackTimeEvents() == v'.execution.CallbackTimeEvents();
  }

  lemma PerformFlushStepEbEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformFlushStep?
    ensures range(v'.execution.eb() - v.execution.eb()) <= {step.e}
  {
    assert v.execution.EvictEnds() == v'.execution.EvictEnds();
    assert v'.execution.Flushes() == v.execution.Flushes() + {step.e};
    assert v.execution.CallbackTimeEvents() == v'.execution.CallbackTimeEvents();
    forall x | x in v'.execution.eb() - v.execution.eb()
      ensures x.1 == step.e
    {
      var me := x.0;
      var rw := x.1;
      if rw != step.e {
        assert (me, rw) in v'.execution.eb();
        assert !((me, rw) in v.execution.eb());
        assert (me, rw) in v'.execution.wit.cbo;
        if (me, rw) in v.execution.wit.cbo {
          assert (me, rw) in Library.prod(v.execution.EvictEnds(), v.execution.Flushes());
          assert (me, rw) in Library.compose(
            v.execution.wit.cbo,
            Library.compose(
              Library.iden(v.execution.CallbackTimeEvents()),
              v.execution.wit.cbo
            )
          );
          assert false;
        }
      }
    }
  }

  lemma StartOnMissCBStepEbEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnMissCBStep?
    ensures range(v'.execution.eb() - v.execution.eb()) <= {step.e}
  {
    assert v'.execution.EvictEnds() == v.execution.EvictEnds();
    assert v'.execution.Flushes() == v.execution.Flushes();
    assert v'.execution.CallbackTimeEvents() == v.execution.CallbackTimeEvents() + {step.e};
  }

  lemma EndOnMissCBStepEbEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnMissCBStep?
    ensures range(v'.execution.eb() - v.execution.eb()) <= {step.e}
  {
    assert v'.execution.EvictEnds() == v.execution.EvictEnds();
    assert v'.execution.Flushes() == v.execution.Flushes();
    assert v'.execution.CallbackTimeEvents() == v.execution.CallbackTimeEvents() + {step.e};
  }

  lemma StartOnEvictCBStepEbEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnEvictCBStep?
    ensures range(v'.execution.eb() - v.execution.eb()) <= {step.e}
  {
    assert v'.execution.EvictEnds() == v.execution.EvictEnds();
    assert v'.execution.Flushes() == v.execution.Flushes();
    assert v'.execution.CallbackTimeEvents() == v.execution.CallbackTimeEvents() + {step.e};
  }

  lemma EndOnEvictCBStepEbEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures range(v'.execution.eb() - v.execution.eb()) <= {step.e}
  {
    assert v'.execution.EvictEnds() == v.execution.EvictEnds() + {step.e};
    assert v'.execution.Flushes() == v.execution.Flushes();
    assert v'.execution.CallbackTimeEvents() == v.execution.CallbackTimeEvents() + {step.e};
    forall x | x in v'.execution.eb()
      ensures x in v.execution.eb()
    {
      var ee := x.0;
      var f := x.1;
      assert ee != step.e;
      assert ((ee, f) in v.execution.wit.cbo - Library.compose(v.execution.wit.cbo, Library.compose(Library.iden(v.execution.CallbackTimeEvents()), v.execution.wit.cbo)));
    }
  }


  lemma EbEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires !step.PerformBranchStep?
    ensures range(v'.execution.eb() - v.execution.eb()) <= {step.e}
  {
    match step {
      case PerformRegularLoadStep(_, _, _) => {
        PerformRegularLoadStepEbEdgesHaveNewEventRange(c, v, v', step);
      }
      case PerformRegularStoreStep(e) => {
        PerformRegularStoreStepEbEdgesHaveNewEventRange(c, v, v', step);
      }
      case PerformRegularRMWStep(_, _, _) => {
        PerformRegularRMWStepEbEdgesHaveNewEventRange(c, v, v', step);
      }
      case PerformMorphLoadStep(_, _) => {
        PerformMorphLoadStepEbEdgesHaveNewEventRange(c, v, v', step);
      }
      case PerformMorphStoreStep(e) => {
        PerformMorphStoreStepEbEdgesHaveNewEventRange(c, v, v', step);
      }
      case PerformMorphRMWStep(_, _) => {
        PerformMorphRMWStepEbEdgesHaveNewEventRange(c, v, v', step);
      }
      case PerformFlushStep(e) => {
        PerformFlushStepEbEdgesHaveNewEventRange(c, v, v', step);
      }
      case StartOnMissCBStep(e) => {
        StartOnMissCBStepEbEdgesHaveNewEventRange(c, v, v', step);
      }
      case EndOnMissCBStep(e) => {
        EndOnMissCBStepEbEdgesHaveNewEventRange(c, v, v', step);
      }
      case StartOnEvictCBStep(e) => {
        StartOnEvictCBStepEbEdgesHaveNewEventRange(c, v, v', step);
      }
      case EndOnEvictCBStep(e) => {
        EndOnEvictCBStepEbEdgesHaveNewEventRange(c, v, v', step);
      }
      case PerformBranchStep(_) => {
        assert false;
      }
    }
  }

  lemma SwEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires !step.PerformBranchStep?
    ensures range(v'.execution.sw() - v.execution.sw()) <= {step.e}
  {}

  lemma AllNewEdgesHaveNewEventRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires !step.PerformBranchStep?
    ensures range(v'.execution.hb_components() - v.execution.hb_components()) <= {step.e}
  {
    reveal Execution.hb_components;
    SbEdgesHaveNewEventRange(c, v, v', step);
    InitToNoninitEdgesHaveNewEventRange(c, v, v', step);
    VfEdgesHaveNewEventRange(c, v, v', step);
    MeEsEdgesHaveNewEventRange(c, v, v', step);
    EeMsEdgesHaveNewEventRange(c, v, v', step);
    EbEdgesHaveNewEventRange(c, v, v', step);
    SwEdgesHaveNewEventRange(c, v, v', step);
  }

  ////////////////////////////////////////////
  // Monotonicity for HB
  ////////////////////////////////////////////
  lemma SbMonotonic(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures v.execution.pre.sb() <= v'.execution.pre.sb()
  {}
  
  lemma InitToNoninitMonotonic(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures v.execution.init_to_noninit() <= v'.execution.init_to_noninit()
  {}

  lemma VfMonotonic(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures v.execution.vf() <= v'.execution.vf()
  {
    forall x | x in v.execution.vf()
      ensures x in v'.execution.vf()
    {
      var ee := x.0;
      var f := x.1;
      assert (ee, f) in v'.execution.wit.cbo;
      assert (ee, f) in v'.execution.wit.cbo -
        Library.compose(
          v'.execution.wit.cbo,
          Library.compose(
            Library.iden(v'.execution.CallbackTimeEvents()),
            v'.execution.wit.cbo
          )
      );
    }
  }

  lemma MeEsMonotonic(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures v.execution.me_es() <= v'.execution.me_es()
  {}

  lemma EeMsMonotonic(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures v.execution.ee_ms() <= v'.execution.ee_ms()
  {}

  lemma EbMonotonic(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures v.execution.eb() <= v'.execution.eb()
  {
    forall x | x in v.execution.eb()
      ensures x in v'.execution.eb()
    {
      var ee := x.0;
      var f := x.1;
      assert (ee, f) in v'.execution.wit.cbo;
      assert (ee, f) in v'.execution.wit.cbo -
        Library.compose(
          v'.execution.wit.cbo,
          Library.compose(
            Library.iden(v'.execution.CallbackTimeEvents()),
            v'.execution.wit.cbo
          )
      );
    }
  }

  lemma SwMonotonic(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures v.execution.sw() <= v'.execution.sw()
  {}

  lemma HbComponentsMonotonic(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures v.execution.hb_components() <= v'.execution.hb_components()
  {
    reveal Execution.hb_components;
    SbMonotonic(c, v, v');
    InitToNoninitMonotonic(c, v, v');
    VfMonotonic(c, v, v');
    MeEsMonotonic(c, v, v');
    EeMsMonotonic(c, v, v');
    EbMonotonic(c, v, v');
    SwMonotonic(c, v, v');
  }

  ////////////////////////////////////////////
  // New Event Range for ECO
  ////////////////////////////////////////////
  lemma RegularLoadPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularLoadStep?
    ensures range(v'.execution.rfmofr() - v.execution.rfmofr()) <= {step.e}
  {
    forall x | x in v'.execution.fr()
      ensures x in v.execution.fr()
    {
      if x.0 == step.e {
        var w_mid :| (w_mid, x.0) in v'.execution.wit.rf && (w_mid, x.1) in v'.execution.wit.mo;
        assert w_mid == step.w;
        assert x.1 in v'.execution.WritesToAddr(step.e.addr);
        assert false;
      }
    }
  }

  lemma RegularStorePreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularStoreStep?
    ensures range(v'.execution.rfmofr() - v.execution.rfmofr()) <= {step.e}
  {}

  lemma RegularRMWPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularRMWStep?
    ensures range(v'.execution.rfmofr() - v.execution.rfmofr()) <= {step.e}
  {}

  lemma MorphLoadPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphLoadStep?
    ensures range(v'.execution.rfmofr() - v.execution.rfmofr()) <= {step.e}
  {}

  lemma MorphStorePreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphStoreStep?
    ensures range(v'.execution.rfmofr() - v.execution.rfmofr()) <= {step.e}
  {}

  lemma MorphRMWPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphRMWStep?
    ensures range(v'.execution.rfmofr() - v.execution.rfmofr()) <= {step.e}
  {}

  lemma FlushPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformFlushStep?
    ensures range(v'.execution.rfmofr() - v.execution.rfmofr()) <= {step.e}
  {}

  lemma StartOnMissCBPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnMissCBStep?
    ensures range(v'.execution.rfmofr() - v.execution.rfmofr()) <= {step.e}
  {}

  lemma EndOnMissCBPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnMissCBStep?
    ensures range(v'.execution.rfmofr() - v.execution.rfmofr()) <= {step.e}
  {}

  lemma StartOnEvictCBPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnEvictCBStep?
    ensures range(v'.execution.rfmofr() - v.execution.rfmofr()) <= {step.e}
  {}

  lemma EndOnEvictCBPreservesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures range(v'.execution.rfmofr() - v.execution.rfmofr()) <= {step.e}
  {}


  lemma AllNewEdgesHaveNewEventRangeRfMoFr(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires !step.PerformBranchStep?
    ensures range(v'.execution.rfmofr() - v.execution.rfmofr()) <= {step.e}
  {
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
        assert false;
      }
    }
  }

  ////////////////////////////////////////////
  // Rrmofr Monotonic
  ////////////////////////////////////////////
  lemma RfMoFrMonotonic(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures v.execution.rfmofr() <= v'.execution.rfmofr()
  {
    reveal Execution.rfmofr;
  }

  ////////////////////////////////////////////
  // Rrmofr Growth looks correct
  ////////////////////////////////////////////
  lemma RMWEventDomRangeRrMoFr'Wellformed(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularRMWStep?
    ensures ((step.e in dom(v'.execution.rfmofr())) ==> AllPairsIdentity(v'.execution.rfmofr(), step.e))
  {
    reveal AllPairsIdentity;
  }

  lemma NewEventDomRangeRrMoFr'Wellformed(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires !step.PerformBranchStep?
    ensures ((step.e in dom(v'.execution.rfmofr())) ==> AllPairsIdentity(v'.execution.rfmofr(), step.e))
  {
    match step {
      case PerformRegularLoadStep(_, _, _) => {
        assert !(step.e in dom(v'.execution.wit.rf));
        assert !(step.e in dom(v'.execution.wit.mo));
        assert !(step.e in dom(v'.execution.fr()));
      }
      case PerformRegularStoreStep(e) => {
        assert !(step.e in dom(v'.execution.wit.rf));
        assert !(step.e in dom(v'.execution.wit.mo));
        assert !(step.e in dom(v'.execution.fr()));
      }
      case PerformRegularRMWStep(_, _, _) => {
        RMWEventDomRangeRrMoFr'Wellformed(c, v, v', step);
      }
      case PerformMorphLoadStep(_, _) => {
        assert !(step.e in dom(v'.execution.wit.rf));
        assert !(step.e in dom(v'.execution.wit.mo));
        assert !(step.e in dom(v'.execution.fr()));
      }
      case PerformMorphStoreStep(e) => {
        assert !(step.e in dom(v'.execution.wit.rf));
        assert !(step.e in dom(v'.execution.wit.mo));
        assert !(step.e in dom(v'.execution.fr()));
      }
      case PerformMorphRMWStep(_, _) => {
        assert !(step.e in dom(v'.execution.wit.rf));
        assert !(step.e in dom(v'.execution.wit.mo));
        assert !(step.e in dom(v'.execution.fr()));
      }
      case PerformFlushStep(e) => {
        assert !(step.e in dom(v'.execution.wit.rf));
        assert !(step.e in dom(v'.execution.wit.mo));
        assert !(step.e in dom(v'.execution.fr()));
      }
      case StartOnMissCBStep(e) => {
        assert !(step.e in dom(v'.execution.wit.rf));
        assert !(step.e in dom(v'.execution.wit.mo));
        assert !(step.e in dom(v'.execution.fr()));
      }
      case EndOnMissCBStep(e) => {
        assert !(step.e in dom(v'.execution.wit.rf));
        assert !(step.e in dom(v'.execution.wit.mo));
        assert !(step.e in dom(v'.execution.fr()));
      }
      case StartOnEvictCBStep(e) => {
        assert !(step.e in dom(v'.execution.wit.rf));
        assert !(step.e in dom(v'.execution.wit.mo));
        assert !(step.e in dom(v'.execution.fr()));
      }
      case EndOnEvictCBStep(e) => {
        assert !(step.e in dom(v'.execution.wit.rf));
        assert !(step.e in dom(v'.execution.wit.mo));
        assert !(step.e in dom(v'.execution.fr()));
      }
      case PerformBranchStep(_) => {
        assert false;
      }
    }
  }

  ////////////////////////////////////////////
  // hb_components growth looks correct
  ////////////////////////////////////////////
  
  lemma PerformRegularLoadEventNotInDomHbComponents'(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularLoadStep?
    ensures 
      && !(step.e in dom(v'.execution.hb_components()))  
  {
    reveal Execution.hb_components;
    assert !(step.e in dom(v'.execution.pre.sb()));
    assert !(step.e in dom(v'.execution.init_to_noninit()));
    assert !(step.e in dom(v'.execution.vf()));
    assert !(step.e in dom(v'.execution.me_es()));
    assert !(step.e in dom(v'.execution.ee_ms()));
    assert !(step.e in dom(v'.execution.eb()));
    assert !(step.e in dom(v'.execution.sw()));
  }

  lemma PerformRegularStoreEventNotInDomHbComponents'(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularStoreStep?
    ensures 
      && !(step.e in dom(v'.execution.hb_components()))
  {
    reveal Execution.hb_components;
    assert !(step.e in dom(v'.execution.pre.sb()));
    assert !(step.e in dom(v'.execution.init_to_noninit()));
    assert !(step.e in dom(v'.execution.vf()));
    assert !(step.e in dom(v'.execution.me_es()));
    assert !(step.e in dom(v'.execution.ee_ms()));
    assert !(step.e in dom(v'.execution.eb()));
    assert !(step.e in dom(v'.execution.sw()));
  }

  lemma PerformRegularRMWEventNotInDomHbComponents'(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularRMWStep?
    ensures 
      && !(step.e in dom(v'.execution.hb_components()))
  {
    reveal Execution.hb_components;
    assert !(step.e in dom(v'.execution.pre.sb()));
    assert !(step.e in dom(v'.execution.init_to_noninit()));
    assert !(step.e in dom(v'.execution.vf()));
    assert !(step.e in dom(v'.execution.me_es()));
    assert !(step.e in dom(v'.execution.ee_ms()));
    assert !(step.e in dom(v'.execution.eb()));
    assert !(step.e in dom(v'.execution.sw()));
  }

  lemma PerformMorphLoadEventNotInDomHbComponents'(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphLoadStep?
    ensures 
      && !(step.e in dom(v'.execution.hb_components()))
  {
    reveal Execution.hb_components;
    assert !(step.e in dom(v'.execution.pre.sb()));
    assert !(step.e in dom(v'.execution.init_to_noninit()));
    assert !(step.e in dom(v'.execution.vf()));
    assert !(step.e in dom(v'.execution.me_es()));
    assert !(step.e in dom(v'.execution.ee_ms()));
    assert !(step.e in dom(v'.execution.eb()));
    assert !(step.e in dom(v'.execution.sw()));
  }

  lemma PerformMorphStoreEventNotInDomHbComponents'(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphStoreStep?
    ensures 
      && !(step.e in dom(v'.execution.hb_components()))
  {
    reveal Execution.hb_components;
    assert !(step.e in dom(v'.execution.pre.sb()));
    assert !(step.e in dom(v'.execution.init_to_noninit()));
    assert !(step.e in dom(v'.execution.vf()));
    assert !(step.e in dom(v'.execution.me_es()));
    assert !(step.e in dom(v'.execution.ee_ms()));
    assert !(step.e in dom(v'.execution.eb()));
    assert !(step.e in dom(v'.execution.sw()));
  }

  lemma PerformMorphRMWEventNotInDomHbComponents'(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphRMWStep?
    ensures 
      && !(step.e in dom(v'.execution.hb_components()))
  {
    reveal Execution.hb_components;
    assert !(step.e in dom(v'.execution.pre.sb()));
    assert !(step.e in dom(v'.execution.init_to_noninit()));
    assert !(step.e in dom(v'.execution.vf()));
    assert !(step.e in dom(v'.execution.me_es()));
    assert !(step.e in dom(v'.execution.ee_ms()));
    assert !(step.e in dom(v'.execution.eb()));
    assert !(step.e in dom(v'.execution.sw()));
  }

  lemma PerformFlushEventNotInDomHbComponents'(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformFlushStep?
    ensures 
      && !(step.e in dom(v'.execution.hb_components()))
  {
    reveal Execution.hb_components;
    assert !(step.e in dom(v'.execution.pre.sb()));
    assert !(step.e in dom(v'.execution.init_to_noninit()));
    assert !(step.e in dom(v'.execution.vf()));
    assert !(step.e in dom(v'.execution.me_es()));
    assert !(step.e in dom(v'.execution.ee_ms()));
    assert !(step.e in dom(v'.execution.eb()));
    assert !(step.e in dom(v'.execution.sw()));
  }

  lemma StartOnMissCBEventNotInDomHbComponents'(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnMissCBStep?
    ensures 
      && !(step.e in dom(v'.execution.hb_components()))
  {
    reveal Execution.hb_components;
    assert !(step.e in dom(v'.execution.pre.sb()));
    assert !(step.e in dom(v'.execution.init_to_noninit()));
    assert !(step.e in dom(v'.execution.vf()));
    assert !(step.e in dom(v'.execution.me_es()));
    assert !(step.e in dom(v'.execution.ee_ms()));
    assert !(step.e in dom(v'.execution.eb()));
    assert !(step.e in dom(v'.execution.sw()));
  }

  lemma EndOnMissCBEventNotInDomHbComponents'(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnMissCBStep?
    ensures 
      && !(step.e in dom(v'.execution.hb_components()))
  {
    reveal Execution.hb_components;
    assert !(step.e in dom(v'.execution.pre.sb()));
    assert !(step.e in dom(v'.execution.init_to_noninit()));
    assert !(step.e in dom(v'.execution.vf()));
    assert !(step.e in dom(v'.execution.me_es()));
    assert !(step.e in dom(v'.execution.ee_ms()));
    assert !(step.e in dom(v'.execution.eb()));
    assert !(step.e in dom(v'.execution.sw()));
  }

  lemma StartOnEvictCBEventNotInDomHbComponents'(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnEvictCBStep?
    ensures 
      && !(step.e in dom(v'.execution.hb_components()))
  {
    reveal Execution.hb_components;
    assert !(step.e in dom(v'.execution.pre.sb()));
    assert !(step.e in dom(v'.execution.init_to_noninit()));
    assert !(step.e in dom(v'.execution.vf()));
    assert !(step.e in dom(v'.execution.me_es()));
    assert !(step.e in dom(v'.execution.ee_ms()));
    assert !(step.e in dom(v'.execution.eb()));
    assert !(step.e in dom(v'.execution.sw()));
  }

  lemma EndOnEvictCBEventNotInDomSb'(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures 
      && !(step.e in dom(v'.execution.pre.sb()))
  {}

  lemma EndOnEvictCBEventNotInDomInitToNoninit'(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures 
      && !(step.e in dom(v'.execution.init_to_noninit()))
  {}

  lemma EndOnEvictCBEventNotInDomVf'(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures 
      && !(step.e in dom(v'.execution.vf()))
  {}

  lemma EndOnEvictCBEventNotInDomMeEs'(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures 
      && !(step.e in dom(v'.execution.me_es()))
  {}

  lemma EndOnEvictCBEventNotInDomEeMs'(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures 
      && !(step.e in dom(v'.execution.ee_ms()))
  {}

  lemma EndOnEvictCBEventNotInDomEb'(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures 
      && !(step.e in dom(v'.execution.eb()))
  {}

  lemma EndOnEvictCBEventNotInDomSw'(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures 
      && !(step.e in dom(v'.execution.sw()))
  {}

  lemma EndOnEvictCBEventNotInDomHbComponents'(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures 
      && !(step.e in dom(v'.execution.hb_components()))
  {
    reveal Execution.hb_components;
    EndOnEvictCBEventNotInDomSb'(c, v, v', step);
    EndOnEvictCBEventNotInDomInitToNoninit'(c, v, v', step);
    EndOnEvictCBEventNotInDomVf'(c, v, v', step);
    EndOnEvictCBEventNotInDomMeEs'(c, v, v', step);
    EndOnEvictCBEventNotInDomEeMs'(c, v, v', step);
    EndOnEvictCBEventNotInDomEb'(c, v, v', step);
    EndOnEvictCBEventNotInDomSw'(c, v, v', step);
  }
  
  lemma NewEventNotInDomHbComponents'(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires !step.PerformBranchStep?
    ensures 
      && !(step.e in dom(v'.execution.hb_components()))  
  {
    match step {
      case PerformRegularLoadStep(_, _, _) => {
        PerformRegularLoadEventNotInDomHbComponents'(c, v, v', step);
      }
      case PerformRegularStoreStep(e) => {
        PerformRegularStoreEventNotInDomHbComponents'(c, v, v', step);
      }
      case PerformRegularRMWStep(_, _, _) => {
        PerformRegularRMWEventNotInDomHbComponents'(c, v, v', step);
      }
      case PerformMorphLoadStep(_, _) => {
        PerformMorphLoadEventNotInDomHbComponents'(c, v, v', step);
      }
      case PerformMorphStoreStep(e) => {
        PerformMorphStoreEventNotInDomHbComponents'(c, v, v', step);
      }
      case PerformMorphRMWStep(_, _) => {
        PerformMorphRMWEventNotInDomHbComponents'(c, v, v', step);
      }
      case PerformFlushStep(e) => {
        PerformFlushEventNotInDomHbComponents'(c, v, v', step);
      }
      case StartOnMissCBStep(e) => {
        StartOnMissCBEventNotInDomHbComponents'(c, v, v', step);
      }
      case EndOnMissCBStep(e) => {
        EndOnMissCBEventNotInDomHbComponents'(c, v, v', step);
      }
      case StartOnEvictCBStep(e) => {
        StartOnEvictCBEventNotInDomHbComponents'(c, v, v', step);
      }
      case EndOnEvictCBStep(e) => {
        EndOnEvictCBEventNotInDomHbComponents'(c, v, v', step);
      }
      case PerformBranchStep(_) => {
        assert false;
      }
    }
  }

  ////////////////////////////////////////////
  // event not in original hb_c
  ////////////////////////////////////////////
  lemma PerformRegularLoadEventNotInDomHbComponents(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularLoadStep?
    ensures 
      && !(step.e in dom(v.execution.hb_components()))  
  {
    reveal Execution.hb_components;
    assert !(step.e in dom(v.execution.pre.sb()));
    assert !(step.e in dom(v.execution.init_to_noninit()));
    assert !(step.e in dom(v.execution.vf()));
    assert !(step.e in dom(v.execution.me_es()));
    assert !(step.e in dom(v.execution.ee_ms()));
    assert !(step.e in dom(v.execution.eb()));
    assert !(step.e in dom(v.execution.sw()));
  }

  lemma PerformRegularStoreEventNotInDomHbComponents(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularStoreStep?
    ensures 
      && !(step.e in dom(v.execution.hb_components()))
  {
    reveal Execution.hb_components;
    assert !(step.e in dom(v.execution.pre.sb()));
    assert !(step.e in dom(v.execution.init_to_noninit()));
    assert !(step.e in dom(v.execution.vf()));
    assert !(step.e in dom(v.execution.me_es()));
    assert !(step.e in dom(v.execution.ee_ms()));
    assert !(step.e in dom(v.execution.eb()));
    assert !(step.e in dom(v.execution.sw()));
  }

  lemma PerformRegularRMWEventNotInDomHbComponents(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularRMWStep?
    ensures 
      && !(step.e in dom(v.execution.hb_components()))
  {
    reveal Execution.hb_components;
    assert !(step.e in dom(v.execution.pre.sb()));
    assert !(step.e in dom(v.execution.init_to_noninit()));
    assert !(step.e in dom(v.execution.vf()));
    assert !(step.e in dom(v.execution.me_es()));
    assert !(step.e in dom(v.execution.ee_ms()));
    assert !(step.e in dom(v.execution.eb()));
    assert !(step.e in dom(v.execution.sw()));
  }

  lemma PerformMorphLoadEventNotInDomHbComponents(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphLoadStep?
    ensures 
      && !(step.e in dom(v.execution.hb_components()))
  {
    reveal Execution.hb_components;
    assert !(step.e in dom(v.execution.pre.sb()));
    assert !(step.e in dom(v.execution.init_to_noninit()));
    assert !(step.e in dom(v.execution.vf()));
    assert !(step.e in dom(v.execution.me_es()));
    assert !(step.e in dom(v.execution.ee_ms()));
    assert !(step.e in dom(v.execution.eb()));
    assert !(step.e in dom(v.execution.sw()));
  }

  lemma PerformMorphStoreEventNotInDomHbComponents(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphStoreStep?
    ensures 
      && !(step.e in dom(v.execution.hb_components()))
  {
    reveal Execution.hb_components;
    assert !(step.e in dom(v.execution.pre.sb()));
    assert !(step.e in dom(v.execution.init_to_noninit()));
    assert !(step.e in dom(v.execution.vf()));
    assert !(step.e in dom(v.execution.me_es()));
    assert !(step.e in dom(v.execution.ee_ms()));
    assert !(step.e in dom(v.execution.eb()));
    assert !(step.e in dom(v.execution.sw()));
  }

  lemma PerformMorphRMWEventNotInDomHbComponents(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphRMWStep?
    ensures 
      && !(step.e in dom(v.execution.hb_components()))
  {
    reveal Execution.hb_components;
    assert !(step.e in dom(v.execution.pre.sb()));
    assert !(step.e in dom(v.execution.init_to_noninit()));
    assert !(step.e in dom(v.execution.vf()));
    assert !(step.e in dom(v.execution.me_es()));
    assert !(step.e in dom(v.execution.ee_ms()));
    assert !(step.e in dom(v.execution.eb()));
    assert !(step.e in dom(v.execution.sw()));
  }

  lemma PerformFlushEventNotInDomHbComponents(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformFlushStep?
    ensures 
      && !(step.e in dom(v.execution.hb_components()))
  {
    reveal Execution.hb_components;
    assert !(step.e in dom(v.execution.pre.sb()));
    assert !(step.e in dom(v.execution.init_to_noninit()));
    assert !(step.e in dom(v.execution.vf()));
    assert !(step.e in dom(v.execution.me_es()));
    assert !(step.e in dom(v.execution.ee_ms()));
    assert !(step.e in dom(v.execution.eb()));
    assert !(step.e in dom(v.execution.sw()));
  }

  lemma StartOnMissCBEventNotInDomHbComponents(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnMissCBStep?
    ensures 
      && !(step.e in dom(v.execution.hb_components()))
  {
    reveal Execution.hb_components;
    assert !(step.e in dom(v.execution.pre.sb()));
    assert !(step.e in dom(v.execution.init_to_noninit()));
    assert !(step.e in dom(v.execution.vf()));
    assert !(step.e in dom(v.execution.me_es()));
    assert !(step.e in dom(v.execution.ee_ms()));
    assert !(step.e in dom(v.execution.eb()));
    assert !(step.e in dom(v.execution.sw()));
  }

  lemma EndOnMissCBEventNotInDomHbComponents(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnMissCBStep?
    ensures 
      && !(step.e in dom(v.execution.hb_components()))
  {
    reveal Execution.hb_components;
    assert !(step.e in dom(v.execution.pre.sb()));
    assert !(step.e in dom(v.execution.init_to_noninit()));
    assert !(step.e in dom(v.execution.vf()));
    assert !(step.e in dom(v.execution.me_es()));
    assert !(step.e in dom(v.execution.ee_ms()));
    assert !(step.e in dom(v.execution.eb()));
    assert !(step.e in dom(v.execution.sw()));
  }

  lemma StartOnEvictCBEventNotInDomHbComponents(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnEvictCBStep?
    ensures 
      && !(step.e in dom(v.execution.hb_components()))
  {
    reveal Execution.hb_components;
    assert !(step.e in dom(v.execution.pre.sb()));
    assert !(step.e in dom(v.execution.init_to_noninit()));
    assert !(step.e in dom(v.execution.vf()));
    assert !(step.e in dom(v.execution.me_es()));
    assert !(step.e in dom(v.execution.ee_ms()));
    assert !(step.e in dom(v.execution.eb()));
    assert !(step.e in dom(v.execution.sw()));
  }
  
  lemma EndOnEvictCBEventNotInDomSb(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures 
      && !(step.e in dom(v.execution.pre.sb()))
  {}

  lemma EndOnEvictCBEventNotInDomInitToNonInit(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures 
      && !(step.e in dom(v.execution.init_to_noninit()))
  {}

  lemma EndOnEvictCBEventNotInDomVf(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures 
      && !(step.e in dom(v.execution.vf()))
  {}

  lemma EndOnEvictCBEventNotInDomMeEs(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures 
      && !(step.e in dom(v.execution.me_es()))
  {}

  lemma EndOnEvictCBEventNotInDomEeMs(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures 
      && !(step.e in dom(v.execution.ee_ms()))
  {}

  lemma EndOnEvictCBEventNotInDomEb(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures 
      && !(step.e in dom(v.execution.eb()))
  {}

  lemma EndOnEvictCBEventNotInDomSw(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures 
      && !(step.e in dom(v.execution.sw()))
  {}

  lemma EndOnEvictCBEventNotInDomHbComponents(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures 
      && !(step.e in dom(v.execution.hb_components()))
  {
    reveal Execution.hb_components;
    EndOnEvictCBEventNotInDomSb(c, v, v', step);
    EndOnEvictCBEventNotInDomInitToNonInit(c, v, v', step);
    EndOnEvictCBEventNotInDomVf(c, v, v', step);
    EndOnEvictCBEventNotInDomMeEs(c, v, v', step);
    EndOnEvictCBEventNotInDomEeMs(c, v, v', step);
    EndOnEvictCBEventNotInDomEb(c, v, v', step);
    EndOnEvictCBEventNotInDomSw(c, v, v', step);
  }

  lemma NewEventNotInDomHbComponents(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires !step.PerformBranchStep?
    ensures 
      && !(step.e in dom(v.execution.hb_components()))  
  {
    match step {
      case PerformRegularLoadStep(_, _, _) => {
        PerformRegularLoadEventNotInDomHbComponents(c, v, v', step);
      }
      case PerformRegularStoreStep(e) => {
        PerformRegularStoreEventNotInDomHbComponents(c, v, v', step);
      }
      case PerformRegularRMWStep(_, _, _) => {
        PerformRegularRMWEventNotInDomHbComponents(c, v, v', step);
      }
      case PerformMorphLoadStep(_, _) => {
        PerformMorphLoadEventNotInDomHbComponents(c, v, v', step);
      }
      case PerformMorphStoreStep(e) => {
        PerformMorphStoreEventNotInDomHbComponents(c, v, v', step);
      }
      case PerformMorphRMWStep(_, _) => {
        PerformMorphRMWEventNotInDomHbComponents(c, v, v', step);
      }
      case PerformFlushStep(e) => {
        PerformFlushEventNotInDomHbComponents(c, v, v', step);
      }
      case StartOnMissCBStep(e) => {
        StartOnMissCBEventNotInDomHbComponents(c, v, v', step);
      }
      case EndOnMissCBStep(e) => {
        EndOnMissCBEventNotInDomHbComponents(c, v, v', step);
      }
      case StartOnEvictCBStep(e) => {
        StartOnEvictCBEventNotInDomHbComponents(c, v, v', step);
      }
      case EndOnEvictCBStep(e) => {
        EndOnEvictCBEventNotInDomHbComponents(c, v, v', step);
      }
      case PerformBranchStep(_) => {
        assert false;
      }
    }
  }
  
  lemma NewEventNotInDomRangeRrMoFr(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires !step.PerformBranchStep?
    ensures 
      && !(step.e in dom(v.execution.rfmofr()))
      && !(step.e in range(v.execution.rfmofr()))
  {
    assert !(step.e in dom(v.execution.wit.rf));
    assert !(step.e in dom(v.execution.wit.mo));
    assert !(step.e in dom(v.execution.fr()));
  }

  ////////////////////////////////////////////
  // Main Proof
  ////////////////////////////////////////////
  lemma SimplifyStepNotInDomRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires !step.PerformBranchStep?
    requires 
      && !(step.e in dom(v.execution.hb_components()))
      && !(step.e in dom(v'.execution.hb_components()))
      && !(step.e in range(v.execution.rfmofr()))
      && !(step.e in dom(v.execution.rfmofr()))
      && ((step.e in dom(v'.execution.rfmofr())) ==> AllPairsIdentity(v'.execution.rfmofr(), step.e))
    ensures
      var rel_hbc := v.execution.hb_components();
      var ext_hbc := v'.execution.hb_components() - v.execution.hb_components();
      var rel_rfmofr := v.execution.rfmofr();
      var ext_rfmofr := v'.execution.rfmofr() - v.execution.rfmofr();
      && !(step.e in dom(rel_hbc))
      && !(step.e in dom(ext_hbc))
      && !(step.e in dom(rel_rfmofr))
      && ((step.e in dom(ext_rfmofr)) ==> AllPairsIdentity(ext_rfmofr, step.e))
      && ((step.e in dom(v'.execution.eco())) ==> AllPairsIdentity(v'.execution.eco(), step.e))
    ensures
      var rel_hbeco := v.execution.hbeco();
      var ext_hbeco := v'.execution.hbeco() - v.execution.hbeco();
      && !(step.e in dom(rel_hbeco))
      && !(step.e in range(rel_hbeco))
      && !(step.e in dom(ext_hbeco))
  {
    var rel_hbc := v.execution.hb_components();
    var ext_hbc := v'.execution.hb_components() - v.execution.hb_components();
    var rel_rfmofr := v.execution.rfmofr();
    var ext_rfmofr := v'.execution.rfmofr() - v.execution.rfmofr();
    var rel_hbeco := v.execution.hbeco();
    var ext_hbeco := v'.execution.hbeco() - v.execution.hbeco();

    // 1) e !in dom(rel_hbeco ~ hbeco) <= dom(hb) == dom(hb_c ~ rel_hbc)
    // 1) e !in dom(rel_hbc) (covered by 1)
    assert !(step.e in dom(rel_hbeco)) && !(step.e in dom(rel_hbc)) by { 
      CompositionDomRange(v.execution.hb(), v.execution.eco());                   // dom(hbeco) <= dom(hb)
      TransClosureDomainRange(rel_hbc);                                           // dom(hbc) == dom(hb)
      assert !(step.e in dom(v.execution.hb_components()));
    }
    // 2) e !in range(rel_hbeco ~ hbeco) <= range(eco) == range(rel_rfmofr)
    assert !(step.e in range(rel_hbeco)) by { 
      CompositionDomRange(v.execution.hb(), v.execution.eco());                   // range(hbeco) <= range(eco)
      TransClosureDomainRange(rel_rfmofr);                                        // range(rfmofr) == range(eco)
      assert !(step.e in range(v.execution.rfmofr()));
    }
    // 3) e !in dom(ext_hbeco) <= dom(hbeco') == dom(hb') == dom(hb_c')
    // 2) e !in dom(ext_hbc) <= dom(hb_c') (covered by 3)
    assert !(step.e in dom(ext_hbeco)) && !(step.e in dom(ext_hbc)) by {
      CompositionDomRange(v'.execution.hb(), v'.execution.eco());                 // dom(hbeco') <= dom(hb')
      TransClosureDomainRange(v'.execution.hb_components());                      // dom(hb') == dom(hb_c')
      assert !(step.e in dom(v'.execution.hb_components()));
    }
    // 3) e !in dom(rel_rfmofr)
    assert !(step.e in dom(rel_rfmofr)) by { 
      assert !(step.e in dom(v.execution.rfmofr()));
    }

    // 4) e in dom(rfmofr') => only (e,e), then for any e in dom(ext_rfmofr) <= dom(rfmofr')
    assert ((step.e in dom(ext_rfmofr)) ==> AllPairsIdentity(ext_rfmofr, step.e)) by { 
      assert ((step.e in dom(v'.execution.rfmofr())) ==> AllPairsIdentity(v'.execution.rfmofr(), step.e));
    }
    // 5) e !in dom(eco') == dom(rfmofr')
    assert ((step.e in dom(v'.execution.eco())) ==> AllPairsIdentity(v'.execution.eco(), step.e)) by {
      TransClosureDomainRange(v'.execution.rfmofr());
      assert ((step.e in dom(v'.execution.rfmofr())) ==> AllPairsIdentity(v'.execution.rfmofr(), step.e));
      TransClosurePreservesAllPairsIdentity(v'.execution.rfmofr(), step.e);
    }
  }

  lemma StepNotInDomRangeImpliesSumIrreflexive(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires !step.PerformBranchStep?
    requires
      var rel_hbc := v.execution.hb_components();
      var ext_hbc := v'.execution.hb_components() - v.execution.hb_components();
      var rel_rfmofr := v.execution.rfmofr();
      var ext_rfmofr := v'.execution.rfmofr() - v.execution.rfmofr();
      && !(step.e in dom(rel_hbc))  
      && !(step.e in dom(ext_hbc))
      && !(step.e in dom(rel_rfmofr))  
      && ((step.e in dom(ext_rfmofr)) ==> AllPairsIdentity(ext_rfmofr, step.e))
      && ((step.e in dom(v'.execution.eco())) ==> AllPairsIdentity(v'.execution.eco(), step.e))
    requires
      var rel_hbeco := v.execution.hbeco();
      var ext_hbeco := v'.execution.hbeco() - v.execution.hbeco();
      && !(step.e in dom(rel_hbeco))
      && !(step.e in range(rel_hbeco))
      && !(step.e in dom(ext_hbeco))
    ensures
      var rel_hbeco := v.execution.hbeco();
      var ext_hbeco := v'.execution.hbeco() - v.execution.hbeco();
      && Library.irreflexive(rel_hbeco + ext_hbeco)
  {
    var rel_hbc := v.execution.hb_components();
    var ext_hbc := v'.execution.hb_components() - v.execution.hb_components();
    HbComponentsMonotonic(c, v, v');
    UnionWithDifferenceIsSameAsUnion(rel_hbc, v'.execution.hb_components());       // hbc + (hbc' - hbc) == hbc'
    var rel_rfmofr := v.execution.rfmofr();
    var ext_rfmofr := v'.execution.rfmofr() - v.execution.rfmofr();
    RfMoFrMonotonic(c, v, v');
    UnionWithDifferenceIsSameAsUnion(rel_rfmofr, v'.execution.rfmofr());       // rfmofr + (rfmofr' - rfmofr) == rfmofr'
    var rel_hbeco := v.execution.hbeco();
    var ext_hbeco := v'.execution.hbeco() - v.execution.hbeco();
    AllNewEdgesHaveNewEventRange(c, v, v', step);
    AllNewEdgesHaveNewEventRangeRfMoFr(c, v, v', step);
    assert !(step.e in dom(rel_rfmofr));
    TransClosureExtension(rel_rfmofr, ext_rfmofr, step.e);
    TransClosureExtension(rel_hbc, ext_hbc, step.e);
    CompositionExtension(v'.execution.hb(), v.execution.hb(), v'.execution.eco(), v.execution.eco(), step.e);
    IrreflexivePreservedUnderNewExtension(rel_hbeco, ext_hbeco, step.e);
  }

  
  lemma SumIrreflexiveImpliesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires !step.PerformBranchStep?
    requires
      var rel_hbeco := v.execution.hbeco();
      var ext_hbeco := v'.execution.hbeco() - v.execution.hbeco();
      && Library.irreflexive(rel_hbeco + ext_hbeco)
    ensures Inv(c, v')
  {
    var rel_hbc := v.execution.hb_components();
    var ext_hbc := v'.execution.hb_components() - v.execution.hb_components();
    HbComponentsMonotonic(c, v, v');
    var rel_rfmofr := v.execution.rfmofr();
    var ext_rfmofr := v'.execution.rfmofr() - v.execution.rfmofr();
    RfMoFrMonotonic(c, v, v');
    var rel_hbeco := v.execution.hbeco();
    var ext_hbeco := v'.execution.hbeco() - v.execution.hbeco();
    TransClosureMonotonic(rel_hbc, v'.execution.hb_components()); // hb <= hb'
    TransClosureMonotonic(rel_rfmofr, v'.execution.rfmofr()); // eco <= eco'
    CompositionMonotonic(v.execution.hb(), v.execution.eco(), v'.execution.hb(), v'.execution.eco()); // hb.eco <= hb'.eco'
    UnionWithDifferenceIsSameAsUnion(rel_hbeco, v'.execution.hbeco());
    assert rel_hbeco + ext_hbeco == v'.execution.hbeco();
  }

  
  lemma NextPreservesInv(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    var step :| NextStep(c, v, v', step);
    if step.PerformBranchStep? {
      assert v'.execution == v.execution;
      assert v'.execution.Coh();
    } else {
      NewEventNotInDomHbComponents(c, v, v', step);
      NewEventNotInDomHbComponents'(c, v, v', step);
      NewEventNotInDomRangeRrMoFr(c, v, v', step);
      NewEventDomRangeRrMoFr'Wellformed(c, v, v', step);
      SimplifyStepNotInDomRange(c, v, v', step);
      StepNotInDomRangeImpliesSumIrreflexive(c, v, v', step);
      SumIrreflexiveImpliesInv(c, v, v', step);
    }
  }
}
