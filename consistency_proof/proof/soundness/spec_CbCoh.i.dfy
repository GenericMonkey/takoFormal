include "../../model/execution.i.dfy"
include "../../model/program.i.dfy"
include "../../model/tako_spec.i.dfy"
include "../../model/types.s.dfy"
include "invariants.i.dfy"



module CbCohProof {
  import opened Execution
  import opened Program
  import opened Types
  import opened TakoSpec
  import opened SpecConsistencyInvariants
  import opened Library

  ghost predicate Safety(c: Constants, v: Variables) {
    && v.execution.WF()
    && v.execution.CbCoh()
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
      case PerformRegularStoreStep(_) => {
        PerformRegularStoreStepVfEdgesHaveNewEventRange(c, v, v', step);
      }
      case PerformRegularRMWStep(_, _, _) => {
        PerformRegularRMWStepVfEdgesHaveNewEventRange(c, v, v', step);
      }
      case PerformMorphLoadStep(_, _) => {
        PerformMorphAccessVfEdgesHaveNewEventRange(c, v, v', step);
      }
      case PerformMorphStoreStep(_) => {
        PerformMorphAccessVfEdgesHaveNewEventRange(c, v, v', step);
      }
      case PerformMorphRMWStep(_, _) => {
        PerformMorphAccessVfEdgesHaveNewEventRange(c, v, v', step);
      }
      case PerformFlushStep(_) => {
        PerformFlushStepVfEdgesHaveNewEventRange(c, v, v', step);
      }
      case StartOnMissCBStep(_) => {
        StartOnMissCBStepVfEdgesHaveNewEventRange(c, v, v', step);
      }
      case EndOnMissCBStep(_) => {
        EndOnMissCBStepVfEdgesHaveNewEventRange(c, v, v', step);
      }
      case StartOnEvictCBStep(_) => {
        StartOnEvictCBStepVfEdgesHaveNewEventRange(c, v, v', step);
      }
      case EndOnEvictCBStep(_) => {
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
      case PerformRegularStoreStep(_) => {
        PerformRegularStoreStepEbEdgesHaveNewEventRange(c, v, v', step);
      }
      case PerformRegularRMWStep(_, _, _) => {
        PerformRegularRMWStepEbEdgesHaveNewEventRange(c, v, v', step);
      }
      case PerformMorphLoadStep(_,_) => {
        PerformMorphLoadStepEbEdgesHaveNewEventRange(c, v, v', step);
      }
      case PerformMorphStoreStep(_) => {
        PerformMorphStoreStepEbEdgesHaveNewEventRange(c, v, v', step);
      }
      case PerformMorphRMWStep(_,_) => {
        PerformMorphRMWStepEbEdgesHaveNewEventRange(c, v, v', step);
      }
      case PerformFlushStep(_) => {
        PerformFlushStepEbEdgesHaveNewEventRange(c, v, v', step);
      }
      case StartOnMissCBStep(_) => {
        StartOnMissCBStepEbEdgesHaveNewEventRange(c, v, v', step);
      }
      case EndOnMissCBStep(_) => {
        EndOnMissCBStepEbEdgesHaveNewEventRange(c, v, v', step);
      }
      case StartOnEvictCBStep(_) => {
        StartOnEvictCBStepEbEdgesHaveNewEventRange(c, v, v', step);
      }
      case EndOnEvictCBStep(_) => {
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

  lemma EndOnEvictCBEventNotInDomHbComponents'(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
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
      case PerformRegularStoreStep(_) => {
        PerformRegularStoreEventNotInDomHbComponents'(c, v, v', step);
      }
      case PerformRegularRMWStep(_, _, _) => {
        PerformRegularRMWEventNotInDomHbComponents'(c, v, v', step);
      }
      case PerformMorphLoadStep(_, _) => {
        PerformMorphLoadEventNotInDomHbComponents'(c, v, v', step);
      }
      case PerformMorphStoreStep(_) => {
        PerformMorphStoreEventNotInDomHbComponents'(c, v, v', step);
      }
      case PerformMorphRMWStep(_, _) => {
        PerformMorphRMWEventNotInDomHbComponents'(c, v, v', step);
      }
      case PerformFlushStep(_) => {
        PerformFlushEventNotInDomHbComponents'(c, v, v', step);
      }
      case StartOnMissCBStep(_) => {
        StartOnMissCBEventNotInDomHbComponents'(c, v, v', step);
      }
      case EndOnMissCBStep(_) => {
        EndOnMissCBEventNotInDomHbComponents'(c, v, v', step);
      }
      case StartOnEvictCBStep(_) => {
        StartOnEvictCBEventNotInDomHbComponents'(c, v, v', step);
      }
      case EndOnEvictCBStep(_) => {
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
      case PerformRegularStoreStep(_) => {
        PerformRegularStoreEventNotInDomHbComponents(c, v, v', step);
      }
      case PerformRegularRMWStep(_, _, _) => {
        PerformRegularRMWEventNotInDomHbComponents(c, v, v', step);
      }
      case PerformMorphLoadStep(_, _) => {
        PerformMorphLoadEventNotInDomHbComponents(c, v, v', step);
      }
      case PerformMorphStoreStep(_) => {
        PerformMorphStoreEventNotInDomHbComponents(c, v, v', step);
      }
      case PerformMorphRMWStep(_, _) => {
        PerformMorphRMWEventNotInDomHbComponents(c, v, v', step);
      }
      case PerformFlushStep(_) => {
        PerformFlushEventNotInDomHbComponents(c, v, v', step);
      }
      case StartOnMissCBStep(_) => {
        StartOnMissCBEventNotInDomHbComponents(c, v, v', step);
      }
      case EndOnMissCBStep(_) => {
        EndOnMissCBEventNotInDomHbComponents(c, v, v', step);
      }
      case StartOnEvictCBStep(_) => {
        StartOnEvictCBEventNotInDomHbComponents(c, v, v', step);
      }
      case EndOnEvictCBStep(_) => {
        EndOnEvictCBEventNotInDomHbComponents(c, v, v', step);
      }
      case PerformBranchStep(_) => {
        assert false;
      }
    }
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
    ensures
      var rel_hbc := v.execution.hb_components();
      var ext_hbc := v'.execution.hb_components() - v.execution.hb_components();
      var rel_rfmofr := v.execution.rfmofr();
      var ext_rfmofr := v'.execution.rfmofr() - v.execution.rfmofr();
      && !(step.e in dom(rel_hbc))
      && !(step.e in dom(ext_hbc))
    ensures
      var rel_hbcbo := v.execution.hbcbo();
      var ext_hbcbo := v'.execution.hbcbo() - v.execution.hbcbo();
      && !(step.e in dom(rel_hbcbo))
      && !(step.e in range(rel_hbcbo))
      && !(step.e in dom(ext_hbcbo))
  {
    var rel_hbc := v.execution.hb_components();
    var ext_hbc := v'.execution.hb_components() - v.execution.hb_components();
    var rel_hbcbo := v.execution.hbcbo();
    var ext_hbcbo := v'.execution.hbcbo() - v.execution.hbcbo();

    // 1) e !in dom(rel_hbeco ~ hbeco) <= dom(hb) == dom(hb_c ~ rel_hbc)
    // 1) e !in dom(rel_hbc) (covered by 1)
    assert !(step.e in dom(rel_hbcbo)) && !(step.e in dom(rel_hbc)) by { 
      CompositionDomRange(v.execution.hb(), v.execution.wit.cbo);                   // dom(hbcbo) <= dom(hb)
      TransClosureDomainRange(rel_hbc);                                           // dom(hbc) == dom(hb)
      assert !(step.e in dom(v.execution.hb_components()));
    }
    // 2) e !in range(rel_hbeco ~ hbeco) <= range(eco) == range(rel_rfmofr)
    assert !(step.e in range(rel_hbcbo)) by { 
      CompositionDomRange(v.execution.hb(), v.execution.wit.cbo);                   // range(hbcbo) <= range(cbo)
    }
    // 3) e !in dom(ext_hbeco) <= dom(hbeco') == dom(hb') == dom(hb_c')
    // 2) e !in dom(ext_hbc) <= dom(hb_c') (covered by 3)
    assert !(step.e in dom(ext_hbcbo)) && !(step.e in dom(ext_hbc)) by {
      CompositionDomRange(v'.execution.hb(), v'.execution.wit.cbo);                 // dom(hbcbo') <= dom(hb')
      TransClosureDomainRange(v'.execution.hb_components());                      // dom(hb') == dom(hb_c')
      assert !(step.e in dom(v'.execution.hb_components()));
    }
  }

  
  lemma StepNotInDomRangeImpliesSumIrreflexive(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires !step.PerformBranchStep?
    requires
      var rel_hbc := v.execution.hb_components();
      var ext_hbc := v'.execution.hb_components() - v.execution.hb_components();
      && !(step.e in dom(rel_hbc))  
      && !(step.e in dom(ext_hbc))
    requires
      var rel_hbcbo := v.execution.hbcbo();
      var ext_hbcbo := v'.execution.hbcbo() - v.execution.hbcbo();
      && !(step.e in dom(rel_hbcbo))
      && !(step.e in range(rel_hbcbo))
      && !(step.e in dom(ext_hbcbo))
    ensures
      var rel_hbcbo := v.execution.hbcbo();
      var ext_hbcbo := v'.execution.hbcbo() - v.execution.hbcbo();
      && Library.irreflexive(rel_hbcbo + ext_hbcbo)
  {
    var rel_hbc := v.execution.hb_components();
    var ext_hbc := v'.execution.hb_components() - v.execution.hb_components();
    HbComponentsMonotonic(c, v, v');
    UnionWithDifferenceIsSameAsUnion(rel_hbc, v'.execution.hb_components());       // hbc + (hbc' - hbc) == hbc'
    var rel_hbcbo := v.execution.hbcbo();
    var ext_hbcbo := v'.execution.hbcbo() - v.execution.hbcbo();
    AllNewEdgesHaveNewEventRange(c, v, v', step);
    TransClosureExtension(rel_hbc, ext_hbc, step.e);
    CompositionExtension(v'.execution.hb(), v.execution.hb(), v'.execution.wit.cbo, v.execution.wit.cbo, step.e);
    IrreflexivePreservedUnderNewExtension(rel_hbcbo, ext_hbcbo, step.e);
  }

  lemma SumIrreflexiveImpliesInv(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires !step.PerformBranchStep?
    requires
      var rel_hbcbo := v.execution.hbcbo();
      var ext_hbcbo := v'.execution.hbcbo() - v.execution.hbcbo();
      && Library.irreflexive(rel_hbcbo + ext_hbcbo)
    ensures Inv(c, v')
  {
    var rel_hbc := v.execution.hb_components();
    var ext_hbc := v'.execution.hb_components() - v.execution.hb_components();
    HbComponentsMonotonic(c, v, v');
    var rel_hbcbo := v.execution.hbcbo();
    var ext_hbcbo := v'.execution.hbcbo() - v.execution.hbcbo();
    TransClosureMonotonic(rel_hbc, v'.execution.hb_components()); // hb <= hb'
    CompositionMonotonic(v.execution.hb(), v.execution.wit.cbo, v'.execution.hb(), v'.execution.wit.cbo); // hb.cbo <= hb'.cbo'
    UnionWithDifferenceIsSameAsUnion(rel_hbcbo, v'.execution.hbcbo());
    assert rel_hbcbo + ext_hbcbo == v'.execution.hbcbo();
  }
  
  lemma NextPreservesInv(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    var step :| NextStep(c, v, v', step);
    if step.PerformBranchStep? {
      assert v'.execution == v.execution;
      assert v'.execution.CbCoh();
    } else {
      NewEventNotInDomHbComponents(c, v, v', step);
      NewEventNotInDomHbComponents'(c, v, v', step);
      SimplifyStepNotInDomRange(c, v, v', step);
      StepNotInDomRangeImpliesSumIrreflexive(c, v, v', step);
      SumIrreflexiveImpliesInv(c, v, v', step);
    }
  }
}