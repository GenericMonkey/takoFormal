include "../../model/execution.i.dfy"
include "../../model/program.i.dfy"
include "../../model/tako_spec.i.dfy"
include "../../model/types.s.dfy"
include "invariants.i.dfy"

module HBProof {
  import opened Execution
  import opened Program
  import opened Types
  import opened TakoSpec
  import opened SpecConsistencyInvariants
  import opened Library

  ghost predicate Safety(c: Constants, v: Variables) {
    && v.execution.WF()
    && v.execution.Hb()
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
    reveal Execution.hb_components;
  }

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
  
  lemma PerformRegularLoadStepEventNotInHB'Dom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularLoadStep?
    ensures !(step.e in dom(v'.execution.hb_components()))
  {
    reveal Execution.hb_components;
    var rest := (v'.execution.init_to_noninit() +
    v'.execution.vf() +
    v'.execution.me_es() +
    v'.execution.ee_ms() +
    v'.execution.eb() +
    v'.execution.sw());
    DomUnionCommute(v'.execution.pre.sb(), rest);
    assert !(step.e in dom(v'.execution.pre.sb()));
    assert !(step.e in dom(rest)) by {
      var rest2 := (v'.execution.vf() +
      v'.execution.me_es() +
      v'.execution.ee_ms() +
      v'.execution.eb() +
      v'.execution.sw());
      DomUnionCommute(v'.execution.init_to_noninit(), rest2);
      assert !(step.e in dom(v'.execution.init_to_noninit()));
      assert !(step.e in dom(rest2)) by {
        var rest3 := (v'.execution.me_es() +
        v'.execution.ee_ms() +
        v'.execution.eb() +
        v'.execution.sw());
        DomUnionCommute(v'.execution.vf(), rest3);
        assert !(step.e in dom(v'.execution.vf()));
        assert !(step.e in dom(rest3)) by {
          var rest4 := (v'.execution.ee_ms() +
          v'.execution.eb() +
          v'.execution.sw());
          DomUnionCommute(v'.execution.me_es(), rest4);
          assert !(step.e in dom(v'.execution.me_es()));
          assert !(step.e in dom(rest4)) by {
            var rest5 := (v'.execution.eb() +
            v'.execution.sw());
            DomUnionCommute(v'.execution.ee_ms(), rest5);
            assert !(step.e in dom(v'.execution.ee_ms()));
            assert !(step.e in dom(rest5)) by {
              DomUnionCommute(v'.execution.eb(), v'.execution.sw());
              assert !(step.e in dom(v'.execution.eb()));
              assert !(step.e in dom(v'.execution.sw()));
            }
          }
        }
      }
    }
  }

  
  lemma PerformRegularStoreStepEventNotInHB'Dom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularStoreStep?
    ensures !(step.e in dom(v'.execution.hb_components()))
  {
    reveal Execution.hb_components;
    var rest := (v'.execution.init_to_noninit() +
    v'.execution.vf() +
    v'.execution.me_es() +
    v'.execution.ee_ms() +
    v'.execution.eb() +
    v'.execution.sw());
    DomUnionCommute(v'.execution.pre.sb(), rest);
    assert !(step.e in dom(v'.execution.pre.sb()));
    assert !(step.e in dom(rest)) by {
      var rest2 := (v'.execution.vf() +
      v'.execution.me_es() +
      v'.execution.ee_ms() +
      v'.execution.eb() +
      v'.execution.sw());
      DomUnionCommute(v'.execution.init_to_noninit(), rest2);
      assert !(step.e in dom(v'.execution.init_to_noninit()));
      assert !(step.e in dom(rest2)) by {
        var rest3 := (v'.execution.me_es() +
        v'.execution.ee_ms() +
        v'.execution.eb() +
        v'.execution.sw());
        DomUnionCommute(v'.execution.vf(), rest3);
        assert !(step.e in dom(v'.execution.vf()));
        assert !(step.e in dom(rest3)) by {
          var rest4 := (v'.execution.ee_ms() +
          v'.execution.eb() +
          v'.execution.sw());
          DomUnionCommute(v'.execution.me_es(), rest4);
          assert !(step.e in dom(v'.execution.me_es()));
          assert !(step.e in dom(rest4)) by {
            var rest5 := (v'.execution.eb() +
            v'.execution.sw());
            DomUnionCommute(v'.execution.ee_ms(), rest5);
            assert !(step.e in dom(v'.execution.ee_ms()));
            assert !(step.e in dom(rest5)) by {
              DomUnionCommute(v'.execution.eb(), v'.execution.sw());
              assert !(step.e in dom(v'.execution.eb()));
              assert !(step.e in dom(v'.execution.sw()));
            }
          }
        }
      }
    }
  }

  
  lemma PerformRegularRMWStepEventNotInHB'Dom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularRMWStep?
    ensures !(step.e in dom(v'.execution.hb_components()))
  {
    reveal Execution.hb_components;
    var rest := (v'.execution.init_to_noninit() +
    v'.execution.vf() +
    v'.execution.me_es() +
    v'.execution.ee_ms() +
    v'.execution.eb() +
    v'.execution.sw());
    DomUnionCommute(v'.execution.pre.sb(), rest);
    assert !(step.e in dom(v'.execution.pre.sb()));
    assert !(step.e in dom(rest)) by {
      var rest2 := (v'.execution.vf() +
      v'.execution.me_es() +
      v'.execution.ee_ms() +
      v'.execution.eb() +
      v'.execution.sw());
      DomUnionCommute(v'.execution.init_to_noninit(), rest2);
      assert !(step.e in dom(v'.execution.init_to_noninit()));
      assert !(step.e in dom(rest2)) by {
        var rest3 := (v'.execution.me_es() +
        v'.execution.ee_ms() +
        v'.execution.eb() +
        v'.execution.sw());
        DomUnionCommute(v'.execution.vf(), rest3);
        assert !(step.e in dom(v'.execution.vf()));
        assert !(step.e in dom(rest3)) by {
          var rest4 := (v'.execution.ee_ms() +
          v'.execution.eb() +
          v'.execution.sw());
          DomUnionCommute(v'.execution.me_es(), rest4);
          assert !(step.e in dom(v'.execution.me_es()));
          assert !(step.e in dom(rest4)) by {
            var rest5 := (v'.execution.eb() +
            v'.execution.sw());
            DomUnionCommute(v'.execution.ee_ms(), rest5);
            assert !(step.e in dom(v'.execution.ee_ms()));
            assert !(step.e in dom(rest5)) by {
              DomUnionCommute(v'.execution.eb(), v'.execution.sw());
              assert !(step.e in dom(v'.execution.eb()));
              assert !(step.e in dom(v'.execution.sw()));
            }
          }
        }
      }
    }
  }

  lemma PerformFlushStepEventNotInHB'Dom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformFlushStep?
    ensures !(step.e in dom(v'.execution.hb_components()))
  {
    reveal Execution.hb_components;
    var rest := (v'.execution.init_to_noninit() +
    v'.execution.vf() +
    v'.execution.me_es() +
    v'.execution.ee_ms() +
    v'.execution.eb() +
    v'.execution.sw());
    DomUnionCommute(v'.execution.pre.sb(), rest);
    assert !(step.e in dom(v'.execution.pre.sb()));
    assert !(step.e in dom(rest)) by {
      var rest2 := (v'.execution.vf() +
      v'.execution.me_es() +
      v'.execution.ee_ms() +
      v'.execution.eb() +
      v'.execution.sw());
      DomUnionCommute(v'.execution.init_to_noninit(), rest2);
      assert !(step.e in dom(v'.execution.init_to_noninit()));
      assert !(step.e in dom(rest2)) by {
        var rest3 := (v'.execution.me_es() +
        v'.execution.ee_ms() +
        v'.execution.eb() +
        v'.execution.sw());
        DomUnionCommute(v'.execution.vf(), rest3);
        assert !(step.e in dom(v'.execution.vf()));
        assert !(step.e in dom(rest3)) by {
          var rest4 := (v'.execution.ee_ms() +
          v'.execution.eb() +
          v'.execution.sw());
          DomUnionCommute(v'.execution.me_es(), rest4);
          assert !(step.e in dom(v'.execution.me_es()));
          assert !(step.e in dom(rest4)) by {
            var rest5 := (v'.execution.eb() +
            v'.execution.sw());
            DomUnionCommute(v'.execution.ee_ms(), rest5);
            assert !(step.e in dom(v'.execution.ee_ms()));
            assert !(step.e in dom(rest5)) by {
              DomUnionCommute(v'.execution.eb(), v'.execution.sw());
              assert !(step.e in dom(v'.execution.eb()));
              assert !(step.e in dom(v'.execution.sw()));
            }
          }
        }
      }
    }
  }

  
  lemma PerformMorphLoadStepEventNotInHB'Dom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphLoadStep?
    ensures !(step.e in dom(v'.execution.hb_components()))
  {
    reveal Execution.hb_components;
    var rest := (v'.execution.init_to_noninit() +
    v'.execution.vf() +
    v'.execution.me_es() +
    v'.execution.ee_ms() +
    v'.execution.eb() +
    v'.execution.sw());
    DomUnionCommute(v'.execution.pre.sb(), rest);
    assert !(step.e in dom(v'.execution.pre.sb()));
    assert !(step.e in dom(rest)) by {
      var rest2 := (v'.execution.vf() +
      v'.execution.me_es() +
      v'.execution.ee_ms() +
      v'.execution.eb() +
      v'.execution.sw());
      DomUnionCommute(v'.execution.init_to_noninit(), rest2);
      assert !(step.e in dom(v'.execution.init_to_noninit()));
      assert !(step.e in dom(rest2)) by {
        var rest3 := (v'.execution.me_es() +
        v'.execution.ee_ms() +
        v'.execution.eb() +
        v'.execution.sw());
        DomUnionCommute(v'.execution.vf(), rest3);
        assert !(step.e in dom(v'.execution.vf()));
        assert !(step.e in dom(rest3)) by {
          var rest4 := (v'.execution.ee_ms() +
          v'.execution.eb() +
          v'.execution.sw());
          DomUnionCommute(v'.execution.me_es(), rest4);
          assert !(step.e in dom(v'.execution.me_es()));
          assert !(step.e in dom(rest4)) by {
            var rest5 := (v'.execution.eb() +
            v'.execution.sw());
            DomUnionCommute(v'.execution.ee_ms(), rest5);
            assert !(step.e in dom(v'.execution.ee_ms()));
            assert !(step.e in dom(rest5)) by {
              DomUnionCommute(v'.execution.eb(), v'.execution.sw());
              assert !(step.e in dom(v'.execution.eb()));
              assert !(step.e in dom(v'.execution.sw()));
            }
          }
        }
      }
    }
  }

  lemma PerformMorphStoreStepEventNotInHB'Dom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphStoreStep?
    ensures !(step.e in dom(v'.execution.hb_components()))
  {
    reveal Execution.hb_components;
    var rest := (v'.execution.init_to_noninit() +
    v'.execution.vf() +
    v'.execution.me_es() +
    v'.execution.ee_ms() +
    v'.execution.eb() +
    v'.execution.sw());
    DomUnionCommute(v'.execution.pre.sb(), rest);
    assert !(step.e in dom(v'.execution.pre.sb()));
    assert !(step.e in dom(rest)) by {
      var rest2 := (v'.execution.vf() +
      v'.execution.me_es() +
      v'.execution.ee_ms() +
      v'.execution.eb() +
      v'.execution.sw());
      DomUnionCommute(v'.execution.init_to_noninit(), rest2);
      assert !(step.e in dom(v'.execution.init_to_noninit()));
      assert !(step.e in dom(rest2)) by {
        var rest3 := (v'.execution.me_es() +
        v'.execution.ee_ms() +
        v'.execution.eb() +
        v'.execution.sw());
        DomUnionCommute(v'.execution.vf(), rest3);
        assert !(step.e in dom(v'.execution.vf()));
        assert !(step.e in dom(rest3)) by {
          var rest4 := (v'.execution.ee_ms() +
          v'.execution.eb() +
          v'.execution.sw());
          DomUnionCommute(v'.execution.me_es(), rest4);
          assert !(step.e in dom(v'.execution.me_es()));
          assert !(step.e in dom(rest4)) by {
            var rest5 := (v'.execution.eb() +
            v'.execution.sw());
            DomUnionCommute(v'.execution.ee_ms(), rest5);
            assert !(step.e in dom(v'.execution.ee_ms()));
            assert !(step.e in dom(rest5)) by {
              DomUnionCommute(v'.execution.eb(), v'.execution.sw());
              assert !(step.e in dom(v'.execution.eb()));
              assert !(step.e in dom(v'.execution.sw()));
            }
          }
        }
      }
    }
  }

  
  lemma PerformMorphRMWStepEventNotInHB'Dom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphRMWStep?
    ensures !(step.e in dom(v'.execution.hb_components()))
  {
    reveal Execution.hb_components;
    var rest := (v'.execution.init_to_noninit() +
    v'.execution.vf() +
    v'.execution.me_es() +
    v'.execution.ee_ms() +
    v'.execution.eb() +
    v'.execution.sw());
    DomUnionCommute(v'.execution.pre.sb(), rest);
    assert !(step.e in dom(v'.execution.pre.sb()));
    assert !(step.e in dom(rest)) by {
      var rest2 := (v'.execution.vf() +
      v'.execution.me_es() +
      v'.execution.ee_ms() +
      v'.execution.eb() +
      v'.execution.sw());
      DomUnionCommute(v'.execution.init_to_noninit(), rest2);
      assert !(step.e in dom(v'.execution.init_to_noninit()));
      assert !(step.e in dom(rest2)) by {
        var rest3 := (v'.execution.me_es() +
        v'.execution.ee_ms() +
        v'.execution.eb() +
        v'.execution.sw());
        DomUnionCommute(v'.execution.vf(), rest3);
        assert !(step.e in dom(v'.execution.vf()));
        assert !(step.e in dom(rest3)) by {
          var rest4 := (v'.execution.ee_ms() +
          v'.execution.eb() +
          v'.execution.sw());
          DomUnionCommute(v'.execution.me_es(), rest4);
          assert !(step.e in dom(v'.execution.me_es()));
          assert !(step.e in dom(rest4)) by {
            var rest5 := (v'.execution.eb() +
            v'.execution.sw());
            DomUnionCommute(v'.execution.ee_ms(), rest5);
            assert !(step.e in dom(v'.execution.ee_ms()));
            assert !(step.e in dom(rest5)) by {
              DomUnionCommute(v'.execution.eb(), v'.execution.sw());
              assert !(step.e in dom(v'.execution.eb()));
              assert !(step.e in dom(v'.execution.sw()));
            }
          }
        }
      }
    }
  }

  lemma StartOnEvictCBStepEventNotInSb'Dom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnEvictCBStep?
    ensures !(step.e in dom(v'.execution.pre.sb()))
  {}

  lemma StartOnEvictCBStepEventNotInInitToNoninit'Dom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnEvictCBStep?
    ensures !(step.e in dom(v'.execution.init_to_noninit()))
  {}

  lemma StartOnEvictCBStepEventNotInVf'Dom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnEvictCBStep?
    ensures !(step.e in dom(v'.execution.vf()))
  {}

  lemma StartOnEvictCBStepEventNotInMeEs'Dom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnEvictCBStep?
    ensures !(step.e in dom(v'.execution.me_es()))
  {}

  lemma StartOnEvictCBStepEventNotInEeMs'Dom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnEvictCBStep?
    ensures !(step.e in dom(v'.execution.ee_ms()))
  {}

  lemma StartOnEvictCBStepEventNotInEb'Dom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnEvictCBStep?
    ensures !(step.e in dom(v'.execution.eb()))
  {}

  lemma StartOnEvictCBStepEventNotInSw'Dom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnEvictCBStep?
    ensures !(step.e in dom(v'.execution.sw()))
  {}

  lemma StartOnEvictCBStepEventNotInHB'Dom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnEvictCBStep?
    ensures !(step.e in dom(v'.execution.hb_components()))
  {
    reveal Execution.hb_components;
    StartOnEvictCBStepEventNotInSb'Dom(c, v, v', step);
    StartOnEvictCBStepEventNotInInitToNoninit'Dom(c, v, v', step);
    StartOnEvictCBStepEventNotInVf'Dom(c, v, v', step);
    StartOnEvictCBStepEventNotInMeEs'Dom(c, v, v', step);
    StartOnEvictCBStepEventNotInEeMs'Dom(c, v, v', step);
    StartOnEvictCBStepEventNotInEb'Dom(c, v, v', step);
    StartOnEvictCBStepEventNotInSw'Dom(c, v, v', step);
  }

  lemma EndOnEvictCBStepEventNotInSb'Dom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures !(step.e in dom(v'.execution.pre.sb()))
  {}

  lemma EndOnEvictCBStepEventNotInInitToNoninit'Dom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures !(step.e in dom(v'.execution.init_to_noninit()))
  {}

  lemma EndOnEvictCBStepEventNotInVf'Dom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures !(step.e in dom(v'.execution.vf()))
  {}

  lemma EndOnEvictCBStepEventNotInMeEs'Dom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures !(step.e in dom(v'.execution.me_es()))
  {}

  lemma EndOnEvictCBStepEventNotInEeMs'Dom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures !(step.e in dom(v'.execution.ee_ms()))
  {}

  lemma EndOnEvictCBStepEventNotInEb'Dom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures !(step.e in dom(v'.execution.eb()))
  {}

  lemma EndOnEvictCBStepEventNotInSw'Dom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures !(step.e in dom(v'.execution.sw()))
  {}


  lemma EndOnEvictCBStepEventNotInHB'Dom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures !(step.e in dom(v'.execution.hb_components()))
  {
    reveal Execution.hb_components;
    EndOnEvictCBStepEventNotInSb'Dom(c, v, v', step);
    EndOnEvictCBStepEventNotInInitToNoninit'Dom(c, v, v', step);
    EndOnEvictCBStepEventNotInVf'Dom(c, v, v', step);
    EndOnEvictCBStepEventNotInMeEs'Dom(c, v, v', step);
    EndOnEvictCBStepEventNotInEeMs'Dom(c, v, v', step);
    EndOnEvictCBStepEventNotInEb'Dom(c, v, v', step);
    EndOnEvictCBStepEventNotInSw'Dom(c, v, v', step);
  }

  lemma StartOnMissCBStepEventNotInHB'Dom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnMissCBStep?
    ensures !(step.e in dom(v'.execution.hb_components()))
  {
    reveal Execution.hb_components;
    var rest := (v'.execution.init_to_noninit() +
    v'.execution.vf() +
    v'.execution.me_es() +
    v'.execution.ee_ms() +
    v'.execution.eb() +
    v'.execution.sw());
    DomUnionCommute(v'.execution.pre.sb(), rest);
    assert !(step.e in dom(v'.execution.pre.sb()));
    assert !(step.e in dom(rest)) by {
      var rest2 := (v'.execution.vf() +
      v'.execution.me_es() +
      v'.execution.ee_ms() +
      v'.execution.eb() +
      v'.execution.sw());
      DomUnionCommute(v'.execution.init_to_noninit(), rest2);
      assert !(step.e in dom(v'.execution.init_to_noninit()));
      assert !(step.e in dom(rest2)) by {
        var rest3 := (v'.execution.me_es() +
        v'.execution.ee_ms() +
        v'.execution.eb() +
        v'.execution.sw());
        DomUnionCommute(v'.execution.vf(), rest3);
        assert !(step.e in dom(v'.execution.vf()));
        assert !(step.e in dom(rest3)) by {
          var rest4 := (v'.execution.ee_ms() +
          v'.execution.eb() +
          v'.execution.sw());
          DomUnionCommute(v'.execution.me_es(), rest4);
          assert !(step.e in dom(v'.execution.me_es()));
          assert !(step.e in dom(rest4)) by {
            var rest5 := (v'.execution.eb() +
            v'.execution.sw());
            DomUnionCommute(v'.execution.ee_ms(), rest5);
            assert !(step.e in dom(v'.execution.ee_ms()));
            assert !(step.e in dom(rest5)) by {
              DomUnionCommute(v'.execution.eb(), v'.execution.sw());
              assert !(step.e in dom(v'.execution.eb()));
              assert !(step.e in dom(v'.execution.sw()));
            }
          }
        }
      }
    }
  }

  lemma EndOnMissCBStepEventNotInHB'Dom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnMissCBStep?
    ensures !(step.e in dom(v'.execution.hb_components()))
  {
    reveal Execution.hb_components;
    var rest := (v'.execution.init_to_noninit() +
    v'.execution.vf() +
    v'.execution.me_es() +
    v'.execution.ee_ms() +
    v'.execution.eb() +
    v'.execution.sw());
    DomUnionCommute(v'.execution.pre.sb(), rest);
    assert !(step.e in dom(v'.execution.pre.sb()));
    assert !(step.e in dom(rest)) by {
      var rest2 := (v'.execution.vf() +
      v'.execution.me_es() +
      v'.execution.ee_ms() +
      v'.execution.eb() +
      v'.execution.sw());
      DomUnionCommute(v'.execution.init_to_noninit(), rest2);
      assert !(step.e in dom(v'.execution.init_to_noninit()));
      assert !(step.e in dom(rest2)) by {
        var rest3 := (v'.execution.me_es() +
        v'.execution.ee_ms() +
        v'.execution.eb() +
        v'.execution.sw());
        DomUnionCommute(v'.execution.vf(), rest3);
        assert !(step.e in dom(v'.execution.vf()));
        assert !(step.e in dom(rest3)) by {
          var rest4 := (v'.execution.ee_ms() +
          v'.execution.eb() +
          v'.execution.sw());
          DomUnionCommute(v'.execution.me_es(), rest4);
          assert !(step.e in dom(v'.execution.me_es()));
          assert !(step.e in dom(rest4)) by {
            var rest5 := (v'.execution.eb() +
            v'.execution.sw());
            DomUnionCommute(v'.execution.ee_ms(), rest5);
            assert !(step.e in dom(v'.execution.ee_ms()));
            assert !(step.e in dom(rest5)) by {
              DomUnionCommute(v'.execution.eb(), v'.execution.sw());
              assert !(step.e in dom(v'.execution.eb()));
              assert !(step.e in dom(v'.execution.sw()));
            }
          }
        }
      }
    }
  }

  
  lemma StepEventNotInHB'Dom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires !step.PerformBranchStep?
    ensures !(step.e in dom(v'.execution.hb_components()))
  {
    match step {
      case PerformRegularLoadStep(_, _, _) => {
        PerformRegularLoadStepEventNotInHB'Dom(c, v, v', step);
      }
      case PerformRegularStoreStep(_) => {
        PerformRegularStoreStepEventNotInHB'Dom(c, v, v', step);
      }
      case PerformRegularRMWStep(_, _, _) => {
        PerformRegularRMWStepEventNotInHB'Dom(c, v, v', step);
      }
      case PerformMorphLoadStep(_, _) => {
        PerformMorphLoadStepEventNotInHB'Dom(c, v, v', step);
      }
      case PerformMorphStoreStep(_) => {
        PerformMorphStoreStepEventNotInHB'Dom(c, v, v', step);
      }
      case PerformMorphRMWStep(_, _) => {
        PerformMorphRMWStepEventNotInHB'Dom(c, v, v', step);
      }
      case PerformFlushStep(_) => {
        PerformFlushStepEventNotInHB'Dom(c, v, v', step);
      }
      case StartOnMissCBStep(_) => {
        StartOnMissCBStepEventNotInHB'Dom(c, v, v', step);
      }
      case EndOnMissCBStep(_) => {
        EndOnMissCBStepEventNotInHB'Dom(c, v, v', step);
      }
      case StartOnEvictCBStep(_) => {
        StartOnEvictCBStepEventNotInHB'Dom(c, v, v', step);
      }
      case EndOnEvictCBStep(_) => {
        EndOnEvictCBStepEventNotInHB'Dom(c, v, v', step);
      }
      case PerformBranchStep(_) => {
        assert false;
      }
    }
  }

  lemma StepEventNotInHBDom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires !step.PerformBranchStep?
    ensures !(step.e in dom(v.execution.hb_components()))
  {
    reveal Execution.hb_components;
  }

  
  lemma StepEventNotInHBRange(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires !step.PerformBranchStep?
    ensures !(step.e in range(v.execution.hb_components()))
  {
    reveal Execution.hb_components;
  }

  lemma StepEventNotInHBDiffDom(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires !step.PerformBranchStep?
    ensures !(step.e in dom(v'.execution.hb_components() - v.execution.hb_components()))
  {
    StepEventNotInHB'Dom(c, v, v', step);
    reveal Execution.hb_components;
  }

  

  lemma NextPreservesInv(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    var step :| NextStep(c, v, v', step);
    if step.PerformBranchStep? {
      assert v'.execution == v.execution;
      assert v'.execution.Hb();
    } else {
      var rel := v.execution.hb_components();
      var ext := v'.execution.hb_components() - v.execution.hb_components();
      HbComponentsMonotonic(c, v, v');
      UnionWithDifferenceIsSameAsUnion(rel, v'.execution.hb_components()); // v'.hb_c == rel + ext
      // v.hb_c <= v'.hb_c
      TransClosureMonotonic(rel, v'.execution.hb_components());
      // v.hb <= v'.hb
      AllNewEdgesHaveNewEventRange(c, v, v', step);
      StepEventNotInHBDom(c, v, v', step); // e !in dom(rel)
      StepEventNotInHBDiffDom(c, v, v', step); // e !in dom(ext)
      // range(ext) <= {e} (proven by AllNewEdgesHaveNewEventRange)
      TransClosureExtension(rel, ext, step.e); // guarantees range(ext) <= {e}
      StepEventNotInHB'Dom(c, v, v', step); // e !in dom(v'.hb_c) => by TCDomRange => e !in dom(v'.hb) => e !in dom(ext_tc)

      var rel_tc := v.execution.hb();
      var ext_tc := v'.execution.hb() - v.execution.hb();
      TransClosureDomainRange(rel); // dom(rel) == dom(rel_tc)
      TransClosureDomainRange(v'.execution.hb_components());
      // e !in dom(rel_tc),  // covered by step.e !in dom(rel)
      StepEventNotInHBRange(c, v, v', step); // e !in range(rel)
      // e !in dom(ext_tc), // covered by step.e !in dom(v'.hb_c) = dom(v'.hb) (v'.hb >= ext_tc)
      // range(ext_tc) <= {e} // covered by TransClosureExtension
      IrreflexivePreservedUnderNewExtension(rel_tc, ext_tc, step.e);
      // irr(rel_tc + irr_tc)
      UnionWithDifferenceIsSameAsUnion(rel_tc, v'.execution.hb());
      assert rel_tc + ext_tc == v'.execution.hb();
      assert v'.execution.Hb();
    }
  }
}
