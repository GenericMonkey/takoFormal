include "../../model/execution.i.dfy"
include "../../model/program.i.dfy"
include "../../model/tako_spec.i.dfy"
include "../../model/types.s.dfy"
include "invariants.i.dfy"

module CboWf9Proof {
  import opened Execution
  import opened Program
  import opened Types
  import opened TakoSpec
  import opened SpecConsistencyInvariants


  ghost predicate Safety(c: Constants, v: Variables) {
    && v.execution.WF()
    && v.execution.CboWf9()

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

  ghost predicate Inv2(c: Constants, v: Variables)
  {
    && EvictEpochExistingEventsN(c, v)
    && LowerEpochExistingEventsN(c, v)
    && InEpochExistingEventsN(c, v)
    && MissEpochExistingEventsN(c, v)
  }

  ghost predicate Inv3(c: Constants, v: Variables) {
    && LowerEpochImpliesCbo(c, v)
    && InEpochMeIsMissEnd(c, v)
    && SameEpochImpliesCbo(c, v)
  }

  ghost predicate Inv(c: Constants, v: Variables) {
    && Safety(c, v)

    // additional invariants
    && Inv0(c, v)

    && Inv1(c, v)
    && Inv2(c, v)
    && Inv3(c, v)
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
    assert v'.execution.Flushes() == v.execution.Flushes();
    assert v'.execution.MissStarts() == v.execution.MissStarts();
    assert v'.execution.EvictEnds() == v.execution.EvictEnds();
  }

  lemma RegularStorePreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularStoreStep?
    ensures Safety(c, v')
  {
    assert v'.execution.Flushes() == v.execution.Flushes();
    assert v'.execution.MissStarts() == v.execution.MissStarts();
    assert v'.execution.EvictEnds() == v.execution.EvictEnds();
  }

  lemma MorphLoadPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphLoadStep?
    ensures Safety(c, v')
  {
    assert v'.execution.Flushes() == v.execution.Flushes();
    assert v'.execution.MissStarts() == v.execution.MissStarts();
    assert v'.execution.EvictEnds() == v.execution.EvictEnds();
  }

  lemma MorphStorePreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphStoreStep?
    ensures Safety(c, v')
  {
    assert v'.execution.Flushes() == v.execution.Flushes();
    assert v'.execution.MissStarts() == v.execution.MissStarts();
    assert v'.execution.EvictEnds() == v.execution.EvictEnds();
  }

  lemma FlushPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformFlushStep?
    ensures Safety(c, v')
  {
    assert v'.execution.Flushes() == v.execution.Flushes() + {step.e};
    assert v'.execution.MissStarts() == v.execution.MissStarts();
    assert v'.execution.EvictEnds() == v.execution.EvictEnds();
    assert v.epochs[step.e.addr].Out?;
    if v.epochs[step.e.addr].epoch == 0 {
      FlushPreservesSafetyMissStartCase(c, v, v', step);
    } else {
      FlushPreservesSafetyEvictEndCase(c, v, v', step);
    }
  }

  lemma FlushPreservesSafetyMissStartCase(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformFlushStep?
    requires v.epochs[step.e.addr].epoch == 0
    ensures Safety(c, v')
  {
    assert v'.execution.Flushes() == v.execution.Flushes() + {step.e};
    assert v'.execution.MissStarts() == v.execution.MissStarts();
    assert v'.execution.EvictEnds() == v.execution.EvictEnds();
    assert v.epochs[step.e.addr].Out?;
    forall x | x in v.execution.eb()
      ensures x in v'.execution.eb()
    {
      var ee := x.0;
      var f := x.1;
      assert ((ee, f) in v'.execution.wit.cbo - Library.compose(v'.execution.wit.cbo, Library.compose(Library.iden(v'.execution.CallbackTimeEvents()), v'.execution.wit.cbo)));
    }

    forall f: Event | f in v'.execution.pre.events && f.F?
      ensures (
        || (forall ms: Event | ms in v'.execution.pre.events && ms.Ms? && SameAddr(ms.addr, f.addr) :: (f, ms) in v'.execution.wit.cbo)
        || (exists ee: Event :: ee in v'.execution.pre.events && ee.Ee? && (ee, f) in v'.execution.eb())
      )
    {
      if f == step.e {
        forall ms: Event | ms in v'.execution.pre.events && ms.Ms? && SameAddr(ms.addr, f.addr) 
          ensures (f, ms) in v'.execution.wit.cbo
        {
          assert WFCallBackBookends(c, v', ms);
        }
      } else {
        assert f in v.execution.pre.events;
      }
    }

    forall f, ee1, ee2 | (ee1, f) in v'.execution.eb() && (ee2, f) in v'.execution.eb() 
    ensures (
      ee1 == ee2
    )
    { 
      if f == step.e {
        assert WFCallBackBookends(c, v', ee1);
        assert WFCallBackBookends(c, v', ee2);
        assert WFCallBackBookends(c, v, ee1);
        assert WFCallBackBookends(c, v, ee2);
      } else {
        assert f in v.execution.pre.events;
        assert ((ee1, f) in v.execution.wit.cbo - 
          Library.compose(
            v.execution.wit.cbo, 
            Library.compose(
              Library.iden(v.execution.CallbackTimeEvents()), 
              v.execution.wit.cbo
            )
          )
        );
        assert ((ee2, f) in v.execution.wit.cbo -
          Library.compose(
            v.execution.wit.cbo,
            Library.compose(
              Library.iden(v.execution.CallbackTimeEvents()),
              v.execution.wit.cbo
            )
          )
        );
        // assert (ee1, f) in v.execution.eb();
        // assert (ee2, f) in v.execution.eb();
      }
    }
  }

  lemma FlushPreservesSafetyEvictEndCaseEbMembership(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformFlushStep?
    requires v.epochs[step.e.addr].epoch != 0
    ensures (
      && var clean_e := Ee(step.e.addr, false, ThreadInfo(CallbackId(step.e.addr, OnEvict(), v.epochs[step.e.addr].epoch - 1), End()));
      && var dirty_e := Ee(step.e.addr, true, ThreadInfo(CallbackId(step.e.addr, OnWriteBack(), v.epochs[step.e.addr].epoch - 1), End()));
      && var ee := if clean_e in v.execution.pre.events then clean_e else dirty_e;
      && (ee, step.e) in v'.execution.eb()
    )
  {
    assert v'.execution.Flushes() == v.execution.Flushes() + {step.e};
    assert v'.execution.MissStarts() == v.execution.MissStarts();
    assert v'.execution.EvictEnds() == v.execution.EvictEnds();
    assert v.epochs[step.e.addr].Out?;
    var clean_e := Ee(step.e.addr, false, ThreadInfo(CallbackId(step.e.addr, OnEvict(), v.epochs[step.e.addr].epoch - 1), End()));
    var dirty_e := Ee(step.e.addr, true, ThreadInfo(CallbackId(step.e.addr, OnWriteBack(), v.epochs[step.e.addr].epoch - 1), End()));
    assert clean_e in v.execution.pre.events || dirty_e in v.execution.pre.events;
    assert !(clean_e in v.execution.pre.events && dirty_e in v.execution.pre.events);
    var ee := if clean_e in v.execution.pre.events then clean_e else dirty_e;
    assert (ee, step.e) in v'.execution.eb() by {
      assert (ee, step.e) in v'.execution.wit.cbo;
      forall e: Event | e in v'.execution.CallbackTimeEvents()
        ensures !((ee, e) in v'.execution.wit.cbo && (e, step.e) in v'.execution.wit.cbo)
      {
        assert WFCallBackBookends(c, v, ee);
        assert WFCallBackBookends(c, v, e);
        if e == ee {
          assert !((ee, e) in v'.execution.wit.cbo);
        } else {
          if e.addr == ee.addr {
            assert e.info.id.count < v.epochs[e.addr].epoch;
            assert !((ee, e) in v'.execution.wit.cbo);
          } else {
            assert !((ee, e) in v'.execution.wit.cbo);
          }
        }
      }
      assert ((ee, step.e) in v'.execution.wit.cbo - Library.compose(v'.execution.wit.cbo, Library.compose(Library.iden(v'.execution.CallbackTimeEvents()), v'.execution.wit.cbo)));
    }
  }

  lemma FlushPreservesSafetyEvictEndCaseEbGrows(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformFlushStep?
    requires v.epochs[step.e.addr].epoch != 0
    ensures (
      && var clean_e := Ee(step.e.addr, false, ThreadInfo(CallbackId(step.e.addr, OnEvict(), v.epochs[step.e.addr].epoch - 1), End()));
      && var dirty_e := Ee(step.e.addr, true, ThreadInfo(CallbackId(step.e.addr, OnWriteBack(), v.epochs[step.e.addr].epoch - 1), End()));
      && var ee := if clean_e in v.execution.pre.events then clean_e else dirty_e;
      && (forall x | x in v'.execution.eb() - {(ee, step.e)} :: x in v.execution.eb())
      && (forall x | x in v.execution.eb() :: x in v'.execution.eb())
    )
  {
    assert v'.execution.Flushes() == v.execution.Flushes() + {step.e};
    assert v'.execution.MissStarts() == v.execution.MissStarts();
    assert v'.execution.EvictEnds() == v.execution.EvictEnds();
    assert v.epochs[step.e.addr].Out?;
    var clean_e := Ee(step.e.addr, false, ThreadInfo(CallbackId(step.e.addr, OnEvict(), v.epochs[step.e.addr].epoch - 1), End()));
    var dirty_e := Ee(step.e.addr, true, ThreadInfo(CallbackId(step.e.addr, OnWriteBack(), v.epochs[step.e.addr].epoch - 1), End()));
    assert clean_e in v.execution.pre.events || dirty_e in v.execution.pre.events;
    assert !(clean_e in v.execution.pre.events && dirty_e in v.execution.pre.events);
    var ee := if clean_e in v.execution.pre.events then clean_e else dirty_e;
    forall x | x in v'.execution.eb() - {(ee, step.e)}
      ensures x in v.execution.eb()
    {
      var ee' := x.0;
      var f := x.1;
      if f == step.e {
        assert ee' != ee;
        // assert WFEvictEnd(c, v, ee');
        assert ee'.info.id.count < v.epochs[ee'.addr].epoch - 1;
        assert (ee', ee) in v.execution.wit.cbo;
        assert false;
      }
      assert ((ee', f) in v.execution.wit.cbo - Library.compose(v.execution.wit.cbo, Library.compose(Library.iden(v.execution.CallbackTimeEvents()), v.execution.wit.cbo)));
    }
    forall x | x in v.execution.eb()
      ensures x in v'.execution.eb()
    {
      var ee := x.0;
      var f := x.1;
      assert ((ee, f) in v'.execution.wit.cbo - Library.compose(v'.execution.wit.cbo, Library.compose(Library.iden(v'.execution.CallbackTimeEvents()), v'.execution.wit.cbo)));
    }
  }

  lemma FlushPreservesSafetyEvictEndCase(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformFlushStep?
    requires v.epochs[step.e.addr].epoch != 0
    ensures Safety(c, v')
  {
    assert v'.execution.Flushes() == v.execution.Flushes() + {step.e};
    assert v'.execution.MissStarts() == v.execution.MissStarts();
    assert v'.execution.EvictEnds() == v.execution.EvictEnds();
    assert v.epochs[step.e.addr].Out?;
    var clean_e := Ee(step.e.addr, false, ThreadInfo(CallbackId(step.e.addr, OnEvict(), v.epochs[step.e.addr].epoch - 1), End()));
    var dirty_e := Ee(step.e.addr, true, ThreadInfo(CallbackId(step.e.addr, OnWriteBack(), v.epochs[step.e.addr].epoch - 1), End()));
    assert clean_e in v.execution.pre.events || dirty_e in v.execution.pre.events;
    assert !(clean_e in v.execution.pre.events && dirty_e in v.execution.pre.events);
    var ee := if clean_e in v.execution.pre.events then clean_e else dirty_e;
    FlushPreservesSafetyEvictEndCaseEbMembership(c, v, v', step);
    FlushPreservesSafetyEvictEndCaseEbGrows(c, v, v', step);
    forall f: Event | f in v'.execution.pre.events && f.F?
      ensures (
        || (forall ms: Event | ms in v'.execution.pre.events && ms.Ms? && SameAddr(ms.addr, f.addr) :: (f, ms) in v'.execution.wit.cbo)
        || (exists ee: Event :: ee in v'.execution.pre.events && ee.Ee? && (ee, f) in v'.execution.eb())
      )
    {
      if f == step.e {
        assert ee in v'.execution.pre.events;
      } else {
        assert f in v.execution.pre.events;
      }
    }
    forall f, ee1, ee2 | (ee1, f) in v'.execution.eb() && (ee2, f) in v'.execution.eb() 
    ensures (
      ee1 == ee2
    )
    { 
      if f == step.e {
        assert ee1 == ee2 by {
          if (ee1, f) in v.execution.wit.cbo || (ee2, f) in v.execution.wit.cbo {
            assert f in v.execution.pre.events;
            assert ((ee1, f) in v.execution.wit.cbo - 
              Library.compose(
                v.execution.wit.cbo, 
                Library.compose(
                  Library.iden(v.execution.CallbackTimeEvents()), 
                  v.execution.wit.cbo
                )
              )
            );
            assert ((ee2, f) in v.execution.wit.cbo -
              Library.compose(
                v.execution.wit.cbo,
                Library.compose(
                  Library.iden(v.execution.CallbackTimeEvents()),
                  v.execution.wit.cbo
                )
              )
            );
          } else {
            assert ee1.info.id.count == v.epochs[ee1.addr].epoch - 1 by {
              assert WFCallBackBookends(c, v, ee1);
              assert ee1.info.id.count <= v.epochs[ee1.addr].epoch - 1;
              if ee1.info.id.count < v.epochs[ee1.addr].epoch - 1 {
                assert (ee1, ee) in v.execution.wit.cbo;
                assert false;
              }
              
            }
            assert ee2.info.id.count == v.epochs[ee2.addr].epoch - 1 by {
              assert WFCallBackBookends(c, v, ee2);
              assert ee2.info.id.count <= v.epochs[ee2.addr].epoch - 1;
              if ee2.info.id.count < v.epochs[ee2.addr].epoch - 1 {
                assert (ee2, ee) in v.execution.wit.cbo;
                assert false;
              }
            }
            assert ee1 == ee;
            assert ee2 == ee;
          }
        }
      } else {
        assert f in v.execution.pre.events;
        assert ((ee1, f) in v.execution.wit.cbo - 
          Library.compose(
            v.execution.wit.cbo, 
            Library.compose(
              Library.iden(v.execution.CallbackTimeEvents()), 
              v.execution.wit.cbo
            )
          )
        );
        assert ((ee2, f) in v.execution.wit.cbo -
          Library.compose(
            v.execution.wit.cbo,
            Library.compose(
              Library.iden(v.execution.CallbackTimeEvents()),
              v.execution.wit.cbo
            )
          )
        );
      }
    }
  }

  lemma StartOnMissCBPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnMissCBStep?
    ensures Safety(c, v')
  {
    assert v'.execution.Flushes() == v.execution.Flushes();
    assert v'.execution.MissStarts() == v.execution.MissStarts() + {step.e};
    assert v'.execution.EvictEnds() == v.execution.EvictEnds();
    forall e: Event | e in v'.execution.pre.events
      ensures !((step.e, e) in v'.execution.wit.cbo)
      ensures !((step.e, e) in v'.execution.eb())
    {

    }
    forall x | x in v'.execution.eb()
      ensures x in v.execution.eb()
    {
      var ee := x.0;
      var f := x.1;
      assert ee != step.e;
      assert ((ee, f) in v.execution.wit.cbo - Library.compose(v.execution.wit.cbo, Library.compose(Library.iden(v.execution.CallbackTimeEvents()), v.execution.wit.cbo)));
    }
    forall x | x in v.execution.eb()
      ensures x in v'.execution.eb()
    {
      var ee := x.0;
      var f := x.1;
      forall e: Event | e in v'.execution.CallbackTimeEvents()
        ensures !((ee, e) in v'.execution.wit.cbo && (e, f) in v'.execution.wit.cbo)
      {}
      assert ((ee, f) in v'.execution.wit.cbo - Library.compose(v'.execution.wit.cbo, Library.compose(Library.iden(v'.execution.CallbackTimeEvents()), v'.execution.wit.cbo)));
    }
  }

  lemma EndOnMissCBPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnMissCBStep?
    ensures Safety(c, v')
  {
    assert v'.execution.Flushes() == v.execution.Flushes();
    assert v'.execution.MissStarts() == v.execution.MissStarts();
    assert v'.execution.EvictEnds() == v.execution.EvictEnds();
  }

  lemma StartOnEvictCBPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnEvictCBStep?
    ensures Safety(c, v')
  {
    assert v'.execution.Flushes() == v.execution.Flushes();
    assert v'.execution.MissStarts() == v.execution.MissStarts();
    assert v'.execution.EvictEnds() == v.execution.EvictEnds();
  }

  lemma EndOnEvictCBPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures Safety(c, v')
  {
    assert v'.execution.Flushes() == v.execution.Flushes();
    assert v'.execution.MissStarts() == v.execution.MissStarts();
    assert v'.execution.EvictEnds() == v.execution.EvictEnds() + {step.e};
    forall e: Event | e in v'.execution.pre.events
      ensures !((step.e, e) in v'.execution.wit.cbo)
      ensures !((step.e, e) in v'.execution.eb())
    {}
    forall x | x in v'.execution.eb()
      ensures x in v.execution.eb()
    {
      var ee := x.0;
      var f := x.1;
      assert ee != step.e;
      assert ((ee, f) in v.execution.wit.cbo - Library.compose(v.execution.wit.cbo, Library.compose(Library.iden(v.execution.CallbackTimeEvents()), v.execution.wit.cbo)));
    }
    forall x | x in v.execution.eb()
      ensures x in v'.execution.eb()
    {
      var ee := x.0;
      var f := x.1;
      forall e: Event | e in v'.execution.CallbackTimeEvents()
        ensures !((ee, e) in v'.execution.wit.cbo && (e, f) in v'.execution.wit.cbo)
      {}
      assert ((ee, f) in v'.execution.wit.cbo - Library.compose(v'.execution.wit.cbo, Library.compose(Library.iden(v'.execution.CallbackTimeEvents()), v'.execution.wit.cbo)));
    }
  }

  lemma RegularRMWPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularRMWStep?
    ensures Safety(c, v')
  {
    assert v'.execution.Flushes() == v.execution.Flushes();
    assert v'.execution.MissStarts() == v.execution.MissStarts();
    assert v'.execution.EvictEnds() == v.execution.EvictEnds();
  }

  lemma MorphRMWPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphRMWStep?
    ensures Safety(c, v')
  {
    assert v'.execution.Flushes() == v.execution.Flushes();
    assert v'.execution.MissStarts() == v.execution.MissStarts();
    assert v'.execution.EvictEnds() == v.execution.EvictEnds();
  }

  lemma BranchPreservesSafety(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformBranchStep?
    ensures Safety(c, v')
  {
    assert v'.execution.Flushes() == v.execution.Flushes();
    assert v'.execution.MissStarts() == v.execution.MissStarts();
    assert v'.execution.EvictEnds() == v.execution.EvictEnds();
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


  ////////////////////////////////////////////////
  // Inv2 lemmas
  ////////////////////////////////////////////////

  lemma RegularLoadPreservesInv2(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularLoadStep?
    ensures Inv2(c, v')
  {
    // weird instability issue
    assert EvictEpochExistingEventsN(c, v');
    assert LowerEpochExistingEventsN(c, v');
    assert InEpochExistingEventsN(c, v');
    assert MissEpochExistingEventsN(c, v');
  }

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

  ////////////////////////////////////////////////
  // Inv3 lemmas
  ////////////////////////////////////////////////

  lemma RegularLoadPreservesInv3(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularLoadStep?
    ensures Inv3(c, v')
  {}

  lemma RegularStorePreservesInv3(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformRegularStoreStep?
    ensures Inv3(c, v')
  {}

  lemma MorphLoadPreservesInv3(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphLoadStep?
    ensures Inv3(c, v')
  {}

  lemma MorphStorePreservesInv3(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformMorphStoreStep?
    ensures Inv3(c, v')
  {}

  lemma FlushPreservesInv3(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.PerformFlushStep?
    ensures Inv3(c, v')
  {}

  lemma StartOnMissCBPreservesInv3(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.StartOnMissCBStep?
    ensures Inv3(c, v')
  {}

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
  {}

  lemma EndOnEvictCBPreservesInv3(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires step.EndOnEvictCBStep?
    ensures Inv3(c, v')
  {}

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
      case PerformMorphRMWStep(_, _) => {
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
      case PerformBranchStep(_) => {
        BranchPreservesInv0(c, v, v', step);
        BranchPreservesInv1(c, v, v', step);
        BranchPreservesInv2(c, v, v', step);
        BranchPreservesInv3(c, v, v', step);
        BranchPreservesSafety(c, v, v', step);
      }
    }
  }
}