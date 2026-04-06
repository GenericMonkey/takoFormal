include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module EngineBoundMsgUniqueCBProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes

  ///////////////////////////////////////////////////////////////////////////////////
  // EachAddrInEngineBoundMsgHasUniqueCB
  ///////////////////////////////////////////////////////////////////////////////////
  lemma CoreNoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    ensures EachAddrInEngineBoundMsgHasUniqueCB(c, v')
  {
    assert v'.network.inFlightEngReqs == v.network.inFlightEngReqs;
  }

  lemma ProxyNoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires v.WF(c)
    requires EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    ensures EachAddrInEngineBoundMsgHasUniqueCB(c, v')
  {
    assert v'.network.inFlightEngReqs == v.network.inFlightEngReqs;
  }

  lemma EngineReceiveCallbackReqNoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires v.WF(c)
    requires EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    ensures EachAddrInEngineBoundMsgHasUniqueCB(c, v')
  {
    forall addr, idx1: nat, idx2: nat | InFlightEngineRequest(c, v', addr, idx1) && InFlightEngineRequest(c, v', addr, idx2)
    ensures (
      && var msg1 := v'.network.inFlightEngReqs[addr][idx1];
      && var msg2 := v'.network.inFlightEngReqs[addr][idx2];
      && ((msg1.engine_req.OnMiss? && msg2.engine_req.OnMiss?) ==> idx1 == idx2)
      && ((msg1.engine_req.OnEvict? && msg2.engine_req.OnEvict?) ==> idx1 == idx2)
      && ((msg1.engine_req.OnWriteBack? && msg2.engine_req.OnWriteBack?) ==> idx1 == idx2)
      && !(msg1.engine_req.OnWriteBack? && msg2.engine_req.OnEvict?)
    ) {
    }
  }

  lemma EngineNotReceiveCallbackReqNoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires !step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires v.WF(c)
    requires EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    ensures EachAddrInEngineBoundMsgHasUniqueCB(c, v')
  {
    assert v'.network.inFlightEngReqs == v.network.inFlightEngReqs;
  }

  lemma EngineNoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires v.WF(c)
    requires EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    ensures EachAddrInEngineBoundMsgHasUniqueCB(c, v')
  {
    if step.tile_step.eng_step.ReceiveCallbackReqStep? {
      EngineReceiveCallbackReqNoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c, v, v', step);
    } else {
      EngineNotReceiveCallbackReqNoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c, v, v', step);
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires v.WF(c)
    requires EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    ensures EachAddrInEngineBoundMsgHasUniqueCB(c, v')
  {
    assert v'.network.inFlightEngReqs == v.network.inFlightEngReqs;
  }

  lemma L2CacheCommunicationNoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires v.WF(c)
    requires EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    ensures EachAddrInEngineBoundMsgHasUniqueCB(c, v')
  {
    assert v'.network.inFlightEngReqs == v.network.inFlightEngReqs;
  }

  lemma L2DirectoryNoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires v.WF(c)
    requires EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    ensures EachAddrInEngineBoundMsgHasUniqueCB(c, v')
  {
    assert v'.network.inFlightEngReqs == v.network.inFlightEngReqs;
  }

  lemma L2ReceiveOnMissDataNoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires v.WF(c)
    requires EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    ensures EachAddrInEngineBoundMsgHasUniqueCB(c, v')
  {
    assert v'.network.inFlightEngReqs == v.network.inFlightEngReqs;
  }

  lemma L2ScheduleCallbackNoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires v.WF(c)
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    requires EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    ensures EachAddrInEngineBoundMsgHasUniqueCB(c, v')
  {
    match step.tile_step.l2_step.eng_req {
      case OnMiss(idx_new) => {
        var addr := step.tile_step.l2_step.addr;
        forall idx: nat | InFlightEngineRequest(c, v, addr, idx)
        ensures (
          && var msg := v.network.inFlightEngReqs[addr][idx];
          && !msg.engine_req.OnMiss?
        ) {
          var msg := v.network.inFlightEngReqs[addr][idx];
          if msg.engine_req.OnMiss? {
            assert InFlightOnMissRequest(c, v, addr, msg.engine_req.idx) by {
              reveal InFlightOnMissRequest;
              assert IsInFlightOnMissRequest(c, v, addr, idx, msg.engine_req.idx);
            }
            assert OnMissInProgress(c, v, addr, msg.engine_req.idx);
            reveal L2PendingCallbackForAddr;
            assert false;
          }
        }
        assert EachAddrInEngineBoundMsgHasUniqueCB(c, v');
      }
      case _ => {
        var addr := step.tile_step.l2_step.addr;
        forall idx: nat | InFlightEngineRequest(c, v, addr, idx)
        ensures (
          && var msg := v.network.inFlightEngReqs[addr][idx];
          && !msg.engine_req.OnEvict?
          && !msg.engine_req.OnWriteBack?
        ) {
          var msg := v.network.inFlightEngReqs[addr][idx];
          if msg.engine_req.OnEvict? {
            assert InFlightOnEvictRequest(c, v, addr, msg.engine_req.val) by {
              reveal InFlightOnEvictRequest;
              assert IsInFlightOnEvictRequest(c, v, addr, idx, msg.engine_req.val);
            }
            assert OnEvictInProgress(c, v, addr, msg.engine_req.val);
            assert false;
          }
          if msg.engine_req.OnWriteBack? {
            assert InFlightOnWritebackRequest(c, v, addr, msg.engine_req.val) by {
              reveal InFlightOnWritebackRequest;
              assert IsInFlightOnWritebackRequest(c, v, addr, idx, msg.engine_req.val);
            }
            assert OnWritebackInProgress(c, v, addr, msg.engine_req.val);
            assert false;
          }
        }
        assert EachAddrInEngineBoundMsgHasUniqueCB(c, v');
      }
    }
  }


  lemma L2NoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires v.WF(c)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    requires EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    ensures EachAddrInEngineBoundMsgHasUniqueCB(c, v')
  {
    match step.tile_step.l2_step {
      case ReceiveCoherenceMessageStep() => {
        L2ReceiveCoherenceMessageNoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c, v, v', step);
      }
      case CacheCommunicationStep(_,_,_,_) => {
        L2CacheCommunicationNoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c, v, v', step);
      }
      case DirectoryStep(_,_,_) => {
        L2DirectoryNoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c, v, v', step);
      }
      case ReceiveOnMissDataStep(_) => {
        L2ReceiveOnMissDataNoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c, v, v', step);
      }
      case ScheduleCallbackStep(_,_,_) => {
        L2ScheduleCallbackNoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c, v, v', step);
      }
    }
  }


  lemma L3NotScheduleCallbackNoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires !step.tile_step.l3_step.ScheduleCallbackStep?
    requires v.WF(c)
    requires EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    ensures EachAddrInEngineBoundMsgHasUniqueCB(c, v')
  {
    assert v'.network.inFlightEngReqs == v.network.inFlightEngReqs;
  }

  lemma L3ScheduleCallbackNoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires v.WF(c)
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    ensures EachAddrInEngineBoundMsgHasUniqueCB(c, v')
  {
    match step.tile_step.l3_step.eng_req {
      case OnMiss(idx_new) => {
        var addr := step.tile_step.l3_step.addr;
        forall idx: nat | InFlightEngineRequest(c, v, addr, idx)
        ensures (
          && var msg := v.network.inFlightEngReqs[addr][idx];
          && !msg.engine_req.OnMiss?
        ) {
          var msg := v.network.inFlightEngReqs[addr][idx];
          if msg.engine_req.OnMiss? {
            assert InFlightOnMissRequest(c, v, addr, msg.engine_req.idx) by {
              reveal InFlightOnMissRequest;
              assert IsInFlightOnMissRequest(c, v, addr, idx, msg.engine_req.idx);
            }
            assert OnMissInProgress(c, v, addr, msg.engine_req.idx);
            reveal L3PendingCallbackForAddr;
            assert false;
          }
        }
        assert EachAddrInEngineBoundMsgHasUniqueCB(c, v');
      }
      case _ => {
        var addr := step.tile_step.l3_step.addr;
        forall idx: nat | InFlightEngineRequest(c, v, addr, idx)
        ensures (
          && var msg := v.network.inFlightEngReqs[addr][idx];
          && !msg.engine_req.OnEvict?
          && !msg.engine_req.OnWriteBack?
        ) {
          var msg := v.network.inFlightEngReqs[addr][idx];
          if msg.engine_req.OnEvict? {
            assert InFlightOnEvictRequest(c, v, addr, msg.engine_req.val) by {
              reveal InFlightOnEvictRequest;
              assert IsInFlightOnEvictRequest(c, v, addr, idx, msg.engine_req.val);
            }
            assert OnEvictInProgress(c, v, addr, msg.engine_req.val);
            assert false;
          }
          if msg.engine_req.OnWriteBack? {
            assert InFlightOnWritebackRequest(c, v, addr, msg.engine_req.val) by {
              reveal InFlightOnWritebackRequest;
              assert IsInFlightOnWritebackRequest(c, v, addr, idx, msg.engine_req.val);
            }
            assert OnWritebackInProgress(c, v, addr, msg.engine_req.val);
            assert false;
          }
        }
        assert EachAddrInEngineBoundMsgHasUniqueCB(c, v');
      }
    }
  }

  lemma L3NoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires v.WF(c)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    ensures EachAddrInEngineBoundMsgHasUniqueCB(c, v')
  {
    if step.tile_step.l3_step.ScheduleCallbackStep? {
      L3ScheduleCallbackNoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c, v, v', step);
    } else {
      L3NotScheduleCallbackNoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c, v, v', step);
    }
  }

  lemma NoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    ensures EachAddrInEngineBoundMsgHasUniqueCB(c, v')
  {
    match step {
      case MemoryStep(msgOps) => {
        assert EachAddrInEngineBoundMsgHasUniqueCB(c, v');
      }
      case TileStep(tile_idx, tile_step, msgOps) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c, v, v', step);
          }
          case L2Step(l2_step) => {
            L2NoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c, v, v', step);
          }
          case L3Step(l3_step) => {
            L3NoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c, v, v', step);
          }
          case EngineStep(eng_step) => {
            EngineNoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c, v, v', step);
          }
          case ProxyStep(proxy_step) => {
            ProxyNoOpPreservesEachAddrInEngineBoundMsgHasUniqueCB(c, v, v', step);
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesEachAddrInEngineBoundMsgHasUniqueCB(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    ensures EachAddrInEngineBoundMsgHasUniqueCB(c, v')
  {}

  lemma StartEndCBPreservesEachAddrInEngineBoundMsgHasUniqueCB(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    ensures EachAddrInEngineBoundMsgHasUniqueCB(c, v')
  {}
}