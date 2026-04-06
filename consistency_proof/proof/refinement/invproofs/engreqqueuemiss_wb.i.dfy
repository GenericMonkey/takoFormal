include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module MsgQueueHeadNoWritebackProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes
  import opened CacheTypes

  lemma CoreNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnWritebackRequest(c, v', addr, val)
    {
      assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
      if InFlightOnWritebackRequest(c, v', addr, val) {
        reveal InFlightOnWritebackRequest;
        var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
        assert InFlightOnWritebackRequest(c, v, addr, val);
        assert false;
      }
    }
  }

  lemma ProxyNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnWritebackRequest(c, v', addr, val)
    {
      assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
      if InFlightOnWritebackRequest(c, v', addr, val) {
        reveal InFlightOnWritebackRequest;
        var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
        assert InFlightOnWritebackRequest(c, v, addr, val);
        assert false;
      }
    }
  }

  lemma MemoryNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnWritebackRequest(c, v', addr, val)
    {
      assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
      if InFlightOnWritebackRequest(c, v', addr, val) {
        reveal InFlightOnWritebackRequest;
        var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
        assert InFlightOnWritebackRequest(c, v, addr, val);
        assert false;
      }
    }
  }

  lemma EngineCacheCommunicationNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnWritebackRequest(c, v', addr, val)
    {
      assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
      if InFlightOnWritebackRequest(c, v', addr, val) {
        reveal InFlightOnWritebackRequest;
        var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
        assert InFlightOnWritebackRequest(c, v, addr, val);
        assert false;
      }
    }
  }

  lemma EngineReceiveCallbackReqNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    requires EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnWritebackRequest(c, v', addr, val)
    {
      if IsInFlightOnMissRequest(c, v, addr, 0, c_idx) {
        if InFlightOnWritebackRequest(c, v', addr, val) {
          reveal InFlightOnWritebackRequest;
          var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx ,val);
          var old_idx := if step.msgOps.recv.val.meta.addr == addr then idx + 1 else idx;
          assert IsInFlightOnWritebackRequest(c, v, addr, old_idx, val);
          assert InFlightOnWritebackRequest(c, v, addr, val);
          assert InFlightOnWritebackRequest(c, v, addr, val);
          assert false;
        }
      } else {
        if InFlightOnWritebackRequest(c, v', addr, val) {
          reveal InFlightOnWritebackRequest;
          var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
          assert IsInFlightOnWritebackRequest(c, v, addr, idx + 1, val);
          assert false;
        }
      }
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires L2AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnWritebackRequest(c, v', addr, val)
    {
      var msg :| msg in step.msgOps.send;
      if IsInFlightOnMissRequest(c, v, addr, 0, c_idx) {
        if InFlightOnWritebackRequest(c, v', addr, val) {
          reveal InFlightOnWritebackRequest;
          var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
          if IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
            assert InFlightOnWritebackRequest(c, v, addr, val);
            assert false;
          } else {
            reveal InFlightOnMissRequest;
            assert OnMissInProgress(c, v, addr, c_idx);
            reveal L2PendingCallbackForAddr;
            assert false;
          }
        }
      } else {
        // sending the onmiss right now, its head of queue
        assert addr == msg.meta.addr;
        assert step.tile_step.l2_step.idx == c_idx;
        assert (!(addr in v.network.inFlightEngReqs) || |v.network.inFlightEngReqs[addr]| == 0);
        reveal InFlightOnWritebackRequest;
        assert !InFlightOnWritebackRequest(c, v, addr, val);
      }
    }
  }

  lemma L2DirectoryNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnWritebackRequest(c, v', addr, val)
    {
      assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
      if InFlightOnWritebackRequest(c, v', addr, val) {
        reveal InFlightOnWritebackRequest;
        var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
        assert InFlightOnWritebackRequest(c, v, addr, val);
        assert false;
      }
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnWritebackRequest(c, v', addr, val)
    {
      assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
      if InFlightOnWritebackRequest(c, v', addr, val) {
        reveal InFlightOnWritebackRequest;
        var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
        assert InFlightOnWritebackRequest(c, v, addr, val);
        assert false;
      }
    }
  }

  lemma L2CacheCommunicationNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnWritebackRequest(c, v', addr, val)
    {
      assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
      if InFlightOnWritebackRequest(c, v', addr, val) {
        reveal InFlightOnWritebackRequest;
        var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
        assert InFlightOnWritebackRequest(c, v, addr, val);
        assert false;
      }
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnWritebackRequest(c, v', addr, val)
    {
      assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
      if InFlightOnWritebackRequest(c, v', addr, val) {
        reveal InFlightOnWritebackRequest;
        var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
        assert InFlightOnWritebackRequest(c, v, addr, val);
        assert false;
      }
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires L3AddressesUnique(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnWritebackRequest(c, v', addr, val)
    {
      var msg :| msg in step.msgOps.send;
      if IsInFlightOnMissRequest(c, v, addr, 0, c_idx) {
        if InFlightOnWritebackRequest(c, v', addr, val) {
          reveal InFlightOnWritebackRequest;
          var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
          if IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
            assert InFlightOnWritebackRequest(c, v, addr, val);
            assert false;
          } else {
            reveal InFlightOnMissRequest;
            assert OnMissInProgress(c, v, addr, c_idx);
            reveal L3PendingCallbackForAddr;
            assert false;
          }
        }
      } else {
        // sending the onmiss right now, its head of queue
        assert addr == msg.meta.addr;
        assert step.tile_step.l3_step.idx == c_idx;
        assert (!(addr in v.network.inFlightEngReqs) || |v.network.inFlightEngReqs[addr]| == 0);
        reveal InFlightOnWritebackRequest;
        assert !InFlightOnWritebackRequest(c, v, addr, val);
      }
    }
  }

  lemma L3NotScheduleCallbackNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires !step.tile_step.l3_step.ScheduleCallbackStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnWritebackRequest(c, v', addr, val)
    {
      assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
      if InFlightOnWritebackRequest(c, v', addr, val) {
        reveal InFlightOnWritebackRequest;
        var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
        assert InFlightOnWritebackRequest(c, v, addr, val);
        assert false;
      }
    }
  }

  lemma NoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v)
    requires L2AddressesUnique(c, v)
    requires L3AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v')
  {
    match step {
      case TileStep(_, tile_step, _) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v, v', step);
              }
            }
          }
          case L3Step(_) => {
            if step.tile_step.l3_step.ScheduleCallbackStep? {
              L3ScheduleCallbackNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v, v', step);
            } else {
              L3NotScheduleCallbackNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v, v', step);
            }
          }
          case EngineStep(e_step) => {
            match e_step {
              case CacheCommunicationStep(_,_,_,_) => {
                EngineCacheCommunicationNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v, v', step);
              }
              case ReceiveCallbackReqStep(_) => {
                EngineReceiveCallbackReqNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v, v', step);
              }
              case _ => {
                assert false;
              }
            }
          }
        }
      }
      case MemoryStep(_) => {
        MemoryNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v, v', step);
      }
    }
  }

  lemma PerformNextInstPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnWritebackRequest(c, v', addr, val)
    {
      assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
      if InFlightOnWritebackRequest(c, v', addr, val) {
        reveal InFlightOnWritebackRequest;
        var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
        assert InFlightOnWritebackRequest(c, v, addr, val);
        assert false;
      }
    }
  }

  lemma StartEndCBPreservesEngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnWritebackRequest(c, v', addr, val)
    {
      assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
      if InFlightOnWritebackRequest(c, v', addr, val) {
        reveal InFlightOnWritebackRequest;
        var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
        assert InFlightOnWritebackRequest(c, v, addr, val);
        assert false;
      }
    }
  }
}