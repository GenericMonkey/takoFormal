include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module MsgQueueHeadNoEvictProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes
  import opened CacheTypes

  lemma CoreNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnEvictRequest(c, v', addr, val)
    {
      assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
      if InFlightOnEvictRequest(c, v', addr, val) {
        reveal InFlightOnEvictRequest;
        var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
        assert InFlightOnEvictRequest(c, v, addr, val);
        assert false;
      }
    }
  }

  lemma ProxyNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnEvictRequest(c, v', addr, val)
    {
      assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
      if InFlightOnEvictRequest(c, v', addr, val) {
        reveal InFlightOnEvictRequest;
        var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
        assert InFlightOnEvictRequest(c, v, addr, val);
        assert false;
      }
    }
  }

  lemma MemoryNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnEvictRequest(c, v', addr, val)
    {
      assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
      if InFlightOnEvictRequest(c, v', addr, val) {
        reveal InFlightOnEvictRequest;
        var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
        assert InFlightOnEvictRequest(c, v, addr, val);
        assert false;
      }
    }
  }

  lemma EngineCacheCommunicationNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnEvictRequest(c, v', addr, val)
    {
      assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
      if InFlightOnEvictRequest(c, v', addr, val) {
        reveal InFlightOnEvictRequest;
        var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
        assert InFlightOnEvictRequest(c, v, addr, val);
        assert false;
      }
    }
  }

  lemma EngineReceiveCallbackReqNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    requires EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnEvictRequest(c, v', addr, val)
    {
      if IsInFlightOnMissRequest(c, v, addr, 0, c_idx) {
        if InFlightOnEvictRequest(c, v', addr, val) {
          reveal InFlightOnEvictRequest;
          var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
          var old_idx := if step.msgOps.recv.val.meta.addr == addr then idx + 1 else idx;
          assert IsInFlightOnEvictRequest(c, v, addr, old_idx, val);
          assert InFlightOnEvictRequest(c, v, addr, val);
          assert false;
        }
      } else {
        if InFlightOnEvictRequest(c, v', addr, val) {
          reveal InFlightOnEvictRequest;
          var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
          assert IsInFlightOnEvictRequest(c, v, addr, idx + 1, val);
          assert false;
        }
      }
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires L2AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnEvictRequest(c, v', addr, val)
    {
      var msg :| msg in step.msgOps.send;
      if IsInFlightOnMissRequest(c, v, addr, 0, c_idx) {
        if InFlightOnEvictRequest(c, v', addr, val) {
          reveal InFlightOnEvictRequest;
          var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
          if IsInFlightOnEvictRequest(c, v, addr, idx, val) {
            assert InFlightOnEvictRequest(c, v, addr, val);
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
        reveal InFlightOnEvictRequest;
        assert !InFlightOnEvictRequest(c, v, addr, val);
      }
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnEvictRequest(c, v', addr, val)
    {
      assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
      if InFlightOnEvictRequest(c, v', addr, val) {
        reveal InFlightOnEvictRequest;
        var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
        assert InFlightOnEvictRequest(c, v, addr, val);
        assert false;
      }
    }
  }

  lemma L2CacheCommunicationNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnEvictRequest(c, v', addr, val)
    {
      assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
      if InFlightOnEvictRequest(c, v', addr, val) {
        reveal InFlightOnEvictRequest;
        var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
        assert InFlightOnEvictRequest(c, v, addr, val);
        assert false;
      }
    }
  }
  
  lemma L2DirectoryNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnEvictRequest(c, v', addr, val)
    {
      assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
      if InFlightOnEvictRequest(c, v', addr, val) {
        reveal InFlightOnEvictRequest;
        var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
        assert InFlightOnEvictRequest(c, v, addr, val);
        assert false;
      }
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnEvictRequest(c, v', addr, val)
    {
      assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
      if InFlightOnEvictRequest(c, v', addr, val) {
        reveal InFlightOnEvictRequest;
        var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
        assert InFlightOnEvictRequest(c, v, addr, val);
        assert false;
      }
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires L3AddressesUnique(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnEvictRequest(c, v', addr, val)
    {
      var msg :| msg in step.msgOps.send;
      if IsInFlightOnMissRequest(c, v, addr, 0, c_idx) {
        if InFlightOnEvictRequest(c, v', addr, val) {
          reveal InFlightOnEvictRequest;
          var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
          if IsInFlightOnEvictRequest(c, v, addr, idx, val) {
            assert InFlightOnEvictRequest(c, v, addr, val);
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
        reveal InFlightOnEvictRequest;
        assert !InFlightOnEvictRequest(c, v, addr, val);
      }
    }
  }

  lemma L3ReqMemoryNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnEvictRequest(c, v', addr, val)
    {
      assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
      if InFlightOnEvictRequest(c, v', addr, val) {
        reveal InFlightOnEvictRequest;
        var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
        assert InFlightOnEvictRequest(c, v, addr, val);
        assert false;
      }
    }
  }

  lemma L3RespMemoryNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnEvictRequest(c, v', addr, val)
    {
      assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
      if InFlightOnEvictRequest(c, v', addr, val) {
        reveal InFlightOnEvictRequest;
        var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
        assert InFlightOnEvictRequest(c, v, addr, val);
        assert false;
      }
    }
  }

  lemma L3ReceiveCoherenceMessageNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnEvictRequest(c, v', addr, val)
    {
      assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
      if InFlightOnEvictRequest(c, v', addr, val) {
        reveal InFlightOnEvictRequest;
        var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
        assert InFlightOnEvictRequest(c, v, addr, val);
        assert false;
      }
    }
  }
  
  lemma L3DirectoryNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnEvictRequest(c, v', addr, val)
    {
      assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
      if InFlightOnEvictRequest(c, v', addr, val) {
        reveal InFlightOnEvictRequest;
        var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
        assert InFlightOnEvictRequest(c, v, addr, val);
        assert false;
      }
    }
  }

  lemma L3ReceiveOnMissDataNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnEvictRequest(c, v', addr, val)
    {
      assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
      if InFlightOnEvictRequest(c, v', addr, val) {
        reveal InFlightOnEvictRequest;
        var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
        assert InFlightOnEvictRequest(c, v, addr, val);
        assert false;
      }
    }
  }

  lemma NoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v)
    requires L2AddressesUnique(c, v)
    requires L3AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v')
  {
    match step {
      case TileStep(_, tile_step, _) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            match l3_step {
              case ScheduleCallbackStep(_,_,_) => {
                L3ScheduleCallbackNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v, v', step);
              }
              case ReqMemoryStep(_,_) => {
                L3ReqMemoryNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v, v', step);
              }
              case RespMemoryStep(_) => {
                L3RespMemoryNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L3ReceiveCoherenceMessageNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L3DirectoryNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L3ReceiveOnMissDataNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v, v', step);
              }
            }
          }
          case EngineStep(e_step) => {
            match e_step {
              case CacheCommunicationStep(_,_,_,_) => {
                EngineCacheCommunicationNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v, v', step);
              }
              case ReceiveCallbackReqStep(_) => {
                EngineReceiveCallbackReqNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v, v', step);
              }
              case _ => {
                assert false;
              }
            }
          }
        }
      }
      case MemoryStep(_) => {
        MemoryNoOpPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v, v', step);
      }
    }
  }

  lemma PerformNextInstPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnEvictRequest(c, v', addr, val)
    {
      assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
      if InFlightOnEvictRequest(c, v', addr, val) {
        reveal InFlightOnEvictRequest;
        var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
        assert InFlightOnEvictRequest(c, v, addr, val);
        assert false;
      }
    }
  }

  lemma StartEndCBPreservesEngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v)
    ensures EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v')
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v', addr, 0, c_idx)
      ensures !InFlightOnEvictRequest(c, v', addr, val)
    {
      assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
      if InFlightOnEvictRequest(c, v', addr, val) {
        reveal InFlightOnEvictRequest;
        var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
        assert InFlightOnEvictRequest(c, v, addr, val);
        assert false;
      }
    }
  }
}