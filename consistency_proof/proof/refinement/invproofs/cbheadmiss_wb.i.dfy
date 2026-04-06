include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module CBHeadMissNoWritebackProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes
  import opened CacheTypes


  lemma CoreNoOpPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
      if OnWritebackInProgress(c, v', addr, val) {
        if InFlightOnWritebackRequest(c, v', addr, val) {
          reveal InFlightOnWritebackRequest;
          var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
          assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
          assert InFlightOnWritebackRequest(c, v, addr, val);
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma ProxyNoOpPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
      if OnWritebackInProgress(c, v', addr, val) {
        if InFlightOnWritebackRequest(c, v', addr, val) {
          reveal InFlightOnWritebackRequest;
          var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
          assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
          assert InFlightOnWritebackRequest(c, v, addr, val);
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma MemoryNoOpPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
      if OnWritebackInProgress(c, v', addr, val) {
        if InFlightOnWritebackRequest(c, v', addr, val) {
          reveal InFlightOnWritebackRequest;
          var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
          assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
          assert InFlightOnWritebackRequest(c, v, addr, val);
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma EngineCacheCommunicationNoOpPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
      if OnWritebackInProgress(c, v', addr, val) {
        if InFlightOnWritebackRequest(c, v', addr, val) {
          reveal InFlightOnWritebackRequest;
          var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
          assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
          assert InFlightOnWritebackRequest(c, v, addr, val);
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma EngineReceiveCallbackReqNoOpPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v)
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      if CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx)) {
        if OnWritebackInProgress(c, v', addr, val) {
          if InFlightOnWritebackRequest(c, v', addr, val) {
            reveal InFlightOnWritebackRequest;
            var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
            var old_idx := if step.msgOps.recv.val.meta.addr == addr then idx + 1 else idx;
            assert IsInFlightOnWritebackRequest(c, v, addr, old_idx, val);
            assert InFlightOnWritebackRequest(c, v, addr, val);
            assert OnWritebackInProgress(c, v, addr, val);
            assert false;
          } else {
            assert CallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
            reveal CallbackPresent;
            var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
            if CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf) {
              var val' := v.tiles[tile].engine.buffer[buf].cb_type.val;
              assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val'));
              assert OnWritebackInProgress(c, v, addr, val');
              assert false;
            } else {
              var val' := step.msgOps.recv.val.engine_req.val;
              assert IsInFlightOnWritebackRequest(c, v, addr, 0, val');
              assert InFlightOnWritebackRequest(c, v, addr, val') by { reveal InFlightOnWritebackRequest; }
              assert OnWritebackInProgress(c, v, addr, val');
              assert false;
            }
          }
        }
      } else {
        assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
        if OnWritebackInProgress(c, v', addr, val) {
          if InFlightOnWritebackRequest(c, v', addr, val) {
            reveal InFlightOnWritebackRequest;
            var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
            var old_idx := if step.msgOps.recv.val.meta.addr == addr then idx + 1 else idx;
            assert IsInFlightOnWritebackRequest(c, v, addr, old_idx, val);
            assert InFlightOnWritebackRequest(c, v, addr, val);
            assert false;
          } else {
            assert CallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
            reveal CallbackPresent;
            assert addr == step.msgOps.recv.val.meta.addr;
            var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
            if CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf) {
              assert IsBufferEntry(c, v, tile, buf);
              assert AddrInTileCBOrderTracker(c, v, addr, tile);
              assert !(step.tile_step.eng_step.idx in v.tiles[tile].engine.cb_order[addr]);
              assert false;
            } else {
              assert IsInFlightOnWritebackRequest(c, v, addr, 0, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by { reveal InFlightOnWritebackRequest; }
              assert false;
            }
          }
        }
      }
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires L2AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
      if OnWritebackInProgress(c, v', addr, val) {
        if InFlightOnWritebackRequest(c, v', addr, val) {
          reveal InFlightOnWritebackRequest;
          var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
          if IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
            assert InFlightOnWritebackRequest(c, v, addr, val);
            assert OnWritebackInProgress(c, v, addr, val);
            assert false;
          } else {
            assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) by { reveal CallbackPresent; }
            assert OnMissInProgress(c, v, addr, c_idx);
            reveal L2PendingCallbackForAddr;
            assert false;
          }
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L2NotScheduleCallbackNoOpPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires !step.tile_step.l2_step.ScheduleCallbackStep?
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
      if OnWritebackInProgress(c, v', addr, val) {
        if InFlightOnWritebackRequest(c, v', addr, val) {
          reveal InFlightOnWritebackRequest;
          var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
          assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
          assert InFlightOnWritebackRequest(c, v, addr, val);
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires L3AddressesUnique(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
      if OnWritebackInProgress(c, v', addr, val) {
        if InFlightOnWritebackRequest(c, v', addr, val) {
          reveal InFlightOnWritebackRequest;
          var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
          if IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
            assert InFlightOnWritebackRequest(c, v, addr, val);
            assert OnWritebackInProgress(c, v, addr, val);
            assert false;
          } else {
            assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) by { reveal CallbackPresent; }
            assert OnMissInProgress(c, v, addr, c_idx);
            reveal L3PendingCallbackForAddr;
            assert false;
          }
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L3NotScheduleCallbackNoOpPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires !step.tile_step.l3_step.ScheduleCallbackStep?
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
      if OnWritebackInProgress(c, v', addr, val) {
        if InFlightOnWritebackRequest(c, v', addr, val) {
          reveal InFlightOnWritebackRequest;
          var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
          assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
          assert InFlightOnWritebackRequest(c, v, addr, val);
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma NoOpPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v)
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    requires L2AddressesUnique(c, v)
    requires L3AddressesUnique(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v')
  {
    match step {
      case TileStep(_, tile_step, _) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v, v', step);
          }
          case L2Step(_) => {
            if step.tile_step.l2_step.ScheduleCallbackStep? {
              L2ScheduleCallbackNoOpPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v, v', step);
            } else {
              L2NotScheduleCallbackNoOpPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v, v', step);
            }
          }
          case L3Step(_) => {
            if step.tile_step.l3_step.ScheduleCallbackStep? {
              L3ScheduleCallbackNoOpPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v, v', step);
            } else {
              L3NotScheduleCallbackNoOpPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v, v', step);
            }
          }
          case EngineStep(e_step) => {
            match e_step {
              case CacheCommunicationStep(_,_,_,_) => {
                EngineCacheCommunicationNoOpPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v, v', step);
              }
              case ReceiveCallbackReqStep(_) => {
                EngineReceiveCallbackReqNoOpPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v, v', step);
              }
              case _ => {
                assert false;
              }
            }
          }
        }
      }
      case MemoryStep(_) => {
        MemoryNoOpPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v, v', step);
      }
    }
  }

  lemma PerformNextInstPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
      if OnWritebackInProgress(c, v', addr, val) {
        if InFlightOnWritebackRequest(c, v', addr, val) {
          reveal InFlightOnWritebackRequest;
          var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
          assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
          assert InFlightOnWritebackRequest(c, v, addr, val);
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma StartCBPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
      if OnWritebackInProgress(c, v', addr, val) {
        if InFlightOnWritebackRequest(c, v', addr, val) {
          reveal InFlightOnWritebackRequest;
          var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
          assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
          assert InFlightOnWritebackRequest(c, v, addr, val);
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma EndWritebackionCBPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict || re == EndOnWriteback
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    requires UniqueTileForCallbackAddr(c, v)
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx))
        || v.tiles[step.tile_idx].engine.buffer[v.tiles[step.tile_idx].engine.cb_order[addr][0]].cb_type.OnEvict?
        || v.tiles[step.tile_idx].engine.buffer[v.tiles[step.tile_idx].engine.cb_order[addr][0]].cb_type.OnWriteBack?;
      if CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx)) {
        if OnWritebackInProgress(c, v', addr, val) {
          if InFlightOnWritebackRequest(c, v', addr, val) {
            reveal InFlightOnWritebackRequest;
            var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
            assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
            assert InFlightOnWritebackRequest(c, v, addr, val);
            assert OnWritebackInProgress(c, v, addr, val);
          } else {
            assert CallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
            reveal CallbackPresent;
            var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
            assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
            assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
            assert OnWritebackInProgress(c, v, addr, val);
          }
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      } else {
        var buf_idx := v.tiles[step.tile_idx].engine.cb_order[addr][0];
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, buf_idx)
        || CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, buf_idx);
        var cur_addr := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr;
        assert cur_addr == addr;
        assert !InFlightOnWritebackRequest(c, v', addr, val) by {
          if InFlightOnWritebackRequest(c, v', addr, val) {
            reveal InFlightOnWritebackRequest;
            var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
            assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
            assert InFlightEngineRequest(c, v, addr, idx);
            assert IsBufferEntry(c, v, step.tile_idx, step.tile_step.eng_step.idx);
            assert false;
          }
        }
        assert !CallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val)) by {
          if CallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val)) {
            reveal CallbackPresent;
            var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
            assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
            assert tile == step.tile_idx;
            assert false;
          }
        }
        assert !OnWritebackInProgress(c, v', addr, val);
      }
    }
  }

  lemma EndOnMissCBPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnMiss
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires UniqueTileForCallbackAddr(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      if CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx)) {
        if OnWritebackInProgress(c, v', addr, val) {
          if InFlightOnWritebackRequest(c, v', addr, val) {
            reveal InFlightOnWritebackRequest;
            var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
            assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
            assert InFlightOnWritebackRequest(c, v, addr, val);
            assert OnWritebackInProgress(c, v, addr, val);
            assert false;
          } else {
            assert CallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
            reveal CallbackPresent;
            var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf);
            assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
            assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
            assert OnWritebackInProgress(c, v, addr, val);
            assert false;
          }
        }
      } else {
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
        var idx2 := v.tiles[step.tile_idx].engine.cb_order[addr][1];
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, idx2);
        // assert idx2 != step.tile_step.eng_step.idx;
        assert false;
      }
    }
  }

  lemma EndCBPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict || re == EndOnMiss || re == EndOnWriteback
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    requires UniqueTileForCallbackAddr(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v')
  {
    if re == EndOnMiss {
      EndOnMissCBPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v, v', step, re);
    } else {
      EndWritebackionCBPreservesCBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v, v', step, re);
    }
  }
}