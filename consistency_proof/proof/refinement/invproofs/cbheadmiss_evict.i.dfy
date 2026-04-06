include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module CBHeadMissNoEvictProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes
  import opened CacheTypes

  lemma CoreNoOpPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
      if OnEvictInProgress(c, v', addr, val) {
        if InFlightOnEvictRequest(c, v', addr, val) {
          reveal InFlightOnEvictRequest;
          var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
          assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
          assert InFlightOnEvictRequest(c, v, addr, val);
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma ProxyNoOpPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
      if OnEvictInProgress(c, v', addr, val) {
        if InFlightOnEvictRequest(c, v', addr, val) {
          reveal InFlightOnEvictRequest;
          var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
          assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
          assert InFlightOnEvictRequest(c, v, addr, val);
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma MemoryNoOpPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
      if OnEvictInProgress(c, v', addr, val) {
        if InFlightOnEvictRequest(c, v', addr, val) {
          reveal InFlightOnEvictRequest;
          var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
          assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
          assert InFlightOnEvictRequest(c, v, addr, val);
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma EngineCacheCommunicationNoOpPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
      if OnEvictInProgress(c, v', addr, val) {
        if InFlightOnEvictRequest(c, v', addr, val) {
          reveal InFlightOnEvictRequest;
          var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
          assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
          assert InFlightOnEvictRequest(c, v, addr, val);
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma EngineReceiveCallbackReqNoOpPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v)
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      if CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx)) {
        if OnEvictInProgress(c, v', addr, val) {
          if InFlightOnEvictRequest(c, v', addr, val) {
            reveal InFlightOnEvictRequest;
            var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
            var old_idx := if step.msgOps.recv.val.meta.addr == addr then idx + 1 else idx;
            assert IsInFlightOnEvictRequest(c, v, addr, old_idx, val);
            assert InFlightOnEvictRequest(c, v, addr, val);
            assert OnEvictInProgress(c, v, addr, val);
            assert false;
          } else {
            assert CallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
            reveal CallbackPresent;
            var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
            if CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf) {
              var val' := v.tiles[tile].engine.buffer[buf].cb_type.val;
              assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val'));
              assert OnEvictInProgress(c, v, addr, val');
              assert false;
            } else {
              var val' := step.msgOps.recv.val.engine_req.val;
              assert IsInFlightOnEvictRequest(c, v, addr, 0, val');
              assert InFlightOnEvictRequest(c, v, addr, val') by { reveal InFlightOnEvictRequest; }
              assert OnEvictInProgress(c, v, addr, val');
              assert false;
            }
          }
        }
      } else {
        assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
        if OnEvictInProgress(c, v', addr, val) {
          if InFlightOnEvictRequest(c, v', addr, val) {
            reveal InFlightOnEvictRequest;
            var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
            var old_idx := if step.msgOps.recv.val.meta.addr == addr then idx + 1 else idx;
            assert IsInFlightOnEvictRequest(c, v, addr, old_idx, val);
            assert InFlightOnEvictRequest(c, v, addr, val);
            assert false;
          } else {
            assert CallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
            reveal CallbackPresent;
            assert addr == step.msgOps.recv.val.meta.addr;
            var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
            if CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf) {
              assert IsBufferEntry(c, v, tile, buf);
              assert AddrInTileCBOrderTracker(c, v, addr, tile);
              assert !(step.tile_step.eng_step.idx in v.tiles[tile].engine.cb_order[addr]);
              assert false;
            } else {
              assert IsInFlightOnEvictRequest(c, v, addr, 0, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by { reveal InFlightOnEvictRequest; }
              assert false;
            }
          }
        }
      }
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires L2AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
      if OnEvictInProgress(c, v', addr, val) {
        if InFlightOnEvictRequest(c, v', addr, val) {
          reveal InFlightOnEvictRequest;
          var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
          if IsInFlightOnEvictRequest(c, v, addr, idx, val) {
            assert InFlightOnEvictRequest(c, v, addr, val);
            assert OnEvictInProgress(c, v, addr, val);
            assert false;
          } else {
            assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) by { reveal CallbackPresent; }
            assert OnMissInProgress(c, v, addr, c_idx);
            reveal L2PendingCallbackForAddr;
            assert false;
          }
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
      if OnEvictInProgress(c, v', addr, val) {
        if InFlightOnEvictRequest(c, v', addr, val) {
          reveal InFlightOnEvictRequest;
          var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
          assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
          assert InFlightOnEvictRequest(c, v, addr, val);
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L2CacheCommunicationNoOpPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
      if OnEvictInProgress(c, v', addr, val) {
        if InFlightOnEvictRequest(c, v', addr, val) {
          reveal InFlightOnEvictRequest;
          var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
          assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
          assert InFlightOnEvictRequest(c, v, addr, val);
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L2DirectoryNoOpPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
      if OnEvictInProgress(c, v', addr, val) {
        if InFlightOnEvictRequest(c, v', addr, val) {
          reveal InFlightOnEvictRequest;
          var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
          assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
          assert InFlightOnEvictRequest(c, v, addr, val);
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
      if OnEvictInProgress(c, v', addr, val) {
        if InFlightOnEvictRequest(c, v', addr, val) {
          reveal InFlightOnEvictRequest;
          var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
          assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
          assert InFlightOnEvictRequest(c, v, addr, val);
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires L3AddressesUnique(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
      if OnEvictInProgress(c, v', addr, val) {
        if InFlightOnEvictRequest(c, v', addr, val) {
          reveal InFlightOnEvictRequest;
          var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
          if IsInFlightOnEvictRequest(c, v, addr, idx, val) {
            assert InFlightOnEvictRequest(c, v, addr, val);
            assert OnEvictInProgress(c, v, addr, val);
            assert false;
          } else {
            assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) by { reveal CallbackPresent; }
            assert OnMissInProgress(c, v, addr, c_idx);
            reveal L3PendingCallbackForAddr;
            assert false;
          }
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L3NotScheduleCallbackNoOpPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires !step.tile_step.l3_step.ScheduleCallbackStep?
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
      if OnEvictInProgress(c, v', addr, val) {
        if InFlightOnEvictRequest(c, v', addr, val) {
          reveal InFlightOnEvictRequest;
          var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
          assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
          assert InFlightOnEvictRequest(c, v, addr, val);
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma NoOpPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v)
    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    requires L2AddressesUnique(c, v)
    requires L3AddressesUnique(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v')
  {
    match step {
      case TileStep(_, tile_step, _) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v, v', step);
              }
            }
          }
          case L3Step(_) => {
            if step.tile_step.l3_step.ScheduleCallbackStep? {
              L3ScheduleCallbackNoOpPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v, v', step);
            } else {
              L3NotScheduleCallbackNoOpPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v, v', step);
            }
          }
          case EngineStep(e_step) => {
            match e_step {
              case CacheCommunicationStep(_,_,_,_) => {
                EngineCacheCommunicationNoOpPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v, v', step);
              }
              case ReceiveCallbackReqStep(_) => {
                EngineReceiveCallbackReqNoOpPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v, v', step);
              }
              case _ => {
                assert false;
              }
            }
          }
        }
      }
      case MemoryStep(_) => {
        MemoryNoOpPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v, v', step);
      }
    }
  }

  lemma PerformNextInstPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
      if OnEvictInProgress(c, v', addr, val) {
        if InFlightOnEvictRequest(c, v', addr, val) {
          reveal InFlightOnEvictRequest;
          var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
          assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
          assert InFlightOnEvictRequest(c, v, addr, val);
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma StartOnEvictPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
      if OnEvictInProgress(c, v', addr, val) {
        if InFlightOnEvictRequest(c, v', addr, val) {
          reveal InFlightOnEvictRequest;
          var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
          assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
          assert InFlightOnEvictRequest(c, v, addr, val);
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }
  
  lemma StartOnMissPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnMiss
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
      if OnEvictInProgress(c, v', addr, val) {
        if InFlightOnEvictRequest(c, v', addr, val) {
          reveal InFlightOnEvictRequest;
          var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
          assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
          assert InFlightOnEvictRequest(c, v, addr, val);
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma StartOnWritebackPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnWriteback
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
      if OnEvictInProgress(c, v', addr, val) {
        if InFlightOnEvictRequest(c, v', addr, val) {
          reveal InFlightOnEvictRequest;
          var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
          assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
          assert InFlightOnEvictRequest(c, v, addr, val);
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma StartCBPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v')
  {
    if re == StartOnEvict {
      StartOnEvictPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v, v', step, re);
    } else if re == StartOnMiss {
      StartOnMissPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v, v', step, re);
    } else if re == StartOnWriteback {
      StartOnWritebackPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v, v', step, re);
    }
  }

  lemma EndEvictionCBPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict || re == EndOnWriteback
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    requires UniqueTileForCallbackAddr(c, v)
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx))
        || v.tiles[step.tile_idx].engine.buffer[v.tiles[step.tile_idx].engine.cb_order[addr][0]].cb_type.OnEvict?
        || v.tiles[step.tile_idx].engine.buffer[v.tiles[step.tile_idx].engine.cb_order[addr][0]].cb_type.OnWriteBack?;
      if CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx)) {
        if OnEvictInProgress(c, v', addr, val) {
          if InFlightOnEvictRequest(c, v', addr, val) {
            reveal InFlightOnEvictRequest;
            var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
            assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
            assert InFlightOnEvictRequest(c, v, addr, val);
            assert OnEvictInProgress(c, v, addr, val);
          } else {
            assert CallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
            reveal CallbackPresent;
            var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
            assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
            assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
            assert OnEvictInProgress(c, v, addr, val);
          }
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      } else {
        var buf_idx := v.tiles[step.tile_idx].engine.cb_order[addr][0];
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, buf_idx)
        || CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, buf_idx);
        var cur_addr := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr;
        assert cur_addr == addr;
        assert !InFlightOnEvictRequest(c, v', addr, val) by {
          if InFlightOnEvictRequest(c, v', addr, val) {
            reveal InFlightOnEvictRequest;
            var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
            assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
            assert InFlightEngineRequest(c, v, addr, idx);
            assert IsBufferEntry(c, v, step.tile_idx, step.tile_step.eng_step.idx);
            assert false;
          }
        }
        assert !CallbackPresent(c, v', addr, EngineRequest.OnEvict(val)) by {
          if CallbackPresent(c, v', addr, EngineRequest.OnEvict(val)) {
            reveal CallbackPresent;
            var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
            assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
            assert tile == step.tile_idx;
            assert false;
          }
        }
        assert !OnEvictInProgress(c, v', addr, val);
      }
    }
  }

  lemma EndOnMissCBPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnMiss
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires UniqueTileForCallbackAddr(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v', addr, 0, EngineRequest.OnMiss(c_idx))
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      if CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx)) {
        if OnEvictInProgress(c, v', addr, val) {
          if InFlightOnEvictRequest(c, v', addr, val) {
            reveal InFlightOnEvictRequest;
            var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
            assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
            assert InFlightOnEvictRequest(c, v, addr, val);
            assert OnEvictInProgress(c, v, addr, val);
            assert false;
          } else {
            assert CallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
            reveal CallbackPresent;
            var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf);
            assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
            assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
            assert OnEvictInProgress(c, v, addr, val);
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

  lemma EndCBPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict || re == EndOnMiss || re == EndOnWriteback
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    requires UniqueTileForCallbackAddr(c, v)
    ensures CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v')
  {
    if re == EndOnMiss {
      EndOnMissCBPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v, v', step, re);
    } else {
      EndEvictionCBPreservesCBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v, v', step, re);
    }
  }
}