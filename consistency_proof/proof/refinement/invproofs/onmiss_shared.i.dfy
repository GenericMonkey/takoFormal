include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module OnMissInProgressSharedProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes
  import opened CacheTypes

  ///////////////////////////////////////////////////////////////////////////////////
  // OnMissInProgressIffCacheEntryPendingShared
  ///////////////////////////////////////////////////////////////////////////////////
  lemma CoreCacheCommunicationGetSNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires step.tile_step.core_step.step.GetSStep?
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L3PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L3PendingCallbackForAddr(c, v, addr, c_idx);
      assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
    }
  }

  lemma CoreCacheCommunicationGetMNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires step.tile_step.core_step.step.GetMStep?
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L3PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L3PendingCallbackForAddr(c, v, addr, c_idx);
      assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
    }
  }

  lemma CoreCacheCommunicationRecvMsgNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires step.tile_step.core_step.step.RecvMsgStep?
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L3PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L3PendingCallbackForAddr(c, v, addr, c_idx);
      assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
    }
  }

  lemma CoreCacheCommunicationEvictNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires step.tile_step.core_step.step.EvictStep?
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L3PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L3PendingCallbackForAddr(c, v, addr, c_idx);
      assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
    }
  }

  lemma CoreNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    if step.tile_step.core_step.CacheCommunicationStep? {
      match step.tile_step.core_step.step {
        case GetSStep() => CoreCacheCommunicationGetSNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
        case GetMStep() => CoreCacheCommunicationGetMNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
        case RecvMsgStep() => CoreCacheCommunicationRecvMsgNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
        case EvictStep() => CoreCacheCommunicationEvictNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
      }
    } else {
      assert false;
    }
  }

  lemma CoreNoOpPreservesRevOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires v.WF(c)
    requires RevOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && L3PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L3PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L3PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v', addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }

  lemma CoreNoOpPreservesOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires v.WF(c)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures OnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    CoreNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
    CoreNoOpPreservesRevOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
  }

  lemma MemoryNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L3PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L3PendingCallbackForAddr(c, v, addr, c_idx);
      assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
    }
  }


  lemma MemoryNoOpPreservesRevOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires v.WF(c)
    requires RevOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && L3PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L3PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L3PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v', addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }

  lemma MemoryNoOpPreservesOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires v.WF(c)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures OnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    MemoryNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
    MemoryNoOpPreservesRevOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
  }


  lemma ProxyNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires step.tile_step.proxy_step.CacheCommunicationStep?
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L3PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        assert OnMissInProgress(c, v, addr, c_idx) by {
          reveal InFlightOnMissRequest;
          var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
          assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
          assert InFlightOnMissRequest(c, v, addr, c_idx);
        }
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        assert OnMissInProgress(c, v, addr, c_idx) by {
          reveal CallbackPresent;
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
            && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
          assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        }
      } else {
        assert OnMissInProgress(c, v, addr, c_idx) by {
          reveal InFlightOnMissResponse;
          var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
          assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
          assert InFlightOnMissResponse(c, v, addr, c_idx);
        }
      }
      assert L3PendingCallbackForAddr(c, v, addr, c_idx);
      assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
    }
  }

  lemma ProxyNoOpPreservesRevOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires v.WF(c)
    requires RevOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && L3PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L3PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L3PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v', addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }


  lemma ProxyNoOpPreservesOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires v.WF(c)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures OnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    ProxyNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
    ProxyNoOpPreservesRevOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
  }

  lemma L3ReqMemoryNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L3PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L3PendingCallbackForAddr(c, v, addr, c_idx);
      assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
    }
  }

  lemma L3ReqMemoryNoOpPreservesRevOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires v.WF(c)
    requires RevOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && L3PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L3PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L3PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v', addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }

  lemma L3RespMemoryNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L3PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L3PendingCallbackForAddr(c, v, addr, c_idx);
      assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
    }
  }

  lemma L3RespMemoryNoOpPreservesRevOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires v.WF(c)
    requires RevOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && L3PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L3PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L3PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v', addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }

  lemma L3DirectoryNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L3PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L3PendingCallbackForAddr(c, v, addr, c_idx);
      assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
    }
  }

  lemma L3DirectoryNoOpPreservesRevOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires v.WF(c)
    requires RevOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && L3PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L3PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L3PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v', addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }

  lemma L3ReceiveCoherenceMessageNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L3PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L3PendingCallbackForAddr(c, v, addr, c_idx);
      assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
    }
  }

  lemma L3ReceiveCoherenceMessageNoOpPreservesRevOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires v.WF(c)
    requires RevOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && L3PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L3PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L3PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v', addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L3PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        if step.tile_step.l3_step.eng_req.OnMiss?
        && c_idx == step.tile_step.l3_step.eng_req.idx
        && addr == step.tile_step.l3_step.addr
        {
          // assert addr == step.tile_step.l2_step.addr;
          assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
        } else {
          var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
          assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
          assert InFlightOnMissRequest(c, v, addr, c_idx);
          assert OnMissInProgress(c, v, addr, c_idx);
          assert L3PendingCallbackForAddr(c, v, addr, c_idx);
        }
        assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
        assert L3PendingCallbackForAddr(c, v, addr, c_idx);
        assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
        assert L3PendingCallbackForAddr(c, v, addr, c_idx);
        assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
      }
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesRevOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires v.WF(c)
    requires RevOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && L3PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      if L3PendingCallbackForAddr(c, v, addr, c_idx) {
        assert OnMissInProgress(c, v, addr, c_idx);
        if InFlightOnMissRequest(c, v, addr, c_idx) {
          reveal InFlightOnMissRequest;
          var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
          assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
          assert InFlightOnMissRequest(c, v', addr, c_idx);
          assert OnMissInProgress(c, v', addr, c_idx);
        } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
          reveal CallbackPresent;
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
            && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
          assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
          assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
          assert OnMissInProgress(c, v', addr, c_idx);
        } else {
          reveal InFlightOnMissResponse;
          var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
          assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
          assert InFlightOnMissResponse(c, v', addr, c_idx);
          assert OnMissInProgress(c, v', addr, c_idx);
        }
      } else {
        assert !L3PendingCallbackForAddr(c, v, addr, c_idx);
        reveal L3PendingCallbackForAddr;
        assert c_idx == step.tile_step.l3_step.eng_req.idx;
        assert addr == step.tile_step.l3_step.addr;
        var idx := if addr in v.network.inFlightEngReqs then |v.network.inFlightEngReqs[addr]| else 0;
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx) by { reveal InFlightOnMissRequest; }
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }

  lemma L3ReceiveOnMissDataNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires v.WF(c)
    requires OnMissRequestOnlyCallbackOrResponse(c, v)
    requires OnMissRequestOnlyRequestOrCallback(c, v)
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    requires EachAddrCacheBoundMsgIsUnique(c, v)
    requires UniqueCacheBoundMsgPerAddr(c, v)
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L3PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L3PendingCallbackForAddr(c, v, addr, c_idx);
      if step.tile_step.l3_step.eng_resp.idx == c_idx && v.tiles[step.tile_idx].l3.cache[c_idx].addr == addr {
        assert IsInFlightOnMissResponse(c, v, addr, step.msgOps.recv.val, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx) by { reveal InFlightOnMissResponse; }
        assert !InFlightOnMissResponse(c, v', addr, c_idx) by {
          reveal InFlightOnMissResponse;
          if InFlightOnMissResponse(c, v', addr, c_idx) {
            var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
            assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
            assert msg == step.msgOps.recv.val;
            assert !IsInFlightOnMissResponse(c, v', addr, step.msgOps.recv.val, c_idx);
            assert false;
          }
        }
        assert !CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert !CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) by { reveal CallbackPresent; }
        assert !InFlightOnMissRequest(c, v', addr, c_idx) by { reveal InFlightOnMissRequest; }
        assert !OnMissInProgress(c, v', addr, c_idx);
        assert false;
      } else {
        assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
      }
    }
  }

  lemma L3ReceiveOnMissDataNoOpPreservesRevOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires v.WF(c)
    requires EachAddrCacheBoundMsgIsUnique(c, v)
    requires UniqueCacheBoundMsgPerAddr(c, v)
    requires RevOnMissInProgressIffCacheEntryPendingShared(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && L3PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L3PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L3PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v', addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        if IsInFlightOnMissResponse(c, v', addr, msg, c_idx) {
          assert InFlightOnMissResponse(c, v', addr, c_idx);
          assert OnMissInProgress(c, v', addr, c_idx);
        } else {
          assert msg == step.msgOps.recv.val;
          reveal L3PendingCallbackForAddr;
          assert !L3PendingCallbackForAddr(c, v', addr, c_idx);
          assert false;
        }
      }
    }
  }

  lemma L3NoOpPreservesOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires v.WF(c)
    requires OnMissRequestOnlyCallbackOrResponse(c, v)
    requires OnMissRequestOnlyRequestOrCallback(c, v)
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    requires EachAddrCacheBoundMsgIsUnique(c, v)
    requires UniqueCacheBoundMsgPerAddr(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures OnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    match step.tile_step.l3_step {
      case ReceiveCoherenceMessageStep() => {
        L3ReceiveCoherenceMessageNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
        L3ReceiveCoherenceMessageNoOpPreservesRevOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
      }
      case DirectoryStep(_, _, _) => {
        L3DirectoryNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
        L3DirectoryNoOpPreservesRevOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
      }
      case ScheduleCallbackStep(_, _, _) => {
        L3ScheduleCallbackNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
        L3ScheduleCallbackNoOpPreservesRevOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
      }
      case ReceiveOnMissDataStep(_) => {
        L3ReceiveOnMissDataNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
        L3ReceiveOnMissDataNoOpPreservesRevOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
      }
      case ReqMemoryStep(_, _) => {
        L3ReqMemoryNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
        L3ReqMemoryNoOpPreservesRevOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
      }
      case RespMemoryStep(_) => {
        L3RespMemoryNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
        L3RespMemoryNoOpPreservesRevOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
      }
    }
  }

  lemma L2CacheCommunicationNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires v.WF(c)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L3PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L3PendingCallbackForAddr(c, v, addr, c_idx);
      assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
    }
  }

  lemma L2DirectoryNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires v.WF(c)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L3PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L3PendingCallbackForAddr(c, v, addr, c_idx);
      assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires v.WF(c)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L3PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L3PendingCallbackForAddr(c, v, addr, c_idx);
      assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires v.WF(c)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L3PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L3PendingCallbackForAddr(c, v, addr, c_idx);
      assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires v.WF(c)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L3PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L3PendingCallbackForAddr(c, v, addr, c_idx);
      assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
    }
  }

  lemma L2NoOpPreservesRevOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires v.WF(c)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires RevOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && L3PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L3PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L3PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v', addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }

  lemma L2NoOpPreservesOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires v.WF(c)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures OnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    match step.tile_step.l2_step {
      case ReceiveCoherenceMessageStep() => {
        L2ReceiveCoherenceMessageNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
      }
      case DirectoryStep(_, _, _) => {
        L2DirectoryNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
      }
      case ScheduleCallbackStep(_, _, _) => {
        L2ScheduleCallbackNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
      }
      case ReceiveOnMissDataStep(_) => {
        L2ReceiveOnMissDataNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
      }
      case CacheCommunicationStep(_,_,_,_) => {
        L2CacheCommunicationNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
      }
    }
    L2NoOpPreservesRevOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
  }

  lemma EngineReceiveCallbackReqNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L3PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        var new_idx := if addr == step.msgOps.recv.val.meta.addr then idx + 1 else idx;
        assert IsInFlightOnMissRequest(c, v, addr, new_idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        if CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx) {
          assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
          assert OnMissInProgress(c, v, addr, c_idx);
        } else {
          assert addr == step.msgOps.recv.val.meta.addr;
          assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
          assert InFlightOnMissRequest(c, v, addr, c_idx) by { reveal InFlightOnMissRequest; }
          assert OnMissInProgress(c, v, addr, c_idx);
        }
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L3PendingCallbackForAddr(c, v, addr, c_idx);
      assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
    }
  }

  lemma EngineCacheCommunicationGetSNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.GetSStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L3PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L3PendingCallbackForAddr(c, v, addr, c_idx);
      assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
    }
  }

  lemma EngineCacheCommunicationGetMNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.GetMStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L3PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L3PendingCallbackForAddr(c, v, addr, c_idx);
      assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
    }
  }

  lemma EngineCacheCommunicationEvictNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.EvictStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L3PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L3PendingCallbackForAddr(c, v, addr, c_idx);
      assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
    }
  }

  lemma EngineCacheCommunicationRecvMsgNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.RecvMsgStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L3PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L3PendingCallbackForAddr(c, v, addr, c_idx);
      assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
    }
  }


  lemma EngineNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    match step.tile_step.eng_step {
      case CacheCommunicationStep(c_step, _, _, _) => {
        match c_step {
          case GetSStep() => {
            EngineCacheCommunicationGetSNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
          }
          case GetMStep() => {
            EngineCacheCommunicationGetMNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
          }
          case EvictStep() => {
            EngineCacheCommunicationEvictNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
          }
          case RecvMsgStep() => {
            EngineCacheCommunicationRecvMsgNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
          }
        }
      }
      case ReceiveCallbackReqStep(_) => {
        EngineReceiveCallbackReqNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
      }
      case _ => {
        assert false;
      }
    }
  }

  lemma EngineReceiveCallbackReqNoOpPreservesRevOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires v.WF(c)
    requires RevOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && L3PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L3PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L3PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx: nat :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        if IsInFlightOnMissRequest(c, v', addr, idx, c_idx) {
          assert InFlightOnMissRequest(c, v', addr, c_idx);
          assert OnMissInProgress(c, v', addr, c_idx);
        } else if idx > 0 && IsInFlightOnMissRequest(c, v', addr, idx - 1, c_idx) {
          assert InFlightOnMissRequest(c, v', addr, c_idx);
          assert OnMissInProgress(c, v', addr, c_idx);
        } else {
          // received, so now callback will be present
          // assert !IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
          assert idx == 0;
          assert step.msgOps.recv.val.engine_req.OnMiss?;
          assert step.msgOps.recv.val.engine_req == EngineRequest.OnMiss(c_idx);
          assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          // && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
          assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) by { reveal CallbackPresent; }
          assert OnMissInProgress(c, v', addr, c_idx);
        }
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v', addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }

  lemma EngineNotReceiveCallbackReqNoOpPreservesRevOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires !step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires v.WF(c)
    requires RevOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && L3PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L3PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L3PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v', addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }

  lemma EngineNoOpPreservesRevOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires v.WF(c)
    requires RevOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    if step.tile_step.eng_step.ReceiveCallbackReqStep? {
      EngineReceiveCallbackReqNoOpPreservesRevOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
    } else {
      EngineNotReceiveCallbackReqNoOpPreservesRevOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
    }
  }

  lemma EngineNoOpPreservesOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires v.WF(c)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures OnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    EngineNoOpPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
    EngineNoOpPreservesRevOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
  }

  lemma NoOpPreservesOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires v.WF(c)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires OnMissRequestOnlyCallbackOrResponse(c, v)
    requires OnMissRequestOnlyRequestOrCallback(c, v)
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    requires EachAddrCacheBoundMsgIsUnique(c, v)
    requires UniqueCacheBoundMsgPerAddr(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures OnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    match step {
      case MemoryStep(msgOps) => {
        MemoryNoOpPreservesOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
      }
      case TileStep(tile_idx, tile_step, msgOps) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
          }
          case L2Step(l2_step) => {
            L2NoOpPreservesOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
          }
          case L3Step(l3_step) => {
            L3NoOpPreservesOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
          }
          case EngineStep(eng_step) => {
            EngineNoOpPreservesOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
          }
          case ProxyStep(proxy_step) => {
            ProxyNoOpPreservesOnMissInProgressIffCacheEntryPendingShared(c, v, v', step);
          }
        }
      }
    }
  }

  ///////////////////////////////////////////////////////////////////
  // Perform Inst Cases
  ///////////////////////////////////////////////////////////////////
  lemma PerformNextInstFwdPreservesOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires v.WF(c)
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L3PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L3PendingCallbackForAddr(c, v, addr, c_idx);
      assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
    }
  }

  lemma PerformNextInstRevPreservesOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires v.WF(c)
    requires RevOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && L3PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L3PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L3PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v', addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }

  lemma PerformNextInstPreservesOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires v.WF(c)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures OnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    PerformNextInstFwdPreservesOnMissInProgressIffCacheEntryPendingShared(c, v, v', step, re);
    PerformNextInstRevPreservesOnMissInProgressIffCacheEntryPendingShared(c, v, v', step, re);
  }

  ///////////////////////////////////////////////////////////////////
  // Start/End CB Cases
  ///////////////////////////////////////////////////////////////////
  lemma StartCBPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L3PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      }
      assert L3PendingCallbackForAddr(c, v, addr, c_idx);
      assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
    }
  }

  lemma StartCBPreservesRevOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback
    requires RevOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && L3PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L3PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L3PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v', addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }


  lemma StartCBPreservesOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures OnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    StartCBPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c, v, v', step, re);
    StartCBPreservesRevOnMissInProgressIffCacheEntryPendingShared(c, v, v', step, re);
  }


  lemma EndCBPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict || re == EndOnMiss || re == EndOnWriteback
    requires FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures FwdOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && OnMissInProgress(c, v', addr, c_idx)
      ensures L3PendingCallbackForAddr(c, v', addr, c_idx)
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        assert OnMissInProgress(c, v, addr, c_idx);
      } else if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert OnMissInProgress(c, v, addr, c_idx);
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        if IsInFlightOnMissResponse(c, v, addr, msg, c_idx) {
          assert InFlightOnMissResponse(c, v, addr, c_idx);
          assert OnMissInProgress(c, v, addr, c_idx);
        } else {
          assert msg in step.msgOps.send;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) by { reveal CallbackPresent; }
          assert OnMissInProgress(c, v, addr, c_idx);
        }
      }
      assert L3PendingCallbackForAddr(c, v, addr, c_idx);
      assert L3PendingCallbackForAddr(c, v', addr, c_idx) by { reveal L3PendingCallbackForAddr; }
    }
  }

  lemma EndCBPreservesRevOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict || re == EndOnMiss || re == EndOnWriteback
    requires RevOnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures RevOnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && L3PendingCallbackForAddr(c, v', addr, c_idx)
      ensures OnMissInProgress(c, v', addr, c_idx)
    {
      assert L3PendingCallbackForAddr(c, v, addr, c_idx) by { reveal L3PendingCallbackForAddr; }
      assert OnMissInProgress(c, v, addr, c_idx);
      if InFlightOnMissRequest(c, v, addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      } else if CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf)
          && v.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        if CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx) {
          assert CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx));
          assert OnMissInProgress(c, v', addr, c_idx);
        } else {
          // this entry finished, so response should exist
          var msg :| msg in step.msgOps.send;
          assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
          assert InFlightOnMissResponse(c, v', addr, c_idx) by { reveal InFlightOnMissResponse; }
          assert OnMissInProgress(c, v', addr, c_idx);
        }
      } else {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        assert OnMissInProgress(c, v', addr, c_idx);
      }
    }
  }


  lemma EndCBPreservesOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict || re == EndOnMiss || re == EndOnWriteback
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures OnMissInProgressIffCacheEntryPendingShared(c, v')
  {
    EndCBPreservesFwdOnMissInProgressIffCacheEntryPendingShared(c, v, v', step, re);
    EndCBPreservesRevOnMissInProgressIffCacheEntryPendingShared(c, v, v', step, re);
  }
}