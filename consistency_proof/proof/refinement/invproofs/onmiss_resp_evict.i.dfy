include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module OnMissResponseNoEvictProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes
  import opened CacheTypes

  lemma CoreCacheCommunicationGetSNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.step.GetSStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma CoreCacheCommunicationGetMNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.step.GetMStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma CoreCacheCommunicationEvictNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.step.EvictStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma CoreCacheCommunicationRecvMsgNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.step.RecvMsgStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma ProxyCacheCommunicationGetSNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires step.tile_step.proxy_step.step.GetSStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma ProxyCacheCommunicationGetMNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires step.tile_step.proxy_step.step.GetMStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma ProxyCacheCommunicationEvictNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires step.tile_step.proxy_step.step.EvictStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma ProxyCacheCommunicationRecvMsgNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep? 
    requires step.tile_step.proxy_step.step.RecvMsgStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      assert InFlightOnMissResponse(c, v, addr, c_idx) by {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      }
      if OnEvictInProgress(c, v', addr, val) {
        if InFlightOnEvictRequest(c, v', addr, val) {
          assert OnEvictInProgress(c, v, addr, val) by {
            reveal InFlightOnEvictRequest;
            var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
            assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
            assert InFlightOnEvictRequest(c, v, addr, val);
          }
          assert false;
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val) by {
            reveal CallbackPresent;
            var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
              && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
            assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
            assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          }
          assert false;
        }
      }
    }
  }

  lemma MemoryNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma EngineCacheCommunicationGetSNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.GetSStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma EngineCacheCommunicationGetMNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.GetMStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma EngineCacheCommunicationEvictNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.EvictStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma EngineCacheCommunicationRecvMsgNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.RecvMsgStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma EngineReceiveCallbackReqNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          if CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf) {
            assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
            assert OnEvictInProgress(c, v, addr, val);
            assert false;
          } else {
            assert IsInFlightOnEvictRequest(c, v, addr, 0, val);
            assert InFlightOnEvictRequest(c, v, addr, val) by { reveal InFlightOnEvictRequest; }
            assert OnEvictInProgress(c, v, addr, val);
            assert false;
          }
        }
      }
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires L2AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
      if OnEvictInProgress(c, v', addr, val) {
        if InFlightOnEvictRequest(c, v', addr, val) {
          reveal InFlightOnEvictRequest;
          var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
          if IsInFlightOnEvictRequest(c, v, addr, idx, val) {
            assert InFlightOnEvictRequest(c, v, addr, val);
            assert OnEvictInProgress(c, v, addr, val);
            assert false;
          } else {
            assert OnMissInProgress(c, v, addr, c_idx);
            reveal L2PendingCallbackForAddr;
            assert false;
          }
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L2CacheCommunicationGetSNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires step.tile_step.l2_step.c_step.GetSStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L2CacheCommunicationGetMNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires step.tile_step.l2_step.c_step.GetMStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L2CacheCommunicationEvictNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires step.tile_step.l2_step.c_step.EvictStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L2CacheCommunicationRecvMsgNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires step.tile_step.l2_step.c_step.RecvMsgStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L2DirectoryNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires L3AddressesUnique(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
      if OnEvictInProgress(c, v', addr, val) {
        if InFlightOnEvictRequest(c, v', addr, val) {
          reveal InFlightOnEvictRequest;
          var idx :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
          if IsInFlightOnEvictRequest(c, v, addr, idx, val) {
            assert InFlightOnEvictRequest(c, v, addr, val);
            assert OnEvictInProgress(c, v, addr, val);
            assert false;
          } else {
            assert OnMissInProgress(c, v, addr, c_idx);
            reveal L3PendingCallbackForAddr;
            assert false;
          }
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
          reveal CallbackPresent;
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L3ReceiveCoherenceMessageNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L3ReceiveOnMissDataNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L3DirectoryNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L3ReqMemoryNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L3RespMemoryNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma NoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    requires L2AddressesUnique(c, v)
    requires L3AddressesUnique(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    match step {
      case TileStep(_, tile_step, _) => {
        match tile_step {
          case CoreStep(core_step) => {
            assert core_step.CacheCommunicationStep?;
            match core_step.step {
              case GetSStep() => {
                CoreCacheCommunicationGetSNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
              }
              case GetMStep() => {
                CoreCacheCommunicationGetMNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
              }
              case EvictStep() => {
                CoreCacheCommunicationEvictNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
              }
              case RecvMsgStep() => {
                CoreCacheCommunicationRecvMsgNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
              }
            }
          }
          case ProxyStep(proxy_step) => {
            assert proxy_step.CacheCommunicationStep?;
            match proxy_step.step {
              case GetSStep() => {
                ProxyCacheCommunicationGetSNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
              }
              case GetMStep() => {
                ProxyCacheCommunicationGetMNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
              }
              case EvictStep() => {
                ProxyCacheCommunicationEvictNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
              }
              case RecvMsgStep() => {
                ProxyCacheCommunicationRecvMsgNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
              }
            }
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
              }
              case CacheCommunicationStep(c_step,_,_,_) => {
                match c_step {
                  case GetSStep() => {
                    L2CacheCommunicationGetSNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
                  }
                  case GetMStep() => {
                    L2CacheCommunicationGetMNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
                  }
                  case EvictStep() => {
                    L2CacheCommunicationEvictNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
                  }
                  case RecvMsgStep() => {
                    L2CacheCommunicationRecvMsgNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
                  }
                }
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            match l3_step {
              case RespMemoryStep(_) => {
                L3RespMemoryNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
              }
              case ReqMemoryStep(_,_) => {
                L3ReqMemoryNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L3DirectoryNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L3ScheduleCallbackNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L3ReceiveCoherenceMessageNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L3ReceiveOnMissDataNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
              }
            }

          }
          case EngineStep(engine_step) => {
            match engine_step {
              case CacheCommunicationStep(c_step,_,_,_) => {
                match c_step {
                  case GetSStep() => {
                    EngineCacheCommunicationGetSNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
                  }
                  case GetMStep() => {
                    EngineCacheCommunicationGetMNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
                  }
                  case EvictStep() => {
                    EngineCacheCommunicationEvictNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
                  }
                  case RecvMsgStep() => {
                    EngineCacheCommunicationRecvMsgNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
                  }
                }
              }
              case ReceiveCallbackReqStep(_) => {
                EngineReceiveCallbackReqNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
              }
              case _ => {
                assert false;
              }
            }
          }
        }
      }
      case MemoryStep(_) => {
        MemoryNoOpPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step);
      }
    }
  }

  lemma PerformNextInstPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma StartCBPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma EndOnEvictPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
        }
        assert OnEvictInProgress(c, v, addr, val);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        // need to circle around here too. this isn't possible because
        // that would mean an onmiss finished in engine while evict was queued (not possible)
        // that is not possible because you can't have evict scheduled (request) before onmiss finishes
        // have to be very careful however, as you can have onmiss following an eviction around
        // i.e. miss chasing evict okay, evict chasing miss not.
        if IsInFlightOnMissResponse(c, v, addr, msg, c_idx) {
          assert InFlightOnMissResponse(c, v, addr, c_idx);
        } else {
          assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
        }
        assert false;
      }
    }
  }

  lemma EndOnWritebackPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnWriteback
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
        }
        assert OnEvictInProgress(c, v, addr, val);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        // need to circle around here too. this isn't possible because
        // that would mean an onmiss finished in engine while evict was queued (not possible)
        // that is not possible because you can't have evict scheduled (request) before onmiss finishes
        // have to be very careful however, as you can have onmiss following an eviction around
        // i.e. miss chasing evict okay, evict chasing miss not.
        if IsInFlightOnMissResponse(c, v, addr, msg, c_idx) {
          assert InFlightOnMissResponse(c, v, addr, c_idx);
        } else {
          assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
        }
        assert false;
      }
    }
  }

  lemma EndOnMissPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnMiss
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnEvictInProgress(c, v', addr, val)
    {
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnEvict(val));
          assert OnEvictInProgress(c, v, addr, val);
        }
        assert OnEvictInProgress(c, v, addr, val);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        // need to circle around here too. this isn't possible because
        // that would mean an onmiss finished in engine while evict was queued (not possible)
        // that is not possible because you can't have evict scheduled (request) before onmiss finishes
        // have to be very careful however, as you can have onmiss following an eviction around
        // i.e. miss chasing evict okay, evict chasing miss not.
        if IsInFlightOnMissResponse(c, v, addr, msg, c_idx) {
          assert InFlightOnMissResponse(c, v, addr, c_idx);
        } else {
          assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx));
        }
        assert false;
      }
    }
  }

  lemma EndCBPreservesInFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict || re == EndOnMiss || re == EndOnWriteback
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoEvictInProgress(c, v')
  {
    if re == EndOnEvict {
      EndOnEvictPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step, re);
    } else if re == EndOnMiss {
      EndOnMissPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step, re);
    } else {
      assert re == EndOnWriteback;
      EndOnWritebackPreservesInFlightOnMissResponseMeansNoEvictInProgress(c, v, v', step, re);
    }
  }
}