include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module OnMissResponseNoWritebackProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes
  import opened CacheTypes

  lemma CoreCacheCommunicationNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      assert InFlightOnMissResponse(c, v, addr, c_idx) by {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      }
      if OnWritebackInProgress(c, v', addr, val) {
        if InFlightOnWritebackRequest(c, v', addr, val) {
          assert OnWritebackInProgress(c, v, addr, val) by {
            reveal InFlightOnWritebackRequest;
            var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
            assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
            assert InFlightOnWritebackRequest(c, v, addr, val);
          }
          assert false;
        } else {
          assert OnWritebackInProgress(c, v, addr, val) by {
            assert CallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
            reveal CallbackPresent;
            var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
              && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
            assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
            assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          }
          assert false;
        }
      }
    }
  }

  lemma ProxyCacheCommunicationGetSNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires step.tile_step.proxy_step.step.GetSStep?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma ProxyCacheCommunicationGetMNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires step.tile_step.proxy_step.step.GetMStep?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma ProxyCacheCommunicationEvictNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires step.tile_step.proxy_step.step.EvictStep?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma ProxyCacheCommunicationRecvMsgNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires step.tile_step.proxy_step.step.RecvMsgStep?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      assert InFlightOnMissResponse(c, v, addr, c_idx) by {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      }
      if OnWritebackInProgress(c, v', addr, val) {
        if InFlightOnWritebackRequest(c, v', addr, val) {
          assert OnWritebackInProgress(c, v, addr, val) by {
            reveal InFlightOnWritebackRequest;
            var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
            assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
            assert InFlightOnWritebackRequest(c, v, addr, val);
          }
          assert false;
        } else {
          assert OnWritebackInProgress(c, v, addr, val) by {
            assert CallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
            reveal CallbackPresent;
            var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
              && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
            assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
            assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          }
          assert false;
        }
      }
    }
  }

  lemma MemoryNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma EngineCacheCommunicationGetSNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.GetSStep?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma EngineCacheCommunicationGetMNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.GetMStep?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma EngineCacheCommunicationEvictNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.EvictStep?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma EngineCacheCommunicationRecvMsgDataNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.RecvMsgStep?
    requires step.msgOps.recv.val.coh_msg.Data?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma EngineCacheCommunicationRecvMsgInvAckNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.RecvMsgStep?
    requires step.msgOps.recv.val.coh_msg.InvAck?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma EngineCacheCommunicationRecvMsgInvNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.RecvMsgStep?
    requires step.msgOps.recv.val.coh_msg.Inv?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma EngineCacheCommunicationRecvMsgFwdGetMNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.RecvMsgStep?
    requires step.msgOps.recv.val.coh_msg.FwdGetM?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma EngineCacheCommunicationRecvMsgFwdGetSNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.RecvMsgStep?
    requires step.msgOps.recv.val.coh_msg.FwdGetS?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma EngineCacheCommunicationRecvMsgPutAckNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.RecvMsgStep?
    requires step.msgOps.recv.val.coh_msg.PutAck?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma EngineCacheCommunicationRecvMsgPutAckStaleNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.RecvMsgStep?
    requires step.msgOps.recv.val.coh_msg.PutAckStale?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma EngineCacheCommunicationRecvMsgNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(
      c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.RecvMsgStep?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    match step.msgOps.recv.val.coh_msg {
      case Data(_,_) => EngineCacheCommunicationRecvMsgDataNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
      case InvAck() => EngineCacheCommunicationRecvMsgInvAckNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
      case Inv() => EngineCacheCommunicationRecvMsgInvNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
      case FwdGetM() => EngineCacheCommunicationRecvMsgFwdGetMNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
      case FwdGetS() => EngineCacheCommunicationRecvMsgFwdGetSNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
      case PutAck() => EngineCacheCommunicationRecvMsgPutAckNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
      case PutAckStale() => EngineCacheCommunicationRecvMsgPutAckStaleNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
      case _ => assert false; // This should not happen as per the requires clause
    }
  }

  lemma EngineReceiveCallbackReqNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          if CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf) {
            assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
            assert OnWritebackInProgress(c, v, addr, val);
            assert false;
          } else {
            assert IsInFlightOnWritebackRequest(c, v, addr, 0, val);
            assert InFlightOnWritebackRequest(c, v, addr, val) by { reveal InFlightOnWritebackRequest; }
            assert OnWritebackInProgress(c, v, addr, val);
            assert false;
          }
        }
      }
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires L2AddressesUnique(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
      if OnWritebackInProgress(c, v', addr, val) {
        if InFlightOnWritebackRequest(c, v', addr, val) {
          reveal InFlightOnWritebackRequest;
          var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
          if IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
            assert InFlightOnWritebackRequest(c, v, addr, val);
            assert OnWritebackInProgress(c, v, addr, val);
            assert false;
          } else {
            assert OnMissInProgress(c, v, addr, c_idx);
            reveal L2PendingCallbackForAddr;
            assert false;
          }
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L2CacheCommunicationGetSNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires step.tile_step.l2_step.c_step.GetSStep?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L2CacheCommunicationGetMNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires step.tile_step.l2_step.c_step.GetMStep?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L2CacheCommunicationEvictNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires step.tile_step.l2_step.c_step.EvictStep?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L2CacheCommunicationRecvMsgNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires step.tile_step.l2_step.c_step.RecvMsgStep?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L2DirectoryNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires L3AddressesUnique(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
      if OnWritebackInProgress(c, v', addr, val) {
        if InFlightOnWritebackRequest(c, v', addr, val) {
          reveal InFlightOnWritebackRequest;
          var idx :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
          if IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
            assert InFlightOnWritebackRequest(c, v, addr, val);
            assert OnWritebackInProgress(c, v, addr, val);
            assert false;
          } else {
            assert OnMissInProgress(c, v, addr, c_idx);
            reveal L3PendingCallbackForAddr;
            assert false;
          }
        } else {
          assert CallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
          reveal CallbackPresent;
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma L3NotScheduleCallbackNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires !step.tile_step.l3_step.ScheduleCallbackStep?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma NoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    requires L2AddressesUnique(c, v)
    requires L3AddressesUnique(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    match step {
      case TileStep(_, tile_step, _) => {
        match tile_step {
          case CoreStep(core_step) => {
            CoreCacheCommunicationNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
          }
          case ProxyStep(proxy_step) => {
            match proxy_step.step {
              case GetSStep() => {
                ProxyCacheCommunicationGetSNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
              }
              case GetMStep() => {
                ProxyCacheCommunicationGetMNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
              }
              case EvictStep() => {
                ProxyCacheCommunicationEvictNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
              }
              case RecvMsgStep() => {
                ProxyCacheCommunicationRecvMsgNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
              }
            }
          }
          case L2Step(l2_step) => {
            match l2_step {
              case CacheCommunicationStep(c_step,_,_,_) => {
                match c_step {
                  case GetSStep() => {
                    L2CacheCommunicationGetSNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
                  }
                  case GetMStep() => {
                    L2CacheCommunicationGetMNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
                  }
                  case EvictStep() => {
                    L2CacheCommunicationEvictNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
                  }
                  case RecvMsgStep() => {
                    L2CacheCommunicationRecvMsgNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
                  }
                }
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
              }
            }
          }
          case L3Step(_) => {
            if step.tile_step.l3_step.ScheduleCallbackStep? {
              L3ScheduleCallbackNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
            } else {
              L3NotScheduleCallbackNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
            }
          }
          case EngineStep(e_step) => {
            match e_step {
              case CacheCommunicationStep(c_step,_,_,_) => {
                match c_step {
                  case GetSStep() => {
                    EngineCacheCommunicationGetSNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
                  }
                  case GetMStep() => {
                    EngineCacheCommunicationGetMNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
                  }
                  case EvictStep() => {
                    EngineCacheCommunicationEvictNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
                  }
                  case RecvMsgStep() => {
                    EngineCacheCommunicationRecvMsgNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
                  }
                }
              }
              case ReceiveCallbackReqStep(_) => {
                EngineReceiveCallbackReqNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
              }
              case _ => {
                assert false;
              }
            }
          }
        }
      }
      case MemoryStep(_) => {
        MemoryNoOpPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step);
      }
    }
  }

  lemma PerformNextInstPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma StartCBPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
      reveal InFlightOnMissResponse;
      var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
      assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      assert InFlightOnMissResponse(c, v, addr, c_idx);
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
          assert false;
        }
      }
    }
  }

  lemma EndOnEvictPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict || re == EndOnMiss || re == EndOnWriteback
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
        }
        assert OnWritebackInProgress(c, v, addr, val);
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

  lemma EndOnMissPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict || re == EndOnMiss || re == EndOnWriteback
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
        }
        assert OnWritebackInProgress(c, v, addr, val);
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

  lemma EndOnWritebackPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict || re == EndOnMiss || re == EndOnWriteback
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    forall addr, c_idx, val | InFlightOnMissResponse(c, v', addr, c_idx)
      ensures !OnWritebackInProgress(c, v', addr, val)
    {
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
          var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, tile, buf)
            && v'.tiles[tile].engine.buffer[buf].cb_type.val == val;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf);
          assert CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val));
          assert OnWritebackInProgress(c, v, addr, val);
        }
        assert OnWritebackInProgress(c, v, addr, val);
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

  lemma EndCBPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict || re == EndOnMiss || re == EndOnWriteback
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures InFlightOnMissResponseMeansNoWritebackInProgress(c, v')
  {
    if re == EndOnEvict {
      EndOnEvictPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step, re);
    } else if re == EndOnMiss {
      EndOnMissPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step, re);
    } else {
      assert re == EndOnWriteback;
      EndOnWritebackPreservesInFlightOnMissResponseMeansNoWritebackInProgress(c, v, v', step, re);
    }
  }
}