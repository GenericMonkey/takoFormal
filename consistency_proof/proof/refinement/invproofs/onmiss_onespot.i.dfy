include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module OnMissRequestOneSpotProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes
  import opened CacheTypes

  lemma CoreNoOpPreservesOnMissRequestOnlyCallbackOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires v.WF(c)
    requires OnMissRequestOnlyCallbackOrResponse(c, v)
    ensures OnMissRequestOnlyCallbackOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma ProxyNoOpPreservesOnMissRequestOnlyCallbackOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires v.WF(c)
    requires OnMissRequestOnlyCallbackOrResponse(c, v)
    ensures OnMissRequestOnlyCallbackOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma L2CacheCommunicationNoOpPreservesOnMissRequestOnlyCallbackOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires v.WF(c)
    requires OnMissRequestOnlyCallbackOrResponse(c, v)
    ensures OnMissRequestOnlyCallbackOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma L2DirectoryNoOpPreservesOnMissRequestOnlyCallbackOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires v.WF(c)
    requires OnMissRequestOnlyCallbackOrResponse(c, v)
    ensures OnMissRequestOnlyCallbackOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesOnMissRequestOnlyCallbackOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires v.WF(c)
    requires OnMissRequestOnlyCallbackOrResponse(c, v)
    ensures OnMissRequestOnlyCallbackOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesOnMissRequestOnlyCallbackOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires v.WF(c)
    requires OnMissRequestOnlyCallbackOrResponse(c, v)
    ensures OnMissRequestOnlyCallbackOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesOnMissRequestOnlyCallbackOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires v.WF(c)
    requires OnMissRequestOnlyCallbackOrResponse(c, v)
    ensures OnMissRequestOnlyCallbackOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma MemoryNoOpPreservesOnMissRequestOnlyCallbackOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires v.WF(c)
    requires OnMissRequestOnlyCallbackOrResponse(c, v)
    ensures OnMissRequestOnlyCallbackOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma L3NoOpPreservesOnMissRequestOnlyCallbackOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires v.WF(c)
    requires OnMissRequestOnlyCallbackOrResponse(c, v)
    ensures OnMissRequestOnlyCallbackOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma EngineNotReceiveCallbackReqNoOpPreservesOnMissRequestOnlyCallbackOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires !step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires v.WF(c)
    requires OnMissRequestOnlyCallbackOrResponse(c, v)
    ensures OnMissRequestOnlyCallbackOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma EngineReceiveCallbackReqNoOpPreservesOnMissRequestOnlyCallbackOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires v.WF(c)
    requires OnMissRequestOnlyCallbackOrResponse(c, v)
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyCallbackOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        reveal CallbackPresent;
        var tile: nat, buf: nat :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        if CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf) {
          assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
          assert false;
        } else {
          assert buf == step.tile_step.eng_step.idx;
          assert IsInFlightOnMissRequest(c, v, addr, 0, c_idx);
          assert InFlightOnMissRequest(c, v, addr, c_idx) by { reveal InFlightOnMissRequest; }
          assert false;
        }
      }
    }
  }

  lemma NoOpPreservesOnMissRequestOnlyCallbackOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires v.WF(c)
    requires OnMissRequestOnlyCallbackOrResponse(c, v)
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyCallbackOrResponse(c, v')
  {
    match step {
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesOnMissRequestOnlyCallbackOrResponse(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesOnMissRequestOnlyCallbackOrResponse(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesOnMissRequestOnlyCallbackOrResponse(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesOnMissRequestOnlyCallbackOrResponse(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesOnMissRequestOnlyCallbackOrResponse(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesOnMissRequestOnlyCallbackOrResponse(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesOnMissRequestOnlyCallbackOrResponse(c, v, v', step);
              }
            }
          }
          case L3Step(_) => {
            L3NoOpPreservesOnMissRequestOnlyCallbackOrResponse(c, v, v', step);
          }
          case EngineStep(eng_step) => {
            if eng_step.ReceiveCallbackReqStep? {
              EngineReceiveCallbackReqNoOpPreservesOnMissRequestOnlyCallbackOrResponse(c, v, v', step);
            } else {
              EngineNotReceiveCallbackReqNoOpPreservesOnMissRequestOnlyCallbackOrResponse(c, v, v', step);
            }
          }
        }
      }
      case MemoryStep(_) => {
        MemoryNoOpPreservesOnMissRequestOnlyCallbackOrResponse(c, v, v', step);
      }
    }
  }

  lemma PerformNextInstPreservesOnMissRequestOnlyCallbackOrResponse(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires OnMissRequestOnlyCallbackOrResponse(c, v)
    ensures OnMissRequestOnlyCallbackOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma StartCBPreservesOnMissRequestOnlyCallbackOrResponse(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback
    requires OnMissRequestOnlyCallbackOrResponse(c, v)
    ensures OnMissRequestOnlyCallbackOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma EndCBPreservesOnMissRequestOnlyCallbackOrResponse(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict || re == EndOnMiss || re == EndOnWriteback
    requires OnMissRequestOnlyCallbackOrResponse(c, v)
    requires UniqueTileForCallbackAddr(c, v)
    ensures OnMissRequestOnlyCallbackOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        if IsInFlightOnMissResponse(c, v, addr, msg, c_idx) {
          assert InFlightOnMissResponse(c, v, addr, c_idx);
          assert false;
        } else {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          assert tile == step.tile_idx;
          assert buf == step.tile_step.eng_step.idx;
          assert msg in step.msgOps.send;
          assert false;
        }
      }
    }
  }

  lemma CoreNoOpPreservesOnMissRequestOnlyRequestOrCallback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires v.WF(c)
    requires OnMissRequestOnlyRequestOrCallback(c, v)
    ensures OnMissRequestOnlyRequestOrCallback(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert false;
      }
    }
  }

  lemma ProxyNoOpPreservesOnMissRequestOnlyRequestOrCallback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires v.WF(c)
    requires OnMissRequestOnlyRequestOrCallback(c, v)
    ensures OnMissRequestOnlyRequestOrCallback(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert false;
      }
    }
  }

  lemma MemoryNoOpPreservesOnMissRequestOnlyRequestOrCallback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires v.WF(c)
    requires OnMissRequestOnlyRequestOrCallback(c, v)
    ensures OnMissRequestOnlyRequestOrCallback(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert false;
      }
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesOnMissRequestOnlyRequestOrCallback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires v.WF(c)
    requires OnMissRequestOnlyRequestOrCallback(c, v)
    ensures OnMissRequestOnlyRequestOrCallback(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert false;
      }
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesOnMissRequestOnlyRequestOrCallback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires v.WF(c)
    requires OnMissRequestOnlyRequestOrCallback(c, v)
    ensures OnMissRequestOnlyRequestOrCallback(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert false;
      }
    }
  }
  lemma L2CacheCommunicationNoOpPreservesOnMissRequestOnlyRequestOrCallback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires v.WF(c)
    requires OnMissRequestOnlyRequestOrCallback(c, v)
    ensures OnMissRequestOnlyRequestOrCallback(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert false;
      }
    }
  }
  
  lemma L2DirectoryNoOpPreservesOnMissRequestOnlyRequestOrCallback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires v.WF(c)
    requires OnMissRequestOnlyRequestOrCallback(c, v)
    ensures OnMissRequestOnlyRequestOrCallback(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert false;
      }
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesOnMissRequestOnlyRequestOrCallback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires v.WF(c)
    requires OnMissRequestOnlyRequestOrCallback(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures OnMissRequestOnlyRequestOrCallback(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        if IsInFlightOnMissRequest(c, v, addr, idx, c_idx) {
          assert InFlightOnMissRequest(c, v, addr, c_idx);
          assert false;
        } else {
          var msg :| msg in step.msgOps.send;
          assert addr == msg.meta.addr;
          assert OnMissInProgress(c, v, addr, c_idx);
          reveal L2PendingCallbackForAddr;
          assert false;
        }
      }
    }
  }

  lemma L3NotScheduleCallbackNoOpPreservesOnMissRequestOnlyRequestOrCallback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires !step.tile_step.l3_step.ScheduleCallbackStep?
    requires v.WF(c)
    requires OnMissRequestOnlyRequestOrCallback(c, v)
    ensures OnMissRequestOnlyRequestOrCallback(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert false;
      }
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesOnMissRequestOnlyRequestOrCallback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires v.WF(c)
    requires OnMissRequestOnlyRequestOrCallback(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures OnMissRequestOnlyRequestOrCallback(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        if IsInFlightOnMissRequest(c, v, addr, idx, c_idx) {
          assert InFlightOnMissRequest(c, v, addr, c_idx);
          assert false;
        } else {
          var msg :| msg in step.msgOps.send;
          assert addr == msg.meta.addr;
          assert OnMissInProgress(c, v, addr, c_idx);
          reveal L3PendingCallbackForAddr;
          assert false;
        }
      }
    }
  }

  lemma EngineNotReceiveCallbackReqNoOpPreservesOnMissRequestOnlyRequestOrCallback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires !step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires v.WF(c)
    requires OnMissRequestOnlyRequestOrCallback(c, v)
    ensures OnMissRequestOnlyRequestOrCallback(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert false;
      }
    }
  }

  lemma EngineReceiveCallbackReqNoOpPreservesOnMissRequestOnlyRequestOrCallback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires v.WF(c)
    requires OnMissRequestOnlyRequestOrCallback(c, v)
    requires EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    ensures OnMissRequestOnlyRequestOrCallback(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        var old_idx := if addr == step.msgOps.recv.val.meta.addr then idx + 1 else idx;
        assert IsInFlightOnMissRequest(c, v, addr, old_idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf)
          && v'.tiles[tile].engine.buffer[buf].cb_type == EngineRequest.OnMiss(c_idx);
        if CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf) {
          assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
          assert false;
        } else {
          assert addr == step.msgOps.recv.val.meta.addr;
          assert InFlightEngineRequest(c, v, addr, old_idx);
          assert InFlightEngineRequest(c, v, addr, 0);
          assert false;
        }
      }
    }
  }


  lemma NoOpPreservesOnMissRequestOnlyRequestOrCallback(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires v.WF(c)
    requires OnMissRequestOnlyRequestOrCallback(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    ensures OnMissRequestOnlyRequestOrCallback(c, v')
  {
    match step {
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesOnMissRequestOnlyRequestOrCallback(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesOnMissRequestOnlyRequestOrCallback(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesOnMissRequestOnlyRequestOrCallback(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesOnMissRequestOnlyRequestOrCallback(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesOnMissRequestOnlyRequestOrCallback(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesOnMissRequestOnlyRequestOrCallback(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesOnMissRequestOnlyRequestOrCallback(c, v, v', step);
              }
            }
          }
          case L3Step(_) => {
            if tile_step.l3_step.ScheduleCallbackStep? {
              L3ScheduleCallbackNoOpPreservesOnMissRequestOnlyRequestOrCallback(c, v, v', step);
            } else {
              L3NotScheduleCallbackNoOpPreservesOnMissRequestOnlyRequestOrCallback(c, v, v', step);
            }
          }
          case EngineStep(eng_step) => {
            if eng_step.ReceiveCallbackReqStep? {
              EngineReceiveCallbackReqNoOpPreservesOnMissRequestOnlyRequestOrCallback(c, v, v', step);
            } else {
              EngineNotReceiveCallbackReqNoOpPreservesOnMissRequestOnlyRequestOrCallback(c, v, v', step);
            }
          }
        }
      }
      case MemoryStep(_) => {
        MemoryNoOpPreservesOnMissRequestOnlyRequestOrCallback(c, v, v', step);
      }
    }
  }

  lemma PerformNextInstPreservesOnMissRequestOnlyRequestOrCallback(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires OnMissRequestOnlyRequestOrCallback(c, v)
    ensures OnMissRequestOnlyRequestOrCallback(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert false;
      }
    }
  }

  lemma StartCBPreservesOnMissRequestOnlyRequestOrCallback(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
    requires OnMissRequestOnlyRequestOrCallback(c, v)
    ensures OnMissRequestOnlyRequestOrCallback(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert false;
      }
    }
  }

  lemma EndCBPreservesOnMissRequestOnlyRequestOrCallback(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires OnMissRequestOnlyRequestOrCallback(c, v)
    ensures OnMissRequestOnlyRequestOrCallback(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && CallbackPresent(c, v', addr, EngineRequest.OnMiss(c_idx)) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal CallbackPresent;
        var tile, buf :| CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf);
        assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
        assert false;
      }
    }
  }

  lemma StartEndCBPreservesOnMissRequestOnlyRequestOrCallback(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires OnMissRequestOnlyRequestOrCallback(c, v)
    ensures OnMissRequestOnlyRequestOrCallback(c, v')
  {
    if re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback {
      StartCBPreservesOnMissRequestOnlyRequestOrCallback(c, v, v', step, re);
    } else if re == EndOnEvict || re == EndOnMiss || re == EndOnWriteback {
      EndCBPreservesOnMissRequestOnlyRequestOrCallback(c, v, v', step, re);
    }
  }

  lemma CoreCacheCommunicationGetSNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires step.tile_step.core_step.step.GetSStep?
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma CoreCacheCommunicationGetMNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires step.tile_step.core_step.step.GetMStep?
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma CoreCacheCommunicationEvictNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires step.tile_step.core_step.step.EvictStep?
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma CoreCacheCommunicationRecvMsgNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires step.tile_step.core_step.step.RecvMsgStep?
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma CoreNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    assert step.tile_step.core_step.CacheCommunicationStep?;
    match step.tile_step.core_step.step {
      case GetSStep() => {
        CoreCacheCommunicationGetSNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
      }
      case GetMStep() => {
        CoreCacheCommunicationGetMNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
      }
      case EvictStep() => {
        CoreCacheCommunicationEvictNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
      }
      case RecvMsgStep() => {
        CoreCacheCommunicationRecvMsgNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
      }
    }
  }

  lemma ProxyCacheCommunicationGetSNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires step.tile_step.proxy_step.CacheCommunicationStep?
    requires step.tile_step.proxy_step.step.GetSStep?
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma ProxyCacheCommunicationGetMNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires step.tile_step.proxy_step.CacheCommunicationStep?
    requires step.tile_step.proxy_step.step.GetMStep?
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma ProxyCacheCommunicationEvictNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires step.tile_step.proxy_step.CacheCommunicationStep?
    requires step.tile_step.proxy_step.step.EvictStep?
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma ProxyCacheCommunicationRecvMsgNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires step.tile_step.proxy_step.CacheCommunicationStep?
    requires step.tile_step.proxy_step.step.RecvMsgStep?
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma ProxyNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    assert step.tile_step.proxy_step.CacheCommunicationStep?;
    match step.tile_step.proxy_step.step {
      case GetSStep() => {
        ProxyCacheCommunicationGetSNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
      }
      case GetMStep() => {
        ProxyCacheCommunicationGetMNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
      }
      case EvictStep() => {
        ProxyCacheCommunicationEvictNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
      }
      case RecvMsgStep() => {
        ProxyCacheCommunicationRecvMsgNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
      }
    }
  }

  lemma MemoryNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires v.WF(c)
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma EngineReceiveCallbackReqNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires v.WF(c)
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        var old_idx := if addr == step.msgOps.recv.val.meta.addr then idx + 1 else idx;
        assert IsInFlightOnMissRequest(c, v, addr, old_idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma EngineCacheCommunicationGetSNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.GetSStep?
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma EngineCacheCommunicationGetMNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.GetMStep?
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma EngineCacheCommunicationEvictNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.EvictStep?
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma EngineCacheCommunicationRecvMsgNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires step.tile_step.eng_step.step.RecvMsgStep?
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma EngineNotReceiveCallbackReqNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires !step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    assert step.tile_step.eng_step.CacheCommunicationStep?;
    match step.tile_step.eng_step.step {
      case GetSStep() => {
        EngineCacheCommunicationGetSNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
      }
      case GetMStep() => {
        EngineCacheCommunicationGetMNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
      }
      case EvictStep() => {
        EngineCacheCommunicationEvictNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
      }
      case RecvMsgStep() => {
        EngineCacheCommunicationRecvMsgNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
      }
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires v.WF(c)
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        reveal InFlightOnMissResponse;
        var msg2 :| IsInFlightOnMissResponse(c, v', addr, msg2, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg2, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        if IsInFlightOnMissRequest(c, v, addr, idx, c_idx) {
          assert InFlightOnMissRequest(c, v, addr, c_idx);
          assert false;
        } else {
          var msg :| msg in step.msgOps.send;
          assert addr == msg.meta.addr;
          assert OnMissInProgress(c, v, addr, c_idx);
          reveal L2PendingCallbackForAddr;
          assert false;
        }
      }
    }
  }

  lemma L2CacheCommunicationNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires v.WF(c)
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires v.WF(c)
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma L2DirectoryNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires v.WF(c)
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires v.WF(c)
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires v.WF(c)
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        reveal InFlightOnMissResponse;
        var msg2 :| IsInFlightOnMissResponse(c, v', addr, msg2, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg2, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        if IsInFlightOnMissRequest(c, v, addr, idx, c_idx) {
          assert InFlightOnMissRequest(c, v, addr, c_idx);
          assert false;
        } else {
          var msg :| msg in step.msgOps.send;
          assert addr == msg.meta.addr;
          assert OnMissInProgress(c, v, addr, c_idx);
          reveal L3PendingCallbackForAddr;
          assert false;
        }
      }
    }
  }

  lemma L3ReceiveOnMissDataNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires v.WF(c)
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma L3ReqMemoryNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires v.WF(c)
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma L3RespMemoryNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires v.WF(c)
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma L3ReceiveCoherenceMessageNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires v.WF(c)
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma L3DirectoryNoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires v.WF(c)
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma NoOpPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires v.WF(c)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    match step {
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            match l3_step {
              case ReceiveCoherenceMessageStep() => {
                L3ReceiveCoherenceMessageNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
              }
              case ReqMemoryStep(_,_) => {
                L3ReqMemoryNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
              }
              case RespMemoryStep(_) => {
                L3RespMemoryNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L3DirectoryNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L3ReceiveOnMissDataNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L3ScheduleCallbackNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
              }
            }
          }
          case EngineStep(eng_step) => {
            if eng_step.ReceiveCallbackReqStep? {
              EngineReceiveCallbackReqNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
            } else {
              EngineNotReceiveCallbackReqNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
            }
          }
        }
      }
      case MemoryStep(_) => {
        MemoryNoOpPreservesOnMissRequestOnlyRequestOrResponse(c, v, v', step);
      }
    }
  }

  lemma PerformNextInstPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma StartCBPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
        assert InFlightOnMissResponse(c, v, addr, c_idx);
        assert false;
      }
    }
  }

  lemma EndCBPreservesOnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict || re == EndOnMiss || re == EndOnWriteback
    requires OnMissRequestOnlyRequestOrResponse(c, v)
    requires OnMissRequestOnlyRequestOrCallback(c, v)
    ensures OnMissRequestOnlyRequestOrResponse(c, v')
  {
    forall addr: Address, c_idx: nat
      ensures !(InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx))
    {
      if InFlightOnMissRequest(c, v', addr, c_idx) && InFlightOnMissResponse(c, v', addr, c_idx) {
        reveal InFlightOnMissRequest;
        var idx :| IsInFlightOnMissRequest(c, v', addr, idx, c_idx);
        assert IsInFlightOnMissRequest(c, v, addr, idx, c_idx);
        assert InFlightOnMissRequest(c, v, addr, c_idx);
        reveal InFlightOnMissResponse;
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        if IsInFlightOnMissResponse(c, v, addr, msg, c_idx) {
          assert InFlightOnMissResponse(c, v, addr, c_idx);
          assert false;
        } else {
          reveal CallbackPresent;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          assert CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx));
          assert msg in step.msgOps.send;
          assert false;
        }
      }
    }
  }
}