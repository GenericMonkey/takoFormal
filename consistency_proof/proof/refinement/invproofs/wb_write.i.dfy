include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module OnWritebackLastWriteProofs {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes
  import opened CacheTypes

  lemma MemoryNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires InFlightOnWritebackRequestHasInterveningWrite(c, v)
    ensures InFlightOnWritebackRequestHasInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.Some?
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert v.g.callback_epochs[addr].wcb.Some?;
    }
  }

  lemma CoreNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires InFlightOnWritebackRequestHasInterveningWrite(c, v)
    ensures InFlightOnWritebackRequestHasInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.Some?
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert v.g.callback_epochs[addr].wcb.Some?;
    }
  }

  lemma EngineNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires InFlightOnWritebackRequestHasInterveningWrite(c, v)
    ensures InFlightOnWritebackRequestHasInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.Some?
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        var new_idx := if step.tile_step.eng_step.ReceiveCallbackReqStep?
          && step.msgOps.recv.val.meta.addr == addr then idx + 1 else idx;
        assert IsInFlightOnWritebackRequest(c, v, addr, new_idx, val);
      }
      assert v.g.callback_epochs[addr].wcb.Some?;
    }
  }

  lemma ProxyNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires InFlightOnWritebackRequestHasInterveningWrite(c, v)
    ensures InFlightOnWritebackRequestHasInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.Some?
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert v.g.callback_epochs[addr].wcb.Some?;
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires InFlightOnWritebackRequestHasInterveningWrite(c, v)
    ensures InFlightOnWritebackRequestHasInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.Some?
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert v.g.callback_epochs[addr].wcb.Some?;
    }
  }

  lemma L2DirectoryNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires InFlightOnWritebackRequestHasInterveningWrite(c, v)
    ensures InFlightOnWritebackRequestHasInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.Some?
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert v.g.callback_epochs[addr].wcb.Some?;
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires InFlightOnWritebackRequestHasInterveningWrite(c, v)
    ensures InFlightOnWritebackRequestHasInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.Some?
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert v.g.callback_epochs[addr].wcb.Some?;
    }
  }

  lemma L2CacheCommunicationNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires InFlightOnWritebackRequestHasInterveningWrite(c, v)
    ensures InFlightOnWritebackRequestHasInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.Some?
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert v.g.callback_epochs[addr].wcb.Some?;
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires L2DirtyBitTracksInterveningWrite(c, v)
    requires PrivateMorphInL2IsCohM(c, v)
    requires InFlightOnWritebackRequestHasInterveningWrite(c, v)
    ensures InFlightOnWritebackRequestHasInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.Some?
    {
      reveal InFlightOnWritebackRequest;
      var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
      if IsInFlightOnWritebackRequest(c, v, addr, idx, val)  {
        assert InFlightOnWritebackRequest(c, v, addr, val);
        assert v.g.callback_epochs[addr].wcb.Some?;
        assert v'.g.callback_epochs[addr].wcb.Some?;
      } else {
        assert step.tile_step.l2_step.eng_req.OnWriteBack?;
        assert DirtyL2CacheEntry(c, v, step.tile_idx, step.tile_step.l2_step.idx);
        assert v.tiles[step.tile_idx].l2.cache[step.tile_step.l2_step.idx].coh.M?;
        assert v'.g.callback_epochs[addr].wcb.Some?;
      }
    }
  }

  lemma L3ReceiveOnMissDataNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires InFlightOnWritebackRequestHasInterveningWrite(c, v)
    ensures InFlightOnWritebackRequestHasInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.Some?
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert v.g.callback_epochs[addr].wcb.Some?;
    }
  }

  lemma L3DirectoryNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires InFlightOnWritebackRequestHasInterveningWrite(c, v)
    ensures InFlightOnWritebackRequestHasInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.Some?
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert v.g.callback_epochs[addr].wcb.Some?;
    }
  }

  lemma L3ReceiveCoherenceMessageNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires InFlightOnWritebackRequestHasInterveningWrite(c, v)
    ensures InFlightOnWritebackRequestHasInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.Some?
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert v.g.callback_epochs[addr].wcb.Some?;
    }
  }

  lemma L3ReqMemoryMessageNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires InFlightOnWritebackRequestHasInterveningWrite(c, v)
    ensures InFlightOnWritebackRequestHasInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.Some?
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert v.g.callback_epochs[addr].wcb.Some?;
    }
  }

  lemma L3RespMemoryMessageNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires InFlightOnWritebackRequestHasInterveningWrite(c, v)
    ensures InFlightOnWritebackRequestHasInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.Some?
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert v.g.callback_epochs[addr].wcb.Some?;
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires L3DirtyBitTracksInterveningWrite(c, v)
    requires InFlightOnWritebackRequestHasInterveningWrite(c, v)
    ensures InFlightOnWritebackRequestHasInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.Some?
    {
      reveal InFlightOnWritebackRequest;
      var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
      if IsInFlightOnWritebackRequest(c, v, addr, idx, val)  {
        assert InFlightOnWritebackRequest(c, v, addr, val);
        assert v.g.callback_epochs[addr].wcb.Some?;
        assert v'.g.callback_epochs[addr].wcb.Some?;
      } else {
        assert step.tile_step.l3_step.eng_req.OnWriteBack?;
        assert DirtyL3CacheEntry(c, v, step.tile_idx, step.tile_step.l3_step.idx);
        assert v'.g.callback_epochs[addr].wcb.Some?;
      }
    }
  }

  lemma NoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L2DirtyBitTracksInterveningWrite(c, v)
    requires L3DirtyBitTracksInterveningWrite(c, v)
    requires PrivateMorphInL2IsCohM(c, v)
    requires InFlightOnWritebackRequestHasInterveningWrite(c, v)
    ensures InFlightOnWritebackRequestHasInterveningWrite(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c, v, v', step);
      }
      case TileStep(_, tile_step, _) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c, v, v', step);
          }
          case EngineStep(_) => {
            EngineNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            match l3_step {
              case ReceiveOnMissDataStep(_) => {
                L3ReceiveOnMissDataNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L3DirectoryNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L3ReceiveCoherenceMessageNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c, v, v', step);
              }
              case ReqMemoryStep(_,_) => {
                L3ReqMemoryMessageNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c, v, v', step);
              }
              case RespMemoryStep(_) => {
                L3RespMemoryMessageNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L3ScheduleCallbackNoOpPreservesInFlightOnWritebackRequestHasInterveningWrite(c, v, v', step);
              }
            }
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesInFlightOnWritebackRequestHasInterveningWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires OnWritebackInProgressMeansNoLoadableInCore(c, v)
    requires OnWritebackInProgressMeansNoLoadableInEngine(c, v)
    requires InFlightOnWritebackRequestHasInterveningWrite(c, v)
    ensures InFlightOnWritebackRequestHasInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.Some?
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert OnWritebackInProgress(c, v, addr, val);
    }
  }

  lemma StartEndCBPreservesInFlightOnWritebackRequestHasInterveningWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)
    requires InFlightOnWritebackRequestHasInterveningWrite(c, v)
    ensures InFlightOnWritebackRequestHasInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.Some?
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert OnWritebackInProgress(c, v, addr, val);
      var entry := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx];
      if re == EndOnMiss && entry.addr == addr {
        assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, entry.cb_type);
        assert false;
      }
    }
  }

  lemma MemoryNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires InFlightOnWritebackRequestMatchesLastWrite(c, v)
    ensures InFlightOnWritebackRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert MatchesLastWriteMorph(c, v, addr, val);
    }
  }

  lemma CoreNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires InFlightOnWritebackRequestMatchesLastWrite(c, v)
    ensures InFlightOnWritebackRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert MatchesLastWriteMorph(c, v, addr, val);
    }
  }

  lemma EngineNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires InFlightOnWritebackRequestMatchesLastWrite(c, v)
    ensures InFlightOnWritebackRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        var new_idx := if step.tile_step.eng_step.ReceiveCallbackReqStep?
          && step.msgOps.recv.val.meta.addr == addr then idx + 1 else idx;
        assert IsInFlightOnWritebackRequest(c, v, addr, new_idx, val);
      }
      assert MatchesLastWriteMorph(c, v, addr, val);
    }
  }

  lemma ProxyNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires InFlightOnWritebackRequestMatchesLastWrite(c, v)
    ensures InFlightOnWritebackRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert MatchesLastWriteMorph(c, v, addr, val);
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires InFlightOnWritebackRequestMatchesLastWrite(c, v)
    ensures InFlightOnWritebackRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert MatchesLastWriteMorph(c, v, addr, val);
    }
  }

  lemma L2DirectoryNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires InFlightOnWritebackRequestMatchesLastWrite(c, v)
    ensures InFlightOnWritebackRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert MatchesLastWriteMorph(c, v, addr, val);
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires InFlightOnWritebackRequestMatchesLastWrite(c, v)
    ensures InFlightOnWritebackRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert MatchesLastWriteMorph(c, v, addr, val);
    }
  }

  lemma L2CacheCommunicationNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires InFlightOnWritebackRequestMatchesLastWrite(c, v)
    ensures InFlightOnWritebackRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert MatchesLastWriteMorph(c, v, addr, val);
    }
  }


  lemma L2ScheduleCallbackNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires InFlightOnWritebackRequestMatchesLastWrite(c, v)
    requires L2DirISMatchesLastWrite(c, v)
    ensures InFlightOnWritebackRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    )
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      reveal InFlightOnWritebackRequest;
      var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
      if IsInFlightOnWritebackRequest(c, v, addr, idx, val)  {
        assert InFlightOnWritebackRequest(c, v, addr, val);
        assert MatchesLastWriteMorph(c, v, addr, val);
        assert MatchesLastWriteMorph(c, v', addr, val);
      } else {
        assert step.tile_step.l2_step.eng_req.OnWriteBack?;
        assert DirIL2CacheEntry(c, v, step.tile_idx, step.tile_step.l2_step.idx);
        assert MatchesLastWriteMorph(c, v', addr, val);
      }
    }
  }

  lemma L3ReceiveOnMissDataNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires InFlightOnWritebackRequestMatchesLastWrite(c, v)
    ensures InFlightOnWritebackRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert MatchesLastWriteMorph(c, v, addr, val);
    }
  }

  lemma L3DirectoryNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires InFlightOnWritebackRequestMatchesLastWrite(c, v)
    ensures InFlightOnWritebackRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert MatchesLastWriteMorph(c, v, addr, val);
    }
  }

  lemma L3ReceiveCoherenceMessageNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires InFlightOnWritebackRequestMatchesLastWrite(c, v)
    ensures InFlightOnWritebackRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert MatchesLastWriteMorph(c, v, addr, val);
    }
  }

  lemma L3ReqMemoryNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires InFlightOnWritebackRequestMatchesLastWrite(c, v)
    ensures InFlightOnWritebackRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert MatchesLastWriteMorph(c, v, addr, val);
    }
  }

  lemma L3RespMemoryNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires InFlightOnWritebackRequestMatchesLastWrite(c, v)
    ensures InFlightOnWritebackRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    ) 
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert MatchesLastWriteMorph(c, v, addr, val);
    }
  }


  lemma L3ScheduleCallbackNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires InFlightOnWritebackRequestMatchesLastWrite(c, v)
    requires L3DirISMatchesLastWrite(c, v)
    ensures InFlightOnWritebackRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    )
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      reveal InFlightOnWritebackRequest;
      var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
      if IsInFlightOnWritebackRequest(c, v, addr, idx, val)  {
        assert InFlightOnWritebackRequest(c, v, addr, val);
        assert MatchesLastWriteMorph(c, v, addr, val);
        assert MatchesLastWriteMorph(c, v', addr, val);
      } else {
        assert step.tile_step.l3_step.eng_req.OnWriteBack?;
        assert DirIL3CacheEntry(c, v, step.tile_idx, step.tile_step.l3_step.idx);
        assert MatchesLastWriteMorph(c, v', addr, val);
      }
    }
  }

  lemma NoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L2DirISMatchesLastWrite(c, v)
    requires L3DirISMatchesLastWrite(c, v)
    requires InFlightOnWritebackRequestMatchesLastWrite(c, v)
    ensures InFlightOnWritebackRequestMatchesLastWrite(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c, v, v', step);
      }
      case TileStep(_, tile_step, _) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c, v, v', step);
          }
          case EngineStep(_) => {
            EngineNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            match l3_step {
              case ReceiveOnMissDataStep(_) => {
                L3ReceiveOnMissDataNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L3DirectoryNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L3ReceiveCoherenceMessageNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c, v, v', step);
              }
              case ReqMemoryStep(_,_) => {
                L3ReqMemoryNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c, v, v', step);
              }
              case RespMemoryStep(_) => {
                L3RespMemoryNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L3ScheduleCallbackNoOpPreservesInFlightOnWritebackRequestMatchesLastWrite(c, v, v', step);
              }
            }
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesInFlightOnWritebackRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires OnWritebackInProgressMeansNoLoadableInCore(c, v)
    requires OnWritebackInProgressMeansNoLoadableInEngine(c, v)
    requires InFlightOnWritebackRequestMatchesLastWrite(c, v)
    ensures InFlightOnWritebackRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    )
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert OnWritebackInProgress(c, v, addr, val);
    }
  }

  lemma StartEndCBPreservesInFlightOnWritebackRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)
    requires InFlightOnWritebackRequestMatchesLastWrite(c, v)
    ensures InFlightOnWritebackRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnWritebackRequest(c, v', addr, val)
    )
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnWritebackRequest(c, v, addr, val) by {
        reveal InFlightOnWritebackRequest;
        var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      }
      assert OnWritebackInProgress(c, v, addr, val);
      
      var entry := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx];
      if re == EndOnMiss && entry.addr == addr {
        assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, entry.cb_type);
        assert false;
      }
    }
  }
}
