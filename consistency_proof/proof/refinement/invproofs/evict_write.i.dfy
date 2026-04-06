include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module OnEvictLastWriteProofs {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes
  import opened CacheTypes

  lemma MemoryNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires InFlightOnEvictRequestHasNoInterveningWrite(c, v)
    ensures InFlightOnEvictRequestHasNoInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.None?
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert v.g.callback_epochs[addr].wcb.None?;
    }
  }

  lemma CoreNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires InFlightOnEvictRequestHasNoInterveningWrite(c, v)
    ensures InFlightOnEvictRequestHasNoInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.None?
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert v.g.callback_epochs[addr].wcb.None?;
    }
  }

  lemma EngineNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires InFlightOnEvictRequestHasNoInterveningWrite(c, v)
    ensures InFlightOnEvictRequestHasNoInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.None?
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        var new_idx := if step.tile_step.eng_step.ReceiveCallbackReqStep?
          && step.msgOps.recv.val.meta.addr == addr then idx + 1 else idx;
        assert IsInFlightOnEvictRequest(c, v, addr, new_idx, val);
      }
      assert v.g.callback_epochs[addr].wcb.None?;
    }
  }

  lemma ProxyNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires InFlightOnEvictRequestHasNoInterveningWrite(c, v)
    ensures InFlightOnEvictRequestHasNoInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.None?
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert v.g.callback_epochs[addr].wcb.None?;
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires InFlightOnEvictRequestHasNoInterveningWrite(c, v)
    ensures InFlightOnEvictRequestHasNoInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.None?
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert v.g.callback_epochs[addr].wcb.None?;
    }
  }

  lemma L2DirectoryNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires InFlightOnEvictRequestHasNoInterveningWrite(c, v)
    ensures InFlightOnEvictRequestHasNoInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.None?
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert v.g.callback_epochs[addr].wcb.None?;
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires InFlightOnEvictRequestHasNoInterveningWrite(c, v)
    ensures InFlightOnEvictRequestHasNoInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.None?
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert v.g.callback_epochs[addr].wcb.None?;
    }
  }

  lemma L2CacheCommunicationNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires InFlightOnEvictRequestHasNoInterveningWrite(c, v)
    ensures InFlightOnEvictRequestHasNoInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.None?
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert v.g.callback_epochs[addr].wcb.None?;
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires InFlightOnEvictRequestHasNoInterveningWrite(c, v)
    requires L2DirtyBitTracksInterveningWrite(c, v)
    requires PrivateMorphInL2IsCohM(c, v)
    ensures InFlightOnEvictRequestHasNoInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.None?
    {
      reveal InFlightOnEvictRequest;
      var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
      if IsInFlightOnEvictRequest(c, v, addr, idx, val)  {
        assert InFlightOnEvictRequest(c, v, addr, val);
        assert v.g.callback_epochs[addr].wcb.None?;
        assert v'.g.callback_epochs[addr].wcb.None?;
      } else {
        assert step.tile_step.l2_step.eng_req.OnEvict?;
        assert CleanL2CacheEntry(c, v, step.tile_idx, step.tile_step.l2_step.idx);
        assert v.tiles[step.tile_idx].l2.cache[step.tile_step.l2_step.idx].coh.M?;
        assert v'.g.callback_epochs[addr].wcb.None?;
      }
    }
  }

  lemma L3ReceiveOnMissDataNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires InFlightOnEvictRequestHasNoInterveningWrite(c, v)
    ensures InFlightOnEvictRequestHasNoInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.None?
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert v.g.callback_epochs[addr].wcb.None?;
    }
  }

  lemma L3DirectoryNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires InFlightOnEvictRequestHasNoInterveningWrite(c, v)
    ensures InFlightOnEvictRequestHasNoInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.None?
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert v.g.callback_epochs[addr].wcb.None?;
    }
  }

  lemma L3ReceiveCoherenceMessageNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires InFlightOnEvictRequestHasNoInterveningWrite(c, v)
    ensures InFlightOnEvictRequestHasNoInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.None?
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert v.g.callback_epochs[addr].wcb.None?;
    }
  }

  lemma L3ReqMemoryMessageNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires InFlightOnEvictRequestHasNoInterveningWrite(c, v)
    ensures InFlightOnEvictRequestHasNoInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.None?
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert v.g.callback_epochs[addr].wcb.None?;
    }
  }

  lemma L3RespMemoryMessageNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires InFlightOnEvictRequestHasNoInterveningWrite(c, v)
    ensures InFlightOnEvictRequestHasNoInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.None?
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert v.g.callback_epochs[addr].wcb.None?;
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires InFlightOnEvictRequestHasNoInterveningWrite(c, v)
    requires L3DirtyBitTracksInterveningWrite(c, v)
    ensures InFlightOnEvictRequestHasNoInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.None?
    {
      reveal InFlightOnEvictRequest;
      var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
      if IsInFlightOnEvictRequest(c, v, addr, idx, val)  {
        assert InFlightOnEvictRequest(c, v, addr, val);
        assert v.g.callback_epochs[addr].wcb.None?;
        assert v'.g.callback_epochs[addr].wcb.None?;
      } else {
        assert step.tile_step.l3_step.eng_req.OnEvict?;
        assert CleanL3CacheEntry(c, v, step.tile_idx, step.tile_step.l3_step.idx);
        assert v'.g.callback_epochs[addr].wcb.None?;
      }
    }
  }

  lemma NoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L2DirtyBitTracksInterveningWrite(c, v)
    requires L3DirtyBitTracksInterveningWrite(c, v)
    requires PrivateMorphInL2IsCohM(c, v)
    requires InFlightOnEvictRequestHasNoInterveningWrite(c, v)
    ensures InFlightOnEvictRequestHasNoInterveningWrite(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c, v, v', step);
      }
      case TileStep(_, tile_step, _) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c, v, v', step);
          }
          case EngineStep(_) => {
            EngineNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            match l3_step {
              case ReceiveOnMissDataStep(_) => {
                L3ReceiveOnMissDataNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L3DirectoryNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L3ReceiveCoherenceMessageNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c, v, v', step);
              }
              case ReqMemoryStep(_,_) => {
                L3ReqMemoryMessageNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c, v, v', step);
              }
              case RespMemoryStep(_) => {
                L3RespMemoryMessageNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L3ScheduleCallbackNoOpPreservesInFlightOnEvictRequestHasNoInterveningWrite(c, v, v', step);
              }
            }
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesInFlightOnEvictRequestHasNoInterveningWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires InFlightOnEvictRequestHasNoInterveningWrite(c, v)
    requires OnEvictInProgressMeansNoLoadableInCore(c, v)
    requires OnEvictInProgressMeansNoLoadableInEngine(c, v)
    ensures InFlightOnEvictRequestHasNoInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.None?
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert OnEvictInProgress(c, v, addr, val);
      // assert v.g.callback_epochs[addr].wcb.None?;
    }
  }

  lemma StartEndCBPreservesInFlightOnEvictRequestHasNoInterveningWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires InFlightOnEvictRequestHasNoInterveningWrite(c, v)
    ensures InFlightOnEvictRequestHasNoInterveningWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures v'.g.callback_epochs[addr].wcb.None?
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
    }
  }

  lemma MemoryNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires InFlightOnEvictRequestMatchesLastWrite(c, v)
    ensures InFlightOnEvictRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert MatchesLastWriteMorph(c, v, addr, val);
    }
  }

  lemma CoreNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires InFlightOnEvictRequestMatchesLastWrite(c, v)
    ensures InFlightOnEvictRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert MatchesLastWriteMorph(c, v, addr, val);
    }
  }

  lemma EngineNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires InFlightOnEvictRequestMatchesLastWrite(c, v)
    ensures InFlightOnEvictRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        var new_idx := if step.tile_step.eng_step.ReceiveCallbackReqStep?
          && step.msgOps.recv.val.meta.addr == addr then idx + 1 else idx;
        assert IsInFlightOnEvictRequest(c, v, addr, new_idx, val);
      }
      assert MatchesLastWriteMorph(c, v, addr, val);
    }
  }

  lemma ProxyNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires InFlightOnEvictRequestMatchesLastWrite(c, v)
    ensures InFlightOnEvictRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert MatchesLastWriteMorph(c, v, addr, val);
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires InFlightOnEvictRequestMatchesLastWrite(c, v)
    ensures InFlightOnEvictRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert MatchesLastWriteMorph(c, v, addr, val);
    }
  }

  lemma L2DirectoryNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires InFlightOnEvictRequestMatchesLastWrite(c, v)
    ensures InFlightOnEvictRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert MatchesLastWriteMorph(c, v, addr, val);
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires InFlightOnEvictRequestMatchesLastWrite(c, v)
    ensures InFlightOnEvictRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert MatchesLastWriteMorph(c, v, addr, val);
    }
  }

  lemma L2CacheCommunicationNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires InFlightOnEvictRequestMatchesLastWrite(c, v)
    ensures InFlightOnEvictRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert MatchesLastWriteMorph(c, v, addr, val);
    }
  }


  lemma L2ScheduleCallbackNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires InFlightOnEvictRequestMatchesLastWrite(c, v)
    requires L2DirISMatchesLastWrite(c, v)
    ensures InFlightOnEvictRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    )
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      reveal InFlightOnEvictRequest;
      var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
      if IsInFlightOnEvictRequest(c, v, addr, idx, val)  {
        assert InFlightOnEvictRequest(c, v, addr, val);
        assert MatchesLastWriteMorph(c, v, addr, val);
        assert MatchesLastWriteMorph(c, v', addr, val);
      } else {
        assert step.tile_step.l2_step.eng_req.OnEvict?;
        assert DirIL2CacheEntry(c, v, step.tile_idx, step.tile_step.l2_step.idx);
        assert MatchesLastWriteMorph(c, v', addr, val);
      }
    }
  }

  lemma L3ReceiveOnMissDataNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires InFlightOnEvictRequestMatchesLastWrite(c, v)
    ensures InFlightOnEvictRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert MatchesLastWriteMorph(c, v, addr, val);
    }
  }

  lemma L3DirectoryNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires InFlightOnEvictRequestMatchesLastWrite(c, v)
    ensures InFlightOnEvictRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert MatchesLastWriteMorph(c, v, addr, val);
    }
  }

  lemma L3ReceiveCoherenceMessageNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires InFlightOnEvictRequestMatchesLastWrite(c, v)
    ensures InFlightOnEvictRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert MatchesLastWriteMorph(c, v, addr, val);
    }
  }

  lemma L3ReqMemoryNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires InFlightOnEvictRequestMatchesLastWrite(c, v)
    ensures InFlightOnEvictRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert MatchesLastWriteMorph(c, v, addr, val);
    }
  }

  lemma L3RespMemoryNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires InFlightOnEvictRequestMatchesLastWrite(c, v)
    ensures InFlightOnEvictRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    ) 
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert MatchesLastWriteMorph(c, v, addr, val);
    }
  }


  lemma L3ScheduleCallbackNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires InFlightOnEvictRequestMatchesLastWrite(c, v)
    requires L3DirISMatchesLastWrite(c, v)
    ensures InFlightOnEvictRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    )
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      reveal InFlightOnEvictRequest;
      var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
      if IsInFlightOnEvictRequest(c, v, addr, idx, val)  {
        assert InFlightOnEvictRequest(c, v, addr, val);
        assert MatchesLastWriteMorph(c, v, addr, val);
        assert MatchesLastWriteMorph(c, v', addr, val);
      } else {
        assert step.tile_step.l3_step.eng_req.OnEvict?;
        assert DirIL3CacheEntry(c, v, step.tile_idx, step.tile_step.l3_step.idx);
        assert MatchesLastWriteMorph(c, v', addr, val);
      }
    }
  }

  lemma NoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L2DirISMatchesLastWrite(c, v)
    requires L3DirISMatchesLastWrite(c, v)
    requires InFlightOnEvictRequestMatchesLastWrite(c, v)
    ensures InFlightOnEvictRequestMatchesLastWrite(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c, v, v', step);
      }
      case TileStep(_, tile_step, _) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c, v, v', step);
          }
          case EngineStep(_) => {
            EngineNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            match l3_step {
              case ReceiveOnMissDataStep(_) => {
                L3ReceiveOnMissDataNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L3DirectoryNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L3ReceiveCoherenceMessageNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c, v, v', step);
              }
              case ReqMemoryStep(_,_) => {
                L3ReqMemoryNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c, v, v', step);
              }
              case RespMemoryStep(_) => {
                L3RespMemoryNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L3ScheduleCallbackNoOpPreservesInFlightOnEvictRequestMatchesLastWrite(c, v, v', step);
              }
            }
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesInFlightOnEvictRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires OnEvictInProgressMeansNoLoadableInCore(c, v)
    requires OnEvictInProgressMeansNoLoadableInEngine(c, v)
    requires InFlightOnEvictRequestMatchesLastWrite(c, v)
    ensures InFlightOnEvictRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    )
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert OnEvictInProgress(c, v, addr, val);
    }
  }

  lemma StartEndCBPreservesInFlightOnEvictRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    requires InFlightOnEvictRequestMatchesLastWrite(c, v)
    ensures InFlightOnEvictRequestMatchesLastWrite(c, v')
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v', addr)
      && InFlightOnEvictRequest(c, v', addr, val)
    )
    ensures MatchesLastWriteMorph(c, v', addr, val)
    {
      assert InFlightOnEvictRequest(c, v, addr, val) by {
        reveal InFlightOnEvictRequest;
        var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      }
      assert OnEvictInProgress(c, v, addr, val);
      var entry := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx];
      if re == EndOnMiss && entry.addr == addr {
        assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, entry.cb_type);
        assert false;
      }
    }
  }
}