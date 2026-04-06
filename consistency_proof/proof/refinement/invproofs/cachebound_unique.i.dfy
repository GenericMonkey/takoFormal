include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module UniqueCacheBoundMsgProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes

  lemma CoreNoOpPreservesUniqueCacheBoundMsgPerAddr(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires v.WF(c)
    requires UniqueCacheBoundMsgPerAddr(c, v)
    ensures UniqueCacheBoundMsgPerAddr(c, v')
  {
    forall msg1, msg2 | InFlightEngineResponse(c, v', msg1) && InFlightEngineResponse(c, v', msg2)
      && msg1.meta.addr == msg2.meta.addr
      ensures msg1 == msg2
    {}
  }

  lemma CoreNoOpPreservesEachAddrCacheBoundMsgIsUnique(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires v.WF(c)
    requires EachAddrCacheBoundMsgIsUnique(c, v)
    ensures EachAddrCacheBoundMsgIsUnique(c, v')
  {
    forall msg | InFlightEngineResponse(c, v', msg)
      ensures v'.network.inFlightMessages[msg] == 1
    {}
  }

  lemma ProxyNoOpPreservesUniqueCacheBoundMsgPerAddr(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires v.WF(c)
    requires UniqueCacheBoundMsgPerAddr(c, v)
    ensures UniqueCacheBoundMsgPerAddr(c, v')
  {
    forall msg1, msg2 | InFlightEngineResponse(c, v', msg1) && InFlightEngineResponse(c, v', msg2)
      && msg1.meta.addr == msg2.meta.addr
      ensures msg1 == msg2
    {}
  }

  lemma ProxyNoOpPreservesEachAddrCacheBoundMsgIsUnique(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires v.WF(c)
    requires EachAddrCacheBoundMsgIsUnique(c, v)
    ensures EachAddrCacheBoundMsgIsUnique(c, v')
  {
    forall msg | InFlightEngineResponse(c, v', msg)
      ensures v'.network.inFlightMessages[msg] == 1
    {}
  }

  lemma EngineNoOpPreservesUniqueCacheBoundMsgPerAddr(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires v.WF(c)
    requires UniqueCacheBoundMsgPerAddr(c, v)
    ensures UniqueCacheBoundMsgPerAddr(c, v')
  {
    forall msg1, msg2 | InFlightEngineResponse(c, v', msg1) && InFlightEngineResponse(c, v', msg2)
      && msg1.meta.addr == msg2.meta.addr
      ensures msg1 == msg2
    {}
  }

  lemma EngineNoOpPreservesEachAddrCacheBoundMsgIsUnique(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires v.WF(c)
    requires EachAddrCacheBoundMsgIsUnique(c, v)
    ensures EachAddrCacheBoundMsgIsUnique(c, v')
  {
    forall msg | InFlightEngineResponse(c, v', msg)
      ensures v'.network.inFlightMessages[msg] == 1
    {}
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesUniqueCacheBoundMsgPerAddr(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires UniqueCacheBoundMsgPerAddr(c, v)
    ensures UniqueCacheBoundMsgPerAddr(c, v')
  {
    forall msg1, msg2 | InFlightEngineResponse(c, v', msg1) && InFlightEngineResponse(c, v', msg2)
      && msg1.meta.addr == msg2.meta.addr
      ensures msg1 == msg2
    {
      assert InFlightEngineResponse(c, v, msg1) && InFlightEngineResponse(c, v, msg2);
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesUniqueCacheBoundMsgPerAddr(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires UniqueCacheBoundMsgPerAddr(c, v)
    ensures UniqueCacheBoundMsgPerAddr(c, v')
  {
    forall msg1, msg2 | InFlightEngineResponse(c, v', msg1) && InFlightEngineResponse(c, v', msg2)
      && msg1.meta.addr == msg2.meta.addr
      ensures msg1 == msg2
    {
      assert InFlightEngineResponse(c, v, msg1) && InFlightEngineResponse(c, v, msg2);
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesUniqueCacheBoundMsgPerAddr(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires UniqueCacheBoundMsgPerAddr(c, v)
    ensures UniqueCacheBoundMsgPerAddr(c, v')
  {
    forall msg1, msg2 | InFlightEngineResponse(c, v', msg1) && InFlightEngineResponse(c, v', msg2)
      && msg1.meta.addr == msg2.meta.addr
      ensures msg1 == msg2
    {
      assert InFlightEngineResponse(c, v, msg1) && InFlightEngineResponse(c, v, msg2);
    }
  }

  lemma L2CacheCommunicationNoOpPreservesUniqueCacheBoundMsgPerAddr(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires UniqueCacheBoundMsgPerAddr(c, v)
    ensures UniqueCacheBoundMsgPerAddr(c, v')
  {
    forall msg1, msg2 | InFlightEngineResponse(c, v', msg1) && InFlightEngineResponse(c, v', msg2)
      && msg1.meta.addr == msg2.meta.addr
      ensures msg1 == msg2
    {
      assert InFlightEngineResponse(c, v, msg1) && InFlightEngineResponse(c, v, msg2);
    }
  }

  lemma L2DirectoryNoOpPreservesUniqueCacheBoundMsgPerAddr(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires UniqueCacheBoundMsgPerAddr(c, v)
    ensures UniqueCacheBoundMsgPerAddr(c, v')
  {
    forall msg1, msg2 | InFlightEngineResponse(c, v', msg1) && InFlightEngineResponse(c, v', msg2)
      && msg1.meta.addr == msg2.meta.addr
      ensures msg1 == msg2
    {
      assert InFlightEngineResponse(c, v, msg1) && InFlightEngineResponse(c, v, msg2);
    }
  }

  lemma L2NoOpPreservesEachAddrCacheBoundMsgIsUnique(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires v.WF(c)
    requires EachAddrCacheBoundMsgIsUnique(c, v)
    ensures EachAddrCacheBoundMsgIsUnique(c, v')
  {
    forall msg | InFlightEngineResponse(c, v', msg)
      ensures v'.network.inFlightMessages[msg] == 1
    {}
  }

  lemma L3NoOpPreservesUniqueCacheBoundMsgPerAddr(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires v.WF(c)
    requires UniqueCacheBoundMsgPerAddr(c, v)
    ensures UniqueCacheBoundMsgPerAddr(c, v')
  {
    forall msg1, msg2 | InFlightEngineResponse(c, v', msg1) && InFlightEngineResponse(c, v', msg2)
      && msg1.meta.addr == msg2.meta.addr
      ensures msg1 == msg2
    {}
  }

  lemma L3NoOpPreservesEachAddrCacheBoundMsgIsUnique(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires v.WF(c)
    requires EachAddrCacheBoundMsgIsUnique(c, v)
    ensures EachAddrCacheBoundMsgIsUnique(c, v')
  {
    forall msg | InFlightEngineResponse(c, v', msg)
      ensures v'.network.inFlightMessages[msg] == 1
    {}
  }

  lemma NoOpPreservesUniqueCacheBoundMsgPerAddr(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires v.WF(c)
    requires UniqueCacheBoundMsgPerAddr(c, v)
    ensures UniqueCacheBoundMsgPerAddr(c, v')
  {
    match step {
      case MemoryStep(msgOps) => {
        assert UniqueCacheBoundMsgPerAddr(c, v');
      }
      case TileStep(tile_idx, tile_step, msgOps) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesUniqueCacheBoundMsgPerAddr(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesUniqueCacheBoundMsgPerAddr(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesUniqueCacheBoundMsgPerAddr(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesUniqueCacheBoundMsgPerAddr(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesUniqueCacheBoundMsgPerAddr(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesUniqueCacheBoundMsgPerAddr(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            L3NoOpPreservesUniqueCacheBoundMsgPerAddr(c, v, v', step);
          }
          case EngineStep(eng_step) => {
            EngineNoOpPreservesUniqueCacheBoundMsgPerAddr(c, v, v', step);
          }
          case ProxyStep(proxy_step) => {
            ProxyNoOpPreservesUniqueCacheBoundMsgPerAddr(c, v, v', step);
          }
        }
      }
    }
  }

  lemma NoOpPreservesEachAddrCacheBoundMsgIsUnique(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires v.WF(c)
    requires EachAddrCacheBoundMsgIsUnique(c, v)
    ensures EachAddrCacheBoundMsgIsUnique(c, v')
  {
    match step {
      case MemoryStep(msgOps) => {
        assert EachAddrCacheBoundMsgIsUnique(c, v');
      }
      case TileStep(tile_idx, tile_step, msgOps) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesEachAddrCacheBoundMsgIsUnique(c, v, v', step);
          }
          case L2Step(l2_step) => {
            L2NoOpPreservesEachAddrCacheBoundMsgIsUnique(c, v, v', step);
          }
          case L3Step(l3_step) => {
            L3NoOpPreservesEachAddrCacheBoundMsgIsUnique(c, v, v', step);
          }
          case EngineStep(eng_step) => {
            EngineNoOpPreservesEachAddrCacheBoundMsgIsUnique(c, v, v', step);
          }
          case ProxyStep(proxy_step) => {
            ProxyNoOpPreservesEachAddrCacheBoundMsgIsUnique(c, v, v', step);
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesUniqueCacheBoundMsgPerAddr(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires v.WF(c)
    requires UniqueCacheBoundMsgPerAddr(c, v)
    ensures UniqueCacheBoundMsgPerAddr(c, v')
  {
    forall msg1, msg2 | InFlightEngineResponse(c, v', msg1) && InFlightEngineResponse(c, v', msg2)
      && msg1.meta.addr == msg2.meta.addr
      ensures msg1 == msg2
    {}
  }

  lemma PerformNextInstPreservesEachAddrCacheBoundMsgIsUnique(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires v.WF(c)
    requires EachAddrCacheBoundMsgIsUnique(c, v)
    ensures EachAddrCacheBoundMsgIsUnique(c, v')
  {
    forall msg | InFlightEngineResponse(c, v', msg)
      ensures v'.network.inFlightMessages[msg] == 1
    {}
  }

  lemma StartCBPreservesUniqueCacheBoundMsgPerAddr(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback
    requires v.WF(c)
    requires UniqueCacheBoundMsgPerAddr(c, v)
    ensures UniqueCacheBoundMsgPerAddr(c, v')
  {
    forall msg1, msg2 | InFlightEngineResponse(c, v', msg1) && InFlightEngineResponse(c, v', msg2)
      && msg1.meta.addr == msg2.meta.addr
      ensures msg1 == msg2
    {}
  }

  lemma StartCBPreservesEachAddrCacheBoundMsgIsUnique(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict || re == StartOnMiss || re == StartOnWriteback
    requires v.WF(c)
    requires EachAddrCacheBoundMsgIsUnique(c, v)
    ensures EachAddrCacheBoundMsgIsUnique(c, v')
  {
    forall msg | InFlightEngineResponse(c, v', msg)
      ensures v'.network.inFlightMessages[msg] == 1
    {}
  }

  lemma EndCBPreservesUniqueCacheBoundMsgPerAddr(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict || re == EndOnMiss || re == EndOnWriteback
    requires v.WF(c)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires OnMissRequestOnlyCallbackOrResponse(c, v)
    requires L2AddressesUnique(c, v)
    requires L3AddressesUnique(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires UniqueCacheBoundMsgPerAddr(c, v)
    ensures UniqueCacheBoundMsgPerAddr(c, v')
  {
    forall msg1, msg2 | InFlightEngineResponse(c, v', msg1) && InFlightEngineResponse(c, v', msg2)
      && msg1.meta.addr == msg2.meta.addr
      ensures msg1 == msg2
    {
      if InFlightEngineResponse(c, v, msg1) && InFlightEngineResponse(c, v, msg2) {
        assert msg1 == msg2;
      } else {
        if InFlightEngineResponse(c, v, msg1) {
          assert msg2 in step.msgOps.send;
          assert IsInFlightOnMissResponse(c, v, msg1.meta.addr, msg1, msg1.engine_resp.idx);
          assert CallbackPresentInBufferLocation(c, v, msg2.meta.addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          assert InFlightOnMissResponse(c, v, msg1.meta.addr, msg1.engine_resp.idx) by { reveal InFlightOnMissResponse; }
          assert CallbackPresent(c, v, msg2.meta.addr, EngineRequest.OnMiss(msg2.engine_resp.idx)) by { reveal CallbackPresent; }
          if msg1.engine_resp.idx == msg2.engine_resp.idx {
            assert false;
          } else {
            assert OnMissInProgress(c, v, msg1.meta.addr, msg1.engine_resp.idx);
            assert OnMissInProgress(c, v, msg1.meta.addr, msg2.engine_resp.idx);
            if PrivateMorph(msg1.meta.addr) {
              reveal L2PendingCallbackForAddr;
              assert false;
            } else {
              assert SharedMorph(msg1.meta.addr);
              reveal L3PendingCallbackForAddr;
              assert false;
            }
          }
        } else if InFlightEngineResponse(c, v, msg2) {
          assert msg1 in step.msgOps.send;
          assert IsInFlightOnMissResponse(c, v, msg2.meta.addr, msg2, msg2.engine_resp.idx);
          assert CallbackPresentInBufferLocation(c, v, msg1.meta.addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          assert InFlightOnMissResponse(c, v, msg2.meta.addr, msg2.engine_resp.idx) by { reveal InFlightOnMissResponse; }
          assert CallbackPresent(c, v, msg1.meta.addr, EngineRequest.OnMiss(msg1.engine_resp.idx)) by { reveal CallbackPresent; }
          if msg1.engine_resp.idx == msg2.engine_resp.idx {
            assert false;
          } else {
            assert OnMissInProgress(c, v, msg1.meta.addr, msg1.engine_resp.idx);
            assert OnMissInProgress(c, v, msg1.meta.addr, msg2.engine_resp.idx);
            if PrivateMorph(msg1.meta.addr) {
              reveal L2PendingCallbackForAddr;
              assert false;
            } else {
              assert SharedMorph(msg1.meta.addr);
              reveal L3PendingCallbackForAddr;
              assert false;
            }
          }
        } else {
          assert msg1 in step.msgOps.send;
          assert msg2 in step.msgOps.send;
          assert msg1 == msg2;
        }
      }
    }
  }

  lemma EndCBPreservesEachAddrCacheBoundMsgIsUnique(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict || re == EndOnMiss || re == EndOnWriteback
    requires v.WF(c)
    requires OnMissRequestOnlyCallbackOrResponse(c, v)
    requires EachAddrCacheBoundMsgIsUnique(c, v)
    ensures EachAddrCacheBoundMsgIsUnique(c, v')
  {
    forall msg | InFlightEngineResponse(c, v', msg)
      ensures v'.network.inFlightMessages[msg] == 1
    {
      if msg in step.msgOps.send && msg in v.network.inFlightMessages {
        assert IsInFlightOnMissResponse(c, v, msg.meta.addr, msg, msg.engine_resp.idx);
        assert CallbackPresentInBufferLocation(c, v, msg.meta.addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
        assert InFlightOnMissResponse(c, v, msg.meta.addr, msg.engine_resp.idx) by { reveal InFlightOnMissResponse; }
        assert CallbackPresent(c, v, msg.meta.addr, EngineRequest.OnMiss(msg.engine_resp.idx)) by { reveal CallbackPresent; }
      }
    }
  }
}