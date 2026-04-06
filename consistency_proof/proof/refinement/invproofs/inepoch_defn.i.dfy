include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module InEpochDefnProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes
  import opened CacheTypes

  lemma MorphAddrIsInL2CacheEntryIsHeldConstant(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent, addr: Address)
    requires Tako.NextStep(c, v, v', step, re)
    requires PrivateMorph(addr)
    requires addr.morphType.idx < |v'.tiles|
    requires v'.tiles[addr.morphType.idx].l2.cache == v.tiles[addr.morphType.idx].l2.cache
    requires (forall msg | InFlightEngineResponse(c, v', msg) :: InFlightEngineResponse(c, v, msg))
    requires MorphAddrIsInL2CacheEntry(c, v', addr)
    ensures MorphAddrIsInL2CacheEntry(c, v, addr)
  {
    reveal MorphAddrIsInL2CacheEntry;
    var c_idx: nat :| (NonEmptyL2CacheEntry(c, v', addr.morphType.idx, c_idx)
     && v'.tiles[addr.morphType.idx].l2.cache[c_idx].addr == addr
     && (v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? ==> InFlightOnMissResponse(c, v', addr, c_idx)));
    assert NonEmptyL2CacheEntry(c, v, addr.morphType.idx, c_idx);
    assert v.tiles[addr.morphType.idx].l2.cache[c_idx].addr == addr;
    if v.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? {
      assert v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB?;
      assert InFlightOnMissResponse(c, v, addr, c_idx) by {
        reveal InFlightOnMissResponse;
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert InFlightEngineResponse(c, v', msg);
        assert InFlightEngineResponse(c, v, msg);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      }
    }
    assert MorphAddrIsInL2CacheEntry(c, v, addr);
  }

  lemma MorphAddrIsInL3CacheEntryIsHeldConstant(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent, addr: Address)
    requires Tako.NextStep(c, v, v', step, re)
    requires SharedMorph(addr)
    requires c.addr_map(addr) < |v'.tiles|
    requires v'.tiles[c.addr_map(addr)].l3.cache == v.tiles[c.addr_map(addr)].l3.cache
    requires (forall msg | InFlightEngineResponse(c, v', msg) :: InFlightEngineResponse(c, v, msg))
    requires MorphAddrIsInL3CacheEntry(c, v', addr)
    ensures MorphAddrIsInL3CacheEntry(c, v, addr)
  {
    reveal MorphAddrIsInL3CacheEntry;
    var c_idx: nat :| (NonEmptyL3CacheEntry(c, v', c.addr_map(addr), c_idx)
     && v'.tiles[c.addr_map(addr)].l3.cache[c_idx].addr == addr
     && (v'.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB? ==> InFlightOnMissResponse(c, v', addr, c_idx)));
    assert NonEmptyL3CacheEntry(c, v, c.addr_map(addr), c_idx);
    assert v.tiles[c.addr_map(addr)].l3.cache[c_idx].addr == addr;
    if v.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB? {
      assert v'.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB?;
      assert InFlightOnMissResponse(c, v, addr, c_idx) by {
        reveal InFlightOnMissResponse;
        assert InFlightOnMissResponse(c, v', addr, c_idx);
        var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
        assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
      }
    }
  }

  lemma CoreStepNoNewEngineResponses(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    ensures forall msg | InFlightEngineResponse(c, v', msg) :: InFlightEngineResponse(c, v, msg)
  {}

  lemma ProxyStepNoNewEngineResponses(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    ensures forall msg | InFlightEngineResponse(c, v', msg) :: InFlightEngineResponse(c, v, msg)
  {}

  lemma MemoryStepNoNewEngineResponses(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    ensures forall msg | InFlightEngineResponse(c, v', msg) :: InFlightEngineResponse(c, v, msg)
  {}

  lemma EngineStepStartCBNoNewEngineResponses(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
    ensures forall msg | InFlightEngineResponse(c, v', msg) :: InFlightEngineResponse(c, v, msg)
  {}

  lemma PerfInstNoNewEngineResponses(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    ensures forall msg | InFlightEngineResponse(c, v', msg) :: InFlightEngineResponse(c, v, msg)
  {}

  lemma EngineStepNoOpNoNewEngineResponses(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    ensures forall msg | InFlightEngineResponse(c, v', msg) :: InFlightEngineResponse(c, v, msg)
  {}

  lemma L2StepNoNewEngineResponses(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    ensures forall msg | InFlightEngineResponse(c, v', msg) :: InFlightEngineResponse(c, v, msg)
  {}

  lemma L3StepNoNewEngineResponses(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    ensures forall msg | InFlightEngineResponse(c, v', msg) :: InFlightEngineResponse(c, v, msg)
  {}

  lemma CoreNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    ensures NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v')
  {
    assert step.tile_step.core_step.CacheCommunicationStep?;
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || MorphAddrIsInL2CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || MorphAddrIsInL3CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
      // ensures (forall val | InFlightOnEvictRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.None?
      //   && v'.g.callback_epochs[addr].me.Me?
      //   && v'.g.callback_epochs[addr].me.val == val
      // ))
      // ensures (forall val | InFlightOnWritebackRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.Some?
      //   && v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   && var wval := if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval;
      //   && wval == val
      // ))
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert MorphAddrIsInL2CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert addr.morphType.idx < |v'.tiles|;
          if MorphAddrIsInL2CacheEntry(c, v', addr) {
            CoreStepNoNewEngineResponses(c, v, v', step);
            MorphAddrIsInL2CacheEntryIsHeldConstant(c, v, v', step, NoOp, addr);
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert MorphAddrIsInL3CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert c.addr_map(addr) < |v'.tiles|;
          if MorphAddrIsInL3CacheEntry(c, v', addr) {
            CoreStepNoNewEngineResponses(c, v, v', step);
            MorphAddrIsInL3CacheEntryIsHeldConstant(c, v, v', step, NoOp, addr);
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;

      // forall val | InFlightOnEvictRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.None?
      //   ensures v'.g.callback_epochs[addr].me.Me?
      //   ensures v'.g.callback_epochs[addr].me.val == val
      // {
      //   assert InFlightOnEvictRequest(c, v, addr, val) by {
      //     reveal InFlightOnEvictRequest;
      //     var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.None?;
      //   assert v'.g.callback_epochs[addr].wcb.None?;
      // }

      // forall val | InFlightOnWritebackRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.Some?
      //   ensures v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   ensures (
      //     (if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval)
      //     ==
      //     val
      //   )
      // {
      //   assert InFlightOnWritebackRequest(c, v, addr, val) by {
      //     reveal InFlightOnWritebackRequest;
      //     var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.Some?;
      //   assert v'.g.callback_epochs[addr].wcb.Some?;
      // }
    }
  }

  lemma ProxyNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    ensures NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || MorphAddrIsInL2CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || MorphAddrIsInL3CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
      // ensures (forall val | InFlightOnEvictRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.None?
      //   && v'.g.callback_epochs[addr].me.Me?
      //   && v'.g.callback_epochs[addr].me.val == val
      // ))
      // ensures (forall val | InFlightOnWritebackRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.Some?
      //   && v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   && var wval := if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval;
      //   && wval == val
      // ))
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert MorphAddrIsInL2CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert addr.morphType.idx < |v'.tiles|;
          if MorphAddrIsInL2CacheEntry(c, v', addr) {
            ProxyStepNoNewEngineResponses(c, v, v', step);
            MorphAddrIsInL2CacheEntryIsHeldConstant(c, v, v', step, NoOp, addr);
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert MorphAddrIsInL3CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert c.addr_map(addr) < |v'.tiles|;
          if MorphAddrIsInL3CacheEntry(c, v', addr) {
            ProxyStepNoNewEngineResponses(c, v, v', step);
            MorphAddrIsInL3CacheEntryIsHeldConstant(c, v, v', step, NoOp, addr);
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;

      // forall val | InFlightOnEvictRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.None?
      //   ensures v'.g.callback_epochs[addr].me.Me?
      //   ensures v'.g.callback_epochs[addr].me.val == val
      // {
      //   assert InFlightOnEvictRequest(c, v, addr, val) by {
      //     reveal InFlightOnEvictRequest;
      //     var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.None?;
      //   assert v'.g.callback_epochs[addr].wcb.None?;
      // }

      // forall val | InFlightOnWritebackRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.Some?
      //   ensures v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   ensures (
      //     (if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval)
      //     ==
      //     val
      //   )
      // {
      //   assert InFlightOnWritebackRequest(c, v, addr, val) by {
      //     reveal InFlightOnWritebackRequest;
      //     var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.Some?;
      //   assert v'.g.callback_epochs[addr].wcb.Some?;
      // }
    }
  }

  lemma MemoryNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    ensures NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || MorphAddrIsInL2CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || MorphAddrIsInL3CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
      // ensures (forall val | InFlightOnEvictRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.None?
      //   && v'.g.callback_epochs[addr].me.Me?
      //   && v'.g.callback_epochs[addr].me.val == val
      // ))
      // ensures (forall val | InFlightOnWritebackRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.Some?
      //   && v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   && var wval := if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval;
      //   && wval == val
      // ))
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert MorphAddrIsInL2CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert addr.morphType.idx < |v'.tiles|;
          if MorphAddrIsInL2CacheEntry(c, v', addr) {
            MemoryStepNoNewEngineResponses(c, v, v', step);
            MorphAddrIsInL2CacheEntryIsHeldConstant(c, v, v', step, NoOp, addr);
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert MorphAddrIsInL3CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert c.addr_map(addr) < |v'.tiles|;
          if MorphAddrIsInL3CacheEntry(c, v', addr) {
            MemoryStepNoNewEngineResponses(c, v, v', step);
            MorphAddrIsInL3CacheEntryIsHeldConstant(c, v, v', step, NoOp, addr);
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;

      // forall val | InFlightOnEvictRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.None?
      //   ensures v'.g.callback_epochs[addr].me.Me?
      //   ensures v'.g.callback_epochs[addr].me.val == val
      // {
      //   assert InFlightOnEvictRequest(c, v, addr, val) by {
      //     reveal InFlightOnEvictRequest;
      //     var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.None?;
      //   assert v'.g.callback_epochs[addr].wcb.None?;
      // }

      // forall val | InFlightOnWritebackRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.Some?
      //   ensures v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   ensures (
      //     (if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval)
      //     ==
      //     val
      //   )
      // {
      //   assert InFlightOnWritebackRequest(c, v, addr, val) by {
      //     reveal InFlightOnWritebackRequest;
      //     var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.Some?;
      //   assert v'.g.callback_epochs[addr].wcb.Some?;
      // }
    }
  }

  lemma EngineNotReceiveCallbackReqNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires !step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    ensures NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v')
  {
    assert step.tile_step.eng_step.CacheCommunicationStep?;
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || MorphAddrIsInL2CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || MorphAddrIsInL3CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
      // ensures (forall val | InFlightOnEvictRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.None?
      //   && v'.g.callback_epochs[addr].me.Me?
      //   && v'.g.callback_epochs[addr].me.val == val
      // ))
      // ensures (forall val | InFlightOnWritebackRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.Some?
      //   && v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   && var wval := if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval;
      //   && wval == val
      // ))
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert MorphAddrIsInL2CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert addr.morphType.idx < |v'.tiles|;
          if MorphAddrIsInL2CacheEntry(c, v', addr) {
            EngineStepNoOpNoNewEngineResponses(c, v, v', step);
            MorphAddrIsInL2CacheEntryIsHeldConstant(c, v, v', step, NoOp, addr);
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert MorphAddrIsInL3CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert c.addr_map(addr) < |v'.tiles|;
          if MorphAddrIsInL3CacheEntry(c, v', addr) {
            EngineStepNoOpNoNewEngineResponses(c, v, v', step);
            MorphAddrIsInL3CacheEntryIsHeldConstant(c, v, v', step, NoOp, addr);
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;

      // forall val | InFlightOnEvictRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.None?
      //   ensures v'.g.callback_epochs[addr].me.Me?
      //   ensures v'.g.callback_epochs[addr].me.val == val
      // {
      //   assert InFlightOnEvictRequest(c, v, addr, val) by {
      //     reveal InFlightOnEvictRequest;
      //     var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.None?;
      //   assert v'.g.callback_epochs[addr].wcb.None?;
      // }

      // forall val | InFlightOnWritebackRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.Some?
      //   ensures v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   ensures (
      //     (if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval)
      //     ==
      //     val
      //   )
      // {
      //   assert InFlightOnWritebackRequest(c, v, addr, val) by {
      //     reveal InFlightOnWritebackRequest;
      //     var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.Some?;
      //   assert v'.g.callback_epochs[addr].wcb.Some?;
      // }
    }
  }

  lemma EngineReceiveCallbackReqNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    ensures NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || MorphAddrIsInL2CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || MorphAddrIsInL3CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
      // ensures (forall val | InFlightOnEvictRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.None?
      //   && v'.g.callback_epochs[addr].me.Me?
      //   && v'.g.callback_epochs[addr].me.val == val
      // ))
      // ensures (forall val | InFlightOnWritebackRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.Some?
      //   && v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   && var wval := if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval;
      //   && wval == val
      // ))
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert MorphAddrIsInL2CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert addr.morphType.idx < |v'.tiles|;
          if MorphAddrIsInL2CacheEntry(c, v', addr) {
            EngineStepNoOpNoNewEngineResponses(c, v, v', step);
            MorphAddrIsInL2CacheEntryIsHeldConstant(c, v, v', step, NoOp, addr);
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                var new_idx := if addr == step.msgOps.recv.val.meta.addr then idx + 1 else idx;
                assert IsInFlightOnEvictRequest(c, v, addr, new_idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                var new_idx := if addr == step.msgOps.recv.val.meta.addr then idx + 1 else idx;
                assert IsInFlightOnWritebackRequest(c, v, addr, new_idx, val);
              }
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert MorphAddrIsInL3CacheEntry(c, v, addr)|| InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {

          assert c.addr_map(addr) < |v'.tiles|;
          if MorphAddrIsInL3CacheEntry(c, v', addr) {
            EngineStepNoOpNoNewEngineResponses(c, v, v', step);
            MorphAddrIsInL3CacheEntryIsHeldConstant(c, v, v', step, NoOp, addr);
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                var new_idx := if addr == step.msgOps.recv.val.meta.addr then idx + 1 else idx;
                assert IsInFlightOnEvictRequest(c, v, addr, new_idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                var new_idx := if addr == step.msgOps.recv.val.meta.addr then idx + 1 else idx;
                assert IsInFlightOnWritebackRequest(c, v, addr, new_idx, val);
              }
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;

      // forall val | InFlightOnEvictRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.None?
      //   ensures v'.g.callback_epochs[addr].me.Me?
      //   ensures v'.g.callback_epochs[addr].me.val == val
      // {
      //   assert InFlightOnEvictRequest(c, v, addr, val) by {
      //     reveal InFlightOnEvictRequest;
      //     var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
      //     var new_idx := if addr == step.msgOps.recv.val.meta.addr then idx + 1 else idx;
      //     assert IsInFlightOnEvictRequest(c, v, addr, new_idx, val);
      //   }
      //   assert v'.g.callback_epochs[addr].wcb.None?;
      //   assert v'.g.callback_epochs[addr].wcb.None?;
      // }

      // forall val | InFlightOnWritebackRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.Some?
      //   ensures v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   ensures (
      //     (if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval)
      //     ==
      //     val
      //   )
      // {
      //   assert InFlightOnWritebackRequest(c, v, addr, val) by {
      //     reveal InFlightOnWritebackRequest;
      //     var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
      //     var new_idx := if addr == step.msgOps.recv.val.meta.addr then idx + 1 else idx;
      //     assert IsInFlightOnWritebackRequest(c, v, addr, new_idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.Some?;
      //   assert v'.g.callback_epochs[addr].wcb.Some?;
      // }
    }
  }

  lemma L2ReceiveOnMissDataNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    ensures NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || MorphAddrIsInL2CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || MorphAddrIsInL3CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
      // ensures (forall val | InFlightOnEvictRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.None?
      //   && v'.g.callback_epochs[addr].me.Me?
      //   && v'.g.callback_epochs[addr].me.val == val
      // ))
      // ensures (forall val | InFlightOnWritebackRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.Some?
      //   && v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   && var wval := if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval;
      //   && wval == val
      // ))
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert MorphAddrIsInL2CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert addr.morphType.idx < |v'.tiles|;
          if MorphAddrIsInL2CacheEntry(c, v', addr) {
            assert MorphAddrIsInL2CacheEntry(c, v, addr) by {
              reveal MorphAddrIsInL2CacheEntry;
              var c_idx: nat :| (NonEmptyL2CacheEntry(c, v', addr.morphType.idx, c_idx)
                && v'.tiles[addr.morphType.idx].l2.cache[c_idx].addr == addr
                && (v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? ==> InFlightOnMissResponse(c, v', addr, c_idx)));
              assert NonEmptyL2CacheEntry(c, v, addr.morphType.idx, c_idx);
              assert v.tiles[addr.morphType.idx].l2.cache[c_idx].addr == addr;
              if v.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? {
                if v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? {
                  assert InFlightOnMissResponse(c, v, addr, c_idx) by {
                    reveal InFlightOnMissResponse;
                    assert InFlightOnMissResponse(c, v', addr, c_idx);
                    var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
                    assert InFlightEngineResponse(c, v', msg);
                    assert InFlightEngineResponse(c, v, msg);
                    assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
                  }
                } else {
                  assert !v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB?;
                  assert step.tile_step.l2_step.ReceiveOnMissDataStep?;
                  var msg := step.msgOps.recv.val;
                  assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
                  assert InFlightOnMissResponse(c, v, addr, c_idx) by { reveal InFlightOnMissResponse; }
                }
              }
            }
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert MorphAddrIsInL3CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert c.addr_map(addr) < |v'.tiles|;
          if MorphAddrIsInL3CacheEntry(c, v', addr) {
            L2StepNoNewEngineResponses(c, v, v', step);
            MorphAddrIsInL3CacheEntryIsHeldConstant(c, v, v', step, NoOp, addr);
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;

      // forall val | InFlightOnEvictRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.None?
      //   ensures v'.g.callback_epochs[addr].me.Me?
      //   ensures v'.g.callback_epochs[addr].me.val == val
      // {
      //   assert InFlightOnEvictRequest(c, v, addr, val) by {
      //     reveal InFlightOnEvictRequest;
      //     var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.None?;
      //   assert v'.g.callback_epochs[addr].wcb.None?;
      // }

      // forall val | InFlightOnWritebackRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.Some?
      //   ensures v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   ensures (
      //     (if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval)
      //     ==
      //     val
      //   )
      // {
      //   assert InFlightOnWritebackRequest(c, v, addr, val) by {
      //     reveal InFlightOnWritebackRequest;
      //     var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.Some?;
      //   assert v'.g.callback_epochs[addr].wcb.Some?;
      // }
    }
  }

  lemma L2DirectoryNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    ensures NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || MorphAddrIsInL2CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || MorphAddrIsInL3CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
      // ensures (forall val | InFlightOnEvictRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.None?
      //   && v'.g.callback_epochs[addr].me.Me?
      //   && v'.g.callback_epochs[addr].me.val == val
      // ))
      // ensures (forall val | InFlightOnWritebackRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.Some?
      //   && v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   && var wval := if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval;
      //   && wval == val
      // ))
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert MorphAddrIsInL2CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert addr.morphType.idx < |v'.tiles|;
          if MorphAddrIsInL2CacheEntry(c, v', addr) {
            assert MorphAddrIsInL2CacheEntry(c, v, addr) by {
              reveal MorphAddrIsInL2CacheEntry;
              var c_idx: nat :| (NonEmptyL2CacheEntry(c, v', addr.morphType.idx, c_idx)
                && v'.tiles[addr.morphType.idx].l2.cache[c_idx].addr == addr
                && (v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? ==> InFlightOnMissResponse(c, v', addr, c_idx)));
              assert NonEmptyL2CacheEntry(c, v, addr.morphType.idx, c_idx);
              assert v.tiles[addr.morphType.idx].l2.cache[c_idx].addr == addr;
              if v.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? {
                if v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? {
                  assert InFlightOnMissResponse(c, v, addr, c_idx) by {
                    reveal InFlightOnMissResponse;
                    assert InFlightOnMissResponse(c, v', addr, c_idx);
                    var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
                    assert InFlightEngineResponse(c, v', msg);
                    assert InFlightEngineResponse(c, v, msg);
                    assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
                  }
                } else {
                  assert !v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB?;
                  assert step.tile_step.l2_step.ReceiveOnMissDataStep?;
                  var msg := step.msgOps.recv.val;
                  assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
                  assert InFlightOnMissResponse(c, v, addr, c_idx) by { reveal InFlightOnMissResponse; }
                }
              }
            }
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert MorphAddrIsInL3CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert c.addr_map(addr) < |v'.tiles|;
          if MorphAddrIsInL3CacheEntry(c, v', addr) {
            L2StepNoNewEngineResponses(c, v, v', step);
            MorphAddrIsInL3CacheEntryIsHeldConstant(c, v, v', step, NoOp, addr);
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;

      // forall val | InFlightOnEvictRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.None?
      //   ensures v'.g.callback_epochs[addr].me.Me?
      //   ensures v'.g.callback_epochs[addr].me.val == val
      // {
      //   assert InFlightOnEvictRequest(c, v, addr, val) by {
      //     reveal InFlightOnEvictRequest;
      //     var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.None?;
      //   assert v'.g.callback_epochs[addr].wcb.None?;
      // }

      // forall val | InFlightOnWritebackRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.Some?
      //   ensures v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   ensures (
      //     (if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval)
      //     ==
      //     val
      //   )
      // {
      //   assert InFlightOnWritebackRequest(c, v, addr, val) by {
      //     reveal InFlightOnWritebackRequest;
      //     var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.Some?;
      //   assert v'.g.callback_epochs[addr].wcb.Some?;
      // }
    }
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    ensures NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || MorphAddrIsInL2CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || MorphAddrIsInL3CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
      // ensures (forall val | InFlightOnEvictRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.None?
      //   && v'.g.callback_epochs[addr].me.Me?
      //   && v'.g.callback_epochs[addr].me.val == val
      // ))
      // ensures (forall val | InFlightOnWritebackRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.Some?
      //   && v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   && var wval := if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval;
      //   && wval == val
      // ))
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert MorphAddrIsInL2CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert addr.morphType.idx < |v'.tiles|;
          if MorphAddrIsInL2CacheEntry(c, v', addr) {
            assert MorphAddrIsInL2CacheEntry(c, v, addr) by {
              reveal MorphAddrIsInL2CacheEntry;
              var c_idx: nat :| (NonEmptyL2CacheEntry(c, v', addr.morphType.idx, c_idx)
                && v'.tiles[addr.morphType.idx].l2.cache[c_idx].addr == addr
                && (v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? ==> InFlightOnMissResponse(c, v', addr, c_idx)));
              assert NonEmptyL2CacheEntry(c, v, addr.morphType.idx, c_idx);
              assert v.tiles[addr.morphType.idx].l2.cache[c_idx].addr == addr;
              if v.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? {
                if v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? {
                  assert InFlightOnMissResponse(c, v, addr, c_idx) by {
                    reveal InFlightOnMissResponse;
                    assert InFlightOnMissResponse(c, v', addr, c_idx);
                    var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
                    assert InFlightEngineResponse(c, v', msg);
                    assert InFlightEngineResponse(c, v, msg);
                    assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
                  }
                } else {
                  assert !v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB?;
                  assert step.tile_step.l2_step.ReceiveOnMissDataStep?;
                  var msg := step.msgOps.recv.val;
                  assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
                  assert InFlightOnMissResponse(c, v, addr, c_idx) by { reveal InFlightOnMissResponse; }
                }
              }
            }
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert MorphAddrIsInL3CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert c.addr_map(addr) < |v'.tiles|;
          if MorphAddrIsInL3CacheEntry(c, v', addr) {
            L2StepNoNewEngineResponses(c, v, v', step);
            MorphAddrIsInL3CacheEntryIsHeldConstant(c, v, v', step, NoOp, addr);
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;

      // forall val | InFlightOnEvictRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.None?
      //   ensures v'.g.callback_epochs[addr].me.Me?
      //   ensures v'.g.callback_epochs[addr].me.val == val
      // {
      //   assert InFlightOnEvictRequest(c, v, addr, val) by {
      //     reveal InFlightOnEvictRequest;
      //     var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.None?;
      //   assert v'.g.callback_epochs[addr].wcb.None?;
      // }

      // forall val | InFlightOnWritebackRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.Some?
      //   ensures v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   ensures (
      //     (if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval)
      //     ==
      //     val
      //   )
      // {
      //   assert InFlightOnWritebackRequest(c, v, addr, val) by {
      //     reveal InFlightOnWritebackRequest;
      //     var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.Some?;
      //   assert v'.g.callback_epochs[addr].wcb.Some?;
      // }
    }
  }

  lemma L2CacheCommunicationGetSNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires step.tile_step.l2_step.c_step.GetSStep?
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    ensures NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || MorphAddrIsInL2CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || MorphAddrIsInL3CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
      // ensures (forall val | InFlightOnEvictRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.None?
      //   && v'.g.callback_epochs[addr].me.Me?
      //   && v'.g.callback_epochs[addr].me.val == val
      // ))
      // ensures (forall val | InFlightOnWritebackRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.Some?
      //   && v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   && var wval := if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval;
      //   && wval == val
      // ))
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert MorphAddrIsInL2CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert addr.morphType.idx < |v'.tiles|;
          if MorphAddrIsInL2CacheEntry(c, v', addr) {
            assert MorphAddrIsInL2CacheEntry(c, v, addr) by {
              reveal MorphAddrIsInL2CacheEntry;
              var c_idx: nat :| (NonEmptyL2CacheEntry(c, v', addr.morphType.idx, c_idx)
                && v'.tiles[addr.morphType.idx].l2.cache[c_idx].addr == addr
                && (v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? ==> InFlightOnMissResponse(c, v', addr, c_idx)));
              assert NonEmptyL2CacheEntry(c, v, addr.morphType.idx, c_idx);
              assert v.tiles[addr.morphType.idx].l2.cache[c_idx].addr == addr;
              if v.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? {
                if v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? {
                  assert InFlightOnMissResponse(c, v, addr, c_idx) by {
                    reveal InFlightOnMissResponse;
                    assert InFlightOnMissResponse(c, v', addr, c_idx);
                    var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
                    assert InFlightEngineResponse(c, v', msg);
                    assert InFlightEngineResponse(c, v, msg);
                    assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
                  }
                } else {
                  assert !v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB?;
                  assert step.tile_step.l2_step.ReceiveOnMissDataStep?;
                  var msg := step.msgOps.recv.val;
                  assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
                  assert InFlightOnMissResponse(c, v, addr, c_idx) by { reveal InFlightOnMissResponse; }
                }
              }
            }
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert MorphAddrIsInL3CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert c.addr_map(addr) < |v'.tiles|;
          if MorphAddrIsInL3CacheEntry(c, v', addr) {
            L2StepNoNewEngineResponses(c, v, v', step);
            MorphAddrIsInL3CacheEntryIsHeldConstant(c, v, v', step, NoOp, addr);
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;

      // forall val | InFlightOnEvictRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.None?
      //   ensures v'.g.callback_epochs[addr].me.Me?
      //   ensures v'.g.callback_epochs[addr].me.val == val
      // {
      //   assert InFlightOnEvictRequest(c, v, addr, val) by {
      //     reveal InFlightOnEvictRequest;
      //     var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.None?;
      //   assert v'.g.callback_epochs[addr].wcb.None?;
      // }

      // forall val | InFlightOnWritebackRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.Some?
      //   ensures v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   ensures (
      //     (if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval)
      //     ==
      //     val
      //   )
      // {
      //   assert InFlightOnWritebackRequest(c, v, addr, val) by {
      //     reveal InFlightOnWritebackRequest;
      //     var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.Some?;
      //   assert v'.g.callback_epochs[addr].wcb.Some?;
      // }
    }
  }

  lemma L2CacheCommunicationGetMNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires step.tile_step.l2_step.c_step.GetMStep?
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    ensures NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || MorphAddrIsInL2CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || MorphAddrIsInL3CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
      // ensures (forall val | InFlightOnEvictRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.None?
      //   && v'.g.callback_epochs[addr].me.Me?
      //   && v'.g.callback_epochs[addr].me.val == val
      // ))
      // ensures (forall val | InFlightOnWritebackRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.Some?
      //   && v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   && var wval := if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval;
      //   && wval == val
      // ))
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert MorphAddrIsInL2CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert addr.morphType.idx < |v'.tiles|;
          if MorphAddrIsInL2CacheEntry(c, v', addr) {
            assert MorphAddrIsInL2CacheEntry(c, v, addr) by {
              reveal MorphAddrIsInL2CacheEntry;
              var c_idx: nat :| (NonEmptyL2CacheEntry(c, v', addr.morphType.idx, c_idx)
                && v'.tiles[addr.morphType.idx].l2.cache[c_idx].addr == addr
                && (v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? ==> InFlightOnMissResponse(c, v', addr, c_idx)));
              assert NonEmptyL2CacheEntry(c, v, addr.morphType.idx, c_idx);
              assert v.tiles[addr.morphType.idx].l2.cache[c_idx].addr == addr;
              if v.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? {
                if v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? {
                  assert InFlightOnMissResponse(c, v, addr, c_idx) by {
                    reveal InFlightOnMissResponse;
                    assert InFlightOnMissResponse(c, v', addr, c_idx);
                    var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
                    assert InFlightEngineResponse(c, v', msg);
                    assert InFlightEngineResponse(c, v, msg);
                    assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
                  }
                } else {
                  assert !v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB?;
                  assert step.tile_step.l2_step.ReceiveOnMissDataStep?;
                  var msg := step.msgOps.recv.val;
                  assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
                  assert InFlightOnMissResponse(c, v, addr, c_idx) by { reveal InFlightOnMissResponse; }
                }
              }
            }
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert MorphAddrIsInL3CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert c.addr_map(addr) < |v'.tiles|;
          if MorphAddrIsInL3CacheEntry(c, v', addr) {
            L2StepNoNewEngineResponses(c, v, v', step);
            MorphAddrIsInL3CacheEntryIsHeldConstant(c, v, v', step, NoOp, addr);
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;

      // forall val | InFlightOnEvictRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.None?
      //   ensures v'.g.callback_epochs[addr].me.Me?
      //   ensures v'.g.callback_epochs[addr].me.val == val
      // {
      //   assert InFlightOnEvictRequest(c, v, addr, val) by {
      //     reveal InFlightOnEvictRequest;
      //     var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.None?;
      //   assert v'.g.callback_epochs[addr].wcb.None?;
      // }

      // forall val | InFlightOnWritebackRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.Some?
      //   ensures v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   ensures (
      //     (if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval)
      //     ==
      //     val
      //   )
      // {
      //   assert InFlightOnWritebackRequest(c, v, addr, val) by {
      //     reveal InFlightOnWritebackRequest;
      //     var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.Some?;
      //   assert v'.g.callback_epochs[addr].wcb.Some?;
      // }
    }
  }

  lemma L2CacheCommunicationEvictNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires step.tile_step.l2_step.c_step.EvictStep?
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    ensures NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || MorphAddrIsInL2CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || MorphAddrIsInL3CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
      // ensures (forall val | InFlightOnEvictRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.None?
      //   && v'.g.callback_epochs[addr].me.Me?
      //   && v'.g.callback_epochs[addr].me.val == val
      // ))
      // ensures (forall val | InFlightOnWritebackRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.Some?
      //   && v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   && var wval := if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval;
      //   && wval == val
      // ))
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert MorphAddrIsInL2CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert addr.morphType.idx < |v'.tiles|;
          if MorphAddrIsInL2CacheEntry(c, v', addr) {
            assert MorphAddrIsInL2CacheEntry(c, v, addr) by {
              reveal MorphAddrIsInL2CacheEntry;
              var c_idx: nat :| (NonEmptyL2CacheEntry(c, v', addr.morphType.idx, c_idx)
                && v'.tiles[addr.morphType.idx].l2.cache[c_idx].addr == addr
                && (v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? ==> InFlightOnMissResponse(c, v', addr, c_idx)));
              assert NonEmptyL2CacheEntry(c, v, addr.morphType.idx, c_idx);
              assert v.tiles[addr.morphType.idx].l2.cache[c_idx].addr == addr;
              if v.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? {
                if v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? {
                  assert InFlightOnMissResponse(c, v, addr, c_idx) by {
                    reveal InFlightOnMissResponse;
                    assert InFlightOnMissResponse(c, v', addr, c_idx);
                    var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
                    assert InFlightEngineResponse(c, v', msg);
                    assert InFlightEngineResponse(c, v, msg);
                    assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
                  }
                } else {
                  assert !v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB?;
                  assert step.tile_step.l2_step.ReceiveOnMissDataStep?;
                  var msg := step.msgOps.recv.val;
                  assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
                  assert InFlightOnMissResponse(c, v, addr, c_idx) by { reveal InFlightOnMissResponse; }
                }
              }
            }
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert MorphAddrIsInL3CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert c.addr_map(addr) < |v'.tiles|;
          if MorphAddrIsInL3CacheEntry(c, v', addr) {
            L2StepNoNewEngineResponses(c, v, v', step);
            MorphAddrIsInL3CacheEntryIsHeldConstant(c, v, v', step, NoOp, addr);
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;

      // forall val | InFlightOnEvictRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.None?
      //   ensures v'.g.callback_epochs[addr].me.Me?
      //   ensures v'.g.callback_epochs[addr].me.val == val
      // {
      //   assert InFlightOnEvictRequest(c, v, addr, val) by {
      //     reveal InFlightOnEvictRequest;
      //     var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.None?;
      //   assert v'.g.callback_epochs[addr].wcb.None?;
      // }

      // forall val | InFlightOnWritebackRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.Some?
      //   ensures v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   ensures (
      //     (if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval)
      //     ==
      //     val
      //   )
      // {
      //   assert InFlightOnWritebackRequest(c, v, addr, val) by {
      //     reveal InFlightOnWritebackRequest;
      //     var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.Some?;
      //   assert v'.g.callback_epochs[addr].wcb.Some?;
      // }
    }
  }

  lemma L2CacheCommunicationRecvMsgNoOpPreservesPrivateMorphAddrInEpochStatus(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, addr: Address)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires step.tile_step.l2_step.c_step.RecvMsgStep?
    requires PrivateMorph(addr) 
    requires addr in v'.g.callback_epochs
    requires (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
      || MorphAddrIsInL2CacheEntry(c, v', addr)
      || InFlightOnEvictRequestForAddr(c, v', addr)
      || InFlightOnWritebackRequestForAddr(c, v', addr)
    ))
    requires addr.morphType.idx < |v.tiles|
    ensures (
      || MorphAddrIsInL2CacheEntry(c, v, addr)
      || InFlightOnEvictRequestForAddr(c, v, addr)
      || InFlightOnWritebackRequestForAddr(c, v, addr)
    )
  {
    assert MorphAddrIsInL2CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
      assert addr.morphType.idx < |v'.tiles|;
      if MorphAddrIsInL2CacheEntry(c, v', addr) {
        assert MorphAddrIsInL2CacheEntry(c, v, addr) by {
          reveal MorphAddrIsInL2CacheEntry;
          var c_idx: nat :| (NonEmptyL2CacheEntry(c, v', addr.morphType.idx, c_idx)
            && v'.tiles[addr.morphType.idx].l2.cache[c_idx].addr == addr
            && (v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? ==> InFlightOnMissResponse(c, v', addr, c_idx)));
          assert NonEmptyL2CacheEntry(c, v, addr.morphType.idx, c_idx);
          assert v.tiles[addr.morphType.idx].l2.cache[c_idx].addr == addr;
          if v.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? {
            if v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? {
              assert InFlightOnMissResponse(c, v, addr, c_idx) by {
                reveal InFlightOnMissResponse;
                assert InFlightOnMissResponse(c, v', addr, c_idx);
                var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
                assert InFlightEngineResponse(c, v', msg);
                assert InFlightEngineResponse(c, v, msg);
                assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
              }
            } else {
              assert !v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB?;
              assert step.tile_step.l2_step.ReceiveOnMissDataStep?;
              var msg := step.msgOps.recv.val;
              assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
              assert InFlightOnMissResponse(c, v, addr, c_idx) by { reveal InFlightOnMissResponse; }
            }
          }
        }
      } else if InFlightOnEvictRequestForAddr(c, v', addr) {
        assert InFlightOnEvictRequestForAddr(c, v, addr) by {
          reveal InFlightOnEvictRequestForAddr;
          var val :| InFlightOnEvictRequest(c, v', addr, val);
          assert InFlightOnEvictRequest(c, v, addr, val) by {
            reveal InFlightOnEvictRequest;
            var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
            assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
          }
        }
      } else {
        assert InFlightOnWritebackRequestForAddr(c, v', addr);
        assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
          reveal InFlightOnWritebackRequestForAddr;
          var val :| InFlightOnWritebackRequest(c, v', addr, val);
          assert InFlightOnWritebackRequest(c, v, addr, val) by {
            reveal InFlightOnWritebackRequest;
            var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
            assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
          }
        }
      }
    }
  }

  lemma L2CacheCommunicationRecvMsgNoOpPreservesSharedMorphAddrInEpochStatus(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, addr: Address)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires step.tile_step.l2_step.c_step.RecvMsgStep?
    requires SharedMorph(addr) 
    requires addr in v'.g.callback_epochs
    requires (SharedMorph(addr) && c.addr_map(addr) < |v.tiles| ==> (
      || MorphAddrIsInL3CacheEntry(c, v', addr)
      || InFlightOnEvictRequestForAddr(c, v', addr)
      || InFlightOnWritebackRequestForAddr(c, v', addr)
    ))
    requires c.addr_map(addr) < |v.tiles|
    ensures (
      || MorphAddrIsInL3CacheEntry(c, v, addr)
      || InFlightOnEvictRequestForAddr(c, v, addr)
      || InFlightOnWritebackRequestForAddr(c, v, addr)
    )
  {
    assert MorphAddrIsInL3CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
      assert c.addr_map(addr) < |v'.tiles|;
      if MorphAddrIsInL3CacheEntry(c, v', addr) {
        L2StepNoNewEngineResponses(c, v, v', step);
        MorphAddrIsInL3CacheEntryIsHeldConstant(c, v, v', step, NoOp, addr);
      } else if InFlightOnEvictRequestForAddr(c, v', addr) {
        assert InFlightOnEvictRequestForAddr(c, v, addr) by {
          reveal InFlightOnEvictRequestForAddr;
          var val :| InFlightOnEvictRequest(c, v', addr, val);
          assert InFlightOnEvictRequest(c, v, addr, val) by {
            reveal InFlightOnEvictRequest;
            var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
            assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
          }
        }
      } else {
        assert InFlightOnWritebackRequestForAddr(c, v', addr);
        assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
          reveal InFlightOnWritebackRequestForAddr;
          var val :| InFlightOnWritebackRequest(c, v', addr, val);
          assert InFlightOnWritebackRequest(c, v, addr, val) by {
            reveal InFlightOnWritebackRequest;
            var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
            assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
          }
        }
      }
    }
  }

  lemma L2CacheCommunicationRecvMsgNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires step.tile_step.l2_step.c_step.RecvMsgStep?
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    ensures NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || MorphAddrIsInL2CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || MorphAddrIsInL3CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
      // ensures (forall val | InFlightOnEvictRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.None?
      //   && v'.g.callback_epochs[addr].me.Me?
      //   && v'.g.callback_epochs[addr].me.val == val
      // ))
      // ensures (forall val | InFlightOnWritebackRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.Some?
      //   && v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   && var wval := if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval;
      //   && wval == val
      // ))
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        L2CacheCommunicationRecvMsgNoOpPreservesPrivateMorphAddrInEpochStatus(c, v, v', step, addr);
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        L2CacheCommunicationRecvMsgNoOpPreservesSharedMorphAddrInEpochStatus(c, v, v', step, addr);
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;

      // forall val | InFlightOnEvictRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.None?
      //   ensures v'.g.callback_epochs[addr].me.Me?
      //   ensures v'.g.callback_epochs[addr].me.val == val
      // {
      //   assert InFlightOnEvictRequest(c, v, addr, val) by {
      //     reveal InFlightOnEvictRequest;
      //     var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.None?;
      //   assert v'.g.callback_epochs[addr].wcb.None?;
      // }

      // forall val | InFlightOnWritebackRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.Some?
      //   ensures v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   ensures (
      //     (if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval)
      //     ==
      //     val
      //   )
      // {
      //   assert InFlightOnWritebackRequest(c, v, addr, val) by {
      //     reveal InFlightOnWritebackRequest;
      //     var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.Some?;
      //   assert v'.g.callback_epochs[addr].wcb.Some?;
      // }
    }
  }

  lemma L2ScheduleCallbackNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    // requires L2DirtyBitMatchesEpoch(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || MorphAddrIsInL2CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || MorphAddrIsInL3CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
      // ensures (forall val | InFlightOnEvictRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.None?
      //   && v'.g.callback_epochs[addr].me.Me?
      //   && v'.g.callback_epochs[addr].me.val == val
      // ))
      // ensures (forall val | InFlightOnWritebackRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.Some?
      //   && v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   && var wval := if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval;
      //   && wval == val
      // ))
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert MorphAddrIsInL2CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert addr.morphType.idx < |v'.tiles|;
          if MorphAddrIsInL2CacheEntry(c, v', addr) {
            reveal MorphAddrIsInL2CacheEntry;
            var c_idx: nat :| (NonEmptyL2CacheEntry(c, v', addr.morphType.idx, c_idx)
              && v'.tiles[addr.morphType.idx].l2.cache[c_idx].addr == addr
              && (v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? ==> InFlightOnMissResponse(c, v', addr, c_idx)));
            if NonEmptyL2CacheEntry(c, v, addr.morphType.idx, c_idx) {
              assert v.tiles[addr.morphType.idx].l2.cache[c_idx].addr == addr;
              if v.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? {
                assert v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB?;
                assert InFlightOnMissResponse(c, v, addr, c_idx) by {
                  reveal InFlightOnMissResponse;
                  assert InFlightOnMissResponse(c, v', addr, c_idx);
                  var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
                  assert InFlightEngineResponse(c, v', msg);
                  assert InFlightEngineResponse(c, v, msg);
                  assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
                }
              }
            } else {
              // we scheduled an onmiss
              assert v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB?;
              assert InFlightOnMissResponse(c, v', addr, c_idx);
              assert InFlightOnMissResponse(c, v, addr, c_idx) by {
                reveal InFlightOnMissResponse;
                var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
                assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
              }
              assert OnMissInProgress(c, v, addr, c_idx);
              reveal L2PendingCallbackForAddr;
              assert false;
            }
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            reveal InFlightOnEvictRequestForAddr;
            var val :| InFlightOnEvictRequest(c, v', addr, val);
            reveal InFlightOnEvictRequest;
            var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
            if !IsInFlightOnEvictRequest(c, v, addr, idx, val) {
              assert MorphAddrIsInL2CacheEntry(c, v, addr) by {
                reveal MorphAddrIsInL2CacheEntry;
                assert NonEmptyL2CacheEntry(c, v, addr.morphType.idx, step.tile_step.l2_step.idx);
                assert DirIL2CacheEntry(c, v, addr.morphType.idx, step.tile_step.l2_step.idx);
              }
            } else {
              assert InFlightOnEvictRequest(c, v, addr, val);
              assert InFlightOnEvictRequestForAddr(c, v, addr);
            }
          } else {
            reveal InFlightOnWritebackRequestForAddr;
            var val :| InFlightOnWritebackRequest(c, v', addr, val);
            reveal InFlightOnWritebackRequest;
            var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
            if !IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
              assert MorphAddrIsInL2CacheEntry(c, v, addr) by {
                reveal MorphAddrIsInL2CacheEntry;
                assert NonEmptyL2CacheEntry(c, v, addr.morphType.idx, step.tile_step.l2_step.idx);
                assert DirIL2CacheEntry(c, v, addr.morphType.idx, step.tile_step.l2_step.idx);
              }
            } else {
              assert InFlightOnWritebackRequest(c, v, addr, val);
              assert InFlightOnWritebackRequestForAddr(c, v, addr);
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert MorphAddrIsInL3CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert c.addr_map(addr) < |v'.tiles|;
          if MorphAddrIsInL3CacheEntry(c, v', addr) {
            L2StepNoNewEngineResponses(c, v, v', step);
            MorphAddrIsInL3CacheEntryIsHeldConstant(c, v, v', step, NoOp, addr);
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;
      // forall val | InFlightOnEvictRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.None?
      //   ensures v'.g.callback_epochs[addr].me.Me?
      //   ensures v'.g.callback_epochs[addr].me.val == val
      // {
      //   reveal InFlightOnEvictRequest;
      //   var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
      //   if IsInFlightOnEvictRequest(c, v, addr, idx, val)  {
      //     assert InFlightOnEvictRequest(c, v, addr, val);
      //     assert v.g.callback_epochs[addr].wcb.None?;
      //     assert v'.g.callback_epochs[addr].wcb.None?;
      //   } else {
      //     assert step.tile_step.l2_step.eng_req.OnEvict?;
      //     assert CleanL2CacheEntry(c, v, step.tile_idx, step.tile_step.l2_step.idx);
      //     assert v'.g.callback_epochs[addr].wcb.None?;
      //   }
      // }

      // forall val | InFlightOnWritebackRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.Some?
      //   ensures v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   ensures (
      //     (if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval)
      //     ==
      //     val
      //   )
      // {
      //   reveal InFlightOnWritebackRequest;
      //   var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
      //   if InFlightOnWritebackRequest(c, v, addr, val) {
      //     assert InFlightOnWritebackRequest(c, v, addr, val);
      //     assert v.g.callback_epochs[addr].wcb.Some?;
      //     assert v'.g.callback_epochs[addr].wcb.Some?;
      //   } else {
      //     // TODO: no idea why this needs extra spelling out for proof when evict case was free
      //     assert !InFlightOnWritebackRequest(c, v, addr, val);
      //     var top := (if addr in v.network.inFlightEngReqs then |v.network.inFlightEngReqs[addr]| else 0);
      //     // forall idx': nat | idx < top
      //     //   ensures !IsInFlightOnWritebackRequest(c, v, addr, idx', val)
      //     // {}
      //     // assert addr in v'.network.inFlightEngReqs;
      //     var msg :| msg in step.msgOps.send;
      //     // assert |step.msgOps.send| == 1;
      //     assert addr == msg.meta.addr by {
      //       if addr != msg.meta.addr {
      //         assert addr in v.network.inFlightEngReqs;
      //         assert v.network.inFlightEngReqs[addr] == v'.network.inFlightEngReqs[addr];
      //         assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      //         assert false;
      //       }
      //     }
      //     assert idx == top by {
      //       if idx != top {
      //         if addr in v.network.inFlightEngReqs {
      //           assert idx < |v.network.inFlightEngReqs[addr]|;
      //           assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      //         }
      //         assert false;
      //       }
      //     }
      //     assert step.tile_step.l2_step.eng_req.OnWriteBack?;
      //     assert DirtyL2CacheEntry(c, v, step.tile_idx, step.tile_step.l2_step.idx);
      //     assert v'.g.callback_epochs[addr].wcb.Some?;
      //   }
      // }
    }
  }

  lemma L3DirectoryNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    ensures NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || MorphAddrIsInL2CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || MorphAddrIsInL3CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
      // ensures (forall val | InFlightOnEvictRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.None?
      //   && v'.g.callback_epochs[addr].me.Me?
      //   && v'.g.callback_epochs[addr].me.val == val
      // ))
      // ensures (forall val | InFlightOnWritebackRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.Some?
      //   && v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   && var wval := if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval;
      //   && wval == val
      // ))
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert MorphAddrIsInL2CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert addr.morphType.idx < |v'.tiles|;
          if MorphAddrIsInL2CacheEntry(c, v', addr) {
            L3StepNoNewEngineResponses(c, v, v', step);
            MorphAddrIsInL2CacheEntryIsHeldConstant(c, v, v', step, NoOp, addr);
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert MorphAddrIsInL3CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert c.addr_map(addr) < |v'.tiles|;
          if MorphAddrIsInL3CacheEntry(c, v', addr) {
            assert MorphAddrIsInL3CacheEntry(c, v, addr) by {
              reveal MorphAddrIsInL3CacheEntry;
              var c_idx: nat :| (NonEmptyL3CacheEntry(c, v', c.addr_map(addr), c_idx)
                && v'.tiles[c.addr_map(addr)].l3.cache[c_idx].addr == addr
                && (v'.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB? ==> InFlightOnMissResponse(c, v', addr, c_idx)));
              assert NonEmptyL3CacheEntry(c, v, c.addr_map(addr), c_idx);
              assert v.tiles[c.addr_map(addr)].l3.cache[c_idx].addr == addr;
              if v.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB? {
                if v'.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB? {
                  assert InFlightOnMissResponse(c, v, addr, c_idx) by {
                    reveal InFlightOnMissResponse;
                    assert InFlightOnMissResponse(c, v', addr, c_idx);
                    var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
                    assert InFlightEngineResponse(c, v', msg);
                    assert InFlightEngineResponse(c, v, msg);
                    assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
                  }
                } else {
                  assert !v'.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB?;
                  assert step.tile_step.l3_step.ReceiveOnMissDataStep?;
                  var msg := step.msgOps.recv.val;
                  assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
                  assert InFlightOnMissResponse(c, v, addr, c_idx) by { reveal InFlightOnMissResponse; }
                }
              }
            }
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;

      // forall val | InFlightOnEvictRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.None?
      //   ensures v'.g.callback_epochs[addr].me.Me?
      //   ensures v'.g.callback_epochs[addr].me.val == val
      // {
      //   assert InFlightOnEvictRequest(c, v, addr, val) by {
      //     reveal InFlightOnEvictRequest;
      //     var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.None?;
      //   assert v'.g.callback_epochs[addr].wcb.None?;
      // }

      // forall val | InFlightOnWritebackRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.Some?
      //   ensures v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   ensures (
      //     (if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval)
      //     ==
      //     val
      //   )
      // {
      //   assert InFlightOnWritebackRequest(c, v, addr, val) by {
      //     reveal InFlightOnWritebackRequest;
      //     var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.Some?;
      //   assert v'.g.callback_epochs[addr].wcb.Some?;
      // }
    }
  }

  lemma L3ReceiveOnMissDataNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    ensures NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || MorphAddrIsInL2CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || MorphAddrIsInL3CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
      // ensures (forall val | InFlightOnEvictRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.None?
      //   && v'.g.callback_epochs[addr].me.Me?
      //   && v'.g.callback_epochs[addr].me.val == val
      // ))
      // ensures (forall val | InFlightOnWritebackRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.Some?
      //   && v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   && var wval := if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval;
      //   && wval == val
      // ))
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert MorphAddrIsInL2CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert addr.morphType.idx < |v'.tiles|;
          if MorphAddrIsInL2CacheEntry(c, v', addr) {
            L3StepNoNewEngineResponses(c, v, v', step);
            MorphAddrIsInL2CacheEntryIsHeldConstant(c, v, v', step, NoOp, addr);
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert MorphAddrIsInL3CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert c.addr_map(addr) < |v'.tiles|;
          if MorphAddrIsInL3CacheEntry(c, v', addr) {
            assert MorphAddrIsInL3CacheEntry(c, v, addr) by {
              reveal MorphAddrIsInL3CacheEntry;
              var c_idx: nat :| (NonEmptyL3CacheEntry(c, v', c.addr_map(addr), c_idx)
                && v'.tiles[c.addr_map(addr)].l3.cache[c_idx].addr == addr
                && (v'.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB? ==> InFlightOnMissResponse(c, v', addr, c_idx)));
              assert NonEmptyL3CacheEntry(c, v, c.addr_map(addr), c_idx);
              assert v.tiles[c.addr_map(addr)].l3.cache[c_idx].addr == addr;
              if v.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB? {
                if v'.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB? {
                  assert InFlightOnMissResponse(c, v, addr, c_idx) by {
                    reveal InFlightOnMissResponse;
                    assert InFlightOnMissResponse(c, v', addr, c_idx);
                    var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
                    assert InFlightEngineResponse(c, v', msg);
                    assert InFlightEngineResponse(c, v, msg);
                    assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
                  }
                } else {
                  assert !v'.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB?;
                  assert step.tile_step.l3_step.ReceiveOnMissDataStep?;
                  var msg := step.msgOps.recv.val;
                  assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
                  assert InFlightOnMissResponse(c, v, addr, c_idx) by { reveal InFlightOnMissResponse; }
                }
              }
            }
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;

      // forall val | InFlightOnEvictRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.None?
      //   ensures v'.g.callback_epochs[addr].me.Me?
      //   ensures v'.g.callback_epochs[addr].me.val == val
      // {
      //   assert InFlightOnEvictRequest(c, v, addr, val) by {
      //     reveal InFlightOnEvictRequest;
      //     var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.None?;
      //   assert v'.g.callback_epochs[addr].wcb.None?;
      // }

      // forall val | InFlightOnWritebackRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.Some?
      //   ensures v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   ensures (
      //     (if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval)
      //     ==
      //     val
      //   )
      // {
      //   assert InFlightOnWritebackRequest(c, v, addr, val) by {
      //     reveal InFlightOnWritebackRequest;
      //     var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.Some?;
      //   assert v'.g.callback_epochs[addr].wcb.Some?;
      // }
    }
  }


  lemma L3ReqMemoryNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    ensures NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || MorphAddrIsInL2CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || MorphAddrIsInL3CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
      // ensures (forall val | InFlightOnEvictRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.None?
      //   && v'.g.callback_epochs[addr].me.Me?
      //   && v'.g.callback_epochs[addr].me.val == val
      // ))
      // ensures (forall val | InFlightOnWritebackRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.Some?
      //   && v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   && var wval := if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval;
      //   && wval == val
      // ))
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert MorphAddrIsInL2CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert addr.morphType.idx < |v'.tiles|;
          if MorphAddrIsInL2CacheEntry(c, v', addr) {
            L3StepNoNewEngineResponses(c, v, v', step);
            MorphAddrIsInL2CacheEntryIsHeldConstant(c, v, v', step, NoOp, addr);
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert MorphAddrIsInL3CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert c.addr_map(addr) < |v'.tiles|;
          if MorphAddrIsInL3CacheEntry(c, v', addr) {
            assert MorphAddrIsInL3CacheEntry(c, v, addr) by {
              reveal MorphAddrIsInL3CacheEntry;
              var c_idx: nat :| (NonEmptyL3CacheEntry(c, v', c.addr_map(addr), c_idx)
                && v'.tiles[c.addr_map(addr)].l3.cache[c_idx].addr == addr
                && (v'.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB? ==> InFlightOnMissResponse(c, v', addr, c_idx)));
              assert NonEmptyL3CacheEntry(c, v, c.addr_map(addr), c_idx);
              assert v.tiles[c.addr_map(addr)].l3.cache[c_idx].addr == addr;
              if v.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB? {
                if v'.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB? {
                  assert InFlightOnMissResponse(c, v, addr, c_idx) by {
                    reveal InFlightOnMissResponse;
                    assert InFlightOnMissResponse(c, v', addr, c_idx);
                    var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
                    assert InFlightEngineResponse(c, v', msg);
                    assert InFlightEngineResponse(c, v, msg);
                    assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
                  }
                } else {
                  assert !v'.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB?;
                  assert step.tile_step.l3_step.ReceiveOnMissDataStep?;
                  var msg := step.msgOps.recv.val;
                  assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
                  assert InFlightOnMissResponse(c, v, addr, c_idx) by { reveal InFlightOnMissResponse; }
                }
              }
            }
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;

      // forall val | InFlightOnEvictRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.None?
      //   ensures v'.g.callback_epochs[addr].me.Me?
      //   ensures v'.g.callback_epochs[addr].me.val == val
      // {
      //   assert InFlightOnEvictRequest(c, v, addr, val) by {
      //     reveal InFlightOnEvictRequest;
      //     var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.None?;
      //   assert v'.g.callback_epochs[addr].wcb.None?;
      // }

      // forall val | InFlightOnWritebackRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.Some?
      //   ensures v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   ensures (
      //     (if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval)
      //     ==
      //     val
      //   )
      // {
      //   assert InFlightOnWritebackRequest(c, v, addr, val) by {
      //     reveal InFlightOnWritebackRequest;
      //     var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.Some?;
      //   assert v'.g.callback_epochs[addr].wcb.Some?;
      // }
    }
  }

  lemma L3RespMemoryNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    ensures NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || MorphAddrIsInL2CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || MorphAddrIsInL3CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
      // ensures (forall val | InFlightOnEvictRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.None?
      //   && v'.g.callback_epochs[addr].me.Me?
      //   && v'.g.callback_epochs[addr].me.val == val
      // ))
      // ensures (forall val | InFlightOnWritebackRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.Some?
      //   && v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   && var wval := if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval;
      //   && wval == val
      // ))
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert MorphAddrIsInL2CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert addr.morphType.idx < |v'.tiles|;
          if MorphAddrIsInL2CacheEntry(c, v', addr) {
            L3StepNoNewEngineResponses(c, v, v', step);
            MorphAddrIsInL2CacheEntryIsHeldConstant(c, v, v', step, NoOp, addr);
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert MorphAddrIsInL3CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert c.addr_map(addr) < |v'.tiles|;
          if MorphAddrIsInL3CacheEntry(c, v', addr) {
            assert MorphAddrIsInL3CacheEntry(c, v, addr) by {
              reveal MorphAddrIsInL3CacheEntry;
              var c_idx: nat :| (NonEmptyL3CacheEntry(c, v', c.addr_map(addr), c_idx)
                && v'.tiles[c.addr_map(addr)].l3.cache[c_idx].addr == addr
                && (v'.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB? ==> InFlightOnMissResponse(c, v', addr, c_idx)));
              assert NonEmptyL3CacheEntry(c, v, c.addr_map(addr), c_idx);
              assert v.tiles[c.addr_map(addr)].l3.cache[c_idx].addr == addr;
              if v.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB? {
                if v'.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB? {
                  assert InFlightOnMissResponse(c, v, addr, c_idx) by {
                    reveal InFlightOnMissResponse;
                    assert InFlightOnMissResponse(c, v', addr, c_idx);
                    var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
                    assert InFlightEngineResponse(c, v', msg);
                    assert InFlightEngineResponse(c, v, msg);
                    assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
                  }
                } else {
                  assert !v'.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB?;
                  assert step.tile_step.l3_step.ReceiveOnMissDataStep?;
                  var msg := step.msgOps.recv.val;
                  assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
                  assert InFlightOnMissResponse(c, v, addr, c_idx) by { reveal InFlightOnMissResponse; }
                }
              }
            }
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;

      // forall val | InFlightOnEvictRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.None?
      //   ensures v'.g.callback_epochs[addr].me.Me?
      //   ensures v'.g.callback_epochs[addr].me.val == val
      // {
      //   assert InFlightOnEvictRequest(c, v, addr, val) by {
      //     reveal InFlightOnEvictRequest;
      //     var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.None?;
      //   assert v'.g.callback_epochs[addr].wcb.None?;
      // }

      // forall val | InFlightOnWritebackRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.Some?
      //   ensures v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   ensures (
      //     (if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval)
      //     ==
      //     val
      //   )
      // {
      //   assert InFlightOnWritebackRequest(c, v, addr, val) by {
      //     reveal InFlightOnWritebackRequest;
      //     var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.Some?;
      //   assert v'.g.callback_epochs[addr].wcb.Some?;
      // }
    }
  }

  lemma L3ReceiveCoherenceMessageNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    ensures NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || MorphAddrIsInL2CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || MorphAddrIsInL3CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
      // ensures (forall val | InFlightOnEvictRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.None?
      //   && v'.g.callback_epochs[addr].me.Me?
      //   && v'.g.callback_epochs[addr].me.val == val
      // ))
      // ensures (forall val | InFlightOnWritebackRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.Some?
      //   && v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   && var wval := if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval;
      //   && wval == val
      // ))
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert MorphAddrIsInL2CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert addr.morphType.idx < |v'.tiles|;
          if MorphAddrIsInL2CacheEntry(c, v', addr) {
            L3StepNoNewEngineResponses(c, v, v', step);
            MorphAddrIsInL2CacheEntryIsHeldConstant(c, v, v', step, NoOp, addr);
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert MorphAddrIsInL3CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert c.addr_map(addr) < |v'.tiles|;
          if MorphAddrIsInL3CacheEntry(c, v', addr) {
            assert MorphAddrIsInL3CacheEntry(c, v, addr) by {
              reveal MorphAddrIsInL3CacheEntry;
              var c_idx: nat :| (NonEmptyL3CacheEntry(c, v', c.addr_map(addr), c_idx)
                && v'.tiles[c.addr_map(addr)].l3.cache[c_idx].addr == addr
                && (v'.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB? ==> InFlightOnMissResponse(c, v', addr, c_idx)));
              assert NonEmptyL3CacheEntry(c, v, c.addr_map(addr), c_idx);
              assert v.tiles[c.addr_map(addr)].l3.cache[c_idx].addr == addr;
              if v.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB? {
                if v'.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB? {
                  assert InFlightOnMissResponse(c, v, addr, c_idx) by {
                    reveal InFlightOnMissResponse;
                    assert InFlightOnMissResponse(c, v', addr, c_idx);
                    var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
                    assert InFlightEngineResponse(c, v', msg);
                    assert InFlightEngineResponse(c, v, msg);
                    assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
                  }
                } else {
                  assert !v'.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB?;
                  assert step.tile_step.l3_step.ReceiveOnMissDataStep?;
                  var msg := step.msgOps.recv.val;
                  assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
                  assert InFlightOnMissResponse(c, v, addr, c_idx) by { reveal InFlightOnMissResponse; }
                }
              }
            }
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;

      // forall val | InFlightOnEvictRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.None?
      //   ensures v'.g.callback_epochs[addr].me.Me?
      //   ensures v'.g.callback_epochs[addr].me.val == val
      // {
      //   assert InFlightOnEvictRequest(c, v, addr, val) by {
      //     reveal InFlightOnEvictRequest;
      //     var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.None?;
      //   assert v'.g.callback_epochs[addr].wcb.None?;
      // }

      // forall val | InFlightOnWritebackRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.Some?
      //   ensures v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   ensures (
      //     (if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval)
      //     ==
      //     val
      //   )
      // {
      //   assert InFlightOnWritebackRequest(c, v, addr, val) by {
      //     reveal InFlightOnWritebackRequest;
      //     var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      //   }
      //   assert v.g.callback_epochs[addr].wcb.Some?;
      //   assert v'.g.callback_epochs[addr].wcb.Some?;
      // }
    }
  }

  lemma L3ScheduleCallbackNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    // requires L3DirtyBitMatchesEpoch(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    ensures NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || MorphAddrIsInL2CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || MorphAddrIsInL3CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
      // ensures (forall val | InFlightOnEvictRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.None?
      //   && v'.g.callback_epochs[addr].me.Me?
      //   && v'.g.callback_epochs[addr].me.val == val
      // ))
      // ensures (forall val | InFlightOnWritebackRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.Some?
      //   && v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   && var wval := if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval;
      //   && wval == val
      // ))
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert MorphAddrIsInL2CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert addr.morphType.idx < |v'.tiles|;
          if MorphAddrIsInL2CacheEntry(c, v', addr) {
            L3StepNoNewEngineResponses(c, v, v', step);
            MorphAddrIsInL2CacheEntryIsHeldConstant(c, v, v', step, NoOp, addr);
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert MorphAddrIsInL3CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert c.addr_map(addr) < |v'.tiles|;
          if MorphAddrIsInL3CacheEntry(c, v', addr) {
            reveal MorphAddrIsInL3CacheEntry;
            var c_idx: nat :| (NonEmptyL3CacheEntry(c, v', c.addr_map(addr), c_idx)
              && v'.tiles[c.addr_map(addr)].l3.cache[c_idx].addr == addr
              && (v'.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB? ==> InFlightOnMissResponse(c, v', addr, c_idx)));
            if NonEmptyL3CacheEntry(c, v, c.addr_map(addr), c_idx) {
              assert v.tiles[c.addr_map(addr)].l3.cache[c_idx].addr == addr;
              if v.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB? {
                assert v'.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB?;
                assert InFlightOnMissResponse(c, v, addr, c_idx) by {
                  reveal InFlightOnMissResponse;
                  assert InFlightOnMissResponse(c, v', addr, c_idx);
                  var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
                  assert InFlightEngineResponse(c, v', msg);
                  assert InFlightEngineResponse(c, v, msg);
                  assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
                }
              }
            } else {
              // we scheduled an onmiss
              assert v'.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB?;
              assert InFlightOnMissResponse(c, v', addr, c_idx);
              assert InFlightOnMissResponse(c, v, addr, c_idx) by {
                reveal InFlightOnMissResponse;
                var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
                assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
              }
              assert OnMissInProgress(c, v, addr, c_idx);
              reveal L3PendingCallbackForAddr;
              assert false;
            }
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            reveal InFlightOnEvictRequestForAddr;
            var val :| InFlightOnEvictRequest(c, v', addr, val);
            reveal InFlightOnEvictRequest;
            var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
            if !IsInFlightOnEvictRequest(c, v, addr, idx, val) {
              assert MorphAddrIsInL3CacheEntry(c, v, addr) by {
                reveal MorphAddrIsInL3CacheEntry;
                assert NonEmptyL3CacheEntry(c, v, c.addr_map(addr), step.tile_step.l3_step.idx);
              }
            } else {
              assert InFlightOnEvictRequest(c, v, addr, val);
              assert InFlightOnEvictRequestForAddr(c, v, addr);
            }
          } else {
            reveal InFlightOnWritebackRequestForAddr;
            var val :| InFlightOnWritebackRequest(c, v', addr, val);
            reveal InFlightOnWritebackRequest;
            var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
            if !IsInFlightOnWritebackRequest(c, v, addr, idx, val) {
              assert MorphAddrIsInL3CacheEntry(c, v, addr) by {
                reveal MorphAddrIsInL3CacheEntry;
                assert NonEmptyL3CacheEntry(c, v, c.addr_map(addr), step.tile_step.l3_step.idx);
              }
            } else {
              assert InFlightOnWritebackRequest(c, v, addr, val);
              assert InFlightOnWritebackRequestForAddr(c, v, addr);
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;
      // forall val | InFlightOnEvictRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.None?
      //   ensures v'.g.callback_epochs[addr].me.Me?
      //   ensures v'.g.callback_epochs[addr].me.val == val
      // {
      //   reveal InFlightOnEvictRequest;
      //   var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
      //   if IsInFlightOnEvictRequest(c, v, addr, idx, val)  {
      //     assert InFlightOnEvictRequest(c, v, addr, val);
      //     assert v.g.callback_epochs[addr].wcb.None?;
      //     assert v'.g.callback_epochs[addr].wcb.None?;
      //   } else {
      //     assert step.tile_step.l3_step.eng_req.OnEvict?;
      //     assert CleanDirIL3CacheEntry(c, v, step.tile_idx, step.tile_step.l3_step.idx);
      //     // assume false;
      //     assert v'.g.callback_epochs[addr].wcb.None?;
      //   }
      // }

      // forall val | InFlightOnWritebackRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.Some?
      //   ensures v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   ensures (
      //     (if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval)
      //     ==
      //     val
      //   )
      // {
      //   reveal InFlightOnWritebackRequest;
      //   var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
      //   if InFlightOnWritebackRequest(c, v, addr, val) {
      //     assert InFlightOnWritebackRequest(c, v, addr, val);
      //     assert v.g.callback_epochs[addr].wcb.Some?;
      //     assert v'.g.callback_epochs[addr].wcb.Some?;
      //   } else {
      //     // TODO: no idea why this needs extra spelling out for proof when evict case was free
      //     assert !InFlightOnWritebackRequest(c, v, addr, val);
      //     var top := (if addr in v.network.inFlightEngReqs then |v.network.inFlightEngReqs[addr]| else 0);
      //     // forall idx': nat | idx < top
      //     //   ensures !IsInFlightOnWritebackRequest(c, v, addr, idx', val)
      //     // {}
      //     // assert addr in v'.network.inFlightEngReqs;
      //     var msg :| msg in step.msgOps.send;
      //     // assert |step.msgOps.send| == 1;
      //     assert addr == msg.meta.addr by {
      //       if addr != msg.meta.addr {
      //         assert addr in v.network.inFlightEngReqs;
      //         assert v.network.inFlightEngReqs[addr] == v'.network.inFlightEngReqs[addr];
      //         assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      //         assert false;
      //       }
      //     }
      //     assert idx == top by {
      //       if idx != top {
      //         if addr in v.network.inFlightEngReqs {
      //           assert idx < |v.network.inFlightEngReqs[addr]|;
      //           assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      //         }
      //         assert false;
      //       }
      //     }
      //     assert step.tile_step.l3_step.eng_req.OnWriteBack?;
      //     assert DirtyDirIL3CacheEntry(c, v, step.tile_idx, step.tile_step.l3_step.idx);
      //     assert v'.g.callback_epochs[addr].wcb.Some?;
      //   }
      // }
    }
  }

  lemma NoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    // requires L2DirtyBitMatchesEpoch(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    // requires L3DirtyBitMatchesEpoch(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    ensures NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v, v', step);
              }
              case CacheCommunicationStep(c_step,_,_,_) => {
                match c_step {
                  case GetSStep() => {
                    L2CacheCommunicationGetSNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v, v', step);
                  }
                  case GetMStep() => {
                    L2CacheCommunicationGetMNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v, v', step);
                  }
                  case EvictStep() => {
                    L2CacheCommunicationEvictNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v, v', step);
                  }
                  case RecvMsgStep() => {
                    L2CacheCommunicationRecvMsgNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v, v', step);
                  }
                }
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            match l3_step {
              case ScheduleCallbackStep(_,_,_) => {
                L3ScheduleCallbackNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L3ReceiveOnMissDataNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L3DirectoryNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v, v', step);
              }
              case ReqMemoryStep(_,_) => {
                L3ReqMemoryNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v, v', step);
              }
              case RespMemoryStep(_) => {
                L3RespMemoryNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L3ReceiveCoherenceMessageNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v, v', step);
              }
            }
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v, v', step);
          }
          case EngineStep(eng_step) => {
            if eng_step.ReceiveCallbackReqStep? {
              EngineReceiveCallbackReqNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v, v', step);
            } else {
              EngineNotReceiveCallbackReqNoOpPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v, v', step);
            }
          }
        }
      }
    }
  }

  lemma StartCBPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)

    requires IdxInCBOrderTrackerIffCallbackPresent(c, v)
    requires NoDupIdxsInCBOrderTracker(c, v)
    requires UniqueTileForCallbackAddr(c, v)
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)


    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)

    requires OnMissRequestOnlyCallbackOrResponse(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)

    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)

    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)

    requires L2AddressesUnique(c, v)
    requires L3AddressesUnique(c, v)

    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    ensures NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || MorphAddrIsInL2CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || MorphAddrIsInL3CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
      // ensures (forall val | InFlightOnEvictRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.None?
      //   && v'.g.callback_epochs[addr].me.Me?
      //   && v'.g.callback_epochs[addr].me.val == val
      // ))
      // ensures (forall val | InFlightOnWritebackRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.Some?
      //   && v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   && var wval := if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval;
      //   && wval == val
      // ))
    {
      var entry := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx];
      if entry.addr != addr {
        assert addr in v.g.callback_epochs;
        if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
          assert MorphAddrIsInL2CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
            assert addr.morphType.idx < |v'.tiles|;
            if MorphAddrIsInL2CacheEntry(c, v', addr) {
              EngineStepStartCBNoNewEngineResponses(c, v, v', step, re);
              MorphAddrIsInL2CacheEntryIsHeldConstant(c, v, v', step, re, addr);
            } else if InFlightOnEvictRequestForAddr(c, v', addr) {
              assert InFlightOnEvictRequestForAddr(c, v, addr) by {
                reveal InFlightOnEvictRequestForAddr;
                var val :| InFlightOnEvictRequest(c, v', addr, val);
                assert InFlightOnEvictRequest(c, v, addr, val) by {
                  reveal InFlightOnEvictRequest;
                  var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                  assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
                }
              }
            } else {
              assert InFlightOnWritebackRequestForAddr(c, v', addr);
              assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
                reveal InFlightOnWritebackRequestForAddr;
                var val :| InFlightOnWritebackRequest(c, v', addr, val);
                assert InFlightOnWritebackRequest(c, v, addr, val) by {
                  reveal InFlightOnWritebackRequest;
                  var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                  assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
                }
              }
            }
          }
        }

        if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
          assert MorphAddrIsInL3CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
            assert c.addr_map(addr) < |v'.tiles|;
            if MorphAddrIsInL3CacheEntry(c, v', addr) {
              EngineStepStartCBNoNewEngineResponses(c, v, v', step, re);
              MorphAddrIsInL3CacheEntryIsHeldConstant(c, v, v', step, re, addr);
            } else if InFlightOnEvictRequestForAddr(c, v', addr) {
              assert InFlightOnEvictRequestForAddr(c, v, addr) by {
                reveal InFlightOnEvictRequestForAddr;
                var val :| InFlightOnEvictRequest(c, v', addr, val);
                assert InFlightOnEvictRequest(c, v, addr, val) by {
                  reveal InFlightOnEvictRequest;
                  var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                  assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
                }
              }
            } else {
              assert InFlightOnWritebackRequestForAddr(c, v', addr);
              assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
                reveal InFlightOnWritebackRequestForAddr;
                var val :| InFlightOnWritebackRequest(c, v', addr, val);
                assert InFlightOnWritebackRequest(c, v, addr, val) by {
                  reveal InFlightOnWritebackRequest;
                  var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                  assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
                }
              }
            }
          }
        }
        assert v.g.callback_epochs[addr].In?;
        assert v'.g.callback_epochs[addr].In?;

        // forall val | InFlightOnEvictRequest(c, v', addr, val)
        //   ensures v'.g.callback_epochs[addr].wcb.None?
        //   ensures v'.g.callback_epochs[addr].me.Me?
        //   ensures v'.g.callback_epochs[addr].me.val == val
        // {
        //   assert InFlightOnEvictRequest(c, v, addr, val) by {
        //     reveal InFlightOnEvictRequest;
        //     var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        //     assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
        //   }
        //   assert v.g.callback_epochs[addr].wcb.None?;
        //   assert v'.g.callback_epochs[addr].wcb.None?;
        // }

        // forall val | InFlightOnWritebackRequest(c, v', addr, val)
        //   ensures v'.g.callback_epochs[addr].wcb.Some?
        //   ensures v'.g.callback_epochs[addr].wcb.val.CBWrite()
        //   ensures (
        //     (if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval)
        //     ==
        //     val
        //   )
        // {
        //   assert InFlightOnWritebackRequest(c, v, addr, val) by {
        //     reveal InFlightOnWritebackRequest;
        //     var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        //     assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
        //   }
        //   assert v.g.callback_epochs[addr].wcb.Some?;
        //   assert v'.g.callback_epochs[addr].wcb.Some?;
        // }
      } else {
        if PrivateMorph(addr) && MorphAddrIsInL2CacheEntry(c, v', addr) {
          assert false by {
            reveal MorphAddrIsInL2CacheEntry;
            var idx: nat :| NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx)
              && v'.tiles[addr.morphType.idx].l2.cache[idx].addr == addr
              && (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? ==> InFlightOnMissResponse(c, v', addr, idx));
            if v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? {
              assert InFlightOnMissResponse(c, v', addr, idx);
              assert InFlightOnMissResponse(c, v, addr, idx) by {
                reveal InFlightOnMissResponse;
                var msg :| IsInFlightOnMissResponse(c, v', addr, msg, idx);
                assert IsInFlightOnMissResponse(c, v, addr, msg, idx);
              }
              assert !entry.cb_type.OnEvict? by {
                if entry.cb_type.OnEvict? {
                  assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
                  assert CallbackPresent(c, v, addr, entry.cb_type) by { reveal CallbackPresent; }
                  assert OnEvictInProgress(c, v, addr, entry.cb_type.val);
                  assert false;
                }
              }
              assert !entry.cb_type.OnWriteBack? by {
                if entry.cb_type.OnWriteBack? {
                  assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
                  assert CallbackPresent(c, v, addr, entry.cb_type) by { reveal CallbackPresent; }
                  assert OnWritebackInProgress(c, v, addr, entry.cb_type.val);
                  assert false;
                }
              }
              assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
              assert CallbackPresent(c, v, addr, entry.cb_type) by { reveal CallbackPresent; }
              if entry.cb_type.idx != idx {
                assert OnMissInProgress(c, v, addr, entry.cb_type.idx);
                assert OnMissInProgress(c, v, addr, idx);
                reveal L2PendingCallbackForAddr;
                assert false;
              }
            } else {
              assert !v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB?;
              assert !entry.cb_type.OnEvict? by {
                if entry.cb_type.OnEvict? {
                  assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
                  assert CallbackPresent(c, v, addr, entry.cb_type) by { reveal CallbackPresent; }
                  assert OnEvictInProgress(c, v, addr, entry.cb_type.val);
                  assert false;
                }
              }
              assert !entry.cb_type.OnWriteBack? by {
                if entry.cb_type.OnWriteBack? {
                  assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
                  assert CallbackPresent(c, v, addr, entry.cb_type) by { reveal CallbackPresent; }
                  assert OnWritebackInProgress(c, v, addr, entry.cb_type.val);
                  assert false;
                }
              }
              assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
              assert CallbackPresent(c, v, addr, entry.cb_type) by { reveal CallbackPresent; }
              assert OnMissInProgress(c, v, addr, entry.cb_type.idx);
              reveal L2PendingCallbackForAddr;
              assert false;
            }
          }
        } else if SharedMorph(addr) && MorphAddrIsInL3CacheEntry(c, v', addr) {
          assert false by {
            reveal MorphAddrIsInL3CacheEntry;
            var idx: nat :| NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx)
              && v'.tiles[c.addr_map(addr)].l3.cache[idx].addr == addr
              && (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? ==> InFlightOnMissResponse(c, v', addr, idx));
            if v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? {
              assert InFlightOnMissResponse(c, v', addr, idx);
              assert InFlightOnMissResponse(c, v, addr, idx) by {
                reveal InFlightOnMissResponse;
                var msg :| IsInFlightOnMissResponse(c, v', addr, msg, idx);
                assert IsInFlightOnMissResponse(c, v, addr, msg, idx);
              }
              assert !entry.cb_type.OnEvict? by {
                if entry.cb_type.OnEvict? {
                  assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
                  assert CallbackPresent(c, v, addr, entry.cb_type) by { reveal CallbackPresent; }
                  assert OnEvictInProgress(c, v, addr, entry.cb_type.val);
                  assert false;
                }
              }
              assert !entry.cb_type.OnWriteBack? by {
                if entry.cb_type.OnWriteBack? {
                  assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
                  assert CallbackPresent(c, v, addr, entry.cb_type) by { reveal CallbackPresent; }
                  assert OnWritebackInProgress(c, v, addr, entry.cb_type.val);
                  assert false;
                }
              }
              assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
              assert CallbackPresent(c, v, addr, entry.cb_type) by { reveal CallbackPresent; }
              if entry.cb_type.idx != idx {
                assert OnMissInProgress(c, v, addr, entry.cb_type.idx);
                assert OnMissInProgress(c, v, addr, idx);
                reveal L3PendingCallbackForAddr;
                assert false;
              }
            } else {
              assert !v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB?;
              assert !entry.cb_type.OnEvict? by {
                if entry.cb_type.OnEvict? {
                  assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
                  assert CallbackPresent(c, v, addr, entry.cb_type) by { reveal CallbackPresent; }
                  assert OnEvictInProgress(c, v, addr, entry.cb_type.val);
                  assert false;
                }
              }
              assert !entry.cb_type.OnWriteBack? by {
                if entry.cb_type.OnWriteBack? {
                  assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
                  assert CallbackPresent(c, v, addr, entry.cb_type) by { reveal CallbackPresent; }
                  assert OnWritebackInProgress(c, v, addr, entry.cb_type.val);
                  assert false;
                }
              }
              assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
              assert CallbackPresent(c, v, addr, entry.cb_type) by { reveal CallbackPresent; }
              assert OnMissInProgress(c, v, addr, entry.cb_type.idx);
              reveal L3PendingCallbackForAddr;
              assert false;
            }
          }
        } else if InFlightOnEvictRequestForAddr(c, v', addr) {
          reveal InFlightOnEvictRequestForAddr;
          var val :| InFlightOnEvictRequest(c, v', addr, val);
          reveal InFlightOnEvictRequest;
          var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
          assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
          assert InFlightOnEvictRequest(c, v, addr, val);
          assert OnEvictInProgress(c, v, addr, val);
          assert InFlightEngineRequest(c, v, addr, idx);
          assert IsBufferEntry(c, v, step.tile_idx, step.tile_step.eng_step.idx);
          assert !entry.cb_type.OnEvict?;
          assert !entry.cb_type.OnWriteBack?;
          assert entry.cb_type.OnMiss?;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          assert CallbackPresent(c, v, addr, entry.cb_type) by { reveal CallbackPresent; }
          assert step.tile_step.eng_step.idx in v.tiles[step.tile_idx].engine.cb_order[addr];
          if step.tile_step.eng_step.idx == v.tiles[step.tile_idx].engine.cb_order[addr][0] {
            assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, entry.cb_type);
            assert false;
          } else {
            assert false;
          }
        } else {
          assert InFlightOnWritebackRequestForAddr(c, v', addr);
          reveal InFlightOnWritebackRequestForAddr;
          var val :| InFlightOnWritebackRequest(c, v', addr, val);
          reveal InFlightOnWritebackRequest;
          var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
          assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
          assert InFlightOnWritebackRequest(c, v, addr, val);
          assert OnWritebackInProgress(c, v, addr, val);
          assert InFlightEngineRequest(c, v, addr, idx);
          assert IsBufferEntry(c, v, step.tile_idx, step.tile_step.eng_step.idx);
          assert !entry.cb_type.OnEvict?;
          assert !entry.cb_type.OnWriteBack?;
          assert entry.cb_type.OnMiss?;
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
          assert CallbackPresent(c, v, addr, entry.cb_type) by { reveal CallbackPresent; }
          assert step.tile_step.eng_step.idx in v.tiles[step.tile_idx].engine.cb_order[addr];
          if step.tile_step.eng_step.idx == v.tiles[step.tile_idx].engine.cb_order[addr][0] {
            assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, entry.cb_type);
            assert false;
          } else {
            assert false;
          }
        }
      }
    }
  }


  lemma EndCBPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback

    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)


    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)

    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)

    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)

    requires InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    requires InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    ensures NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v')
  {

    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || MorphAddrIsInL2CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || MorphAddrIsInL3CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
      // ensures (forall val | InFlightOnEvictRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.None?
      //   && v'.g.callback_epochs[addr].me.Me?
      //   && v'.g.callback_epochs[addr].me.val == val
      // ))
      // ensures (forall val | InFlightOnWritebackRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.Some?
      //   && v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   && var wval := if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval;
      //   && wval == val
      // ))
    {
      var entry := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx];
      if entry.addr != addr {
        assert addr in v.g.callback_epochs;
        if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
          assert MorphAddrIsInL2CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
            assert addr.morphType.idx < |v'.tiles|;
            if MorphAddrIsInL2CacheEntry(c, v', addr) {
              assert MorphAddrIsInL2CacheEntry(c, v, addr) by {
                reveal MorphAddrIsInL2CacheEntry;
                var c_idx: nat :| (NonEmptyL2CacheEntry(c, v', addr.morphType.idx, c_idx)
                  && v'.tiles[addr.morphType.idx].l2.cache[c_idx].addr == addr
                  && (v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? ==> InFlightOnMissResponse(c, v', addr, c_idx)));
                assert NonEmptyL2CacheEntry(c, v, addr.morphType.idx, c_idx);
                assert v.tiles[addr.morphType.idx].l2.cache[c_idx].addr == addr;
                if v.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB? {
                  assert v'.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB?;
                  assert InFlightOnMissResponse(c, v, addr, c_idx) by {
                    reveal InFlightOnMissResponse;
                    assert InFlightOnMissResponse(c, v', addr, c_idx);
                    var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
                    assert InFlightEngineResponse(c, v', msg);
                    assert InFlightEngineResponse(c, v, msg);
                    assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
                  }
                }
              }
            } else if InFlightOnEvictRequestForAddr(c, v', addr) {
              assert InFlightOnEvictRequestForAddr(c, v, addr) by {
                reveal InFlightOnEvictRequestForAddr;
                var val :| InFlightOnEvictRequest(c, v', addr, val);
                assert InFlightOnEvictRequest(c, v, addr, val) by {
                  reveal InFlightOnEvictRequest;
                  var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                  assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
                }
              }
            } else {
              assert InFlightOnWritebackRequestForAddr(c, v', addr);
              assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
                reveal InFlightOnWritebackRequestForAddr;
                var val :| InFlightOnWritebackRequest(c, v', addr, val);
                assert InFlightOnWritebackRequest(c, v, addr, val) by {
                  reveal InFlightOnWritebackRequest;
                  var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                  assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
                }
              }
            }
          }
        }

        if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
          assert MorphAddrIsInL3CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
            assert c.addr_map(addr) < |v'.tiles|;
            if MorphAddrIsInL3CacheEntry(c, v', addr) {
              assert MorphAddrIsInL3CacheEntry(c, v, addr) by {
                reveal MorphAddrIsInL3CacheEntry;
                var c_idx: nat :| (NonEmptyL3CacheEntry(c, v', c.addr_map(addr), c_idx)
                  && v'.tiles[c.addr_map(addr)].l3.cache[c_idx].addr == addr
                  && (v'.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB? ==> InFlightOnMissResponse(c, v', addr, c_idx)));
                assert NonEmptyL3CacheEntry(c, v, c.addr_map(addr), c_idx);
                assert v.tiles[c.addr_map(addr)].l3.cache[c_idx].addr == addr;
                if v.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB? {
                  assert v'.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB?;
                  assert InFlightOnMissResponse(c, v, addr, c_idx) by {
                    reveal InFlightOnMissResponse;
                    assert InFlightOnMissResponse(c, v', addr, c_idx);
                    var msg :| IsInFlightOnMissResponse(c, v', addr, msg, c_idx);
                    assert InFlightEngineResponse(c, v', msg);
                    assert InFlightEngineResponse(c, v, msg);
                    assert IsInFlightOnMissResponse(c, v, addr, msg, c_idx);
                  }
                }
              }
            } else if InFlightOnEvictRequestForAddr(c, v', addr) {
              assert InFlightOnEvictRequestForAddr(c, v, addr) by {
                reveal InFlightOnEvictRequestForAddr;
                var val :| InFlightOnEvictRequest(c, v', addr, val);
                assert InFlightOnEvictRequest(c, v, addr, val) by {
                  reveal InFlightOnEvictRequest;
                  var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                  assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
                }
              }
            } else {
              assert InFlightOnWritebackRequestForAddr(c, v', addr);
              assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
                reveal InFlightOnWritebackRequestForAddr;
                var val :| InFlightOnWritebackRequest(c, v', addr, val);
                assert InFlightOnWritebackRequest(c, v, addr, val) by {
                  reveal InFlightOnWritebackRequest;
                  var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                  assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
                }
              }
            }
          }
        }

        assert v.g.callback_epochs[addr].In?;
        assert v'.g.callback_epochs[addr].In?;

        // forall val | InFlightOnEvictRequest(c, v', addr, val)
        //   ensures v'.g.callback_epochs[addr].wcb.None?
        //   ensures v'.g.callback_epochs[addr].me.Me?
        //   ensures v'.g.callback_epochs[addr].me.val == val
        // {
        //   assert InFlightOnEvictRequest(c, v, addr, val) by {
        //     reveal InFlightOnEvictRequest;
        //     var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
        //     assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
        //   }
        //   assert v.g.callback_epochs[addr].wcb.None?;
        //   assert v'.g.callback_epochs[addr].wcb.None?;
        // }

        // forall val | InFlightOnWritebackRequest(c, v', addr, val)
        //   ensures v'.g.callback_epochs[addr].wcb.Some?
        //   ensures v'.g.callback_epochs[addr].wcb.val.CBWrite()
        //   ensures (
        //     (if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval)
        //     ==
        //     val
        //   )
        // {
        //   assert InFlightOnWritebackRequest(c, v, addr, val) by {
        //     reveal InFlightOnWritebackRequest;
        //     var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
        //     assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
        //   }
        //   assert v.g.callback_epochs[addr].wcb.Some?;
        //   assert v'.g.callback_epochs[addr].wcb.Some?;
        // }
      } else {
        if PrivateMorph(addr) && MorphAddrIsInL2CacheEntry(c, v', addr) {
          forall val
            ensures !OnEvictInProgress(c, v, addr, val)
            ensures !OnWritebackInProgress(c, v, addr, val)
          {
            reveal MorphAddrIsInL2CacheEntry;
            var idx: nat :| NonEmptyL2CacheEntry(c, v', addr.morphType.idx, idx)
              && v'.tiles[addr.morphType.idx].l2.cache[idx].addr == addr
              && (v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? ==> InFlightOnMissResponse(c, v', addr, idx));
            if v'.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? {
              assert InFlightOnMissResponse(c, v', addr, idx);
              assert InFlightOnMissResponse(c, v, addr, idx) || CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(idx)) by {
                reveal InFlightOnMissResponse;
                var msg :| IsInFlightOnMissResponse(c, v', addr, msg, idx);
                if !IsInFlightOnMissResponse(c, v, addr, msg, idx) {
                  assert msg in step.msgOps.send;
                  assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(idx));
                }
              }
              assert !OnEvictInProgress(c, v, addr, val);
              assert !OnWritebackInProgress(c, v, addr, val);
            } else {
              assert !v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB?;
              assert !OnEvictInProgress(c, v, addr, val);
              assert !OnWritebackInProgress(c, v, addr, val);
            }
          }
          assert !entry.cb_type.OnEvict? by {
            if entry.cb_type.OnEvict? {
              assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
              assert CallbackPresent(c, v, addr, entry.cb_type) by { reveal CallbackPresent; }
              assert OnEvictInProgress(c, v, addr, entry.cb_type.val);
              assert false;
            }
          }
          assert !entry.cb_type.OnWriteBack? by {
            if entry.cb_type.OnWriteBack? {
              assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
              assert CallbackPresent(c, v, addr, entry.cb_type) by { reveal CallbackPresent; }
              assert OnWritebackInProgress(c, v, addr, entry.cb_type.val);
              assert false;
            }
          }
          assert re == EndOnMiss;
          forall val
            ensures !InFlightOnEvictRequest(c, v', addr, val)
          {
            if InFlightOnEvictRequest(c, v', addr, val) {
              reveal InFlightOnEvictRequest;
              var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
              assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              assert InFlightOnEvictRequest(c, v, addr, val);
              assert OnEvictInProgress(c, v, addr, val);
              assert false;
            }
          }
          forall val
            ensures !InFlightOnWritebackRequest(c, v', addr, val)
          {
            if InFlightOnWritebackRequest(c, v', addr, val) {
              reveal InFlightOnWritebackRequest;
              var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
              assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              assert InFlightOnWritebackRequest(c, v, addr, val);
              assert OnWritebackInProgress(c, v, addr, val);
              assert false;
            }
          }
        } else if SharedMorph(addr) && MorphAddrIsInL3CacheEntry(c, v', addr) {
          forall val
            ensures !OnEvictInProgress(c, v, addr, val)
            ensures !OnWritebackInProgress(c, v, addr, val)
          {
            reveal MorphAddrIsInL3CacheEntry;
            var idx: nat :| NonEmptyL3CacheEntry(c, v', c.addr_map(addr), idx)
              && v'.tiles[c.addr_map(addr)].l3.cache[idx].addr == addr
              && (v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? ==> InFlightOnMissResponse(c, v', addr, idx));
            if v'.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? {
              assert InFlightOnMissResponse(c, v', addr, idx);
              assert InFlightOnMissResponse(c, v, addr, idx) || CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(idx)) by {
                reveal InFlightOnMissResponse;
                var msg :| IsInFlightOnMissResponse(c, v', addr, msg, idx);
                if !IsInFlightOnMissResponse(c, v, addr, msg, idx) {
                  assert msg in step.msgOps.send;
                  assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(idx));
                }
              }
              assert !OnEvictInProgress(c, v, addr, val);
              assert !OnWritebackInProgress(c, v, addr, val);
            } else {
              assert !v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB?;
              assert !OnEvictInProgress(c, v, addr, val);
              assert !OnWritebackInProgress(c, v, addr, val);
            }
          }
          assert !entry.cb_type.OnEvict? by {
            if entry.cb_type.OnEvict? {
              assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
              assert CallbackPresent(c, v, addr, entry.cb_type) by { reveal CallbackPresent; }
              assert OnEvictInProgress(c, v, addr, entry.cb_type.val);
              assert false;
            }
          }
          assert !entry.cb_type.OnWriteBack? by {
            if entry.cb_type.OnWriteBack? {
              assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
              assert CallbackPresent(c, v, addr, entry.cb_type) by { reveal CallbackPresent; }
              assert OnWritebackInProgress(c, v, addr, entry.cb_type.val);
              assert false;
            }
          }
          assert re == EndOnMiss;
          forall val
            ensures !InFlightOnEvictRequest(c, v', addr, val)
          {
            if InFlightOnEvictRequest(c, v', addr, val) {
              reveal InFlightOnEvictRequest;
              var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
              assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              assert InFlightOnEvictRequest(c, v, addr, val);
              assert OnEvictInProgress(c, v, addr, val);
              assert false;
            }
          }
          forall val
            ensures !InFlightOnWritebackRequest(c, v', addr, val)
          {
            if InFlightOnWritebackRequest(c, v', addr, val) {
              reveal InFlightOnWritebackRequest;
              var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
              assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              assert InFlightOnWritebackRequest(c, v, addr, val);
              assert OnWritebackInProgress(c, v, addr, val);
              assert false;
            }
          }
        } else if InFlightOnEvictRequestForAddr(c, v', addr) {
          reveal InFlightOnEvictRequestForAddr;
          var val :| InFlightOnEvictRequest(c, v', addr, val);
          reveal InFlightOnEvictRequest;
          var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
          assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
          assert InFlightOnEvictRequest(c, v, addr, val);
          assert OnEvictInProgress(c, v, addr, val);
          assert InFlightEngineRequest(c, v, addr, idx);
          assert IsBufferEntry(c, v, step.tile_idx, step.tile_step.eng_step.idx);
          assert !entry.cb_type.OnEvict?;
          assert !entry.cb_type.OnWriteBack?;
          assert entry.cb_type.OnMiss?;
          assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, entry.cb_type);
          assert false;
        } else {
          assert InFlightOnWritebackRequestForAddr(c, v', addr);
          reveal InFlightOnWritebackRequestForAddr;
          var val :| InFlightOnWritebackRequest(c, v', addr, val);
          reveal InFlightOnWritebackRequest;
          var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
          assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
          assert InFlightOnWritebackRequest(c, v, addr, val);
          assert OnWritebackInProgress(c, v, addr, val);
          assert InFlightEngineRequest(c, v, addr, idx);
          assert IsBufferEntry(c, v, step.tile_idx, step.tile_step.eng_step.idx);
          assert !entry.cb_type.OnEvict?;
          assert !entry.cb_type.OnWriteBack?;
          assert entry.cb_type.OnMiss?;
          assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, entry.cb_type);
          assert false;
        }
      }
    }
  }

  lemma PerformNextInstPreservesNoOnMissInEngineAndInFlightEvictionMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    requires ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)

    // requires OnEvictInProgressMeansNoLoadableInCore(c, v)
    // requires OnEvictInProgressMeansNoLoadableInEngine(c, v)
    // requires OnWritebackInProgressMeansNoLoadableInCore(c, v)
    // requires OnWritebackInProgressMeansNoLoadableInEngine(c, v)

    ensures NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || MorphAddrIsInL2CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || MorphAddrIsInL3CacheEntry(c, v', addr)
        || InFlightOnEvictRequestForAddr(c, v', addr)
        || InFlightOnWritebackRequestForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
      // ensures (forall val | InFlightOnEvictRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.None?
      //   && v'.g.callback_epochs[addr].me.Me?
      //   && v'.g.callback_epochs[addr].me.val == val
      // ))
      // ensures (forall val | InFlightOnWritebackRequest(c, v', addr, val) :: (
      //   && v'.g.callback_epochs[addr].wcb.Some?
      //   && v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   && var wval := if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval;
      //   && wval == val
      // ))
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert MorphAddrIsInL2CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert addr.morphType.idx < |v'.tiles|;
          if MorphAddrIsInL2CacheEntry(c, v', addr) {
            PerfInstNoNewEngineResponses(c, v, v', step, re);
            MorphAddrIsInL2CacheEntryIsHeldConstant(c, v, v', step, re, addr);
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert MorphAddrIsInL3CacheEntry(c, v, addr) || InFlightOnEvictRequestForAddr(c, v, addr) || InFlightOnWritebackRequestForAddr(c, v, addr) by {
          assert c.addr_map(addr) < |v'.tiles|;
          if MorphAddrIsInL3CacheEntry(c, v', addr) {
            PerfInstNoNewEngineResponses(c, v, v', step, re);
            MorphAddrIsInL3CacheEntryIsHeldConstant(c, v, v', step, re, addr);
          } else if InFlightOnEvictRequestForAddr(c, v', addr) {
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
              var val :| InFlightOnEvictRequest(c, v', addr, val);
              assert InFlightOnEvictRequest(c, v, addr, val) by {
                reveal InFlightOnEvictRequest;
                var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
                assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
              }
            }
          } else {
            assert InFlightOnWritebackRequestForAddr(c, v', addr);
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
              var val :| InFlightOnWritebackRequest(c, v', addr, val);
              assert InFlightOnWritebackRequest(c, v, addr, val) by {
                reveal InFlightOnWritebackRequest;
                var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
                assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
              }
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;

      // forall val | InFlightOnEvictRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.None?
      //   ensures v'.g.callback_epochs[addr].me.Me?
      //   ensures v'.g.callback_epochs[addr].me.val == val
      // {
      //   assert InFlightOnEvictRequest(c, v, addr, val) by {
      //     reveal InFlightOnEvictRequest;
      //     var idx: nat :| IsInFlightOnEvictRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnEvictRequest(c, v, addr, idx, val);
      //   }
      //   assert OnEvictInProgress(c, v, addr, val);
      // }

      // forall val | InFlightOnWritebackRequest(c, v', addr, val)
      //   ensures v'.g.callback_epochs[addr].wcb.Some?
      //   ensures v'.g.callback_epochs[addr].wcb.val.CBWrite()
      //   ensures (
      //     (if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval)
      //     ==
      //     val
      //   )
      // {
      //   assert InFlightOnWritebackRequest(c, v, addr, val) by {
      //     reveal InFlightOnWritebackRequest;
      //     var idx: nat :| IsInFlightOnWritebackRequest(c, v', addr, idx, val);
      //     assert IsInFlightOnWritebackRequest(c, v, addr, idx, val);
      //   }
      //   assert OnWritebackInProgress(c, v, addr, val);
      // }
    }
  }

  lemma CoreNoOpPreservesUnstartedEvictionInEngineMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires step.tile_step.core_step.CacheCommunicationStep?
    requires UnstartedEvictionInEngineMeansInEpoch(c, v)
    ensures UnstartedEvictionInEngineMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || UnstartedOnEvictEntryForAddr(c, v', addr)
        || UnstartedOnWritebackEntryForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || UnstartedOnEvictEntryForAddr(c, v', addr)
        || UnstartedOnWritebackEntryForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert UnstartedOnEvictEntryForAddr(c, v, addr) || UnstartedOnWritebackEntryForAddr(c, v, addr) by {
          assert addr.morphType.idx < |v'.tiles|;
          if UnstartedOnEvictEntryForAddr(c, v', addr) {
            assert UnstartedOnEvictEntryForAddr(c, v, addr) by {
              reveal UnstartedOnEvictEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
              var e := EngineRequest.OnEvict(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          } else {
            assert UnstartedOnWritebackEntryForAddr(c, v', addr);
            assert UnstartedOnWritebackEntryForAddr(c, v, addr) by {
              reveal UnstartedOnWritebackEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
              var e := EngineRequest.OnWriteBack(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert UnstartedOnEvictEntryForAddr(c, v, addr) || UnstartedOnWritebackEntryForAddr(c, v, addr) by {
          assert c.addr_map(addr) < |v'.tiles|;
          if UnstartedOnEvictEntryForAddr(c, v', addr) {
            assert UnstartedOnEvictEntryForAddr(c, v, addr) by {
              reveal UnstartedOnEvictEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
              var e := EngineRequest.OnEvict(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          } else {
            assert UnstartedOnWritebackEntryForAddr(c, v', addr);
            assert UnstartedOnWritebackEntryForAddr(c, v, addr) by {
              reveal UnstartedOnWritebackEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
              var e := EngineRequest.OnWriteBack(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;
    }
  }

  lemma ProxyNoOpPreservesUnstartedEvictionInEngineMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires UnstartedEvictionInEngineMeansInEpoch(c, v)
    ensures UnstartedEvictionInEngineMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || UnstartedOnEvictEntryForAddr(c, v', addr)
        || UnstartedOnWritebackEntryForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || UnstartedOnEvictEntryForAddr(c, v', addr)
        || UnstartedOnWritebackEntryForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert UnstartedOnEvictEntryForAddr(c, v, addr) || UnstartedOnWritebackEntryForAddr(c, v, addr) by {
          assert addr.morphType.idx < |v'.tiles|;
          if UnstartedOnEvictEntryForAddr(c, v', addr) {
            assert UnstartedOnEvictEntryForAddr(c, v, addr) by {
              reveal UnstartedOnEvictEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
              var e := EngineRequest.OnEvict(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          } else {
            assert UnstartedOnWritebackEntryForAddr(c, v', addr);
            assert UnstartedOnWritebackEntryForAddr(c, v, addr) by {
              reveal UnstartedOnWritebackEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
              var e := EngineRequest.OnWriteBack(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert UnstartedOnEvictEntryForAddr(c, v, addr) || UnstartedOnWritebackEntryForAddr(c, v, addr) by {
          assert c.addr_map(addr) < |v'.tiles|;
          if UnstartedOnEvictEntryForAddr(c, v', addr) {
            assert UnstartedOnEvictEntryForAddr(c, v, addr) by {
              reveal UnstartedOnEvictEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
              var e := EngineRequest.OnEvict(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          } else {
            assert UnstartedOnWritebackEntryForAddr(c, v', addr);
            assert UnstartedOnWritebackEntryForAddr(c, v, addr) by {
              reveal UnstartedOnWritebackEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
              var e := EngineRequest.OnWriteBack(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;
    }
  }

  lemma MemoryNoOpPreservesUnstartedEvictionInEngineMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires UnstartedEvictionInEngineMeansInEpoch(c, v)
    ensures UnstartedEvictionInEngineMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || UnstartedOnEvictEntryForAddr(c, v', addr)
        || UnstartedOnWritebackEntryForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || UnstartedOnEvictEntryForAddr(c, v', addr)
        || UnstartedOnWritebackEntryForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert UnstartedOnEvictEntryForAddr(c, v, addr) || UnstartedOnWritebackEntryForAddr(c, v, addr) by {
          assert addr.morphType.idx < |v'.tiles|;
          if UnstartedOnEvictEntryForAddr(c, v', addr) {
            assert UnstartedOnEvictEntryForAddr(c, v, addr) by {
              reveal UnstartedOnEvictEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
              var e := EngineRequest.OnEvict(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          } else {
            assert UnstartedOnWritebackEntryForAddr(c, v', addr);
            assert UnstartedOnWritebackEntryForAddr(c, v, addr) by {
              reveal UnstartedOnWritebackEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
              var e := EngineRequest.OnWriteBack(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert UnstartedOnEvictEntryForAddr(c, v, addr) || UnstartedOnWritebackEntryForAddr(c, v, addr) by {
          assert c.addr_map(addr) < |v'.tiles|;
          if UnstartedOnEvictEntryForAddr(c, v', addr) {
            assert UnstartedOnEvictEntryForAddr(c, v, addr) by {
              reveal UnstartedOnEvictEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
              var e := EngineRequest.OnEvict(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          } else {
            assert UnstartedOnWritebackEntryForAddr(c, v', addr);
            assert UnstartedOnWritebackEntryForAddr(c, v, addr) by {
              reveal UnstartedOnWritebackEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
              var e := EngineRequest.OnWriteBack(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;
    }
  }

  lemma EngineCacheCommunicationNoOpPreservesUnstartedEvictionInEngineMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires UnstartedEvictionInEngineMeansInEpoch(c, v)
    ensures UnstartedEvictionInEngineMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || UnstartedOnEvictEntryForAddr(c, v', addr)
        || UnstartedOnWritebackEntryForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || UnstartedOnEvictEntryForAddr(c, v', addr)
        || UnstartedOnWritebackEntryForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert UnstartedOnEvictEntryForAddr(c, v, addr) || UnstartedOnWritebackEntryForAddr(c, v, addr) by {
          assert addr.morphType.idx < |v'.tiles|;
          if UnstartedOnEvictEntryForAddr(c, v', addr) {
            assert UnstartedOnEvictEntryForAddr(c, v, addr) by {
              reveal UnstartedOnEvictEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
              var e := EngineRequest.OnEvict(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          } else {
            assert UnstartedOnWritebackEntryForAddr(c, v', addr);
            assert UnstartedOnWritebackEntryForAddr(c, v, addr) by {
              reveal UnstartedOnWritebackEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
              var e := EngineRequest.OnWriteBack(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert UnstartedOnEvictEntryForAddr(c, v, addr) || UnstartedOnWritebackEntryForAddr(c, v, addr) by {
          assert c.addr_map(addr) < |v'.tiles|;
          if UnstartedOnEvictEntryForAddr(c, v', addr) {
            assert UnstartedOnEvictEntryForAddr(c, v, addr) by {
              reveal UnstartedOnEvictEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
              var e := EngineRequest.OnEvict(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          } else {
            assert UnstartedOnWritebackEntryForAddr(c, v', addr);
            assert UnstartedOnWritebackEntryForAddr(c, v, addr) by {
              reveal UnstartedOnWritebackEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
              var e := EngineRequest.OnWriteBack(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;
    }
  }

  lemma EngineReceiveCallbackReqNoOpPreservesUnstartedEvictionInEngineMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    requires UnstartedEvictionInEngineMeansInEpoch(c, v)
    ensures UnstartedEvictionInEngineMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || UnstartedOnEvictEntryForAddr(c, v', addr)
        || UnstartedOnWritebackEntryForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || UnstartedOnEvictEntryForAddr(c, v', addr)
        || UnstartedOnWritebackEntryForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert addr.morphType.idx < |v'.tiles|;
        if !UnstartedOnEvictEntryForAddr(c, v, addr) && !UnstartedOnWritebackEntryForAddr(c, v, addr) {
          if UnstartedOnEvictEntryForAddr(c, v', addr) {
            reveal UnstartedOnEvictEntryForAddr;
            reveal UnstartedCallbackPresent;
            assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx)
              && v'.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type == step.msgOps.recv.val.engine_req
              && !v'.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].started;
            assert IsInFlightOnEvictRequest(c, v, addr, 0, step.msgOps.recv.val.engine_req.val);
            assert InFlightOnEvictRequest(c, v, addr, step.msgOps.recv.val.engine_req.val) by {
              reveal InFlightOnEvictRequest;
            }
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
            }
          } else {
            assert UnstartedOnWritebackEntryForAddr(c, v', addr);
            reveal UnstartedOnWritebackEntryForAddr;
            reveal UnstartedCallbackPresent;
            assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx)
              && v'.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type == step.msgOps.recv.val.engine_req
              && !v'.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].started;
            assert IsInFlightOnWritebackRequest(c, v, addr, 0, step.msgOps.recv.val.engine_req.val);
            assert InFlightOnWritebackRequest(c, v, addr, step.msgOps.recv.val.engine_req.val) by {
              reveal InFlightOnWritebackRequest;
            }
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert c.addr_map(addr) < |v'.tiles|;
        if !UnstartedOnEvictEntryForAddr(c, v, addr) && !UnstartedOnWritebackEntryForAddr(c, v, addr) {
          if UnstartedOnEvictEntryForAddr(c, v', addr) {
            reveal UnstartedOnEvictEntryForAddr;
            reveal UnstartedCallbackPresent;
            assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx)
              && v'.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type == step.msgOps.recv.val.engine_req
              && !v'.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].started;
            assert IsInFlightOnEvictRequest(c, v, addr, 0, step.msgOps.recv.val.engine_req.val);
            assert InFlightOnEvictRequest(c, v, addr, step.msgOps.recv.val.engine_req.val) by {
              reveal InFlightOnEvictRequest;
            }
            assert InFlightOnEvictRequestForAddr(c, v, addr) by {
              reveal InFlightOnEvictRequestForAddr;
            }
          } else {
            assert UnstartedOnWritebackEntryForAddr(c, v', addr);
            reveal UnstartedOnWritebackEntryForAddr;
            reveal UnstartedCallbackPresent;
            assert CallbackPresentInBufferLocation(c, v', addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx)
              && v'.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type == step.msgOps.recv.val.engine_req
              && !v'.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].started;
            assert IsInFlightOnWritebackRequest(c, v, addr, 0, step.msgOps.recv.val.engine_req.val);
            assert InFlightOnWritebackRequest(c, v, addr, step.msgOps.recv.val.engine_req.val) by {
              reveal InFlightOnWritebackRequest;
            }
            assert InFlightOnWritebackRequestForAddr(c, v, addr) by {
              reveal InFlightOnWritebackRequestForAddr;
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;
    }
  }

  lemma L2NoOpPreservesUnstartedEvictionInEngineMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires UnstartedEvictionInEngineMeansInEpoch(c, v)
    ensures UnstartedEvictionInEngineMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || UnstartedOnEvictEntryForAddr(c, v', addr)
        || UnstartedOnWritebackEntryForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || UnstartedOnEvictEntryForAddr(c, v', addr)
        || UnstartedOnWritebackEntryForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert UnstartedOnEvictEntryForAddr(c, v, addr) || UnstartedOnWritebackEntryForAddr(c, v, addr) by {
          assert addr.morphType.idx < |v'.tiles|;
          if UnstartedOnEvictEntryForAddr(c, v', addr) {
            assert UnstartedOnEvictEntryForAddr(c, v, addr) by {
              reveal UnstartedOnEvictEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
              var e := EngineRequest.OnEvict(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          } else {
            assert UnstartedOnWritebackEntryForAddr(c, v', addr);
            assert UnstartedOnWritebackEntryForAddr(c, v, addr) by {
              reveal UnstartedOnWritebackEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
              var e := EngineRequest.OnWriteBack(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert UnstartedOnEvictEntryForAddr(c, v, addr) || UnstartedOnWritebackEntryForAddr(c, v, addr) by {
          assert c.addr_map(addr) < |v'.tiles|;
          if UnstartedOnEvictEntryForAddr(c, v', addr) {
            assert UnstartedOnEvictEntryForAddr(c, v, addr) by {
              reveal UnstartedOnEvictEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
              var e := EngineRequest.OnEvict(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          } else {
            assert UnstartedOnWritebackEntryForAddr(c, v', addr);
            assert UnstartedOnWritebackEntryForAddr(c, v, addr) by {
              reveal UnstartedOnWritebackEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
              var e := EngineRequest.OnWriteBack(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;
    }
  }
  
  lemma L3NoOpPreservesUnstartedEvictionInEngineMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires UnstartedEvictionInEngineMeansInEpoch(c, v)
    ensures UnstartedEvictionInEngineMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || UnstartedOnEvictEntryForAddr(c, v', addr)
        || UnstartedOnWritebackEntryForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || UnstartedOnEvictEntryForAddr(c, v', addr)
        || UnstartedOnWritebackEntryForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert UnstartedOnEvictEntryForAddr(c, v, addr) || UnstartedOnWritebackEntryForAddr(c, v, addr) by {
          assert addr.morphType.idx < |v'.tiles|;
          if UnstartedOnEvictEntryForAddr(c, v', addr) {
            assert UnstartedOnEvictEntryForAddr(c, v, addr) by {
              reveal UnstartedOnEvictEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
              var e := EngineRequest.OnEvict(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          } else {
            assert UnstartedOnWritebackEntryForAddr(c, v', addr);
            assert UnstartedOnWritebackEntryForAddr(c, v, addr) by {
              reveal UnstartedOnWritebackEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
              var e := EngineRequest.OnWriteBack(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert UnstartedOnEvictEntryForAddr(c, v, addr) || UnstartedOnWritebackEntryForAddr(c, v, addr) by {
          assert c.addr_map(addr) < |v'.tiles|;
          if UnstartedOnEvictEntryForAddr(c, v', addr) {
            assert UnstartedOnEvictEntryForAddr(c, v, addr) by {
              reveal UnstartedOnEvictEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
              var e := EngineRequest.OnEvict(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          } else {
            assert UnstartedOnWritebackEntryForAddr(c, v', addr);
            assert UnstartedOnWritebackEntryForAddr(c, v, addr) by {
              reveal UnstartedOnWritebackEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
              var e := EngineRequest.OnWriteBack(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;
    }
  }

  lemma NoOpPreservesUnstartedEvictionInEngineMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    requires UnstartedEvictionInEngineMeansInEpoch(c, v)
    ensures UnstartedEvictionInEngineMeansInEpoch(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesUnstartedEvictionInEngineMeansInEpoch(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesUnstartedEvictionInEngineMeansInEpoch(c, v, v', step);
          }
          case L2Step(l2_step) => {
            L2NoOpPreservesUnstartedEvictionInEngineMeansInEpoch(c, v, v', step);
          }
          case L3Step(l3_step) => {
            L3NoOpPreservesUnstartedEvictionInEngineMeansInEpoch(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesUnstartedEvictionInEngineMeansInEpoch(c, v, v', step);
          }
          case EngineStep(eng_step) => {
            if eng_step.ReceiveCallbackReqStep? {
              EngineReceiveCallbackReqNoOpPreservesUnstartedEvictionInEngineMeansInEpoch(c, v, v', step);
            } else {
              EngineCacheCommunicationNoOpPreservesUnstartedEvictionInEngineMeansInEpoch(c, v, v', step);
            }
          }
        }
      }
    }
  }
  
  lemma StartEndCBPreservesUnstartedEvictionInEngineMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires UniqueTileForCallbackAddr(c, v)
    requires CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    requires CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)
    requires UnstartedEvictionInEngineMeansInEpoch(c, v)
    ensures UnstartedEvictionInEngineMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || UnstartedOnEvictEntryForAddr(c, v', addr)
        || UnstartedOnWritebackEntryForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || UnstartedOnEvictEntryForAddr(c, v', addr)
        || UnstartedOnWritebackEntryForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
    {
      var entry := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx];
      if entry.addr != addr {
        assert addr in v.g.callback_epochs;
        if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
          assert UnstartedOnEvictEntryForAddr(c, v, addr) || UnstartedOnWritebackEntryForAddr(c, v, addr) by {
            assert addr.morphType.idx < |v'.tiles|;
            if UnstartedOnEvictEntryForAddr(c, v', addr) {
              assert UnstartedOnEvictEntryForAddr(c, v, addr) by {
                reveal UnstartedOnEvictEntryForAddr;
                var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
                var e := EngineRequest.OnEvict(val);
                assert UnstartedCallbackPresent(c, v, addr, e) by {
                  reveal UnstartedCallbackPresent;
                  var tile: nat, buf: nat :| (
                    && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                    && v'.tiles[tile].engine.buffer[buf].cb_type == e
                    && !v'.tiles[tile].engine.buffer[buf].started
                  );
                  assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
                }
              }
            } else {
              assert UnstartedOnWritebackEntryForAddr(c, v', addr);
              assert UnstartedOnWritebackEntryForAddr(c, v, addr) by {
                reveal UnstartedOnWritebackEntryForAddr;
                var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
                var e := EngineRequest.OnWriteBack(val);
                assert UnstartedCallbackPresent(c, v, addr, e) by {
                  reveal UnstartedCallbackPresent;
                  var tile: nat, buf: nat :| (
                    && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                    && v'.tiles[tile].engine.buffer[buf].cb_type == e
                    && !v'.tiles[tile].engine.buffer[buf].started
                  );
                  assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
                }
              }
            }
          }
        }

        if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
          assert UnstartedOnEvictEntryForAddr(c, v, addr) || UnstartedOnWritebackEntryForAddr(c, v, addr) by {
            assert c.addr_map(addr) < |v'.tiles|;
            if UnstartedOnEvictEntryForAddr(c, v', addr) {
              assert UnstartedOnEvictEntryForAddr(c, v, addr) by {
                reveal UnstartedOnEvictEntryForAddr;
                var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
                var e := EngineRequest.OnEvict(val);
                assert UnstartedCallbackPresent(c, v, addr, e) by {
                  reveal UnstartedCallbackPresent;
                  var tile: nat, buf: nat :| (
                    && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                    && v'.tiles[tile].engine.buffer[buf].cb_type == e
                    && !v'.tiles[tile].engine.buffer[buf].started
                  );
                  assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
                }
              }
            } else {
              assert UnstartedOnWritebackEntryForAddr(c, v', addr);
              assert UnstartedOnWritebackEntryForAddr(c, v, addr) by {
                reveal UnstartedOnWritebackEntryForAddr;
                var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
                var e := EngineRequest.OnWriteBack(val);
                assert UnstartedCallbackPresent(c, v, addr, e) by {
                  reveal UnstartedCallbackPresent;
                  var tile: nat, buf: nat :| (
                    && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                    && v'.tiles[tile].engine.buffer[buf].cb_type == e
                    && !v'.tiles[tile].engine.buffer[buf].started
                  );
                  assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
                }
              }
            }
          }
        }
        assert v.g.callback_epochs[addr].In?;
        assert v'.g.callback_epochs[addr].In?;
      } else {
        if re == StartOnMiss || re == EndOnMiss {
          assert CBOrderTrackerIndexIsRequest(c, v, addr, 0, entry.cb_type);
          forall val
            ensures !CallbackPresent(c, v, addr, EngineRequest.OnEvict(val))
            ensures !CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val))
          {
            
            assert !OnEvictInProgress(c, v, addr, val);
            assert !OnWritebackInProgress(c, v, addr, val);
          }
          reveal UnstartedOnEvictEntryForAddr;
          reveal UnstartedOnWritebackEntryForAddr;
          reveal UnstartedCallbackPresent;
          reveal CallbackPresent;
          assert false;
        } else if re == StartOnEvict || re == EndOnEvict {
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, step.tile_idx, step.tile_step.eng_step.idx);
          if UnstartedOnEvictEntryForAddr(c, v', addr) {
            reveal UnstartedOnEvictEntryForAddr;
            var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
            var e := EngineRequest.OnEvict(val);
            reveal UnstartedCallbackPresent;
            var tile: nat, buf: nat :| (
              && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
              && v'.tiles[tile].engine.buffer[buf].cb_type == e
              && !v'.tiles[tile].engine.buffer[buf].started
            );
            assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
            assert false;
          } else {
            assert UnstartedOnWritebackEntryForAddr(c, v', addr);
            reveal UnstartedOnWritebackEntryForAddr;
            var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
            var e := EngineRequest.OnWriteBack(val);
            reveal UnstartedCallbackPresent;
            var tile: nat, buf: nat :| (
              && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
              && v'.tiles[tile].engine.buffer[buf].cb_type == e
              && !v'.tiles[tile].engine.buffer[buf].started
            );
            assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
            assert false;
          }
        } else {
          assert re == StartOnWriteback || re == EndOnWriteback; 
          assert CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, step.tile_idx, step.tile_step.eng_step.idx);
          if UnstartedOnEvictEntryForAddr(c, v', addr) {
            reveal UnstartedOnEvictEntryForAddr;
            var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
            var e := EngineRequest.OnEvict(val);
            reveal UnstartedCallbackPresent;
            var tile: nat, buf: nat :| (
              && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
              && v'.tiles[tile].engine.buffer[buf].cb_type == e
              && !v'.tiles[tile].engine.buffer[buf].started
            );
            assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
            assert false;
          } else {
            assert UnstartedOnWritebackEntryForAddr(c, v', addr);
            reveal UnstartedOnWritebackEntryForAddr;
            var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
            var e := EngineRequest.OnWriteBack(val);
            reveal UnstartedCallbackPresent;
            var tile: nat, buf: nat :| (
              && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
              && v'.tiles[tile].engine.buffer[buf].cb_type == e
              && !v'.tiles[tile].engine.buffer[buf].started
            );
            assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
            assert false;
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesUnstartedEvictionInEngineMeansInEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires UnstartedEvictionInEngineMeansInEpoch(c, v)
    ensures UnstartedEvictionInEngineMeansInEpoch(c, v')
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v'.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v'.tiles| ==> (
        || UnstartedOnEvictEntryForAddr(c, v', addr)
        || UnstartedOnWritebackEntryForAddr(c, v', addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v'.tiles| ==> (
        || UnstartedOnEvictEntryForAddr(c, v', addr)
        || UnstartedOnWritebackEntryForAddr(c, v', addr)
      ))
    )
      ensures v'.g.callback_epochs[addr].In?
    {
      assert addr in v.g.callback_epochs;
      if PrivateMorph(addr) && addr.morphType.idx < |v.tiles| {
        assert UnstartedOnEvictEntryForAddr(c, v, addr) || UnstartedOnWritebackEntryForAddr(c, v, addr) by {
          assert addr.morphType.idx < |v'.tiles|;
          if UnstartedOnEvictEntryForAddr(c, v', addr) {
            assert UnstartedOnEvictEntryForAddr(c, v, addr) by {
              reveal UnstartedOnEvictEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
              var e := EngineRequest.OnEvict(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          } else {
            assert UnstartedOnWritebackEntryForAddr(c, v', addr);
            assert UnstartedOnWritebackEntryForAddr(c, v, addr) by {
              reveal UnstartedOnWritebackEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
              var e := EngineRequest.OnWriteBack(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          }
        }
      }

      if SharedMorph(addr) && c.addr_map(addr) < |v.tiles| {
        assert UnstartedOnEvictEntryForAddr(c, v, addr) || UnstartedOnWritebackEntryForAddr(c, v, addr) by {
          assert c.addr_map(addr) < |v'.tiles|;
          if UnstartedOnEvictEntryForAddr(c, v', addr) {
            assert UnstartedOnEvictEntryForAddr(c, v, addr) by {
              reveal UnstartedOnEvictEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnEvict(val));
              var e := EngineRequest.OnEvict(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          } else {
            assert UnstartedOnWritebackEntryForAddr(c, v', addr);
            assert UnstartedOnWritebackEntryForAddr(c, v, addr) by {
              reveal UnstartedOnWritebackEntryForAddr;
              var val :| UnstartedCallbackPresent(c, v', addr, EngineRequest.OnWriteBack(val));
              var e := EngineRequest.OnWriteBack(val);
              assert UnstartedCallbackPresent(c, v, addr, e) by {
                reveal UnstartedCallbackPresent;
                var tile: nat, buf: nat :| (
                  && CallbackPresentInBufferLocation(c, v', addr, EngReqToCBType(e), tile, buf)
                  && v'.tiles[tile].engine.buffer[buf].cb_type == e
                  && !v'.tiles[tile].engine.buffer[buf].started
                );
                assert CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf);
              }
            }
          }
        }
      }
      assert v.g.callback_epochs[addr].In?;
      assert v'.g.callback_epochs[addr].In?;
    }
  }
}