include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module DirtyBitMatchesEpochProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes
  import opened CacheTypes

  lemma NoOpPreservesL2DirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L2DirtyBitTracksInterveningWrite(c, v)
    requires PutMFromOwnerL2MeansInterveningWrite(c, v)
    requires DataFromOwnerL2MeansInterveningWrite(c, v)
    requires PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    requires DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v)
    requires L2QueueHeadsWellformed(c, v)                // :(
    requires OnMissResponseMeansInEpochWithNoWrite(c, v)
    requires PreMStateMeansNotDirtyL2(c, v)
    ensures L2DirtyBitTracksInterveningWrite(c, v')
  {
    if step.TileStep? && step.tile_step.L2Step? {
      forall core: nat, idx: nat | (
        && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
        && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
        && v'.tiles[core].l2.cache[idx].coh.Loadable()
      )
      ensures (
        && var addr := v'.tiles[core].l2.cache[idx].addr;
        && ((DirtyL2CacheEntry(c, v', core, idx)
          && (
            || DirIL2CacheEntry(c, v', core, idx)
            || DirSL2CacheEntry(c, v', core, idx)
          )
        ) ==> (
          && v'.g.callback_epochs[addr].wcb.Some?
        ))
        && ((CleanL2CacheEntry(c, v', core, idx) 
          && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)
          && (
            || DirIL2CacheEntry(c, v', core, idx)
            || DirSL2CacheEntry(c, v', core, idx)
          )
        ) ==> (
          && v'.g.callback_epochs[addr].wcb.None?
        ))
      )
      {
        var addr := v'.tiles[core].l2.cache[idx].addr;
        if DirtyL2CacheEntry(c, v', core, idx) &&
          (DirIL2CacheEntry(c, v', core, idx) || DirSL2CacheEntry(c, v', core, idx))
        {
          if step.tile_step.l2_step.DirectoryStep?
            && core == step.tile_idx && step.tile_step.l2_step.opt_idx.Some?
            && idx == step.tile_step.l2_step.opt_idx.val
          {
            if step.tile_step.l2_step.msg.coh_msg.PutM? {
              if v.tiles[core].l2.cache[idx].dir.M? && v.tiles[core].l2.cache[idx].dir.owner == step.tile_step.l2_step.msg.meta.src {
                assert PutMInFlight(c, v, addr, v.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), step.tile_step.l2_step.msg.coh_msg.val) by {
                  reveal PutMInFlight;
                }
              }
            } else if step.tile_step.l2_step.msg.coh_msg.Data? {
              assert v.tiles[core].l2.cache[idx].dir.SD?;
              assert DataInFlight(c, v, addr, step.tile_step.l2_step.msg.meta.src, Cache(core, L2), step.tile_step.l2_step.msg.coh_msg.val) by {
                reveal DataInFlight;
              }
            } 
          }
        } 
        if CleanL2CacheEntry(c, v', core, idx)
          && (
            || DirIL2CacheEntry(c, v', core, idx) 
            || DirSL2CacheEntry(c, v', core, idx)
          )
        {
          if step.tile_step.l2_step.ReceiveOnMissDataStep? 
            && core == step.tile_idx && idx == step.tile_step.l2_step.eng_resp.idx
          {
            assert IsInFlightOnMissResponse(c, v, addr, step.msgOps.recv.val, idx);
          }
          if step.tile_step.l2_step.DirectoryStep? 
            && core == step.tile_idx && step.tile_step.l2_step.opt_idx.Some?
            && idx == step.tile_step.l2_step.opt_idx.val
          {
            if step.tile_step.l2_step.msg.coh_msg.PutM? {
              if v.tiles[core].l2.cache[idx].dir.M? && v.tiles[core].l2.cache[idx].dir.owner == step.tile_step.l2_step.msg.meta.src {
                assert PutMInFlight(c, v, addr, v.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), step.tile_step.l2_step.msg.coh_msg.val) by {
                  reveal PutMInFlight;
                }
              }
            } else if step.tile_step.l2_step.msg.coh_msg.Data? {
                assert DataInFlight(c, v, addr, step.tile_step.l2_step.msg.meta.src, Cache(core, L2), step.tile_step.l2_step.msg.coh_msg.val) by {
                  reveal DataInFlight;
                }
            }
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesL2DirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires L2DirtyBitTracksInterveningWrite(c, v)
    requires EL1PrivateMorphAddressesAreCorrectCore(c, v)
    requires L1PrivateMorphAddressesAreCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)

    requires L2DirectoryInIMeansNoLoadableInCore(c, v)
    requires L2DirectoryInIMeansNoLoadableInEngine(c, v)
    requires L2DirectoryInSMeansNoMInCore(c, v)
    requires L2DirectoryInSMeansNoMInEngine(c, v)
    ensures L2DirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
      && v'.tiles[core].l2.cache[idx].coh.Loadable()
    )
    ensures (
      && var addr := v'.tiles[core].l2.cache[idx].addr;
      && ((DirtyL2CacheEntry(c, v', core, idx)
        && (
          || DirIL2CacheEntry(c, v', core, idx)
          || DirSL2CacheEntry(c, v', core, idx)
        )
      ) ==> (
        && v'.g.callback_epochs[addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx) 
        && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)
        && (
          || DirIL2CacheEntry(c, v', core, idx) 
          || DirSL2CacheEntry(c, v', core, idx)
        )
      ) ==> (
        && v'.g.callback_epochs[addr].wcb.None?
      ))
    )
    {
      // assert core == v'.tiles[core].l2.cache[idx].addr.morphType.idx;
      // need L1 in M state implies dir is not in I or S state, so value doesn't need to match
      if step.tile_step.CoreStep? {
        if step.tile_step.core_step.inst.RMW? || step.tile_step.core_step.inst.Store? {
          if step.tile_step.core_step.inst.addr == v'.tiles[core].l2.cache[idx].addr {
            // assert core == step.tile_idx;
            // assert v.tiles[core].core.cache[step.tile_step.core_step.idx].addr == step.tile_step.core_step.inst.addr;
            // assert v.tiles[core].core.cache[step.tile_step.core_step.idx].coh.M?;
            assert v.tiles[step.tile_idx].core.cache[step.tile_step.core_step.idx].addr == step.tile_step.core_step.inst.addr;
            assert v.tiles[step.tile_idx].core.cache[step.tile_step.core_step.idx].coh.M?;
          }
        }
      } else {
        assert step.tile_step.EngineStep?;
        if step.tile_step.eng_step.inst.RMW? || step.tile_step.eng_step.inst.Store? {
          if step.tile_step.eng_step.inst.addr == v'.tiles[core].l2.cache[idx].addr {
            // assert core == step.tile_idx;
            assert v.tiles[step.tile_idx].engine.cache[step.tile_step.eng_step.c_idx].coh.M?;
          }
        }
      }
    }
  }

  lemma StartEndCBPreservesL2DirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires L2DirtyBitTracksInterveningWrite(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires L2AddressesUnique(c, v)
    requires L3AddressesUnique(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires L3AddrNotInCacheMeansL2AddrNotInCache(c, v)
    ensures L2DirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v', core, idx)
      && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)
      && v'.tiles[core].l2.cache[idx].coh.Loadable()
    )
    ensures (
      && var addr := v'.tiles[core].l2.cache[idx].addr;
      && ((DirtyL2CacheEntry(c, v', core, idx)
        && (
          || DirIL2CacheEntry(c, v', core, idx)
          || DirSL2CacheEntry(c, v', core, idx)
        )
      ) ==> (
        && v'.g.callback_epochs[addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v', core, idx) 
        && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)
        && (
          || DirIL2CacheEntry(c, v', core, idx) 
          || DirSL2CacheEntry(c, v', core, idx)
        )
      ) ==> (
        && v'.g.callback_epochs[addr].wcb.None?
      ))
    )
    {
      if re == EndOnMiss && v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr == v'.tiles[core].l2.cache[idx].addr {
        // assert step.tile_idx == core;
        assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].l2.cache[idx].addr, CallbackType.OnMiss, step.tile_idx, step.tile_step.eng_step.idx);
        var cb := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type;
        assert CallbackPresent(c, v, v'.tiles[core].l2.cache[idx].addr, cb) by {
          reveal CallbackPresent;
        }
        assert OnMissInProgress(c, v, v'.tiles[core].l2.cache[idx].addr, cb.idx);
        if PrivateMorph(v'.tiles[core].l2.cache[idx].addr) {
          reveal L2PendingCallbackForAddr;
          assert idx == cb.idx;
          assert v'.tiles[core].l2.cache[idx].PendingCB?;
          assert false;
        } else {
          assert SharedMorph(v'.tiles[core].l2.cache[idx].addr);
          reveal L3PendingCallbackForAddr;
          assert L3AddrNotInCache(c, v, c.addr_map(v'.tiles[core].l2.cache[idx].addr), v'.tiles[core].l2.cache[idx].addr);
          assert L2AddrNotInCache(c, v, core, v'.tiles[core].l2.cache[idx].addr);
        }
      }
    }
  }

  lemma NoOpPreservesL3DirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires PutMFromOwnerL3MeansInterveningWrite(c, v)
    requires DataFromOwnerL3MeansInterveningWrite(c, v)
    requires L3QueueHeadsWellformed(c, v)
    requires OnMissResponseMeansInEpochWithNoWrite(c, v)
    requires PendingMemMeansNonMorphAddress(c, v)
    requires L3DirtyBitTracksInterveningWrite(c, v)
    ensures L3DirtyBitTracksInterveningWrite(c, v')
  {
    if step.TileStep? && step.tile_step.L3Step? {
      forall core: nat, idx: nat | (
        && NonEmptyNonPendingL3CacheEntry(c, v', core, idx)
        && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
        && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
      )
      ensures (
        && var addr := v'.tiles[core].l3.cache[idx].addr;
        && ((DirtyL3CacheEntry(c, v', core, idx)
          && (
            || DirIL3CacheEntry(c, v', core, idx)
            || DirSL3CacheEntry(c, v', core, idx)
          )
        ) ==> (
          && v'.g.callback_epochs[addr].wcb.Some?
        ))
        && ((CleanL3CacheEntry(c, v', core, idx) 
          && (
            || DirIL3CacheEntry(c, v', core, idx) 
            || DirSL3CacheEntry(c, v', core, idx)
          )
        ) ==> (
          && v'.g.callback_epochs[addr].wcb.None?
        ))
      )
      {
        var addr := v'.tiles[core].l3.cache[idx].addr;
        if DirtyL3CacheEntry(c, v', core, idx) &&
          (DirIL3CacheEntry(c, v', core, idx) || DirSL3CacheEntry(c, v', core, idx))
        {
          if step.tile_step.l3_step.DirectoryStep?
            && core == step.tile_idx && step.tile_step.l3_step.opt_idx.Some?
            && idx == step.tile_step.l3_step.opt_idx.val
          {
            if step.tile_step.l3_step.msg.coh_msg.PutM? {
              if v.tiles[core].l3.cache[idx].dir.M? && v.tiles[core].l3.cache[idx].dir.owner == step.tile_step.l3_step.msg.meta.src {
                assert PutMInFlight(c, v, addr, v.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), step.tile_step.l3_step.msg.coh_msg.val) by {
                  reveal PutMInFlight;
                }
              }
            } else if step.tile_step.l3_step.msg.coh_msg.Data? {
              assert v.tiles[core].l3.cache[idx].dir.SD?;
              assert DataInFlight(c, v, addr, step.tile_step.l3_step.msg.meta.src, Cache(core, L3), step.tile_step.l3_step.msg.coh_msg.val) by {
                reveal DataInFlight;
              }
            } 
          }
        } 
        if CleanL3CacheEntry(c, v', core, idx)
          && (DirIL3CacheEntry(c, v', core, idx) || DirSL3CacheEntry(c, v', core, idx))
        {
          if step.tile_step.l3_step.ReceiveOnMissDataStep? 
            && core == step.tile_idx && idx == step.tile_step.l3_step.eng_resp.idx
          {
            assert IsInFlightOnMissResponse(c, v, addr, step.msgOps.recv.val, idx);
          }
          else if step.tile_step.l3_step.RespMemoryStep? 
            && core == step.tile_idx && idx == step.tile_step.l3_step.idx
            && v.tiles[core].l3.cache[idx].PendingMem?
          {
            assert v.tiles[core].l3.cache[idx].addr.Regular?;
            assert false;
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesL3DirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires L3DirectoryInIMeansL2AddrNotInCache(c, v)
    requires L3DirectoryInSMeansNoMInL2(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInCore(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInEngine(c, v)
    requires MInCoreMeansMinL2(c, v)
    requires MInEngineMeansMinL2(c, v)
    requires L3DirtyBitTracksInterveningWrite(c, v)
    ensures L3DirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat | (
      && NonEmptyNonPendingL3CacheEntry(c, v', core, idx)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
    ensures (
      && var addr := v'.tiles[core].l3.cache[idx].addr;
      && ((DirtyL3CacheEntry(c, v', core, idx)
        && (
          || DirIL3CacheEntry(c, v', core, idx)
          || DirSL3CacheEntry(c, v', core, idx)
        )
      ) ==> (
        && v'.g.callback_epochs[addr].wcb.Some?
      ))
      && ((CleanL3CacheEntry(c, v', core, idx) 
        && (
          || DirIL3CacheEntry(c, v', core, idx) 
          || DirSL3CacheEntry(c, v', core, idx)
        )
      ) ==> (
        && v'.g.callback_epochs[addr].wcb.None?
      ))
    )
    {
      // assert core == c.addr_map(v'.tiles[core].l3.cache[idx].addr);
      // need L1 in M state implies dir is in M state, so value doesn't need to match
      if step.tile_step.CoreStep? {
        if step.tile_step.core_step.inst.RMW? || step.tile_step.core_step.inst.Store? {
          if step.tile_step.core_step.inst.addr == v'.tiles[core].l3.cache[idx].addr {
            assert v.tiles[step.tile_idx].core.cache[step.tile_step.core_step.idx].addr == step.tile_step.core_step.inst.addr;
            assert v.tiles[step.tile_idx].core.cache[step.tile_step.core_step.idx].coh.M?;
            assert !L2AddrNotInCache(c, v, step.tile_idx, step.tile_step.core_step.inst.addr);
            var idx2: nat :| NonEmptyNonPendingL2CacheEntry(c, v, step.tile_idx, idx2) && v.tiles[step.tile_idx].l2.cache[idx2].addr == step.tile_step.core_step.inst.addr;
            assert CohML2CacheEntry(c, v, step.tile_idx, idx2);
            assert !DirIL3CacheEntry(c, v, core, idx);
            assert !DirSL3CacheEntry(c, v, core, idx);
          }
        }
      } else {
        assert step.tile_step.EngineStep?;
        if step.tile_step.eng_step.inst.RMW? || step.tile_step.eng_step.inst.Store? {
          if step.tile_step.eng_step.inst.addr == v'.tiles[core].l3.cache[idx].addr {
            assert v.tiles[step.tile_idx].engine.cache[step.tile_step.eng_step.c_idx].coh.M?;
            assert !L2AddrNotInCache(c, v, step.tile_idx, step.tile_step.eng_step.inst.addr);
            var idx2: nat :| NonEmptyNonPendingL2CacheEntry(c, v, step.tile_idx, idx2) && v.tiles[step.tile_idx].l2.cache[idx2].addr == step.tile_step.eng_step.inst.addr;
            assert CohML2CacheEntry(c, v, step.tile_idx, idx2);
            assert !DirIL3CacheEntry(c, v, core, idx);
            assert !DirSL3CacheEntry(c, v, core, idx);
          }
        }
      }
    }
  }

  lemma StartEndCBPreservesL3DirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires L3AddressesUnique(c, v)
    requires OnMissInProgressIffCacheEntryPendingShared(c, v)
    requires L3DirtyBitTracksInterveningWrite(c, v)
    ensures L3DirtyBitTracksInterveningWrite(c, v')
  {
    forall core: nat, idx: nat | (
      && NonEmptyNonPendingL3CacheEntry(c, v', core, idx)
      && AddrIsInEpoch(c, v', v'.tiles[core].l3.cache[idx].addr)
      && SharedMorph(v'.tiles[core].l3.cache[idx].addr)
    )
    ensures (
      && var addr := v'.tiles[core].l3.cache[idx].addr;
      && ((DirtyL3CacheEntry(c, v', core, idx)
        && (
          || DirIL3CacheEntry(c, v', core, idx)
          || DirSL3CacheEntry(c, v', core, idx)
        )
      ) ==> (
        && v'.g.callback_epochs[addr].wcb.Some?
      ))
      && ((CleanL3CacheEntry(c, v', core, idx) 
        && (
          || DirIL3CacheEntry(c, v', core, idx) 
          || DirSL3CacheEntry(c, v', core, idx)
        )
      ) ==> (
        && v'.g.callback_epochs[addr].wcb.None?
      ))
    )
    {
      if re == EndOnMiss && v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr == v'.tiles[core].l3.cache[idx].addr {
        assert step.tile_idx == core;
        assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].l3.cache[idx].addr, CallbackType.OnMiss, core, step.tile_step.eng_step.idx);
        var cb := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type;
        assert CallbackPresent(c, v, v'.tiles[core].l3.cache[idx].addr, cb) by {
          reveal CallbackPresent;
        }
        assert OnMissInProgress(c, v, v'.tiles[core].l3.cache[idx].addr, cb.idx);
        reveal L3PendingCallbackForAddr;
        assert idx == cb.idx;
        assert v'.tiles[core].l3.cache[idx].PendingCB?;
      }
    }
  }

  /*
  lemma NoOpPreservesL2DirtyBitMatchesEpoch(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L2DirtyBitMatchesEpoch(c, v)
    requires PutMFromOwnerL2MeansEpochHasWcb(c, v)       // XD
    requires PutMFromProxyL2MeansEpochDataMatches(c, v)  // XD
    requires DataFromOwnerL2MeansEpochHasWcb(c, v)       // XD
    requires DataFromProxyL2MeansEpochDataMatches(c, v)  // XD
    requires EpochEntryInMorphWorkingSet(c, v)           // :(
    requires L2QueueHeadsWellformed(c, v)                // :(
    requires OnMissResponseMeansInEpochWithNoWrite(c, v) // XD
    ensures L2DirtyBitMatchesEpoch(c, v')
  {
    if step.TileStep? && step.tile_step.L2Step? {
      forall core: nat, idx: nat | NonEmptyL2CacheEntry(c, v', core, idx) && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)
        ensures (
          && var addr := v'.tiles[core].l2.cache[idx].addr;
          && ((DirtyL2CacheEntry(c, v', core, idx) && (DirIL2CacheEntry(c, v', core, idx) || DirSL2CacheEntry(c, v', core, idx))) ==> (
            && v'.g.callback_epochs[addr].wcb.Some?
            && v'.g.callback_epochs[addr].wcb.val.CBWrite()
            && var wval := if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval;
            && wval == v'.tiles[core].l2.cache[idx].dir.val
          ))
          && ((CleanL2CacheEntry(c, v', core, idx) 
            && (
              || DirIL2CacheEntry(c, v', core, idx) 
              || DirSL2CacheEntry(c, v', core, idx)
              || DirSDProxyOwnerL2CacheEntry(c, v', core, idx)
              || DirMProxyOwnerL2CacheEntry(c, v', core, idx)
            )
          ) ==> (
            && v'.g.callback_epochs[addr].wcb.None?
            && v'.g.callback_epochs[addr].me.Me?
            && ((DirIL2CacheEntry(c, v', core, idx) || DirSL2CacheEntry(c, v', core, idx)) ==> 
              v'.g.callback_epochs[addr].me.val == v'.tiles[core].l2.cache[idx].dir.val
            )
          ))
        )
      {
        var addr := v'.tiles[core].l2.cache[idx].addr;
        if DirtyL2CacheEntry(c, v', core, idx) &&
          (DirIL2CacheEntry(c, v', core, idx) || DirSL2CacheEntry(c, v', core, idx))
        {
          if step.tile_step.l2_step.DirectoryStep?
            && core == step.tile_idx && step.tile_step.l2_step.opt_idx.Some?
            && idx == step.tile_step.l2_step.opt_idx.val
          {
            if step.tile_step.l2_step.msg.coh_msg.PutM? {
              if v.tiles[core].l2.cache[idx].dir.M? && v.tiles[core].l2.cache[idx].dir.owner == step.tile_step.l2_step.msg.meta.src {
                if v.tiles[core].l2.cache[idx].dir.owner == Cache(core, Proxy) {
                  assert DirtyL2CacheEntry(c, v, core, idx);
                }
                assert PutMInFlight(c, v, addr, v.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), step.tile_step.l2_step.msg.coh_msg.val) by {
                  reveal PutMInFlight;
                }
              }
            } else if step.tile_step.l2_step.msg.coh_msg.Data? {
              assert v.tiles[core].l2.cache[idx].dir.SD?;
              assert DataInFlight(c, v, addr, step.tile_step.l2_step.msg.meta.src, Cache(core, L2), step.tile_step.l2_step.msg.coh_msg.val) by {
                reveal DataInFlight;
              }
            } 
            /*else if step.tile_step.l2_step.msg.coh_msg.GetS? {
              assert (
                || DirIL2CacheEntry(c, v, core, idx) 
                || DirSL2CacheEntry(c, v, core, idx)
                || DirML2CacheEntry(c, v, core, idx)
              );
              assert DirtyL2CacheEntry(c, v, core, idx);
              assert !DirMProxyOwnerL2CacheEntry(c, v, core, idx);
              assert !DirSDProxyOwnerL2CacheEntry(c, v, core, idx);
            } 
            else if step.tile_step.l2_step.msg.coh_msg.GetM? {
              assert (
                || DirIL2CacheEntry(c, v, core, idx) 
                || DirSL2CacheEntry(c, v, core, idx)
                || DirML2CacheEntry(c, v, core, idx)
              );
              // already dirty
              if DirMProxyOwnerL2CacheEntry(c, v, core, idx) {
                // its possible that it is NOT some here:
                // scenario:
                // 1. GetM from L1: Dir M
                // 2. GetM from Proxy: Dir M Proxy Owner, FwdGetM sent, dirty marked...
                // 3. GetM from eL1... <-- here

                // chance that FwdGetM is stalled waiting for write for L1
                // so there is no write yet...
                assume false;
              }
            }*/
          }
        } 
        // the issue: FwdGetM from the proxy will "launder" the dirty bit
        if CleanL2CacheEntry(c, v', core, idx)
          && (
            || DirIL2CacheEntry(c, v', core, idx) 
            || DirSL2CacheEntry(c, v', core, idx)
            || DirSDProxyOwnerL2CacheEntry(c, v', core, idx)
            || DirMProxyOwnerL2CacheEntry(c, v', core, idx)
          )
        {
          if step.tile_step.l2_step.DirectoryStep?
            && core == step.tile_idx 
            && step.tile_step.l2_step.opt_idx.Some?
            && idx == step.tile_step.l2_step.opt_idx.val
          {
            if step.tile_step.l2_step.msg.coh_msg.PutM? {
              // assert CleanL2CacheEntry(c, v, core, idx);
              // ideally need M + proxy owner as another guarantee here
              assert v'.g.callback_epochs[addr].wcb.None?;
              // assert v'.g.callback_epochs[addr].me.Me?;
              // assert !v.tiles[core].l2.cache[idx].dirty;
              if DirMProxyOwnerL2CacheEntry(c, v, core, idx) {
                // inv: PutM from Proxy when wcb is None and me is Me ==> returning val == me.val
                assert PutMInFlight(c, v, addr, step.tile_step.l2_step.msg.meta.src, Cache(core, L2), step.tile_step.l2_step.msg.coh_msg.val) by {
                  reveal PutMInFlight;
                }
              }
            } else if step.tile_step.l2_step.msg.coh_msg.Data? {
              assert v'.g.callback_epochs[addr].wcb.None?;
              // assert v'.g.callback_epochs[addr].me.Me?;
              if v.tiles[core].l2.cache[idx].dir.SD? && step.tile_step.l2_step.msg.meta.src == Cache(core, Proxy) {
                // inv: Data from Proxy when wcb is None and me is Me ==> returning val == me.val
                assert DataInFlight(c, v, addr, step.tile_step.l2_step.msg.meta.src, Cache(core, L2), step.tile_step.l2_step.msg.coh_msg.val) by {
                  reveal DataInFlight;
                }
              }
            // } else if step.tile_step.l2_step.msg.coh_msg.GetS? {
            //   assert (
            //     || DirIL2CacheEntry(c, v, core, idx) 
            //     || DirSL2CacheEntry(c, v, core, idx)
            //     || DirMProxyOwnerL2CacheEntry(c, v, core, idx)
            //   );
            // } else if step.tile_step.l2_step.msg.coh_msg.GetM? {
            //   assert (
            //     || DirIL2CacheEntry(c, v, core, idx) 
            //     || DirSL2CacheEntry(c, v, core, idx)
            //     || DirML2CacheEntry(c, v, core, idx)
            //   );
            }
          } else if step.tile_step.l2_step.ReceiveOnMissDataStep? 
            && core == step.tile_idx && idx == step.tile_step.l2_step.eng_resp.idx
          {
            assert IsInFlightOnMissResponse(c, v, addr, step.msgOps.recv.val, idx);
          } 
        }
      }
    }
  }

  
  lemma PerformNextInstPreservesL2DirtyBitMatchesEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires L2DirtyBitMatchesEpoch(c, v)
    requires EL1PrivateMorphAddressesAreCorrectCore(c, v)
    requires L1PrivateMorphAddressesAreCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires HavingDataInMMeansDirectoryinMorSDCore(c, v)     // :(
    requires HavingDataInMMeansDirectoryinMorSDEngine(c, v)   // :(
    ensures L2DirtyBitMatchesEpoch(c, v')
  {
    forall core: nat, idx: nat | NonEmptyL2CacheEntry(c, v', core, idx) && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr)  && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)
      ensures (
        && var addr := v'.tiles[core].l2.cache[idx].addr;
        && ((DirtyL2CacheEntry(c, v', core, idx) && (DirIL2CacheEntry(c, v', core, idx) || DirSL2CacheEntry(c, v', core, idx))) ==> (
            && v'.g.callback_epochs[addr].wcb.Some?
            && v'.g.callback_epochs[addr].wcb.val.CBWrite()
            && var wval := if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval;
            && wval == v'.tiles[core].l2.cache[idx].dir.val
          )
        )
        && ((CleanL2CacheEntry(c, v', core, idx) 
          && (
            || DirIL2CacheEntry(c, v', core, idx) 
            || DirSL2CacheEntry(c, v', core, idx)
            || DirSDProxyOwnerL2CacheEntry(c, v', core, idx)
            || DirMProxyOwnerL2CacheEntry(c, v', core, idx)
          )
        ) ==> (
          && v'.g.callback_epochs[addr].wcb.None?
          && v'.g.callback_epochs[addr].me.Me?
          && ((DirIL2CacheEntry(c, v', core, idx) || DirSL2CacheEntry(c, v', core, idx)) ==> 
            v'.g.callback_epochs[addr].me.val == v'.tiles[core].l2.cache[idx].dir.val
          )
        ))
      )
    {
      assert core == v'.tiles[core].l2.cache[idx].addr.morphType.idx;
      // need L1 in M state implies dir is in M state, so value doesn't need to match
      if step.tile_step.CoreStep? {
        if step.tile_step.core_step.inst.RMW? || step.tile_step.core_step.inst.Store? {
          if step.tile_step.core_step.inst.addr == v'.tiles[core].l2.cache[idx].addr {
            assert core == step.tile_idx;
            assert v.tiles[core].core.cache[step.tile_step.core_step.idx].coh.M?;
            // we know that the new owner can't be proxy, as then we know a fwdgetM is en route 
            // here, which means we would have marked the dirty bit.
            if DirMProxyOwnerL2CacheEntry(c, v, core, idx) {
              assert DirtyL2CacheEntry(c, v, core, idx);
            }
          }
        }
      } else {
        assert step.tile_step.EngineStep?;
        if step.tile_step.eng_step.inst.RMW? || step.tile_step.eng_step.inst.Store? {
          if step.tile_step.eng_step.inst.addr == v'.tiles[core].l2.cache[idx].addr {
            assert core == step.tile_idx;
            assert v.tiles[core].engine.cache[step.tile_step.eng_step.c_idx].coh.M?;
            if DirMProxyOwnerL2CacheEntry(c, v, core, idx) {
              assert DirtyL2CacheEntry(c, v, core, idx);
            }
          }
        }
      }
    }
  }

  lemma StartEndCBPreservesL2DirtyBitMatchesEpoch(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires L2DirtyBitMatchesEpoch(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires L2AddressesUnique(c, v)
    requires OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    ensures L2DirtyBitMatchesEpoch(c, v')
  {
    forall core: nat, idx: nat | NonEmptyL2CacheEntry(c, v', core, idx) && AddrIsInEpoch(c, v', v'.tiles[core].l2.cache[idx].addr) && PrivateMorph(v'.tiles[core].l2.cache[idx].addr)
      ensures (
        && var addr := v'.tiles[core].l2.cache[idx].addr;
        && ((DirtyL2CacheEntry(c, v', core, idx) && (DirIL2CacheEntry(c, v', core, idx) || DirSL2CacheEntry(c, v', core, idx))) ==> (
            && v'.g.callback_epochs[addr].wcb.Some?
            && v'.g.callback_epochs[addr].wcb.val.CBWrite()
            && var wval := if v'.g.callback_epochs[addr].wcb.val.Wcb? then v'.g.callback_epochs[addr].wcb.val.val else v'.g.callback_epochs[addr].wcb.val.wval;
            && wval == v'.tiles[core].l2.cache[idx].dir.val
          )
        )
        && ((CleanL2CacheEntry(c, v', core, idx) 
          && (
            || DirIL2CacheEntry(c, v', core, idx) 
            || DirSL2CacheEntry(c, v', core, idx)
            || DirSDProxyOwnerL2CacheEntry(c, v', core, idx)
            || DirMProxyOwnerL2CacheEntry(c, v', core, idx)
          )
        ) ==> (
          && v'.g.callback_epochs[addr].wcb.None?
          && v'.g.callback_epochs[addr].me.Me?
          && ((DirIL2CacheEntry(c, v', core, idx) || DirSL2CacheEntry(c, v', core, idx)) ==> 
            v'.g.callback_epochs[addr].me.val == v'.tiles[core].l2.cache[idx].dir.val
          )
        ))
      )
    {
      if re == EndOnMiss && v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].addr == v'.tiles[core].l2.cache[idx].addr {
        assert step.tile_idx == core;
        assert CallbackPresentInBufferLocation(c, v, v'.tiles[core].l2.cache[idx].addr, CallbackType.OnMiss, core, step.tile_step.eng_step.idx);
        var cb := v.tiles[step.tile_idx].engine.buffer[step.tile_step.eng_step.idx].cb_type;
        assert CallbackPresent(c, v, v'.tiles[core].l2.cache[idx].addr, cb) by {
          reveal CallbackPresent;
        }
        assert OnMissInProgress(c, v, v'.tiles[core].l2.cache[idx].addr, cb.idx);
        reveal L2PendingCallbackForAddr;
        assert idx == cb.idx;
        assert v'.tiles[core].l2.cache[idx].PendingCB?;
      }
    }
  }
  */
}