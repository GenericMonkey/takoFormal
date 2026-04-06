include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module L2DirectoryILoadableProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes
  import opened CacheTypes

  // Assuming this now
  // L2DirectoryInIMeansNoLoadableInCore
  // L2DirectoryInIMeansNoLoadableInEngine
  // L2DirectoryInIMeansNoLoadableInProxy

  /*lemma CoreNoOpPreservesL2DirectoryInIMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires L2DirectoryInIMeansNoLoadableInCore(c, v)
    requires DataInFlightToT1MeansDirectoryNotInI(c, v)
    requires InvAckInFlightToT1MeansDirectoryNotInI(c, v)
    requires L2AddressesUnique(c, v)
    ensures L2DirectoryInIMeansNoLoadableInCore(c, v')
  {

    forall core: nat, idx1: nat, idx2: nat | (
      && DirIL2CacheEntry(c, v', core, idx1)
      && idx2 < |v'.tiles[core].core.cache|
      && v'.tiles[core].core.cache[idx2].addr == v'.tiles[core].l2.cache[idx1].addr
    )
    ensures !v'.tiles[core].core.cache[idx2].coh.HasMostRecentVal()
    {
      assert DirIL2CacheEntry(c, v, core, idx1);
      if core == step.tile_idx
        && idx2 == step.tile_step.core_step.idx
        && step.tile_step.core_step.step.RecvMsgStep?
        && (
          || step.msgOps.recv.val.coh_msg.Data?
          || step.msgOps.recv.val.coh_msg.InvAck?
        )
      {
        if step.msgOps.recv.val.coh_msg.Data? {
          assert DataInFlight(c, v, v'.tiles[core].core.cache[idx2].addr, step.msgOps.recv.val.meta.src, Cache(step.tile_idx, L1), step.msgOps.recv.val.coh_msg.val) by {
            reveal DataInFlight;
          }
          assert false;
        } else {
          assert step.msgOps.recv.val.coh_msg.InvAck?;
          assert InvAckInFlight(c, v, v'.tiles[core].core.cache[idx2].addr, step.msgOps.recv.val.meta.src, Cache(step.tile_idx, L1)) by {
            reveal InvAckInFlight;
          }
          assert false;
        }
      }
    }
  }

  lemma L2NoOpPreservesL2DirectoryInIMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires L2DirectoryInIMeansNoLoadableInCore(c, v)
    requires L1AddressesUnique(c, v)
    requires L2AddressesUnique(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInCore(c, v)
    requires L1PrivateMorphAddressesAreCorrectCore(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires L2CohSToMMeansL2DirSorI(c, v)
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires L2DirSharersAlwaysTier1Cache(c, v)
    requires PutMFromOwnerMeansNoLoadableInCore(c, v)
    requires PutMInFlightMeansSourceIsEvicting(c, v)
    requires NotSharerSMeansNoLoadableInCore(c, v)
    requires PutSFromSharerMeansNoLoadableInCore(c, v)
    ensures L2DirectoryInIMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirIL2CacheEntry(c, v', core, idx1)
      && idx2 < |v'.tiles[core].core.cache|
      && v'.tiles[core].core.cache[idx2].addr == v'.tiles[core].l2.cache[idx1].addr
    )
    ensures !v'.tiles[core].core.cache[idx2].coh.HasMostRecentVal()
    {
      if !DirIL2CacheEntry(c, v, core, idx1) {
        if step.tile_step.l2_step.ReceiveOnMissDataStep? {
          assert L2AddrNotInCache(c, v, core, v.tiles[core].l2.cache[idx1].addr);
        } else if step.tile_step.l2_step.CacheCommunicationStep? {
          if step.tile_step.l2_step.c_step.GetSStep? {
           // this is because GetS is underspecified i believe
            assert L2AddrNotInCache(c, v, core, v'.tiles[core].l2.cache[idx1].addr);
          } else if step.tile_step.l2_step.c_step.GetMStep? {
            assert L2AddrNotInCache(c, v, core, v'.tiles[core].l2.cache[idx1].addr);
          } else {
            assert step.tile_step.l2_step.c_step.RecvMsgStep?;
            assert step.tile_step.l2_step.msg.coh_msg.Data?;
            assert core == step.tile_idx;
            assert step.tile_step.l2_step.idx == idx1;
            if v.tiles[core].l2.cache[idx1].coh.SMAD? {
              if !v.tiles[core].l2.cache[idx1].dir.S? {
                assert v.tiles[core].l2.cache[idx1].dir.I?;
                assert false;
              }
            } else {
              assert L2AddrNotInCache(c, v, core, v'.tiles[core].l2.cache[idx1].addr);
            }
          }
        } else {
          assert step.tile_step.l2_step.DirectoryStep?;
          assert core == step.tile_idx;
          assert step.tile_step.l2_step.opt_idx.val == idx1;
          if step.tile_step.l2_step.msg.coh_msg.PutM? {
            if DirML2CacheEntry(c, v, core, idx1) {
              assert step.tile_step.l2_step.msg.meta.src == v.tiles[core].l2.cache[idx1].dir.owner;
              // putm from owner means not loadable in any T1
              assert PutMInFlight(c, v, v.tiles[core].l2.cache[idx1].addr, step.tile_step.l2_step.msg.meta.src, Cache(core, L2), step.tile_step.l2_step.msg.coh_msg.val) by {
                reveal PutMInFlight;
              }
            } else {
              // need to consider the case where a PutM is a PutS S -> I
              assert DirSL2CacheEntry(c, v, core, idx1);
              assert v.tiles[core].l2.cache[idx1].dir.sharers - { step.tile_step.l2_step.msg.meta.src } == {};
              assert PutMInFlight(c, v, v.tiles[core].l2.cache[idx1].addr, step.tile_step.l2_step.msg.meta.src, Cache(core, L2), step.tile_step.l2_step.msg.coh_msg.val) by {
                reveal PutMInFlight;
              }
              if step.tile_step.l2_step.msg.meta.src != Cache(core, L1) {
                assert !(Cache(core, L1) in v.tiles[core].l2.cache[idx1].dir.sharers) by {
                  if Cache(core, L1) in v.tiles[core].l2.cache[idx1].dir.sharers {
                    assert Cache(core, L1) in (v.tiles[core].l2.cache[idx1].dir.sharers - {step.tile_step.l2_step.msg.meta.src});
                    assert false;
                  }
                }
              }
            }
          } else if step.tile_step.l2_step.msg.coh_msg.PutS? {
            assert v.tiles[core].l2.cache[idx1].dir.sharers - {step.tile_step.l2_step.msg.meta.src} == {};
            if step.tile_step.l2_step.msg.meta.src == Cache(core, L1) {
              assert PutSInFlight(c, v, v.tiles[core].l2.cache[idx1].addr, step.tile_step.l2_step.msg.meta.src, Cache(core, L2)) by {
                reveal PutSInFlight;
              }
            } else {
              assert DirSL2CacheEntry(c, v, core, idx1);
              assert !(Cache(core, L1) in v.tiles[core].l2.cache[idx1].dir.sharers) by {
                if Cache(core, L1) in v.tiles[core].l2.cache[idx1].dir.sharers {
                  assert Cache(core, L1) in v.tiles[core].l2.cache[idx1].dir.sharers - {step.tile_step.l2_step.msg.meta.src};
                  assert false;
                }
              }
            }
          } else {
            assert step.tile_step.l2_step.msg.coh_msg.Data?;
            assert DirSDL2CacheEntry(c, v, core, idx1);
            assert !(Cache(core, L1) in v.tiles[core].l2.cache[idx1].dir.sharers);
          }
        }
      }
    }
  }

  lemma OtherNoOpPreservesL2DirectoryInIMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? ==> (
      || step.tile_step.ProxyStep?
      || step.tile_step.EngineStep?
      || step.tile_step.L3Step?
    )
    requires L2DirectoryInIMeansNoLoadableInCore(c, v)
    ensures L2DirectoryInIMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirIL2CacheEntry(c, v', core, idx1)
      && idx2 < |v'.tiles[core].core.cache|
      && v'.tiles[core].core.cache[idx2].addr == v'.tiles[core].l2.cache[idx1].addr
    )
    ensures !v'.tiles[core].core.cache[idx2].coh.HasMostRecentVal()
    {
      assert DirIL2CacheEntry(c, v, core, idx1);
    }
  }

  lemma NoOpPreservesL2DirectoryInIMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L2DirectoryInIMeansNoLoadableInCore(c, v)
    requires DataInFlightToT1MeansDirectoryNotInI(c, v)
    requires InvAckInFlightToT1MeansDirectoryNotInI(c, v)
    requires L1AddressesUnique(c, v)
    requires L2AddressesUnique(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInCore(c, v)
    requires L1PrivateMorphAddressesAreCorrectCore(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires L2CohSToMMeansL2DirSorI(c, v)
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires L2DirSharersAlwaysTier1Cache(c, v)
    requires PutMFromOwnerMeansNoLoadableInCore(c, v)
    requires PutMInFlightMeansSourceIsEvicting(c, v)
    requires NotSharerSMeansNoLoadableInCore(c, v)
    requires PutSFromSharerMeansNoLoadableInCore(c, v)
    ensures L2DirectoryInIMeansNoLoadableInCore(c, v')
  {
    if step.TileStep? {
      if step.tile_step.CoreStep? {
        CoreNoOpPreservesL2DirectoryInIMeansNoLoadableInCore(c, v, v', step);
      } else if step.tile_step.L2Step? {
        L2NoOpPreservesL2DirectoryInIMeansNoLoadableInCore(c, v, v', step);
      }
    } else {
      OtherNoOpPreservesL2DirectoryInIMeansNoLoadableInCore(c, v, v', step);
    }
  }

  lemma StartEndCBPreservesL2DirectoryInIMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires L2DirectoryInIMeansNoLoadableInCore(c, v)
    ensures L2DirectoryInIMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirIL2CacheEntry(c, v', core, idx1)
      && idx2 < |v'.tiles[core].core.cache|
      && v'.tiles[core].core.cache[idx2].addr == v'.tiles[core].l2.cache[idx1].addr
    )
    ensures !v'.tiles[core].core.cache[idx2].coh.HasMostRecentVal()
    {
      assert DirIL2CacheEntry(c, v, core, idx1);
    }
  }

  lemma PerformNextInstPreservesL2DirectoryInIMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires L2DirectoryInIMeansNoLoadableInCore(c, v)
    ensures L2DirectoryInIMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirIL2CacheEntry(c, v', core, idx1)
      && idx2 < |v'.tiles[core].core.cache|
      && v'.tiles[core].core.cache[idx2].addr == v'.tiles[core].l2.cache[idx1].addr
    )
    ensures !v'.tiles[core].core.cache[idx2].coh.HasMostRecentVal()
    {
      assert DirIL2CacheEntry(c, v, core, idx1);
    }
  }


  lemma EngineNoOpPreservesL2DirectoryInIMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires L2DirectoryInIMeansNoLoadableInEngine(c, v)
    requires DataInFlightToT1MeansDirectoryNotInI(c, v)
    requires InvAckInFlightToT1MeansDirectoryNotInI(c, v)
    requires L2AddressesUnique(c, v)
    ensures L2DirectoryInIMeansNoLoadableInEngine(c, v')
  {

    forall core: nat, idx1: nat, idx2: nat | (
      && DirIL2CacheEntry(c, v', core, idx1)
      && idx2 < |v'.tiles[core].engine.cache|
      && v'.tiles[core].engine.cache[idx2].addr == v'.tiles[core].l2.cache[idx1].addr
    )
    ensures !v'.tiles[core].engine.cache[idx2].coh.HasMostRecentVal()
    {
      assert DirIL2CacheEntry(c, v, core, idx1);
      if core == step.tile_idx
        && step.tile_step.eng_step.CacheCommunicationStep?
        && idx2 == step.tile_step.eng_step.c_idx
        && step.tile_step.eng_step.step.RecvMsgStep?
        && (
          || step.msgOps.recv.val.coh_msg.Data?
          || step.msgOps.recv.val.coh_msg.InvAck?
        )
      {
        if step.msgOps.recv.val.coh_msg.Data? {
          assert DataInFlight(c, v, v'.tiles[core].engine.cache[idx2].addr, step.msgOps.recv.val.meta.src, Cache(step.tile_idx, eL1), step.msgOps.recv.val.coh_msg.val) by {
            reveal DataInFlight;
          }
          assert false;
        } else {
          assert step.msgOps.recv.val.coh_msg.InvAck?;
          assert InvAckInFlight(c, v, v'.tiles[core].engine.cache[idx2].addr, step.msgOps.recv.val.meta.src, Cache(step.tile_idx, eL1)) by {
            reveal InvAckInFlight;
          }
          assert false;
        }
      }
    }
  }

  lemma L2NoOpPreservesL2DirectoryInIMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires L2DirectoryInIMeansNoLoadableInEngine(c, v)
    requires EL1AddressesUnique(c, v)
    requires L2AddressesUnique(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInEngine(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires L2CohSToMMeansL2DirSorI(c, v)
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires L2DirSharersAlwaysTier1Cache(c, v)
    requires PutMFromOwnerMeansNoLoadableInEngine(c, v)
    requires PutMInFlightMeansSourceIsEvicting(c, v)
    requires NotSharerSMeansNoLoadableInEngine(c, v)
    requires PutSFromSharerMeansNoLoadableInEngine(c, v)
    ensures L2DirectoryInIMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirIL2CacheEntry(c, v', core, idx1)
      && idx2 < |v'.tiles[core].engine.cache|
      && v'.tiles[core].engine.cache[idx2].addr == v'.tiles[core].l2.cache[idx1].addr
    )
    ensures !v'.tiles[core].engine.cache[idx2].coh.HasMostRecentVal()
    {
      if !DirIL2CacheEntry(c, v, core, idx1) {
        if step.tile_step.l2_step.ReceiveOnMissDataStep? {
          assert L2AddrNotInCache(c, v, core, v.tiles[core].l2.cache[idx1].addr);
        } else if step.tile_step.l2_step.CacheCommunicationStep? {
          if step.tile_step.l2_step.c_step.GetSStep? {
           // this is because GetS is underspecified i believe
            assert L2AddrNotInCache(c, v, core, v'.tiles[core].l2.cache[idx1].addr);
          } else if step.tile_step.l2_step.c_step.GetMStep? {
            assert L2AddrNotInCache(c, v, core, v'.tiles[core].l2.cache[idx1].addr);
          } else {
            assert step.tile_step.l2_step.c_step.RecvMsgStep?;
            assert step.tile_step.l2_step.msg.coh_msg.Data?;
            assert core == step.tile_idx;
            assert step.tile_step.l2_step.idx == idx1;
            if v.tiles[core].l2.cache[idx1].coh.SMAD? {
              if !v.tiles[core].l2.cache[idx1].dir.S? {
                assert v.tiles[core].l2.cache[idx1].dir.I?;
                assert false;
              }
            } else {
              assert L2AddrNotInCache(c, v, core, v'.tiles[core].l2.cache[idx1].addr);
            }
          }
        } else {
          assert step.tile_step.l2_step.DirectoryStep?;
          assert core == step.tile_idx;
          assert step.tile_step.l2_step.opt_idx.val == idx1;
          if step.tile_step.l2_step.msg.coh_msg.PutM? {
            if DirML2CacheEntry(c, v, core, idx1) {
              assert step.tile_step.l2_step.msg.meta.src == v.tiles[core].l2.cache[idx1].dir.owner;
              // putm from owner means not loadable in any T1
              assert PutMInFlight(c, v, v.tiles[core].l2.cache[idx1].addr, step.tile_step.l2_step.msg.meta.src, Cache(core, L2), step.tile_step.l2_step.msg.coh_msg.val) by {
                reveal PutMInFlight;
              }
            } else {
              // need to consider the case where a PutM is a PutS S -> I
              assert DirSL2CacheEntry(c, v, core, idx1);
              assert v.tiles[core].l2.cache[idx1].dir.sharers - { step.tile_step.l2_step.msg.meta.src } == {};
              assert PutMInFlight(c, v, v.tiles[core].l2.cache[idx1].addr, step.tile_step.l2_step.msg.meta.src, Cache(core, L2), step.tile_step.l2_step.msg.coh_msg.val) by {
                reveal PutMInFlight;
              }
              if step.tile_step.l2_step.msg.meta.src != Cache(core, eL1) {
                assert !(Cache(core, eL1) in v.tiles[core].l2.cache[idx1].dir.sharers) by {
                  if Cache(core, eL1) in v.tiles[core].l2.cache[idx1].dir.sharers {
                    assert Cache(core, eL1) in (v.tiles[core].l2.cache[idx1].dir.sharers - {step.tile_step.l2_step.msg.meta.src});
                    assert false;
                  }
                }
              }
            }
          } else if step.tile_step.l2_step.msg.coh_msg.PutS? {
            assert v.tiles[core].l2.cache[idx1].dir.sharers - {step.tile_step.l2_step.msg.meta.src} == {};
            if step.tile_step.l2_step.msg.meta.src == Cache(core, eL1) {
              assert PutSInFlight(c, v, v.tiles[core].l2.cache[idx1].addr, step.tile_step.l2_step.msg.meta.src, Cache(core, L2)) by {
                reveal PutSInFlight;
              }
            } else {
              assert DirSL2CacheEntry(c, v, core, idx1);
              assert !(Cache(core, eL1) in v.tiles[core].l2.cache[idx1].dir.sharers) by {
                if Cache(core, eL1) in v.tiles[core].l2.cache[idx1].dir.sharers {
                  assert Cache(core, eL1) in v.tiles[core].l2.cache[idx1].dir.sharers - {step.tile_step.l2_step.msg.meta.src};
                  assert false;
                }
              }
            }
          } else {
            assert step.tile_step.l2_step.msg.coh_msg.Data?;
            assert DirSDL2CacheEntry(c, v, core, idx1);
            assert !(Cache(core, eL1) in v.tiles[core].l2.cache[idx1].dir.sharers);
          }
        }
      }
    }
  }

  lemma OtherNoOpPreservesL2DirectoryInIMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? ==> (
      || step.tile_step.ProxyStep?
      || step.tile_step.CoreStep?
      || step.tile_step.L3Step?
    )
    requires L2DirectoryInIMeansNoLoadableInEngine(c, v)
    ensures L2DirectoryInIMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirIL2CacheEntry(c, v', core, idx1)
      && idx2 < |v'.tiles[core].engine.cache|
      && v'.tiles[core].engine.cache[idx2].addr == v'.tiles[core].l2.cache[idx1].addr
    )
    ensures !v'.tiles[core].engine.cache[idx2].coh.HasMostRecentVal()
    {
      assert DirIL2CacheEntry(c, v, core, idx1);
    }
  }

  lemma NoOpPreservesL2DirectoryInIMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L2DirectoryInIMeansNoLoadableInEngine(c, v)
    requires DataInFlightToT1MeansDirectoryNotInI(c, v)
    requires InvAckInFlightToT1MeansDirectoryNotInI(c, v)
    requires EL1AddressesUnique(c, v)
    requires L2AddressesUnique(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInEngine(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires L2CohSToMMeansL2DirSorI(c, v)
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires L2DirSharersAlwaysTier1Cache(c, v)
    requires PutMInFlightMeansSourceIsEvicting(c, v)
    requires PutMFromOwnerMeansNoLoadableInEngine(c, v)
    requires NotSharerSMeansNoLoadableInEngine(c, v)
    requires PutSFromSharerMeansNoLoadableInEngine(c, v)
    ensures L2DirectoryInIMeansNoLoadableInEngine(c, v')
  {
    if step.TileStep? {
      if step.tile_step.EngineStep? {
        EngineNoOpPreservesL2DirectoryInIMeansNoLoadableInEngine(c, v, v', step);
      } else if step.tile_step.L2Step? {
        L2NoOpPreservesL2DirectoryInIMeansNoLoadableInEngine(c, v, v', step);
      }
    } else {
      OtherNoOpPreservesL2DirectoryInIMeansNoLoadableInEngine(c, v, v', step);
    }
  }

  lemma StartEndCBPreservesL2DirectoryInIMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires L2DirectoryInIMeansNoLoadableInEngine(c, v)
    ensures L2DirectoryInIMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirIL2CacheEntry(c, v', core, idx1)
      && idx2 < |v'.tiles[core].engine.cache|
      && v'.tiles[core].engine.cache[idx2].addr == v'.tiles[core].l2.cache[idx1].addr
    )
    ensures !v'.tiles[core].engine.cache[idx2].coh.HasMostRecentVal()
    {
      assert DirIL2CacheEntry(c, v, core, idx1);
    }
  }

  lemma PerformNextInstPreservesL2DirectoryInIMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires L2DirectoryInIMeansNoLoadableInEngine(c, v)
    ensures L2DirectoryInIMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirIL2CacheEntry(c, v', core, idx1)
      && idx2 < |v'.tiles[core].engine.cache|
      && v'.tiles[core].engine.cache[idx2].addr == v'.tiles[core].l2.cache[idx1].addr
    )
    ensures !v'.tiles[core].engine.cache[idx2].coh.HasMostRecentVal()
    {
      assert DirIL2CacheEntry(c, v, core, idx1);
    }
  }

  lemma ProxyNoOpPreservesL2DirectoryInIMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires L2DirectoryInIMeansNoLoadableInProxy(c, v)
    requires DataInFlightToT1MeansDirectoryNotInI(c, v)
    requires InvAckInFlightToT1MeansDirectoryNotInI(c, v)
    requires L2AddressesUnique(c, v)
    ensures L2DirectoryInIMeansNoLoadableInProxy(c, v')
  {

    forall core: nat, idx1: nat, idx2: nat | (
      && DirIL2CacheEntry(c, v', core, idx1)
      && idx2 < |v'.tiles[core].proxy.cache|
      && v'.tiles[core].proxy.cache[idx2].addr == v'.tiles[core].l2.cache[idx1].addr
    )
    ensures !v'.tiles[core].proxy.cache[idx2].coh.HasMostRecentVal()
    {
      assert DirIL2CacheEntry(c, v, core, idx1);
      if core == step.tile_idx
        && idx2 == step.tile_step.proxy_step.idx
        && step.tile_step.proxy_step.step.RecvMsgStep?
        && (
          || step.msgOps.recv.val.coh_msg.Data?
          || step.msgOps.recv.val.coh_msg.InvAck?
        )
      {
        if step.msgOps.recv.val.coh_msg.Data? {
          assert DataInFlight(c, v, v'.tiles[core].proxy.cache[idx2].addr, step.msgOps.recv.val.meta.src, Cache(step.tile_idx, Proxy), step.msgOps.recv.val.coh_msg.val) by {
            reveal DataInFlight;
          }
          assert false;
        } else {
          assert step.msgOps.recv.val.coh_msg.InvAck?;
          assert InvAckInFlight(c, v, v'.tiles[core].proxy.cache[idx2].addr, step.msgOps.recv.val.meta.src, Cache(step.tile_idx, Proxy)) by {
            reveal InvAckInFlight;
          }
          assert false;
        }
      }
    }
  }

  lemma L2NoOpPreservesL2DirectoryInIMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires L2DirectoryInIMeansNoLoadableInProxy(c, v)
    requires L2AddressesUnique(c, v)
    requires ProxyAddressesUnique(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInProxy(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires L2CohSToMMeansL2DirSorI(c, v)
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires L2DirSharersAlwaysTier1Cache(c, v)
    requires PutMFromOwnerMeansNoLoadableInProxy(c, v)
    requires NotSharerSMeansNoLoadableInProxy(c, v)
    requires PutMInFlightMeansSourceIsEvicting(c, v)
    requires PutSFromSharerMeansNoLoadableInProxy(c, v)
    ensures L2DirectoryInIMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirIL2CacheEntry(c, v', core, idx1)
      && idx2 < |v'.tiles[core].proxy.cache|
      && v'.tiles[core].proxy.cache[idx2].addr == v'.tiles[core].l2.cache[idx1].addr
    )
    ensures !v'.tiles[core].proxy.cache[idx2].coh.HasMostRecentVal()
    {
      if !DirIL2CacheEntry(c, v, core, idx1) {
        if step.tile_step.l2_step.ReceiveOnMissDataStep? {
          assert L2AddrNotInCache(c, v, core, v.tiles[core].l2.cache[idx1].addr);
        } else if step.tile_step.l2_step.CacheCommunicationStep? {
          if step.tile_step.l2_step.c_step.GetSStep? {
           // this is because GetS is underspecified i believe
            assert L2AddrNotInCache(c, v, core, v'.tiles[core].l2.cache[idx1].addr);
          } else if step.tile_step.l2_step.c_step.GetMStep? {
            assert L2AddrNotInCache(c, v, core, v'.tiles[core].l2.cache[idx1].addr);
          } else {
            assert step.tile_step.l2_step.c_step.RecvMsgStep?;
            assert step.tile_step.l2_step.msg.coh_msg.Data?;
            assert core == step.tile_idx;
            assert step.tile_step.l2_step.idx == idx1;
            if v.tiles[core].l2.cache[idx1].coh.SMAD? {
              if !v.tiles[core].l2.cache[idx1].dir.S? {
                assert v.tiles[core].l2.cache[idx1].dir.I?;
                assert false;
              }
            } else {
              assert L2AddrNotInCache(c, v, core, v'.tiles[core].l2.cache[idx1].addr);
            }
          }
        } else {
          assert step.tile_step.l2_step.DirectoryStep?;
          assert core == step.tile_idx;
          assert step.tile_step.l2_step.opt_idx.val == idx1;
          
          if step.tile_step.l2_step.msg.coh_msg.PutM? {
            if DirML2CacheEntry(c, v, core, idx1) {
              assert step.tile_step.l2_step.msg.meta.src == v.tiles[core].l2.cache[idx1].dir.owner;
              // putm from owner means not loadable in any T1
              assert PutMInFlight(c, v, v.tiles[core].l2.cache[idx1].addr, step.tile_step.l2_step.msg.meta.src, Cache(core, L2), step.tile_step.l2_step.msg.coh_msg.val) by {
                reveal PutMInFlight;
              }
            } else {
              // need to consider the case where a PutM is a PutS S -> I
              assert DirSL2CacheEntry(c, v, core, idx1);
              assert v.tiles[core].l2.cache[idx1].dir.sharers - { step.tile_step.l2_step.msg.meta.src } == {};
              assert PutMInFlight(c, v, v.tiles[core].l2.cache[idx1].addr, step.tile_step.l2_step.msg.meta.src, Cache(core, L2), step.tile_step.l2_step.msg.coh_msg.val) by {
                reveal PutMInFlight;
              }
              if step.tile_step.l2_step.msg.meta.src != Cache(core, Proxy) {
                assert !(Cache(core, Proxy) in v.tiles[core].l2.cache[idx1].dir.sharers) by {
                  if Cache(core, Proxy) in v.tiles[core].l2.cache[idx1].dir.sharers {
                    assert Cache(core, Proxy) in (v.tiles[core].l2.cache[idx1].dir.sharers - {step.tile_step.l2_step.msg.meta.src});
                    assert false;
                  }
                }
              }
            }
          } else if step.tile_step.l2_step.msg.coh_msg.PutS? {
            assert v.tiles[core].l2.cache[idx1].dir.sharers - {step.tile_step.l2_step.msg.meta.src} == {};
            if step.tile_step.l2_step.msg.meta.src == Cache(core, Proxy) {
              assert PutSInFlight(c, v, v.tiles[core].l2.cache[idx1].addr, step.tile_step.l2_step.msg.meta.src, Cache(core, L2)) by {
                reveal PutSInFlight;
              }
            } else {
              assert DirSL2CacheEntry(c, v, core, idx1);
              assert !(Cache(core, Proxy) in v.tiles[core].l2.cache[idx1].dir.sharers) by {
                if Cache(core, Proxy) in v.tiles[core].l2.cache[idx1].dir.sharers {
                  assert Cache(core, Proxy) in v.tiles[core].l2.cache[idx1].dir.sharers - {step.tile_step.l2_step.msg.meta.src};
                  assert false;
                }
              }
            }
          } else {
            assert step.tile_step.l2_step.msg.coh_msg.Data?;
            assert DirSDL2CacheEntry(c, v, core, idx1);
            assert !(Cache(core, Proxy) in v.tiles[core].l2.cache[idx1].dir.sharers);
          }
        }
      }
    }
  }

  lemma OtherNoOpPreservesL2DirectoryInIMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? ==> (
      || step.tile_step.CoreStep?
      || step.tile_step.EngineStep?
      || step.tile_step.L3Step?
    )
    requires L2DirectoryInIMeansNoLoadableInProxy(c, v)
    ensures L2DirectoryInIMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirIL2CacheEntry(c, v', core, idx1)
      && idx2 < |v'.tiles[core].proxy.cache|
      && v'.tiles[core].proxy.cache[idx2].addr == v'.tiles[core].l2.cache[idx1].addr
    )
    ensures !v'.tiles[core].proxy.cache[idx2].coh.HasMostRecentVal()
    {
      assert DirIL2CacheEntry(c, v, core, idx1);
    }
  }

  lemma NoOpPreservesL2DirectoryInIMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L2DirectoryInIMeansNoLoadableInProxy(c, v)
    requires DataInFlightToT1MeansDirectoryNotInI(c, v)
    requires InvAckInFlightToT1MeansDirectoryNotInI(c, v)
    requires ProxyAddressesUnique(c, v)
    requires L2AddressesUnique(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInProxy(c, v)
    requires L1PrivateMorphAddressesAreCorrectCore(c, v)
    requires EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    requires L2CohSToMMeansL2DirSorI(c, v)
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires L2DirSharersAlwaysTier1Cache(c, v)
    requires PutMFromOwnerMeansNoLoadableInProxy(c, v)
    requires PutMInFlightMeansSourceIsEvicting(c, v)
    requires NotSharerSMeansNoLoadableInProxy(c, v)
    requires PutSFromSharerMeansNoLoadableInProxy(c, v)
    ensures L2DirectoryInIMeansNoLoadableInProxy(c, v')
  {
    if step.TileStep? {
      if step.tile_step.ProxyStep? {
        ProxyNoOpPreservesL2DirectoryInIMeansNoLoadableInProxy(c, v, v', step);
      } else if step.tile_step.L2Step? {
        L2NoOpPreservesL2DirectoryInIMeansNoLoadableInProxy(c, v, v', step);
      }
    } else {
      OtherNoOpPreservesL2DirectoryInIMeansNoLoadableInProxy(c, v, v', step);
    }
  }

  lemma StartEndCBPreservesL2DirectoryInIMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.Next(c, v, v', re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires L2DirectoryInIMeansNoLoadableInProxy(c, v)
    ensures L2DirectoryInIMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirIL2CacheEntry(c, v', core, idx1)
      && idx2 < |v'.tiles[core].proxy.cache|
      && v'.tiles[core].proxy.cache[idx2].addr == v'.tiles[core].l2.cache[idx1].addr
    )
    ensures !v'.tiles[core].proxy.cache[idx2].coh.HasMostRecentVal()
    {
      assert DirIL2CacheEntry(c, v, core, idx1);
    }
  }

  lemma PerformNextInstPreservesL2DirectoryInIMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires L2DirectoryInIMeansNoLoadableInProxy(c, v)
    ensures L2DirectoryInIMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirIL2CacheEntry(c, v', core, idx1)
      && idx2 < |v'.tiles[core].proxy.cache|
      && v'.tiles[core].proxy.cache[idx2].addr == v'.tiles[core].l2.cache[idx1].addr
    )
    ensures !v'.tiles[core].proxy.cache[idx2].coh.HasMostRecentVal()
    {
      assert DirIL2CacheEntry(c, v, core, idx1);
    }
  }
  */
}