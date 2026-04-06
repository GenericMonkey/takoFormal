include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module AddrInCacheLoadableProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened CacheTypes
  import opened EngineTypes


  lemma CoreNoOpPreservesL2AddrNotInCacheMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires L2AddrNotInCacheMeansNoLoadableInCore(c, v)
    requires DataInFlightToT1MeansDirectoryNotInI(c, v)
    ensures L2AddrNotInCacheMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, addr: Address | (
      && L2AddrNotInCache(c, v', core, addr)
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && v'.tiles[core].core.cache[idx].addr == addr
    )
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert L2AddrNotInCache(c, v, core, addr);
      if core == step.tile_idx
        && idx == step.tile_step.core_step.idx
        && step.tile_step.core_step.step.RecvMsgStep?
        && step.msgOps.recv.val.coh_msg.Data?
      {
        if step.msgOps.recv.val.coh_msg.Data? {
          assert DataInFlight(c, v, v'.tiles[core].core.cache[idx].addr, step.msgOps.recv.val.meta.src, Cache(step.tile_idx, L1), step.msgOps.recv.val.coh_msg.val) by {
            reveal DataInFlight;
          }
          assert false;
        } 
      }
    }
  }

  lemma L2NoOpPreservesL2AddrNotInCacheMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires L2AddrNotInCacheMeansNoLoadableInCore(c, v)
    requires L2DirectoryInIMeansNoLoadableInCore(c, v)
    ensures L2AddrNotInCacheMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, addr: Address | (
      && L2AddrNotInCache(c, v', core, addr)
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && v'.tiles[core].core.cache[idx].addr == addr
    )
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      if !L2AddrNotInCache(c, v, core, addr) {
        if step.tile_step.l2_step.ScheduleCallbackStep? {
          assert !step.tile_step.l2_step.eng_req.OnMiss?;
          assert DirIL2CacheEntry(c, v, core, step.tile_step.l2_step.idx);
        }
      }
    }
  }

  lemma OtherNoOpPreservesL2AddrNotInCacheMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? ==> (
      || step.tile_step.ProxyStep?
      || step.tile_step.EngineStep?
      || step.tile_step.L3Step?
    )
    requires L2AddrNotInCacheMeansNoLoadableInCore(c, v)
    ensures L2AddrNotInCacheMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, addr: Address | (
      && L2AddrNotInCache(c, v', core, addr)
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && v'.tiles[core].core.cache[idx].addr == addr
    )
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert L2AddrNotInCache(c, v, core, addr);
    }
  }

  lemma NoOpPreservesL2AddrNotInCacheMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires DataInFlightToT1MeansDirectoryNotInI(c, v)
    requires L2DirectoryInIMeansNoLoadableInCore(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInCore(c, v)
    ensures L2AddrNotInCacheMeansNoLoadableInCore(c, v')
  {
    if step.TileStep? && step.tile_step.CoreStep? {
      CoreNoOpPreservesL2AddrNotInCacheMeansNoLoadableInCore(c, v, v', step);
    } else if step.TileStep? && step.tile_step.L2Step? {
      L2NoOpPreservesL2AddrNotInCacheMeansNoLoadableInCore(c, v, v', step);
    } else {
      OtherNoOpPreservesL2AddrNotInCacheMeansNoLoadableInCore(c, v, v', step);
    }
  }

  lemma PerformNextInstPreservesL2AddrNotInCacheMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires L2AddrNotInCacheMeansNoLoadableInCore(c, v)
    ensures L2AddrNotInCacheMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, addr: Address | (
      && L2AddrNotInCache(c, v', core, addr)
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && v'.tiles[core].core.cache[idx].addr == addr
    )
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert L2AddrNotInCache(c, v, core, addr);
    }
  }

  lemma StartEndCBPreservesL2AddrNotInCacheMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires L2AddrNotInCacheMeansNoLoadableInCore(c, v)
    ensures L2AddrNotInCacheMeansNoLoadableInCore(c, v')
  {
    forall core: nat, idx: nat, addr: Address | (
      && L2AddrNotInCache(c, v', core, addr)
      && core < |v'.tiles|
      && idx < |v'.tiles[core].core.cache|
      && v'.tiles[core].core.cache[idx].addr == addr
    )
    ensures !v'.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    {
      assert L2AddrNotInCache(c, v, core, addr);
    }
  }

  lemma EngineNoOpPreservesL2AddrNotInCacheMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires L2AddrNotInCacheMeansNoLoadableInEngine(c, v)
    requires DataInFlightToT1MeansDirectoryNotInI(c, v)
    ensures L2AddrNotInCacheMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, addr: Address | (
      && L2AddrNotInCache(c, v', core, addr)
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && v'.tiles[core].engine.cache[idx].addr == addr
    )
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      assert L2AddrNotInCache(c, v, core, addr);
      if core == step.tile_idx
        && step.tile_step.eng_step.CacheCommunicationStep?
        && step.tile_step.eng_step.step.RecvMsgStep?
        && idx == step.tile_step.eng_step.c_idx
        && step.msgOps.recv.val.coh_msg.Data?
      {
        if step.msgOps.recv.val.coh_msg.Data? {
          assert DataInFlight(c, v, v'.tiles[core].engine.cache[idx].addr, step.msgOps.recv.val.meta.src, Cache(step.tile_idx, eL1), step.msgOps.recv.val.coh_msg.val) by {
            reveal DataInFlight;
          }
          assert false;
        } 
      }
    }
  }

  lemma L2NoOpPreservesL2AddrNotInCacheMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires L2AddrNotInCacheMeansNoLoadableInEngine(c, v)
    requires L2DirectoryInIMeansNoLoadableInEngine(c, v)
    ensures L2AddrNotInCacheMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, addr: Address | (
      && L2AddrNotInCache(c, v', core, addr)
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && v'.tiles[core].engine.cache[idx].addr == addr
    )
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      if !L2AddrNotInCache(c, v, core, addr) {
        if step.tile_step.l2_step.ScheduleCallbackStep? {
          assert !step.tile_step.l2_step.eng_req.OnMiss?;
          assert DirIL2CacheEntry(c, v, core, step.tile_step.l2_step.idx);
        }
      }
    }
  }

  lemma OtherNoOpPreservesL2AddrNotInCacheMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? ==> (
      || step.tile_step.ProxyStep?
      || step.tile_step.CoreStep?
      || step.tile_step.L3Step?
    )
    requires L2AddrNotInCacheMeansNoLoadableInEngine(c, v)
    ensures L2AddrNotInCacheMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, addr: Address | (
      && L2AddrNotInCache(c, v', core, addr)
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && v'.tiles[core].engine.cache[idx].addr == addr
    )
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      assert L2AddrNotInCache(c, v, core, addr);
    }
  }

  lemma NoOpPreservesL2AddrNotInCacheMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires DataInFlightToT1MeansDirectoryNotInI(c, v)
    requires L2DirectoryInIMeansNoLoadableInEngine(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInEngine(c, v)
    ensures L2AddrNotInCacheMeansNoLoadableInEngine(c, v')
  {
    if step.TileStep? && step.tile_step.EngineStep? {
      EngineNoOpPreservesL2AddrNotInCacheMeansNoLoadableInEngine(c, v, v', step);
    } else if step.TileStep? && step.tile_step.L2Step? {
      L2NoOpPreservesL2AddrNotInCacheMeansNoLoadableInEngine(c, v, v', step);
    } else {
      OtherNoOpPreservesL2AddrNotInCacheMeansNoLoadableInEngine(c, v, v', step);
    }
  }

  lemma PerformNextInstPreservesL2AddrNotInCacheMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires L2AddrNotInCacheMeansNoLoadableInEngine(c, v)
    ensures L2AddrNotInCacheMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, addr: Address | (
      && L2AddrNotInCache(c, v', core, addr)
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && v'.tiles[core].engine.cache[idx].addr == addr
    )
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      assert L2AddrNotInCache(c, v, core, addr);
    }
  }

  lemma StartEndCBPreservesL2AddrNotInCacheMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires L2AddrNotInCacheMeansNoLoadableInEngine(c, v)
    ensures L2AddrNotInCacheMeansNoLoadableInEngine(c, v')
  {
    forall core: nat, idx: nat, addr: Address | (
      && L2AddrNotInCache(c, v', core, addr)
      && core < |v'.tiles|
      && idx < |v'.tiles[core].engine.cache|
      && v'.tiles[core].engine.cache[idx].addr == addr
    )
    ensures !v'.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    {
      assert L2AddrNotInCache(c, v, core, addr);
    }
  }

  lemma ProxyNoOpPreservesL2AddrNotInCacheMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires L2AddrNotInCacheMeansNoLoadableInProxy(c, v)
    requires DataInFlightToT1MeansDirectoryNotInI(c, v)
    ensures L2AddrNotInCacheMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, addr: Address | (
      && L2AddrNotInCache(c, v', core, addr)
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && v'.tiles[core].proxy.cache[idx].addr == addr
    )
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      assert L2AddrNotInCache(c, v, core, addr);
      if core == step.tile_idx
        && idx == step.tile_step.proxy_step.idx
        && step.tile_step.proxy_step.step.RecvMsgStep?
        && step.msgOps.recv.val.coh_msg.Data?
      {
        if step.msgOps.recv.val.coh_msg.Data? {
          assert DataInFlight(c, v, v'.tiles[core].proxy.cache[idx].addr, step.msgOps.recv.val.meta.src, Cache(step.tile_idx, Proxy), step.msgOps.recv.val.coh_msg.val) by {
            reveal DataInFlight;
          }
          assert false;
        } 
      }
    }
  }

  lemma L2NoOpPreservesL2AddrNotInCacheMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires L2AddrNotInCacheMeansNoLoadableInProxy(c, v)
    requires L2DirectoryInIMeansNoLoadableInProxy(c, v)
    ensures L2AddrNotInCacheMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, addr: Address | (
      && L2AddrNotInCache(c, v', core, addr)
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && v'.tiles[core].proxy.cache[idx].addr == addr
    )
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      if !L2AddrNotInCache(c, v, core, addr) {
        if step.tile_step.l2_step.ScheduleCallbackStep? {
          assert !step.tile_step.l2_step.eng_req.OnMiss?;
          assert DirIL2CacheEntry(c, v, core, step.tile_step.l2_step.idx);
        }
      }
    }
  }

  
  lemma OtherNoOpPreservesL2AddrNotInCacheMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? ==> (
      || step.tile_step.CoreStep?
      || step.tile_step.EngineStep?
      || step.tile_step.L3Step?
    )
    requires L2AddrNotInCacheMeansNoLoadableInProxy(c, v)
    ensures L2AddrNotInCacheMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, addr: Address | (
      && L2AddrNotInCache(c, v', core, addr)
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && v'.tiles[core].proxy.cache[idx].addr == addr
    )
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      assert L2AddrNotInCache(c, v, core, addr);
    }
  }
  
  lemma NoOpPreservesL2AddrNotInCacheMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires DataInFlightToT1MeansDirectoryNotInI(c, v)
    requires L2DirectoryInIMeansNoLoadableInProxy(c, v)
    requires L2AddrNotInCacheMeansNoLoadableInProxy(c, v)
    ensures L2AddrNotInCacheMeansNoLoadableInProxy(c, v')
  {
    if step.TileStep? && step.tile_step.ProxyStep? {
      ProxyNoOpPreservesL2AddrNotInCacheMeansNoLoadableInProxy(c, v, v', step);
    } else if step.TileStep? && step.tile_step.L2Step? {
      L2NoOpPreservesL2AddrNotInCacheMeansNoLoadableInProxy(c, v, v', step);
    } else {
      OtherNoOpPreservesL2AddrNotInCacheMeansNoLoadableInProxy(c, v, v', step);
    }
  }

  lemma PerformNextInstPreservesL2AddrNotInCacheMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires L2AddrNotInCacheMeansNoLoadableInProxy(c, v)
    ensures L2AddrNotInCacheMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, addr: Address | (
      && L2AddrNotInCache(c, v', core, addr)
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && v'.tiles[core].proxy.cache[idx].addr == addr
    )
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      assert L2AddrNotInCache(c, v, core, addr);
    }
  }

  lemma StartEndCBPreservesL2AddrNotInCacheMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires L2AddrNotInCacheMeansNoLoadableInProxy(c, v)
    ensures L2AddrNotInCacheMeansNoLoadableInProxy(c, v')
  {
    forall core: nat, idx: nat, addr: Address | (
      && L2AddrNotInCache(c, v', core, addr)
      && core < |v'.tiles|
      && idx < |v'.tiles[core].proxy.cache|
      && v'.tiles[core].proxy.cache[idx].addr == addr
    )
    ensures !v'.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    {
      assert L2AddrNotInCache(c, v, core, addr);
    }
  }
}