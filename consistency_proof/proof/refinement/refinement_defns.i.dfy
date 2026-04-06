include "../../model/types.s.dfy"
include "../../model/tako_spec.i.dfy"
include "../../model/tako.i.dfy"

// This defines the functions needed to express the refinement obligation

abstract module RefinementDefns {
  import opened RefinementTypes
  import TakoSpec
  import Tako
  import opened MessageType
  import opened EngineTypes
  import opened CacheTypes

  ghost function ConstantsAbstraction(c: Tako.Constants) : TakoSpec.Constants
    requires c.WF()

  ghost function VariablesAbstraction(c: Tako.Constants, v: Tako.Variables) : TakoSpec.Variables
    requires v.WF(c)

  ghost predicate Inv(c: Tako.Constants, v: Tako.Variables)

}

// This is the module that actually implements the functions and predicates

module TakoRefinementDefns refines RefinementDefns {
  import opened Types
  import opened Execution
  import Engine

  ghost function ConstantsAbstraction(c: Tako.Constants) : TakoSpec.Constants
  // requires c.WF()
  {
    TakoSpec.Constants(p := c.program)
  }

  ghost function VariablesAbstraction(c: Tako.Constants, v: Tako.Variables) : TakoSpec.Variables
  // requires v.WF(c)
  {
    TakoSpec.Variables(epochs := v.g.callback_epochs, pcs := v.g.pcs, execution := v.g.execution)
  }

  ghost predicate InvPerfStore(c: Tako.Constants, v: Tako.Variables)
  {
    && v.WF(c)
    // invariants from perform store case
    && CoreRuntimeDataMatchesWithGhostRuntimeData(c, v)
    && UniqueTileForCallbackAddr(c, v)
    && RunningCallbackValuesAgree(c, v)
    && UniqueCurrentCallbacktoAddr(c, v)
    && CurrentCallbackIsRunning(c, v)
  }

  ghost predicate InvCorrectCore(c: Tako.Constants, v: Tako.Variables)
  {
    && v.WF(c)
    // invariants to ensure callback uniqueness
    && EachAddrInEngineIsInCorrectCore(c, v)
    && EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    && L2PrivateMorphAddressesAreCorrectCore(c, v)
    && EachAddrInCacheBoundMsgHasCorrectCore(c, v)
    && L3MorphAddressesAreCorrectCore(c, v)
    && L1PrivateMorphAddressesAreCorrectCore(c, v)
    && EL1PrivateMorphAddressesAreCorrectCore(c, v)
    && ProxyPrivateMorphAddressesAreCorrectCore(c, v)
  }

  ghost predicate InvAddressesUnique(c: Tako.Constants, v: Tako.Variables)
  {
    // invariants to ensure addresses are unique
    && L1AddressesUnique(c, v)
    && EL1AddressesUnique(c, v)
    && ProxyAddressesUnique(c, v)
    && L2AddressesUnique(c, v)
    && L3AddressesUnique(c, v)
  }

  ghost predicate InvCallbackProgress(c: Tako.Constants, v: Tako.Variables)
  {
    && v.WF(c)
    && EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    && EachAddrInEngineBoundMsgHasUniqueCB(c, v)
    && OnMissInProgressIffCacheEntryPendingPrivate(c, v)
    && ExistingCacheEntryMeansNoEvictInProgressPrivate(c, v)
    && ExistingCacheEntryMeansNoWritebackInProgressPrivate(c, v)
    && OnMissInProgressIffCacheEntryPendingShared(c, v)
    && ExistingCacheEntryMeansNoEvictInProgressShared(c, v)
    && ExistingCacheEntryMeansNoWritebackInProgressShared(c, v)
    && OnMissRequestOnlyCallbackOrResponse(c, v)
    && OnMissRequestOnlyRequestOrCallback(c, v)
    && OnMissRequestOnlyRequestOrResponse(c, v)
    && EachAddrCacheBoundMsgIsUnique(c, v)
    && UniqueCacheBoundMsgPerAddr(c, v)

    && InFlightOnMissResponseMeansNoEvictInProgress(c, v)
    && CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c, v)
    && EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c, v)

    && IdxInCBOrderTrackerIffCallbackPresent(c, v)
    && NoDupIdxsInCBOrderTracker(c, v)

    && InFlightOnMissResponseMeansNoWritebackInProgress(c, v)
    && CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c, v)
    && EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c, v)
  }

  ghost predicate InvStartCallback(c: Tako.Constants, v: Tako.Variables)
  {
    && v.WF(c)
    // invariants from start on miss, evict, wb case
    && UnstartedBufferEntryWellformed(c, v)
    && ExistingCallbackIdsHaveCorrectEpoch(c, v)
    && EpochsConsistentWithCBOrderTrackerMiss(c, v)
    && EpochsConsistentWithCBOrderTrackerEvict(c, v)
    && EpochsConsistentWithCBOrderTrackerWriteback(c, v)
  }

  ghost predicate InvEpochs(c: Tako.Constants, v: Tako.Variables)
  {
    && EachAddrInEngineBoundMsgInWorkingSet(c, v)
    && OnlyHeadOfCBOrderTrackerIsRunning(c, v)
    && MorphWorkingSetInEpochs(c, v)
    && EpochEntryInMorphWorkingSet(c, v)
    && NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c, v)
    && PendingMemMeansNonMorphAddress(c, v)
    && NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c, v)
    && UnstartedEvictionInEngineMeansInEpoch(c, v)
  }

  ghost predicate InvDirtyBit(c: Tako.Constants, v: Tako.Variables)
  {
    && L2DirtyBitTracksInterveningWrite(c, v)
    && L3DirtyBitTracksInterveningWrite(c, v)

    && InFlightOnEvictRequestHasNoInterveningWrite(c, v)
    && InFlightOnWritebackRequestHasInterveningWrite(c, v)
    
    && PutMFromOwnerL2MeansInterveningWrite(c, v) // XD
    && DataFromOwnerL2MeansInterveningWrite(c, v) // XD
    && PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v) // XD
    && DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c, v) // XD

    && PutMFromOwnerL3MeansInterveningWrite(c, v)
    && DataFromOwnerL3MeansInterveningWrite(c, v)

    && DirtyMorphAddressMeansInterveningWriteCore(c, v)    // XD
    && DirtyMorphAddressMeansInterveningWriteEngine(c, v)  // XD
    && LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c, v)  // XD
    && MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c, v) // XD
    && MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c, v) // XD
    && MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c, v) // XD
    && MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c, v)

    && MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c, v) // XD
    && MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c, v) // XD
    && MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c, v) // XD
    && MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c, v) // XD
    
    && PreMStateMeansNotDirtyCore(c, v)               // XD
    && PreMStateMeansNotDirtyEngine(c, v)           // XD 
    && PreMStateMeansNotDirtyL2(c, v)               // XD

    && OnMissResponseMeansInEpochWithNoWrite(c, v)        // XD
    && DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c, v)
    && FwdGetSInFlightFromProxyMeansDirtyBitSet(c, v)
    && FwdGetMInFlightFromProxyMeansDirtyBitSet(c, v)
  }

  ghost predicate InvCoherenceState(c: Tako.Constants, v: Tako.Variables)
  {
    && InFlightOnEvictRequestMatchesLastWrite(c, v)
    && InFlightOnWritebackRequestMatchesLastWrite(c, v)
    
    && L2DirISMatchesLastWrite(c, v)                        // Assumption
    && L3DirISMatchesLastWrite(c, v)                        // Assumption

    && CoreLoadableMatchesLastWriteMorph(c, v)                   // Assumption
    && EngineLoadableMatchesLastWriteMorph(c, v)                 // Assumption
    
    && CoreLoadableMatchesLastWriteRegular(c, v)                 // Assumption
    && EngineLoadableMatchesLastWriteRegular(c, v)               // Assumption


    && OnEvictInProgressMeansNoLoadableInCore(c, v)
    && OnEvictInProgressMeansNoLoadableInEngine(c, v)
    && OnEvictInProgressMeansNoLoadableInProxy(c, v)

    && OnWritebackInProgressMeansNoLoadableInCore(c, v)
    && OnWritebackInProgressMeansNoLoadableInEngine(c, v)
    && OnWritebackInProgressMeansNoLoadableInProxy(c, v)

    && L2DirectoryInIMeansNoLoadableInCore(c, v)             // Assumption
    && L2DirectoryInIMeansNoLoadableInEngine(c, v)           // Assumption
    && L2DirectoryInIMeansNoLoadableInProxy(c, v)            // Assumption
  
    && L2DirectoryInSMeansNoMInCore(c, v)                    // Assumption
    && L2DirectoryInSMeansNoMInEngine(c, v)                  // Assumption
    && L3DirectoryInSMeansNoMInL2(c, v)                      // Assumption

    && L2DirectoryInSDAndMInCoreMeansFormerOwner(c, v)       // Assumption
    && L2DirectoryInSDAndMInEngineMeansFormerOwner(c, v)     // Assumption
  
    && L2DirectoryInMAndMInCoreMeansOwnerOrFwdGetMInFlight(c, v)   // Assumption
    && L2DirectoryInMAndMInEngineMeansOwnerOrFwdGetMInFlight(c, v) // Assumption

    && L2AddrNotInCacheMeansNoLoadableInCore(c, v)
    && L2AddrNotInCacheMeansNoLoadableInEngine(c, v)
    && L2AddrNotInCacheMeansNoLoadableInProxy(c, v)

    && L3AddrNotInCacheMeansL2AddrNotInCache(c, v)           // Assumption
    && L3DirectoryInIMeansL2AddrNotInCache(c, v)             // Assumption
    
    && L1InCohMMeansAddrNotInOtherL1s(c, v)                  // Assumption
    && EL1InCohMMeansAddrNotInOtherL1s(c, v)                 // Assumption
    && L2InCohMMeansAddrNotInOtherL2s(c, v)                  // Assumption

    && L1InCohMMeansNoT1DataInFlight(c, v)                   // Assumption
    && EL1InCohMMeansNoT1DataInFlight(c, v)                  // Assumption

    && MInCoreMeansMinL2(c, v)                               // Assumption
    && MInEngineMeansMinL2(c, v)                             // Assumption

    && L2DirMorSDMeansL2CohM(c, v)    // XD
    && L2NotDirIMeansLoadableCoh(c, v) //XD
    && PrivateMorphInL2IsCohM(c, v) 

  }

  ghost predicate InvWFMessages(c: Tako.Constants, v: Tako.Variables)
  {
    && v.WF(c)
    && L2QueueHeadsWellformed(c, v)
    && L3QueueHeadsWellformed(c, v)
    && MemMessagesWellformed(c, v)
  
    && L3DirOwnerIsAlwaysTier2Cache(c, v)
    && L3DirSharersAlwaysTier2Cache(c, v)
    && L2DirOwnerIsAlwaysTier1Cache(c, v)
    && L2DirSharersAlwaysTier1Cache(c, v)

    && AllFwdReqsToTier1HasTier1Source(c, v)
    && AllFwdReqsToTier2HasTier2Source(c, v)
    && AllFwdReqsFromTier1HasTier1Dst(c, v)
    && AllReqsToTier2HasTier1Source(c, v)
    && AllReqsToTier3HasTier2Source(c, v)
    && AllPutAcksToTier2HasTier3Source(c, v)
    && AllDataToTier2FromCache(c, v)
    && AllDataToTier3FromTier2Cache(c, v)
  }
  
  ghost predicate InvCoherenceMessages(c: Tako.Constants, v: Tako.Variables)
  {
  //   // Merge?
    && PutMFromOwnerMeansNoLoadableInCore(c, v)             // Assumption
    && PutMFromOwnerMeansNoLoadableInEngine(c, v)           // Assumption
  //   && PutMFromOwnerMeansNoLoadableInProxy(c, v)

  //   // Merge?
  //   && PutSFromSharerMeansNoLoadableInCore(c, v)
  //   && PutSFromSharerMeansNoLoadableInEngine(c, v)
  //   && PutSFromSharerMeansNoLoadableInProxy(c, v)

  //   && DataInFlightToT1AndDirectorySSDMeansDstIsSharer(c, v)

    && PutMInFlightMeansSourceIsEvicting(c, v)              // Assumption
  //   && PutSInFlightMeansSourceIsEvicting(c, v)
    && GetMInFlightMeansSourceIsTransitioningToM(c, v)      // Assumption
    && FwdGetMInFlightToT1MeansSourceIsTransitioningToM(c, v) // might be easy?
    && GetSInFlightToT2MeansSourceIsTransitioningToS(c, v)  // Assumption
    && FwdGetSInFlightToT1MeansSourceIsTransitioningToS(c, v) // might be easy?
    && FwdGetSInFlightMeansDirectoryIsSD(c, v) // might be easy?
    && FwdGetSInFlightMeansSrcDstDifferent(c, v)


    && DataInFlightToT1MeansDirectoryNotInI(c, v)           // Assumption
  //   && InvAckInFlightToT1MeansDirectoryNotInI(c, v)

    && DataInFlightToT2FromT1MeansDirectoryInSD(c, v)       // Assumption
    && DataInFlightToT3FromT2MeansDirectoryInSD(c, v)       // Assumption

    && NoGetSAndReturningData(c, v)                     // Assumption
    && NoGetMAndReturningData(c, v)                     // Assumption

    && NoGetsAndDirML2(c, v)                            // Assumption
  }

  ghost predicate InvPerfLoad(c: Tako.Constants, v: Tako.Variables)
  {
    && AddrInEpochMeansEventsWellformed(c, v)
    && AddrInEpochMeansEventsMatchAddrAtomicity(c, v)
    && WritesToAddrWellFormed(c, v)
    && AllWritesInWritesToAddr(c, v)
    && MoDeterminedByWritesToAddrOrder(c, v)
    && AllMoInWritesToAddr(c, v)
    && AllWritesToAddrLessThanCurrentPCCore(c, v)
    && AllWritesToAddrLessThanCurrentPCEngine(c, v)
    && WritesToAddrHaveValidThreadIds(c, v)
  }

  ghost predicate Inv(c: Tako.Constants, v: Tako.Variables)
  {
    && InvAddressesUnique(c, v)
    && InvPerfLoad(c, v)
    && InvPerfStore(c, v)
    && InvCorrectCore(c, v)
    && InvCallbackProgress(c, v)
    && InvStartCallback(c, v)
    && InvEpochs(c, v)
    && InvDirtyBit(c, v)
    && InvWFMessages(c, v)
    && InvCoherenceState(c, v)
    && InvCoherenceMessages(c, v)
    // && Inv5(c, v)
    // && InvCoherenceTier1Messages(c, v)
    // && InvCoherenceTier1State(c, v)
    // && InvCoherenceTier2State(c, v)
  }

  ghost predicate ValidSpecCoreId(c: Tako.Constants, v: Tako.Variables, id: ThreadId)
  {
    id.CoreId? && id in v.g.pcs
  }

  ghost predicate ThreadIdMatchesCoreId(c: Tako.Constants, v: Tako.Variables, id: ThreadId)
    requires ValidSpecCoreId(c, v, id)
  {
    && id.id < |v.tiles| 
    && v.g.pcs[id].pc == PC(v.tiles[id.id].core.pc, v.tiles[id.id].core.count)
    && v.g.pcs[id].regs == v.tiles[id.id].core.regs
    && v.g.pcs[id].vals == seq(
      |v.tiles[id.id].core.results|,
      (i: nat)
        requires i < |v.tiles[id.id].core.results|
      => (
        v.tiles[id.id].core.results[i].1
      )
    )
  }

  ghost predicate CoreRuntimeDataMatchesWithGhostRuntimeData(c: Tako.Constants, v: Tako.Variables)
  {
    forall id: ThreadId | ValidSpecCoreId(c, v, id) :: (
      ThreadIdMatchesCoreId(c, v, id)
    )
  }

  ghost predicate SpecCallbackId(c: Tako.Constants, v: Tako.Variables, id: ThreadId)
  {
    && id.CallbackId?
    && id in v.g.pcs
  }

  ghost predicate CurrentSpecCallbackId(c: Tako.Constants, v: Tako.Variables, id: ThreadId)
  {
    && SpecCallbackId(c, v, id)
    && !v.g.pcs[id].pc.End?
  }

  ghost predicate ValuesMatchForCallbackId(c: Tako.Constants, v: Tako.Variables, data: RuntimeData, tile: nat, buf: nat)
    requires IsBufferEntry(c, v, tile, buf)
  {
    && data.pc == PC(v.tiles[tile].engine.buffer[buf].pc, v.tiles[tile].engine.buffer[buf].count)
    && data.regs == v.tiles[tile].engine.buffer[buf].regs
    && data.vals == v.tiles[tile].engine.buffer[buf].values
  }

  ghost predicate CallbackRunningInBufferLocation(c: Tako.Constants, v: Tako.Variables, addr: Address, cb: CallbackType, tile: nat, buf: nat)
  {
    && CallbackPresentInBufferLocation(c, v, addr, cb, tile, buf)
    && v.tiles[tile].engine.buffer[buf].started
  }

  ghost predicate CallbackPresentInBufferLocation(c: Tako.Constants, v: Tako.Variables, addr: Address, cb: CallbackType, tile: nat, buf: nat)
  {
    && IsBufferEntry(c, v, tile, buf)
    && v.tiles[tile].engine.buffer[buf].addr == addr
    && EngReqToCBType(v.tiles[tile].engine.buffer[buf].cb_type) == cb
  }

  ghost predicate IsBufferEntry(c: Tako.Constants, v: Tako.Variables, tile: nat, buf: nat)
  {
    && tile < |v.tiles|
    && buf < |v.tiles[tile].engine.buffer|
    && v.tiles[tile].engine.buffer[buf].BufferEntry?
  }

  ghost predicate RunningCallbackValuesAgree(c: Tako.Constants, v: Tako.Variables)
    requires v.WF(c)
  {
    forall addr, cb, tile: nat, buf | CallbackRunningInBufferLocation(c, v, addr, cb, tile, buf) :: (
      && addr in v.g.callback_epochs
      && var id := CallbackId(addr, cb, v.g.callback_epochs[addr].epoch);
      && CurrentSpecCallbackId(c, v, id)
      && Engine.IsNextCallback(c.tiles[tile].engine, v.tiles[tile].engine, buf)
      && ValuesMatchForCallbackId(c, v, v.g.pcs[id], tile, buf)
    )
  }

  ghost opaque predicate CallbackPresent(c: Tako.Constants, v: Tako.Variables, addr: Address, e: EngineRequest)
  {
    exists tile: nat, buf: nat :: (
      && CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf)
      && v.tiles[tile].engine.buffer[buf].cb_type == e
    )
  }

  ghost opaque predicate UnstartedCallbackPresent(c: Tako.Constants, v: Tako.Variables, addr: Address, e: EngineRequest)
  {
    exists tile: nat, buf: nat :: (
      && CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, buf)
      && v.tiles[tile].engine.buffer[buf].cb_type == e
      && !v.tiles[tile].engine.buffer[buf].started
    )
  }

  ghost opaque predicate CallbackRunning(c: Tako.Constants, v: Tako.Variables, addr: Address, cb: CallbackType)
  {
    exists tile, buf :: (CallbackRunningInBufferLocation(c, v, addr, cb, tile, buf))
  }

  ghost predicate UniqueCurrentCallbacktoAddr(c: Tako.Constants, v: Tako.Variables)
  {
    forall id: ThreadId | CurrentSpecCallbackId(c, v, id) :: (
      && id.addr in v.g.callback_epochs
      && id.count == v.g.callback_epochs[id.addr].epoch
      && (v.g.callback_epochs[id.addr].Miss? || v.g.callback_epochs[id.addr].Evict?)
      && (v.g.callback_epochs[id.addr].Miss? ==> id.cb.OnMiss?)
      && (v.g.callback_epochs[id.addr].Evict? && !v.g.callback_epochs[id.addr].dirty ==> id.cb.OnEvict?)
      && (v.g.callback_epochs[id.addr].Evict? && v.g.callback_epochs[id.addr].dirty ==> id.cb.OnWriteBack?)
    )
  }

  ghost predicate CurrentCallbackIsRunning(c: Tako.Constants, v: Tako.Variables)
  {
    forall id: ThreadId | CurrentSpecCallbackId(c, v, id) ::
      && CallbackRunning(c, v, id.addr, id.cb)
  }

  ghost predicate UniqueTileForCallbackAddr(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address, cb1: CallbackType, cb2: CallbackType, t1: nat, t2: nat, b1: nat, b2: nat | (
      && CallbackPresentInBufferLocation(c, v, addr, cb1, t1, b1) 
      && CallbackPresentInBufferLocation(c, v, addr, cb2, t2, b2)
    ) :: (
      && t1 == t2
      && (cb1 == cb2 ==> b1 == b2)
      && !(cb1.OnEvict? && cb2.OnWriteBack?)
    )
  }

  ghost predicate WritesToAddrWellFormed(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address, idx : nat | (
      && addr in v.g.writes_to_addr
      && idx < |v.g.writes_to_addr[addr]|
    ) :: (
      && v.g.writes_to_addr[addr][idx] in v.g.execution.pre.events
      && v.g.writes_to_addr[addr][idx].addr == addr
      && v.g.writes_to_addr[addr][idx].RegWrite()
      && (v.g.writes_to_addr[addr][idx].W? ==> (
        || !addr.atomic 
        || (
          && v.g.writes_to_addr[addr][idx].val == Just(0)
          && v.g.writes_to_addr[addr][idx].info.id == Initial()
        )
      ))
      && (v.g.writes_to_addr[addr][idx].RMW? ==> addr.atomic)
    )
  }

  ghost predicate AllWritesInWritesToAddr(c: Tako.Constants, v: Tako.Variables)
  {
    forall w: Event | (
      && w in v.g.execution.pre.events
      && w.RegWrite()
    ) :: (
      && w.addr in v.g.writes_to_addr
      && w in v.g.writes_to_addr[w.addr]
    )
  }

  ghost predicate AllMoInWritesToAddr(c: Tako.Constants, v: Tako.Variables)
  {
    forall w1: Event, w2: Event | (
      && w1.RegWrite()
      && w2.RegWrite()
      && (w1, w2) in v.g.execution.wit.mo
    ) :: (
      && w1.addr == w2.addr
      && w1.addr in v.g.writes_to_addr
      && w1 in v.g.writes_to_addr[w1.addr]
      && w2 in v.g.writes_to_addr[w2.addr]
    )
  }

  ghost predicate WritesToAddrHaveValidThreadIds(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address, idx : nat | (
      && addr in v.g.writes_to_addr
      && idx < |v.g.writes_to_addr[addr]|
      && v.g.writes_to_addr[addr][idx].info.id.CallbackId?
    ) :: (
      && SpecCallbackId(c, v, v.g.writes_to_addr[addr][idx].info.id)
    )
  }

  ghost predicate AllWritesToAddrLessThanCurrentPCCore(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address, idx: nat, core: nat | (
      && core < |v.tiles|
      && addr in v.g.writes_to_addr
      && idx < |v.g.writes_to_addr[addr]|
      && v.g.writes_to_addr[addr][idx].info.id == CoreId(core)
    ) :: (
      && v.g.writes_to_addr[addr][idx].info.pc.less_than(
        PC(v.tiles[core].core.pc, v.tiles[core].core.count)
      )
    )
  }

  ghost predicate AllWritesToAddrLessThanCurrentPCEngine(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address, idx: nat, id: ThreadId, tile: nat, buf: nat | (
      && addr in v.g.writes_to_addr
      && idx < |v.g.writes_to_addr[addr]|
      && CurrentSpecCallbackId(c, v, id)
      && CallbackRunningInBufferLocation(c, v, id.addr, id.cb, tile, buf)
      && v.g.writes_to_addr[addr][idx].info.id == id
    ) :: (
      && v.g.writes_to_addr[addr][idx].info.pc.less_than(
        PC(v.tiles[tile].engine.buffer[buf].pc, v.tiles[tile].engine.buffer[buf].count)
      )
    )
  }

  ghost predicate MoDeterminedByWritesToAddrOrder(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address, idx1 : nat, idx2: nat | (
      && addr in v.g.writes_to_addr
      && idx1 < |v.g.writes_to_addr[addr]|
      && idx2 < |v.g.writes_to_addr[addr]|
    ) :: (
      (idx1 < idx2)
      <==>
      ((v.g.writes_to_addr[addr][idx1], v.g.writes_to_addr[addr][idx2]) in v.g.execution.wit.mo)
    )
  }

  ghost predicate InFlightEngineRequest(c: Tako.Constants, v: Tako.Variables, addr: Address, idx: nat)
  {
    
    && addr in v.network.inFlightEngReqs 
    && idx < |v.network.inFlightEngReqs[addr]|
    && v.network.inFlightEngReqs[addr][idx].EngineRequest? // redundant (only engine requests in this map)
  }

  ghost predicate InFlightEngineResponse(c: Tako.Constants, v: Tako.Variables, msg: Message)
  {
    
    && msg in v.network.inFlightMessages 
    && msg.EngineResponse?
  }

  // ghost predicate InFlightMemoryResponse(c: Tako.Constants, v: Tako.Variables, msg: Message)
  // {
  //   
  //   && msg in v.network.inFlightMessages 
  //   && msg.CoherenceMsg?
  //   && msg.meta.src == Mem()
  // }

  ghost predicate AddrLocIsCorrect(c: Tako.Constants, v: Tako.Variables, addr: Address, loc: Location)
    requires loc.Cache?
  {
    && addr.Morph?
    && (addr.morphType.Private? ==> (
      && addr.morphType.idx == loc.core
      && loc.level == L2
    ))
    && (addr.morphType.Shared? ==> (
      && c.addr_map(addr) == loc.core
      && loc.level == L3
    ))
  }


  ghost predicate EachAddrInEngineIsInCorrectCore(c: Tako.Constants, v: Tako.Variables)
  {
    forall tile: nat, buf : nat | IsBufferEntry(c, v, tile, buf) :: (
      && v.tiles[tile].engine.buffer[buf].req_loc.Cache?
      && v.tiles[tile].engine.buffer[buf].req_loc.core == tile
      && AddrLocIsCorrect(c, v, v.tiles[tile].engine.buffer[buf].addr, v.tiles[tile].engine.buffer[buf].req_loc)
    )
  }

  ghost predicate EachAddrInEngineBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr, idx: nat | InFlightEngineRequest(c, v, addr, idx) :: (
      && var msg := v.network.inFlightEngReqs[addr][idx];
      && msg.meta.dst.Engine?
      && msg.meta.src.Cache?
      && msg.meta.addr == addr
      && msg.meta.dst.core == msg.meta.src.core
      && msg.meta.dst.core < |c.tiles|
      && AddrLocIsCorrect(c, v, msg.meta.addr, msg.meta.src)
    )
  }

  ghost predicate EachAddrInCacheBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables)
  {
    forall msg | InFlightEngineResponse(c, v, msg) :: (
      && msg.meta.src.Engine?
      && msg.meta.dst.Cache?
      && msg.meta.dst.core == msg.meta.src.core
      && msg.meta.dst.core < |c.tiles|
      && AddrLocIsCorrect(c, v, msg.meta.addr, msg.meta.dst)
    )
  }

  ghost predicate L1PrivateMorphAddressesAreCorrectCore(c: Tako.Constants, v: Tako.Variables)
    requires v.WF(c)
  {
    && (forall core: nat, idx: nat | (
        && NonEmptyL1CacheEntry(c, v, core, idx)
        && PrivateMorph(v.tiles[core].core.cache[idx].addr)
    ) :: (
      && v.tiles[core].core.cache[idx].addr.morphType.idx == core
      && v.tiles[core].core.cache[idx].addr in c.program.WorkingSet()
    ))
  }

  ghost predicate EL1PrivateMorphAddressesAreCorrectCore(c: Tako.Constants, v: Tako.Variables)
    requires v.WF(c)
  {
    && (forall core: nat, idx: nat | (
        && NonEmptyEL1CacheEntry(c, v, core, idx)
        && PrivateMorph(v.tiles[core].engine.cache[idx].addr)
    ) :: (
      && v.tiles[core].engine.cache[idx].addr.morphType.idx == core
      && v.tiles[core].engine.cache[idx].addr in c.program.WorkingSet()
    ))
  }

  ghost predicate ProxyPrivateMorphAddressesAreCorrectCore(c: Tako.Constants, v: Tako.Variables)
    requires v.WF(c)
  {
    && (forall core: nat, idx: nat | (
        && NonEmptyProxyCacheEntry(c, v, core, idx)
        && PrivateMorph(v.tiles[core].proxy.cache[idx].addr)
    ) :: (
      && v.tiles[core].proxy.cache[idx].addr.morphType.idx == core
      && v.tiles[core].proxy.cache[idx].addr in c.program.WorkingSet()
    ))
  }

  // its only the pending CB addrs, we can borrow shared morphs from cache comms
  ghost predicate L2PrivateMorphAddressesAreCorrectCore(c: Tako.Constants, v: Tako.Variables)
    requires v.WF(c)
  {
    && (forall core: nat, idx: nat | (
        && NonEmptyL2CacheEntry(c, v, core, idx)
        && PrivateMorph(v.tiles[core].l2.cache[idx].addr)
    ) :: (
      && v.tiles[core].l2.cache[idx].addr.morphType.idx == core
      && v.tiles[core].l2.cache[idx].addr in c.program.WorkingSet()
    ))
  }

  ghost predicate L3MorphAddressesAreCorrectCore(c: Tako.Constants, v: Tako.Variables)
    requires v.WF(c)
  {
    && (forall core: nat, idx: nat | (
        && NonEmptyL3CacheEntry(c, v, core, idx)
        && v.tiles[core].l3.cache[idx].addr.Morph?
    ) :: (
      && v.tiles[core].l3.cache[idx].addr.morphType.Shared?
      && c.addr_map(v.tiles[core].l3.cache[idx].addr) == core
      && v.tiles[core].l3.cache[idx].addr in c.program.WorkingSet()
    ))
  }

  ghost predicate EngReqsInNetworkAreDiffThanCurrentCallbacks(c: Tako.Constants, v: Tako.Variables)
  {
    forall tile: nat, buf : nat, idx: nat | (
      && IsBufferEntry(c, v, tile, buf) 
      && InFlightEngineRequest(c, v, v.tiles[tile].engine.buffer[buf].addr, idx) 
    ) :: (
      && var msg := v.network.inFlightEngReqs[v.tiles[tile].engine.buffer[buf].addr][idx];
      && !(msg.engine_req.OnMiss? && v.tiles[tile].engine.buffer[buf].cb_type.OnMiss?)
      && !(msg.engine_req.OnEvict? && v.tiles[tile].engine.buffer[buf].cb_type.OnEvict?)
      && !(msg.engine_req.OnEvict? && v.tiles[tile].engine.buffer[buf].cb_type.OnWriteBack?)
      && !(msg.engine_req.OnWriteBack? && v.tiles[tile].engine.buffer[buf].cb_type.OnWriteBack?)
      && !(msg.engine_req.OnWriteBack? && v.tiles[tile].engine.buffer[buf].cb_type.OnEvict?)
    )
  }

  // assumptions for InvCallbackProgress

  ghost predicate EachAddrInEngineBoundMsgHasUniqueCB(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr, idx1: nat, idx2: nat | InFlightEngineRequest(c, v, addr, idx1) && InFlightEngineRequest(c, v, addr, idx2) :: (
      && var msg1 := v.network.inFlightEngReqs[addr][idx1];
      && var msg2 := v.network.inFlightEngReqs[addr][idx2];
      && ((msg1.engine_req.OnMiss? && msg2.engine_req.OnMiss?) ==> idx1 == idx2)
      && ((msg1.engine_req.OnEvict? && msg2.engine_req.OnEvict?) ==> idx1 == idx2)
      && ((msg1.engine_req.OnWriteBack? && msg2.engine_req.OnWriteBack?) ==> idx1 == idx2)
      && !(msg1.engine_req.OnWriteBack? && msg2.engine_req.OnEvict?)
    )
  }

  ghost predicate UniqueCacheBoundMsgPerAddr(c: Tako.Constants, v: Tako.Variables)
  {
    forall msg1, msg2 | InFlightEngineResponse(c, v, msg1) && InFlightEngineResponse(c, v, msg2) 
      && msg1.meta.addr == msg2.meta.addr :: (
      msg1 == msg2
    )
  }

  ghost predicate EachAddrCacheBoundMsgIsUnique(c: Tako.Constants, v: Tako.Variables)
  {
    forall msg | InFlightEngineResponse(c, v, msg) :: (
      v.network.inFlightMessages[msg] == 1
    )
  }

  ghost predicate IsInFlightOnMissRequest(c: Tako.Constants, v: Tako.Variables, addr: Address, idx: nat, c_idx: nat)
  {
    && InFlightEngineRequest(c, v, addr, idx)
    && var msg := v.network.inFlightEngReqs[addr][idx];
    && msg.engine_req == EngineRequest.OnMiss(c_idx)
  }

  ghost predicate IsInFlightOnEvictRequest(c: Tako.Constants, v: Tako.Variables, addr: Address, idx: nat, val: Value)
  {
    && InFlightEngineRequest(c, v, addr, idx)
    && var msg := v.network.inFlightEngReqs[addr][idx];
    && msg.engine_req == EngineRequest.OnEvict(val)
  }

  ghost predicate IsInFlightOnWritebackRequest(c: Tako.Constants, v: Tako.Variables, addr: Address, idx: nat, val: Value)
  {
    && InFlightEngineRequest(c, v, addr, idx)
    && var msg := v.network.inFlightEngReqs[addr][idx];
    && msg.engine_req == EngineRequest.OnWriteBack(val)
  }

  ghost predicate IsInFlightOnMissResponse(c: Tako.Constants, v: Tako.Variables, addr: Address, msg: Message, c_idx: nat)
  {
    && InFlightEngineResponse(c, v, msg)
    && msg.engine_resp.idx == c_idx
    && msg.meta.addr == addr
  }

  ghost opaque predicate InFlightOnMissRequest(c: Tako.Constants, v: Tako.Variables, addr: Address, c_idx: nat)
  {
    && (exists idx :: IsInFlightOnMissRequest(c, v, addr, idx, c_idx))
  }

  ghost opaque predicate InFlightOnEvictRequest(c: Tako.Constants, v: Tako.Variables, addr: Address, val: Value)
  {
    && (exists idx :: IsInFlightOnEvictRequest(c, v, addr, idx, val))
  }

  ghost opaque predicate InFlightOnWritebackRequest(c: Tako.Constants, v: Tako.Variables, addr: Address, val: Value)
  {
    && (exists idx :: IsInFlightOnWritebackRequest(c, v, addr, idx, val))
  }

  ghost opaque predicate InFlightOnMissResponse(c: Tako.Constants, v: Tako.Variables, addr: Address, c_idx: nat)
  {
    && (exists msg :: IsInFlightOnMissResponse(c, v, addr, msg, c_idx))
  }

  ghost predicate OnMissInProgress(c: Tako.Constants, v: Tako.Variables, addr: Address, c_idx: nat)
  {
    || InFlightOnMissRequest(c, v, addr, c_idx)
    || CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx))
    || InFlightOnMissResponse(c, v, addr, c_idx)
  }

  ghost predicate OnEvictInProgress(c: Tako.Constants, v: Tako.Variables, addr: Address, val: Value)
  {
    || InFlightOnEvictRequest(c, v, addr, val)
    || CallbackPresent(c, v, addr, EngineRequest.OnEvict(val))
  }

  ghost predicate OnWritebackInProgress(c: Tako.Constants, v: Tako.Variables, addr: Address, val: Value)
  {
    || InFlightOnWritebackRequest(c, v, addr, val)
    || CallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val))
  }

  ghost predicate PrivateMorph(addr: Address)
  {
    addr.Morph? && addr.morphType.Private?
  }

  ghost predicate SharedMorph(addr: Address)
  {
    addr.Morph? && addr.morphType.Shared?
  }
  // Private address request location invariants

  ghost opaque predicate L2PendingCallbackForAddr(c: Tako.Constants, v: Tako.Variables, addr: Address, c_idx: nat)
    requires PrivateMorph(addr)
  {
    && addr.morphType.idx < |v.tiles|
    && c_idx < |v.tiles[addr.morphType.idx].l2.cache|
    && v.tiles[addr.morphType.idx].l2.cache[c_idx].addr == addr
    && v.tiles[addr.morphType.idx].l2.cache[c_idx].PendingCB?
  }

  ghost predicate OnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables)
  {
    && FwdOnMissInProgressIffCacheEntryPendingPrivate(c, v)
    && RevOnMissInProgressIffCacheEntryPendingPrivate(c, v)
  }
  
  ghost predicate FwdOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && OnMissInProgress(c, v, addr, c_idx) :: (
      L2PendingCallbackForAddr(c, v, addr, c_idx)
    )
  }

  ghost predicate RevOnMissInProgressIffCacheEntryPendingPrivate(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address, c_idx: nat | PrivateMorph(addr) && L2PendingCallbackForAddr(c, v, addr, c_idx) :: (
      OnMissInProgress(c, v, addr, c_idx)
    )
  }

  ghost predicate ExistingCacheEntryMeansNoEvictInProgressPrivate(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, c_idx: nat, val: Value | (
      && NonEmptyL2CacheEntry(c, v, core, c_idx) 
      && !v.tiles[core].l2.cache[c_idx].PendingCB?
      && PrivateMorph(v.tiles[core].l2.cache[c_idx].addr)
    ) :: (
      !OnEvictInProgress(c, v, v.tiles[core].l2.cache[c_idx].addr, val)
    )
  }

  ghost predicate InFlightOnMissResponseMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr, c_idx, val | (
      InFlightOnMissResponse(c, v, addr, c_idx)
    ) :: (
      !OnEvictInProgress(c, v, addr, val)
    )
  }

  ghost predicate InFlightOnMissResponseMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr, c_idx, val | (
      InFlightOnMissResponse(c, v, addr, c_idx)
    ) :: (
      !OnWritebackInProgress(c, v, addr, val)
    )
  }

  ghost predicate ExistingCacheEntryMeansNoWritebackInProgressPrivate(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL2CacheEntry(c, v, core, idx)
      && !v.tiles[core].l2.cache[idx].PendingCB?
      && PrivateMorph(v.tiles[core].l2.cache[idx].addr)
    ) :: (
      !OnWritebackInProgress(c, v, v.tiles[core].l2.cache[idx].addr, val)
    )
  }

  // Shared address request location invariants
  ghost opaque predicate L3PendingCallbackForAddr(c: Tako.Constants, v: Tako.Variables, addr: Address, c_idx: nat)
    requires SharedMorph(addr)
  {
    && c.addr_map(addr) < |v.tiles|
    && c_idx < |v.tiles[c.addr_map(addr)].l3.cache|
    && v.tiles[c.addr_map(addr)].l3.cache[c_idx].PendingCB?
    && v.tiles[c.addr_map(addr)].l3.cache[c_idx].addr == addr
  }
  
  ghost predicate OnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables)
  {
    && FwdOnMissInProgressIffCacheEntryPendingShared(c, v)
    && RevOnMissInProgressIffCacheEntryPendingShared(c, v)
  }

  ghost predicate FwdOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && OnMissInProgress(c, v, addr, c_idx) :: (
      L3PendingCallbackForAddr(c, v, addr, c_idx)
    )
  }

  ghost predicate RevOnMissInProgressIffCacheEntryPendingShared(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address, c_idx: nat | SharedMorph(addr) && L3PendingCallbackForAddr(c, v, addr, c_idx) :: (
      OnMissInProgress(c, v, addr, c_idx)
    )
  }

  ghost predicate ExistingCacheEntryMeansNoEvictInProgressShared(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v, core, idx) 
      && !v.tiles[core].l3.cache[idx].PendingCB? 
      && SharedMorph(v.tiles[core].l3.cache[idx].addr)
    ) :: (
      !OnEvictInProgress(c, v, v.tiles[core].l3.cache[idx].addr, val)
    )
  }

  ghost predicate ExistingCacheEntryMeansNoWritebackInProgressShared(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, val: Value | (
      && NonEmptyL3CacheEntry(c, v, core, idx)
      && !v.tiles[core].l3.cache[idx].PendingCB? 
      && SharedMorph(v.tiles[core].l3.cache[idx].addr)
    ) :: (
      !OnWritebackInProgress(c, v, v.tiles[core].l3.cache[idx].addr, val)
    )
  }

  ghost predicate OnMissRequestOnlyRequestOrCallback(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address, c_idx: nat :: (
      && !(InFlightOnMissRequest(c, v, addr, c_idx) && CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)))
    )
  }
  
  ghost predicate OnMissRequestOnlyRequestOrResponse(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address, c_idx: nat :: (
      && !(InFlightOnMissRequest(c, v, addr, c_idx) && InFlightOnMissResponse(c, v, addr, c_idx))
    )
  }

  ghost predicate OnMissRequestOnlyCallbackOrResponse(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address, c_idx: nat :: (
      && !(CallbackPresent(c, v, addr, EngineRequest.OnMiss(c_idx)) && InFlightOnMissResponse(c, v, addr, c_idx))
    )
  }
  
  ghost predicate AddrInTileCBOrderTracker(c: Tako.Constants, v: Tako.Variables, addr: Address, tile: nat)
  {
    && tile < |v.tiles|
    && addr in v.tiles[tile].engine.cb_order
  }

  ghost predicate CBOrderTrackerValidIndex(c: Tako.Constants, v: Tako.Variables, addr: Address, tile: nat, o_idx: nat)
  {
    && AddrInTileCBOrderTracker(c, v, addr, tile)
    && o_idx < |v.tiles[tile].engine.cb_order[addr]|
  }

  ghost predicate CBOrderTrackerIndexIsRequest(c: Tako.Constants, v: Tako.Variables, addr: Address, o_idx: nat, e: EngineRequest)
  {
    && addr.Morph?
    && var tile := if addr.morphType.Private? then addr.morphType.idx else c.addr_map(addr);
    && CBOrderTrackerValidIndex(c, v, addr, tile, o_idx)
    && CallbackPresentInBufferLocation(c, v, addr, EngReqToCBType(e), tile, v.tiles[tile].engine.cb_order[addr][o_idx])
    && v.tiles[tile].engine.buffer[v.tiles[tile].engine.cb_order[addr][o_idx]].cb_type == e
  }

  ghost predicate CBOrderTrackerHeadOnMissMeansNoEvictInProgress(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx)) :: (
      !OnEvictInProgress(c, v, addr, val)
    )
  }

  ghost predicate CBOrderTrackerHeadOnMissMeansNoWritebackInProgress(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr, c_idx, val | CBOrderTrackerIndexIsRequest(c, v, addr, 0, EngineRequest.OnMiss(c_idx)) :: (
      !OnWritebackInProgress(c, v, addr, val)
    )
  }

  ghost predicate EngReqQueueHeadOnMissMeansNoInFlightOnEvictRequest(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v, addr, 0, c_idx) :: (
      !InFlightOnEvictRequest(c, v, addr, val)
    )
  }

  ghost predicate EngReqQueueHeadOnMissMeansNoInFlightOnWritebackRequest(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr, c_idx, val | IsInFlightOnMissRequest(c, v, addr, 0, c_idx) :: (
      !InFlightOnWritebackRequest(c, v, addr, val)
    )
  }

  ghost predicate IdxInCBOrderTrackerIffCallbackPresent(c: Tako.Constants, v: Tako.Variables)
  {
    && FwdIdxInCBOrderTrackerIffCallbackPresent(c, v)
    && RevIdxInCBOrderTrackerIffCallbackPresent(c, v)
  }
  
  ghost predicate FwdIdxInCBOrderTrackerIffCallbackPresent(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address, t: nat, b: nat |
      (
        && IsBufferEntry(c, v, t, b) 
        && v.tiles[t].engine.buffer[b].addr == addr
      )
      ::
      (
        && AddrInTileCBOrderTracker(c, v, addr, t)
        && b in v.tiles[t].engine.cb_order[addr]
      )
  }

  ghost predicate RevIdxInCBOrderTrackerIffCallbackPresent(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address, t: nat, b: nat |
      (
        && AddrInTileCBOrderTracker(c, v, addr, t)
        && b in v.tiles[t].engine.cb_order[addr]
      )
      ::
      (
        && IsBufferEntry(c, v, t, b) 
        && v.tiles[t].engine.buffer[b].addr == addr
      )
  }
  
  ghost predicate NoDupIdxsInCBOrderTracker(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address, t: nat, idx1: nat, idx2: nat |
      (
        && CBOrderTrackerValidIndex(c, v, addr, t, idx1)
        && CBOrderTrackerValidIndex(c, v, addr, t, idx2)
        && v.tiles[t].engine.cb_order[addr][idx1] == v.tiles[t].engine.cb_order[addr][idx2]
      )
    ::
      idx1 == idx2
  }

  ghost predicate IsUnstartedBufferEntry(c: Tako.Constants, v: Tako.Variables, tile: nat, buf: nat)
  {
    && IsBufferEntry(c, v, tile, buf)
    && !v.tiles[tile].engine.buffer[buf].started
  }


  // OnEvict Invariants
  ghost predicate UnstartedBufferEntryWellformed(c: Tako.Constants, v: Tako.Variables)
  {
    forall tile: nat, buf: nat | IsUnstartedBufferEntry(c, v, tile, buf) :: (
      && var entry := v.tiles[tile].engine.buffer[buf];
      && match entry.cb_type {
        case OnEvict(_) => entry.addr in c.program.onEvictCBs
        case OnWriteBack(_) => entry.addr in c.program.onWBCBs
        case OnMiss(_) => entry.addr in c.program.onMissCBs
      }
      && var regs := if entry.cb_type.OnMiss? then map[] else map[ EvictReg() := entry.cb_type.val ];
      && ValuesMatchForCallbackId(c, v, RuntimeData(PC(0, 0), regs, []), tile, buf)
    )
  }

  ghost predicate EpochsConsistentWithCBOrderTrackerMiss(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address, tile: nat | CBOrderTrackerValidIndex(c, v, addr, tile, 0) :: (
      && addr in v.g.callback_epochs
      && var buf := v.tiles[tile].engine.cb_order[addr][0];
      && (CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf) ==>
        (
          && (IsUnstartedBufferEntry(c, v, tile, buf) ==> (
            && v.g.callback_epochs[addr].Out?
          ))
          && (CallbackRunningInBufferLocation(c, v, addr, CallbackType.OnMiss, tile, buf) ==> v.g.callback_epochs[addr].Miss?)
        )
      )
    )
  }

  ghost predicate EpochsConsistentWithCBOrderTrackerEvict(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address, tile: nat | CBOrderTrackerValidIndex(c, v, addr, tile, 0) :: (
      && addr in v.g.callback_epochs
      && var buf := v.tiles[tile].engine.cb_order[addr][0];
      && (CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf) ==>
        (
          && (IsUnstartedBufferEntry(c, v, tile, buf) ==> (
            && v.g.callback_epochs[addr].In?
            && v.g.callback_epochs[addr].wcb.None? // some if callback type is OnWB
            && MatchesLastWriteMorph(c, v, addr, v.tiles[tile].engine.buffer[buf].cb_type.val)
          ))
          && (CallbackRunningInBufferLocation(c, v, addr, CallbackType.OnEvict, tile, buf) ==> v.g.callback_epochs[addr].Evict?)
        )
      )
    )
  }

  ghost predicate EpochsConsistentWithCBOrderTrackerWriteback(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address, tile: nat | CBOrderTrackerValidIndex(c, v, addr, tile, 0) :: (
      && addr in v.g.callback_epochs
      && var buf := v.tiles[tile].engine.cb_order[addr][0];
      && (CallbackPresentInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf) ==>
        (
          && (IsUnstartedBufferEntry(c, v, tile, buf) ==> (
            && v.g.callback_epochs[addr].In?
            && v.g.callback_epochs[addr].wcb.Some? // some if callback type is onevict
            && MatchesLastWriteMorph(c, v, addr, v.tiles[tile].engine.buffer[buf].cb_type.val)
          ))
          && (CallbackRunningInBufferLocation(c, v, addr, CallbackType.OnWriteBack, tile, buf) ==> v.g.callback_epochs[addr].Evict?)
        )
      )
    )
  }

  ghost predicate EachAddrInEngineBoundMsgInWorkingSet(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr, idx: nat | InFlightEngineRequest(c, v, addr, idx) :: (
      && var msg := v.network.inFlightEngReqs[addr][idx];
      && addr in c.program.WorkingSet()
      && match msg.engine_req {
        case OnEvict(_) => addr in c.program.onEvictCBs
        case OnWriteBack(_) => addr in c.program.onWBCBs
        case OnMiss(_) => addr in c.program.onMissCBs
      } 
    )
  }

  ghost predicate ExistingCallbackIdsHaveCorrectEpoch(c: Tako.Constants, v: Tako.Variables)
  {
    forall id | SpecCallbackId(c, v, id) :: (
      && id.addr in v.g.callback_epochs
      && match v.g.callback_epochs[id.addr] {
        case Out(_) => id.count < v.g.callback_epochs[id.addr].epoch
        case Miss(_) | In(_,_,_) => (
          && (id.cb.OnMiss? ==> id.count <= v.g.callback_epochs[id.addr].epoch)
          && (!id.cb.OnMiss? ==> id.count < v.g.callback_epochs[id.addr].epoch)
        )
        case Evict(_,_,_) => id.count <= v.g.callback_epochs[id.addr].epoch
      }
    )
  }

  ghost predicate OnlyHeadOfCBOrderTrackerIsRunning(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address, tile: nat, buf: nat, cb | 
      CallbackRunningInBufferLocation(c, v, addr, cb, tile, buf)
    ::
      (
        && CBOrderTrackerValidIndex(c, v, addr, tile, 0)
        && buf == v.tiles[tile].engine.cb_order[addr][0]
        && IsBufferEntry(c, v, tile, buf)
        && cb == EngReqToCBType(v.tiles[tile].engine.buffer[buf].cb_type)
      )
  }

  ghost predicate MorphWorkingSetInEpochs(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address | addr in c.program.WorkingSet() && addr.Morph? :: (
      && addr in v.g.callback_epochs
    )
  }

  ghost predicate EpochEntryInMorphWorkingSet(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address | addr in v.g.callback_epochs :: (
      && addr in c.program.WorkingSet()
      && addr.Morph?
    )
  }

  ghost predicate NoEvictionInProgressAndOnMissUnstartedMeansOutEpoch(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v.g.callback_epochs
      && (forall val :: !OnEvictInProgress(c, v, addr, val))
      && (forall val :: !OnWritebackInProgress(c, v, addr, val))
      && (PrivateMorph(addr) && addr.morphType.idx < |v.tiles| ==> 
        (forall idx: nat | NonEmptyL2CacheEntry(c, v, addr.morphType.idx, idx) :: (
          || v.tiles[addr.morphType.idx].l2.cache[idx].addr != addr
          || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
          || (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
        ))
      )
      && (SharedMorph(addr) && c.addr_map(addr) < |v.tiles| ==> 
        (forall idx: nat | NonEmptyL3CacheEntry(c, v, c.addr_map(addr), idx) :: (
          || v.tiles[c.addr_map(addr)].l3.cache[idx].addr != addr
          || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && InFlightOnMissRequest(c, v, addr, idx))
          || (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? && UnstartedCallbackPresent(c, v, addr, EngineRequest.OnMiss(idx)))
        ))
      )
    ) :: (
      && v.g.callback_epochs[addr].Out?
    )
  }

  ghost predicate PendingMemMeansNonMorphAddress(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat | NonEmptyL3CacheEntry(c, v, core, idx) && v.tiles[core].l3.cache[idx].PendingMem? :: (
      v.tiles[core].l3.cache[idx].addr.Regular?
    )
  }

  ghost opaque predicate MorphAddrIsInL2CacheEntry(c: Tako.Constants, v: Tako.Variables, addr: Address)
  {
    && PrivateMorph(addr)
    && (exists idx: nat :: (
       && NonEmptyL2CacheEntry(c, v, addr.morphType.idx, idx)
       && v.tiles[addr.morphType.idx].l2.cache[idx].addr == addr
       && (v.tiles[addr.morphType.idx].l2.cache[idx].PendingCB? ==> InFlightOnMissResponse(c, v, addr, idx))
    ))
  }

  ghost opaque predicate MorphAddrIsInL3CacheEntry(c: Tako.Constants, v: Tako.Variables, addr: Address)
  {
    && SharedMorph(addr)
    && (exists idx: nat :: (
       && NonEmptyL3CacheEntry(c, v, c.addr_map(addr), idx)
       && v.tiles[c.addr_map(addr)].l3.cache[idx].addr == addr
       && (v.tiles[c.addr_map(addr)].l3.cache[idx].PendingCB? ==> InFlightOnMissResponse(c, v, addr, idx))
    ))
  }

  ghost opaque predicate InFlightOnEvictRequestForAddr(c: Tako.Constants, v: Tako.Variables, addr: Address)
  {
    exists val :: InFlightOnEvictRequest(c, v, addr, val)
  }

  ghost opaque predicate InFlightOnWritebackRequestForAddr(c: Tako.Constants, v: Tako.Variables, addr: Address)
  {
    exists val :: InFlightOnWritebackRequest(c, v, addr, val)
  }

  ghost opaque predicate UnstartedOnEvictEntryForAddr(c: Tako.Constants, v: Tako.Variables, addr: Address)
  {
    exists val :: UnstartedCallbackPresent(c, v, addr, EngineRequest.OnEvict(val))
  }

  ghost opaque predicate UnstartedOnWritebackEntryForAddr(c: Tako.Constants, v: Tako.Variables, addr: Address)
  {
    exists val :: UnstartedCallbackPresent(c, v, addr, EngineRequest.OnWriteBack(val))
  }

  ghost predicate AddrIsInEpoch(c: Tako.Constants, v: Tako.Variables, addr: Address)
  {
    && addr in v.g.callback_epochs
    && v.g.callback_epochs[addr].In?
  }

  ghost predicate MatchesLastWriteRegular(c: Tako.Constants, v: Tako.Variables, addr: Address, val: Value)
    requires addr in v.g.writes_to_addr
  {
    && |v.g.writes_to_addr[addr]| > 0
    && var last := |v.g.writes_to_addr[addr]| - 1;
    && v.g.writes_to_addr[addr][last].RegWrite()
    && var wval := if v.g.writes_to_addr[addr][last].W?
      then v.g.writes_to_addr[addr][last].val
      else v.g.writes_to_addr[addr][last].wval;
    && wval == val
  }

  ghost predicate MatchesLastWriteMorph(c: Tako.Constants, v: Tako.Variables, addr: Address, val: Value)
    requires AddrIsInEpoch(c, v, addr)
  {
    && (v.g.callback_epochs[addr].wcb.Some? ==> (
      && v.g.callback_epochs[addr].wcb.val.CBWrite()
      && var wval := if v.g.callback_epochs[addr].wcb.val.Wcb? 
        then v.g.callback_epochs[addr].wcb.val.val 
        else v.g.callback_epochs[addr].wcb.val.wval;
      && wval == val
    ))
    && (v.g.callback_epochs[addr].wcb.None? ==> (
      && v.g.callback_epochs[addr].me.Me?
      && v.g.callback_epochs[addr].me.val == val
    ))
  }

  ghost predicate NoOnMissInEngineAndInFlightEvictionMeansInEpoch(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v.g.callback_epochs
      // need data in cache or in flight on miss response
      && (PrivateMorph(addr) && addr.morphType.idx < |v.tiles| ==> (
        || MorphAddrIsInL2CacheEntry(c, v, addr)
        || InFlightOnEvictRequestForAddr(c, v, addr)
        || InFlightOnWritebackRequestForAddr(c, v, addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v.tiles| ==> (
        || MorphAddrIsInL3CacheEntry(c, v, addr)
        || InFlightOnEvictRequestForAddr(c, v, addr)
        || InFlightOnWritebackRequestForAddr(c, v, addr)
      ))
    ) :: (
      && v.g.callback_epochs[addr].In?
    )
  }

  ghost predicate UnstartedEvictionInEngineMeansInEpoch(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address | (
      && addr.Morph?
      && addr in v.g.callback_epochs
      && (PrivateMorph(addr) && addr.morphType.idx < |v.tiles| ==> (
        || UnstartedOnEvictEntryForAddr(c, v, addr)
        || UnstartedOnWritebackEntryForAddr(c, v, addr)
      ))
      && (SharedMorph(addr) && c.addr_map(addr) < |v.tiles| ==> (
        || UnstartedOnEvictEntryForAddr(c, v, addr)
        || UnstartedOnWritebackEntryForAddr(c, v, addr)
      ))
    ) :: (
      && v.g.callback_epochs[addr].In?
    )
  }

  ghost predicate AddrInEpochMeansEventsWellformed(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address | (
      && AddrIsInEpoch(c, v, addr)
    ) :: (
      && (v.g.callback_epochs[addr].wcb.Some? ==> v.g.callback_epochs[addr].wcb.val.addr == addr)
      && v.g.callback_epochs[addr].me.addr == addr
    )
  }
  ghost predicate AddrInEpochMeansEventsMatchAddrAtomicity(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address | (
      && AddrIsInEpoch(c, v, addr)
      && v.g.callback_epochs[addr].wcb.Some?
    ) :: (
      && v.g.callback_epochs[addr].wcb.val.Wcb? == !addr.atomic
      && v.g.callback_epochs[addr].wcb.val.RMWcb? == addr.atomic
    )
  }

  ghost predicate InFlightOnEvictRequestHasNoInterveningWrite(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v, addr)
      && InFlightOnEvictRequest(c, v, addr, val)
    ) :: (
      && v.g.callback_epochs[addr].wcb.None?
    )
  }

  ghost predicate InFlightOnWritebackRequestHasInterveningWrite(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v, addr)
      && InFlightOnWritebackRequest(c, v, addr, val)
    ) :: (
      && v.g.callback_epochs[addr].wcb.Some?
    )
  }

  ghost predicate InFlightOnEvictRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v, addr)
      && InFlightOnEvictRequest(c, v, addr, val)
    ) :: (
      && MatchesLastWriteMorph(c, v, addr, val)
    )
  }

  ghost predicate InFlightOnWritebackRequestMatchesLastWrite(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address, val: Value | (
      && AddrIsInEpoch(c, v, addr)
      && InFlightOnWritebackRequest(c, v, addr, val)
    ) :: (
      && MatchesLastWriteMorph(c, v, addr, val)
    )
  }

  ghost predicate CohML1CacheEntry(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  {
    && NonEmptyL1CacheEntry(c, v, core, idx)
    && v.tiles[core].core.cache[idx].coh.M?
  }

  ghost predicate CohMEL1CacheEntry(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  {
    && NonEmptyEL1CacheEntry(c, v, core, idx)
    && v.tiles[core].engine.cache[idx].coh.M?
  }

  ghost predicate CohMProxyCacheEntry(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  {
    && NonEmptyProxyCacheEntry(c, v, core, idx)
    && v.tiles[core].proxy.cache[idx].coh.M?
  }

  ghost predicate DirIL2CacheEntry(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  {
    && NonEmptyNonPendingL2CacheEntry(c, v, core, idx)
    && v.tiles[core].l2.cache[idx].dir.I?
  }

  ghost predicate DirtyL2CacheEntry(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  {
    && NonEmptyNonPendingL2CacheEntry(c, v, core, idx)
    && v.tiles[core].l2.cache[idx].dirty
  }

  ghost predicate CleanL2CacheEntry(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  {
    && NonEmptyNonPendingL2CacheEntry(c, v, core, idx)
    && !v.tiles[core].l2.cache[idx].dirty
  }

  ghost predicate DirSL2CacheEntry(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  {
    && NonEmptyNonPendingL2CacheEntry(c, v, core, idx)
    && v.tiles[core].l2.cache[idx].dir.S?
  }

  ghost predicate DirSL3CacheEntry(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  {
    && NonEmptyNonPendingL3CacheEntry(c, v, core, idx)
    && v.tiles[core].l3.cache[idx].dir.S?
  }

  ghost predicate DirML2CacheEntry(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  {
    && NonEmptyNonPendingL2CacheEntry(c, v, core, idx)
    && v.tiles[core].l2.cache[idx].dir.M?
  }

  ghost predicate DirML3CacheEntry(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  {
    && NonEmptyNonPendingL3CacheEntry(c, v, core, idx)
    && v.tiles[core].l3.cache[idx].dir.M?
  }

  ghost predicate DirSDL2CacheEntry(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  {
    && NonEmptyNonPendingL2CacheEntry(c, v, core, idx)
    && v.tiles[core].l2.cache[idx].dir.SD?
  }

  ghost predicate DirSDL3CacheEntry(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  {
    && NonEmptyNonPendingL3CacheEntry(c, v, core, idx)
    && v.tiles[core].l3.cache[idx].dir.SD?
  }

  ghost predicate DirMProxyOwnerL2CacheEntry(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  {
    && DirML2CacheEntry(c, v, core, idx)
    && v.tiles[core].l2.cache[idx].dir.owner == Cache(core, Proxy)
  }

  ghost predicate DirSDProxyOwnerL2CacheEntry(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  {
    && DirSDL2CacheEntry(c, v, core, idx)
    && v.tiles[core].l2.cache[idx].dir.former_owner == Cache(core, Proxy)
  }

  ghost predicate CohSToML2CacheEntry(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  {
    && NonEmptyNonPendingL2CacheEntry(c, v, core, idx)
    && v.tiles[core].l2.cache[idx].coh.Loadable()
    && !v.tiles[core].l2.cache[idx].coh.M?
  }

  ghost predicate CohML2CacheEntry(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  {
    && NonEmptyNonPendingL2CacheEntry(c, v, core, idx)
    && v.tiles[core].l2.cache[idx].coh.M?
  }

  ghost predicate DirIL3CacheEntry(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  {
    && core < |v.tiles|
    && idx < |v.tiles[core].l3.cache|
    && v.tiles[core].l3.cache[idx].L3Entry?
    && v.tiles[core].l3.cache[idx].dir.I?
  }

  ghost predicate DirtyL3CacheEntry(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  {
    && NonEmptyNonPendingL3CacheEntry(c, v, core, idx)
    && v.tiles[core].l3.cache[idx].dirty
  }

  ghost predicate CleanL3CacheEntry(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  {
    && NonEmptyNonPendingL3CacheEntry(c, v, core, idx)
    && !v.tiles[core].l3.cache[idx].dirty
  }

  
  ghost predicate L2DirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v, core, idx) 
      && v.tiles[core].l2.cache[idx].coh.Loadable()
      && AddrIsInEpoch(c, v, v.tiles[core].l2.cache[idx].addr)
    ) :: (
      && var addr := v.tiles[core].l2.cache[idx].addr;
      && ((DirtyL2CacheEntry(c, v, core, idx) 
        && (
          || DirIL2CacheEntry(c, v, core, idx) 
          || DirSL2CacheEntry(c, v, core, idx)
        )
      ) ==> (
        && v.g.callback_epochs[addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v, core, idx) 
        && PrivateMorph(v.tiles[core].l2.cache[idx].addr)
        && (
          || DirIL2CacheEntry(c, v, core, idx) 
          || DirSL2CacheEntry(c, v, core, idx)
        )
      ) ==> (
        && v.g.callback_epochs[addr].wcb.None?
      ))
    )
  }

  ghost predicate L3DirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat | (
      && NonEmptyNonPendingL3CacheEntry(c, v, core, idx) 
      && AddrIsInEpoch(c, v, v.tiles[core].l3.cache[idx].addr)
      && SharedMorph(v.tiles[core].l3.cache[idx].addr)
    ) :: (
      && var addr := v.tiles[core].l3.cache[idx].addr;
      && ((DirtyL3CacheEntry(c, v, core, idx) 
        && (
          || DirIL3CacheEntry(c, v, core, idx) 
          || DirSL3CacheEntry(c, v, core, idx)
        )
      ) ==> (
        && v.g.callback_epochs[addr].wcb.Some?
      ))
      && ((CleanL3CacheEntry(c, v, core, idx) 
        && (
          || DirIL3CacheEntry(c, v, core, idx) 
          || DirSL3CacheEntry(c, v, core, idx)
        )
      ) ==> (
        && v.g.callback_epochs[addr].wcb.None?
      ))
    )
  }

  ghost predicate EngineLoadableMatchesLastWriteMorph(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat | (
      && NonEmptyEL1CacheEntry(c, v, core, idx)
      && v.tiles[core].engine.cache[idx].coh.Loadable()
      && AddrIsInEpoch(c, v, v.tiles[core].engine.cache[idx].addr) 
    ) :: (
      && var entry := v.tiles[core].engine.cache[idx];
      && MatchesLastWriteMorph(c, v, entry.addr, entry.coh.val)
    )
  }

  ghost predicate CoreLoadableMatchesLastWriteMorph(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat | (
      && NonEmptyL1CacheEntry(c, v, core, idx)
      && v.tiles[core].core.cache[idx].coh.Loadable()
      && AddrIsInEpoch(c, v, v.tiles[core].core.cache[idx].addr) 
    ) :: (
      && var entry := v.tiles[core].core.cache[idx];
      && MatchesLastWriteMorph(c, v, entry.addr, entry.coh.val)
    )
  }

  ghost predicate EngineLoadableMatchesLastWriteRegular(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat | (
      && NonEmptyEL1CacheEntry(c, v, core, idx)
      && v.tiles[core].engine.cache[idx].coh.Loadable()
      && v.tiles[core].engine.cache[idx].addr in v.g.writes_to_addr
    ) :: (
      && var entry := v.tiles[core].engine.cache[idx];
      && MatchesLastWriteRegular(c, v, entry.addr, entry.coh.val)
    )
  }

  ghost predicate CoreLoadableMatchesLastWriteRegular(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat | (
      && NonEmptyL1CacheEntry(c, v, core, idx)
      && v.tiles[core].core.cache[idx].coh.Loadable()
      && v.tiles[core].core.cache[idx].addr in v.g.writes_to_addr
    ) :: (
      && var entry := v.tiles[core].core.cache[idx];
      && MatchesLastWriteRegular(c, v, entry.addr, entry.coh.val)
    )
  }

  ghost predicate L2DirISMatchesLastWrite(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat | (
      && (DirIL2CacheEntry(c, v, core, idx) || DirSL2CacheEntry(c, v, core, idx))
      && AddrIsInEpoch(c, v, v.tiles[core].l2.cache[idx].addr) 
      && PrivateMorph(v.tiles[core].l2.cache[idx].addr)
    ) :: (
      && var entry := v.tiles[core].l2.cache[idx];
      && MatchesLastWriteMorph(c, v, entry.addr, entry.dir.val)
    )
  }

  ghost predicate L3DirISMatchesLastWrite(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat | (
      && (DirIL3CacheEntry(c, v, core, idx) || DirSL3CacheEntry(c, v, core, idx))
      && AddrIsInEpoch(c, v, v.tiles[core].l3.cache[idx].addr) 
      && SharedMorph(v.tiles[core].l3.cache[idx].addr)
    ) :: (
      && var entry := v.tiles[core].l3.cache[idx];
      && MatchesLastWriteMorph(c, v, entry.addr, entry.dir.val)
    )
  }

  
  // ghost predicate L2DirIMeansNo(c: Tako.Constants, v: Tako.Variables)
  // {
  //   forall core: nat, idx: nat | (
  //     && (DirIL2CacheEntry(c, v, core, idx) || DirSL2CacheEntry(c, v, core, idx))
  //     && AddrIsInEpoch(c, v, v.tiles[core].l2.cache[idx].addr) 
  //     && PrivateMorph(v.tiles[core].l2.cache[idx].addr)
  //   ) :: (
  //     && var entry := v.tiles[core].l2.cache[idx];
  //     && MatchesLastWriteMorph(c, v, entry.addr, entry.dir.val)
  //   )
  // }

  ghost predicate L2QueueHeadsWellformed(c: Tako.Constants, v: Tako.Variables)
    requires v.WF(c)
  {
    forall core: nat | core < |v.tiles| :: (
      && (v.tiles[core].l2.next_coh_msg_t1[0].Some? ==> (
        && v.tiles[core].l2.next_coh_msg_t1[0].val.meta.src.Cache?
        && v.tiles[core].l2.next_coh_msg_t1[0].val.meta.src.level.Tier1()
        && v.tiles[core].l2.next_coh_msg_t1[0].val.meta.src.core == core
      ))
      && (v.tiles[core].l2.next_coh_msg_t1[1].Some? ==> (
        && v.tiles[core].l2.next_coh_msg_t1[1].val.meta.src.Cache?
        && v.tiles[core].l2.next_coh_msg_t1[1].val.meta.src.level.Tier1()
        && v.tiles[core].l2.next_coh_msg_t1[1].val.meta.src.core == core
      ))
      && (v.tiles[core].l2.next_coh_msg_t2[0].Some? ==> (
        && v.tiles[core].l2.next_coh_msg_t2[0].val.meta.src.Cache?
        && (
          || v.tiles[core].l2.next_coh_msg_t2[0].val.meta.src.level.L2?
          || v.tiles[core].l2.next_coh_msg_t2[0].val.meta.src.level.L3?
        )
      ))
      && (v.tiles[core].l2.next_coh_msg_t2[1].Some? ==> (
        && v.tiles[core].l2.next_coh_msg_t2[1].val.meta.src.Cache?
        && (
          || v.tiles[core].l2.next_coh_msg_t2[1].val.meta.src.level.L2?
          || v.tiles[core].l2.next_coh_msg_t2[1].val.meta.src.level.L3?
        )
      ))
    )
  }

  ghost predicate L3QueueHeadsWellformed(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, channel: nat | core < |v.tiles| && channel < |v.tiles[core].l3.next_coh_msg| :: (
      && (v.tiles[core].l3.next_coh_msg[channel].Some? ==> (
        && v.tiles[core].l3.next_coh_msg[channel].val.meta.src.Cache?
        && v.tiles[core].l3.next_coh_msg[channel].val.meta.src.level.L2?
      ))
    )
  }

  ghost predicate MemMessagesWellformed(c: Tako.Constants, v: Tako.Variables)
  {
    forall msg | msg in v.network.inFlightMessages && msg.meta.dst == Mem() :: (
      && msg.meta.src.Cache?
      && msg.meta.src.level.L3?
    )
  }

  ghost predicate PutMFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v, core, idx)
      && v.tiles[core].l2.cache[idx].dir.owner.Cache?
      && !v.tiles[core].l2.cache[idx].dir.owner.level.Proxy?
      && PutMInFlight(c, v, v.tiles[core].l2.cache[idx].addr, v.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && AddrIsInEpoch(c, v, v.tiles[core].l2.cache[idx].addr)
    ) :: (
      && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.Some?
    )
  }

  ghost predicate DataFromOwnerL2MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL2CacheEntry(c, v, core, idx)
      && src.Cache?
      && src.level.Tier1()
      && !src.level.Proxy?
      && DataInFlight(c, v, v.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val)
      && AddrIsInEpoch(c, v, v.tiles[core].l2.cache[idx].addr)
    ) :: (
      && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.Some?
    )
  }

  ghost predicate PutMFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v, core, idx)
      && v.tiles[core].l2.cache[idx].dir.owner == Cache(core, Proxy)
      && PutMInFlight(c, v, v.tiles[core].l2.cache[idx].addr, v.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && AddrIsInEpoch(c, v, v.tiles[core].l2.cache[idx].addr)
    ) :: (
      && (DirtyL2CacheEntry(c, v, core, idx) ==> (
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v, core, idx) && PrivateMorph(v.tiles[core].l2.cache[idx].addr)) ==> (
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.None?
      ))
    )
  }

  ghost predicate DataFromProxyL2MeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, val: Value | (
      && DirSDL2CacheEntry(c, v, core, idx)
      && v.tiles[core].l2.cache[idx].dir.former_owner == Cache(core, Proxy)
      && DataInFlight(c, v, v.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val)
      && AddrIsInEpoch(c, v, v.tiles[core].l2.cache[idx].addr)
    ) :: (
      && (DirtyL2CacheEntry(c, v, core, idx) ==> (
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v, core, idx) && PrivateMorph(v.tiles[core].l2.cache[idx].addr)) ==> (
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.None?
      ))
    )
  }

  ghost predicate PutMFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML3CacheEntry(c, v, core, idx)
      && v.tiles[core].l3.cache[idx].dir.owner.Cache?
      && v.tiles[core].l3.cache[idx].dir.owner.level.L2?
      && PutMInFlight(c, v, v.tiles[core].l3.cache[idx].addr, v.tiles[core].l3.cache[idx].dir.owner, Cache(core, L3), val)
      && AddrIsInEpoch(c, v, v.tiles[core].l3.cache[idx].addr)
    ) :: (
      && v.g.callback_epochs[v.tiles[core].l3.cache[idx].addr].wcb.Some?
    )
  }

  ghost predicate DataFromOwnerL3MeansInterveningWrite(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL3CacheEntry(c, v, core, idx)
      && src.Cache?
      && src.level.L2?
      && DataInFlight(c, v, v.tiles[core].l3.cache[idx].addr, src, Cache(core, L3), val)
      && AddrIsInEpoch(c, v, v.tiles[core].l3.cache[idx].addr)
    ) :: (
      && v.g.callback_epochs[v.tiles[core].l3.cache[idx].addr].wcb.Some?
    )
  }

  ghost predicate DirtyMorphAddressMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat | (
      && NonEmptyL1CacheEntry(c, v, core, idx)
      && v.tiles[core].core.cache[idx].dirty
      && v.tiles[core].core.cache[idx].coh.Loadable()
      // && (
      //   || v.tiles[core].core.cache[idx].coh.Loadable()
      //   || v.tiles[core].core.cache[idx].coh.MIA?
      //   || v.tiles[core].core.cache[idx].coh.MIF?
      // )
      // can't use MIA/MIF as we run into issues with startend (don't have a contradiction for why we could be evicting)
      && AddrIsInEpoch(c, v, v.tiles[core].core.cache[idx].addr)
    ) :: (
      && v.g.callback_epochs[v.tiles[core].core.cache[idx].addr].wcb.Some?
    )
  }
  
  ghost predicate DirtyMorphAddressMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat | (
      && NonEmptyEL1CacheEntry(c, v, core, idx)
      && v.tiles[core].engine.cache[idx].dirty
      && v.tiles[core].engine.cache[idx].coh.Loadable()
      // && (
      //   || v.tiles[core].engine.cache[idx].coh.Loadable()
      //   || v.tiles[core].engine.cache[idx].coh.MIA?
      //   || v.tiles[core].engine.cache[idx].coh.MIF?
      // )
      && AddrIsInEpoch(c, v, v.tiles[core].engine.cache[idx].addr)
    ) :: (
      && v.g.callback_epochs[v.tiles[core].engine.cache[idx].addr].wcb.Some?
    )
  }

  ghost predicate LoadableStateMorphAddressMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyProxyCacheEntry(c, v, core, idx1)
      && NonEmptyL2CacheEntry(c, v, core, idx2)
      && (
        || v.tiles[core].proxy.cache[idx1].coh.M?
        || v.tiles[core].proxy.cache[idx1].coh.IMA?
        || v.tiles[core].proxy.cache[idx1].coh.SMA?
      )
      // && v.tiles[core].proxy.cache[idx1].coh.HasMostRecentVal()
      && v.tiles[core].l2.cache[idx2].addr == v.tiles[core].proxy.cache[idx1].addr
      && AddrIsInEpoch(c, v, v.tiles[core].proxy.cache[idx1].addr)
    ) :: (
      && (DirtyL2CacheEntry(c, v, core, idx2) ==> (
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx2].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v, core, idx2) && PrivateMorph(v.tiles[core].proxy.cache[idx1].addr)) ==> (
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx2].addr].wcb.None?
      ))
    )
  }

  ghost predicate MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteCore(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyL1CacheEntry(c, v, core, idx1)
      && (
        || v.tiles[core].core.cache[idx1].coh.MIA?
        || v.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (
        || (DirML2CacheEntry(c, v, core, idx2) && v.tiles[core].l2.cache[idx2].dir.owner == Cache(core, L1))
        || (DirSDL2CacheEntry(c, v, core, idx2) && v.tiles[core].l2.cache[idx2].dir.former_owner == Cache(core, L1))
      )
      && v.tiles[core].l2.cache[idx2].addr == v.tiles[core].core.cache[idx1].addr
      && AddrIsInEpoch(c, v, v.tiles[core].core.cache[idx1].addr)
    ) :: (
      && v.g.callback_epochs[v.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
  }

  ghost predicate MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyEL1CacheEntry(c, v, core, idx1)
      && (
        || v.tiles[core].engine.cache[idx1].coh.MIA?
        || v.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (
        || (DirML2CacheEntry(c, v, core, idx2) && v.tiles[core].l2.cache[idx2].dir.owner == Cache(core, eL1))
        || (DirSDL2CacheEntry(c, v, core, idx2) && v.tiles[core].l2.cache[idx2].dir.former_owner == Cache(core, eL1))
      )
      && v.tiles[core].l2.cache[idx2].addr == v.tiles[core].engine.cache[idx1].addr
      && AddrIsInEpoch(c, v, v.tiles[core].engine.cache[idx1].addr)
    ) :: (
      && v.g.callback_epochs[v.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
  }

  ghost predicate MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v, core, idx1)
      && (
        || v.tiles[core].core.cache[idx1].coh.MIA?
        || v.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v, v.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v, v.tiles[core].core.cache[idx1].addr)
    ) :: (
      && v.g.callback_epochs[v.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
  }

  ghost predicate MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteCore(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat | (
      && NonEmptyL1CacheEntry(c, v, core, idx1)
      && (
        || v.tiles[core].core.cache[idx1].coh.MIA?
        || v.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v, v.tiles[core].core.cache[idx1].addr, src, Cache(core, L1)))
      && AddrIsInEpoch(c, v, v.tiles[core].core.cache[idx1].addr)
    ) :: (
      && v.g.callback_epochs[v.tiles[core].core.cache[idx1].addr].wcb.Some?
    )
  }

  ghost predicate MEvictingMorphAddressWithFwdGetSInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat | (
      && NonEmptyEL1CacheEntry(c, v, core, idx1)
      && (
        || v.tiles[core].engine.cache[idx1].coh.MIA?
        || v.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetSInFlight(c, v, v.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v, v.tiles[core].engine.cache[idx1].addr)
    ) :: (
      && v.g.callback_epochs[v.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
  }

  ghost predicate MEvictingMorphAddressWithFwdGetMInFlightMeansInterveningWriteEngine(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat | (
      && NonEmptyEL1CacheEntry(c, v, core, idx1)
      && (
        || v.tiles[core].engine.cache[idx1].coh.MIA?
        || v.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (exists src :: FwdGetMInFlight(c, v, v.tiles[core].engine.cache[idx1].addr, src, Cache(core, eL1)))
      && AddrIsInEpoch(c, v, v.tiles[core].engine.cache[idx1].addr)
    ) :: (
      && v.g.callback_epochs[v.tiles[core].engine.cache[idx1].addr].wcb.Some?
    )
  }

  ghost predicate MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteProxy(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyProxyCacheEntry(c, v, core, idx1)
      && NonEmptyL2CacheEntry(c, v, core, idx2)
      && (
        || v.tiles[core].proxy.cache[idx1].coh.MIA?
        || v.tiles[core].proxy.cache[idx1].coh.MIF?
      )
      && (
        || DirMProxyOwnerL2CacheEntry(c, v, core, idx2)
        || DirSDProxyOwnerL2CacheEntry(c, v, core, idx2)
      )
      && v.tiles[core].l2.cache[idx2].addr == v.tiles[core].proxy.cache[idx1].addr
      && AddrIsInEpoch(c, v, v.tiles[core].proxy.cache[idx1].addr)
    ) :: (
      && (DirtyL2CacheEntry(c, v, core, idx2) ==> (
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx2].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v, core, idx2) && PrivateMorph(v.tiles[core].proxy.cache[idx1].addr)) ==> (
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx2].addr].wcb.None?
      ))
    )
  }

  // can got with the overrestrictive M/SD route I believe
  ghost predicate MEvictingMorphAddressWithMatchingDirOwnerMatchesDirtyInterveningWriteL2(c: Tako.Constants, v: Tako.Variables)
  {
    forall core1: nat, idx1: nat, core2: nat, idx2: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v, core1, idx1)
      && (
        || v.tiles[core1].l2.cache[idx1].coh.MIA?
        || v.tiles[core1].l2.cache[idx1].coh.MIF?
      )
      && (
        || (DirML3CacheEntry(c, v, core2, idx2) && v.tiles[core2].l3.cache[idx2].dir.owner == Cache(core1, L2))
        || (DirSDL3CacheEntry(c, v, core2, idx2) && v.tiles[core2].l3.cache[idx2].dir.former_owner == Cache(core1, L2))
      )
      && v.tiles[core2].l3.cache[idx2].addr == v.tiles[core1].l2.cache[idx1].addr
      && AddrIsInEpoch(c, v, v.tiles[core1].l2.cache[idx1].addr)
    ) :: (
      && v.g.callback_epochs[v.tiles[core1].l2.cache[idx1].addr].wcb.Some?
    )
  }

  ghost predicate PrivateMorphInL2IsCohM(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v, core, idx)
      && PrivateMorph(v.tiles[core].l2.cache[idx].addr)
    ) :: (
      && CohML2CacheEntry(c, v, core, idx)
    )
  }
  
  /*
  ghost predicate PutMFromOwnerL2MeansEpochHasWcb(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v, core, idx)
      && v.tiles[core].l2.cache[idx].dir.owner.Cache?
      && !v.tiles[core].l2.cache[idx].dir.owner.level.Proxy?
      && PutMInFlight(c, v, v.tiles[core].l2.cache[idx].addr, v.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && v.tiles[core].l2.cache[idx].addr.Morph?
    ) :: (
      && AddrIsInEpoch(c, v, v.tiles[core].l2.cache[idx].addr)
      && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.Some?
      && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.CBWrite()
      && var wval := if v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.Wcb? then v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.val else v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.wval;
      && wval == val
    )
  }

  ghost predicate DataFromOwnerL2MeansEpochHasWcb(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL2CacheEntry(c, v, core, idx)
      && src.Cache?
      && src.level.Tier1()
      && !src.level.Proxy?
      && DataInFlight(c, v, v.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val)
      && v.tiles[core].l2.cache[idx].addr.Morph?
    ) :: (
      && AddrIsInEpoch(c, v, v.tiles[core].l2.cache[idx].addr)
      && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.Some?
      && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.CBWrite()
      && var wval := if v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.Wcb? then v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.val else v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.wval;
      && wval == val
    )
  }

  ghost predicate PutMFromProxyL2MeansEpochDataMatches(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v, core, idx)
      && v.tiles[core].l2.cache[idx].dir.owner == Cache(core, Proxy)
      && PutMInFlight(c, v, v.tiles[core].l2.cache[idx].addr, v.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && PrivateMorph(v.tiles[core].l2.cache[idx].addr)
    ) :: (
      && AddrIsInEpoch(c, v, v.tiles[core].l2.cache[idx].addr)
      && (DirtyL2CacheEntry(c, v, core, idx) ==> (
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.Some?
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.CBWrite()
        && var wval := if v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.Wcb? then v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.val else v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.wval;
        && wval == val
      ))
      && (CleanL2CacheEntry(c, v, core, idx) ==> (
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.None?
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].me.Me?
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].me.val == val
      ))
    )
  }

  ghost predicate DataFromProxyL2MeansEpochDataMatches(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, val: Value | (
      && DirSDL2CacheEntry(c, v, core, idx)
      && DataInFlight(c, v, v.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val)
      && PrivateMorph(v.tiles[core].l2.cache[idx].addr)
    ) :: (
      && AddrIsInEpoch(c, v, v.tiles[core].l2.cache[idx].addr)
      && (DirtyL2CacheEntry(c, v, core, idx) ==> (
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.Some?
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.CBWrite()
        && var wval := if v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.Wcb? then v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.val else v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.wval;
        && wval == val
      ))
      && (CleanL2CacheEntry(c, v, core, idx) ==> (
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.None?
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].me.Me?
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].me.val == val
      ))
    )
  }
  */

  // ghost predicate L2DirtyBitMatchesEpoch(c: Tako.Constants, v: Tako.Variables)
  // {
  //   forall core: nat, idx: nat | NonEmptyL2CacheEntry(c, v, core, idx) && AddrIsInEpoch(c, v, v.tiles[core].l2.cache[idx].addr) && PrivateMorph(v.tiles[core].l2.cache[idx].addr) :: (
  //     && var addr := v.tiles[core].l2.cache[idx].addr;
  //     && ((DirtyL2CacheEntry(c, v, core, idx) && (DirIL2CacheEntry(c, v, core, idx) || DirSL2CacheEntry(c, v, core, idx))) ==> (
  //         && v.g.callback_epochs[addr].wcb.Some?
  //         && v.g.callback_epochs[addr].wcb.val.CBWrite()
  //         && var wval := if v.g.callback_epochs[addr].wcb.val.Wcb? then v.g.callback_epochs[addr].wcb.val.val else v.g.callback_epochs[addr].wcb.val.wval;
  //         && wval == v.tiles[core].l2.cache[idx].dir.val
  //       )
  //     )
  //     && ((CleanL2CacheEntry(c, v, core, idx) 
  //       && (
  //         || DirIL2CacheEntry(c, v, core, idx) 
  //         || DirSL2CacheEntry(c, v, core, idx)
  //         || DirSDProxyOwnerL2CacheEntry(c, v, core, idx)
  //         || DirMProxyOwnerL2CacheEntry(c, v, core, idx)
  //       )
  //     ) ==> (
  //       && v.g.callback_epochs[addr].wcb.None?
  //       && v.g.callback_epochs[addr].me.Me?
  //       && ((DirIL2CacheEntry(c, v, core, idx) || DirSL2CacheEntry(c, v, core, idx)) ==> 
  //         v.g.callback_epochs[addr].me.val == v.tiles[core].l2.cache[idx].dir.val
  //       )
  //     ))
  //   )
  // }

  // ghost predicate L3DirtyBitMatchesEpoch(c: Tako.Constants, v: Tako.Variables)
  // {
  //   forall core: nat, idx: nat | DirIL3CacheEntry(c, v, core, idx) && AddrIsInEpoch(c, v, v.tiles[core].l3.cache[idx].addr) && SharedMorph(v.tiles[core].l3.cache[idx].addr) :: (
  //     && var addr := v.tiles[core].l3.cache[idx].addr;
  //     && (DirtyDirIL3CacheEntry(c, v, core, idx) ==> (
  //       && v.g.callback_epochs[addr].wcb.Some?
  //       && v.g.callback_epochs[addr].wcb.val.CBWrite()
  //       && var wval := if v.g.callback_epochs[addr].wcb.val.Wcb? then v.g.callback_epochs[addr].wcb.val.val else v.g.callback_epochs[addr].wcb.val.wval;
  //       && wval == v.tiles[core].l3.cache[idx].dir.val
  //     ))
  //     && (CleanDirIL3CacheEntry(c, v, core, idx) ==> (
  //       && v.g.callback_epochs[addr].wcb.None?
  //       && v.g.callback_epochs[addr].me.Me?
  //       && v.g.callback_epochs[addr].me.val == v.tiles[core].l3.cache[idx].dir.val
  //     ))
  //   )
  // }

  ghost predicate OnMissResponseMeansInEpochWithNoWrite(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr: Address, c_idx: nat, msg: Message | IsInFlightOnMissResponse(c, v, addr, msg, c_idx) :: (
      && AddrIsInEpoch(c, v, addr)
      && v.g.callback_epochs[addr].wcb.None?
      && v.g.callback_epochs[addr].me.Me?
      && msg.engine_resp.val == v.g.callback_epochs[addr].me.val
    )
  }
  
  ghost predicate OnEvictInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v.tiles|
      && idx < |v.tiles[core].core.cache|
      && OnEvictInProgress(c, v, v.tiles[core].core.cache[idx].addr, val)
      :: (
      && !v.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    )
  }

  ghost predicate OnEvictInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v.tiles|
      && idx < |v.tiles[core].engine.cache|
      && OnEvictInProgress(c, v, v.tiles[core].engine.cache[idx].addr, val)
      :: (
      && !v.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    )
  }

  ghost predicate OnEvictInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v.tiles|
      && idx < |v.tiles[core].proxy.cache|
      && OnEvictInProgress(c, v, v.tiles[core].proxy.cache[idx].addr, val)
      :: (
      && !v.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    )
  }

  ghost predicate OnWritebackInProgressMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v.tiles|
      && idx < |v.tiles[core].core.cache|
      && OnWritebackInProgress(c, v, v.tiles[core].core.cache[idx].addr, val)
      :: (
      && !v.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    )
  }

  ghost predicate OnWritebackInProgressMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v.tiles|
      && idx < |v.tiles[core].engine.cache|
      && OnWritebackInProgress(c, v, v.tiles[core].engine.cache[idx].addr, val)
      :: (
      && !v.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    )
  }

  ghost predicate OnWritebackInProgressMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, val: Value |
      && core < |v.tiles|
      && idx < |v.tiles[core].proxy.cache|
      && OnWritebackInProgress(c, v, v.tiles[core].proxy.cache[idx].addr, val)
      :: (
      && !v.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    )
  }
  
  // be very careful here
  // some issues
  // 2. if we want l3addr->l2addr, we should weaken to allow l2 to have stuff in non loadable form
  // TODO: potentially add IMA as a carveout here too.
  ghost predicate L2AddrNotInCache(c: Tako.Constants, v: Tako.Variables, core: nat, addr: Address)
  {
    (forall i: nat | NonEmptyL2CacheEntry(c, v, core, i) :: (
      || v.tiles[core].l2.cache[i].addr != addr
      || v.tiles[core].l2.cache[i].PendingCB?
      || (v.tiles[core].l2.cache[i].L2Entry? && !v.tiles[core].l2.cache[i].coh.Loadable())
    ))
  }

  ghost predicate L3AddrNotInCache(c: Tako.Constants, v: Tako.Variables, core: nat, addr: Address)
  {
    (forall i: nat | NonEmptyL3CacheEntry(c, v, core, i) :: (
      || v.tiles[core].l3.cache[i].addr != addr
      || !v.tiles[core].l3.cache[i].L3Entry?
    ))
  }

  // same core doesn't have data in higher tiers. No guarantees about other cores
  ghost predicate L2AddrNotInCacheMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, addr: Address | (
      && L2AddrNotInCache(c, v, core, addr)
      && core < |v.tiles|
      && idx < |v.tiles[core].core.cache|
      && v.tiles[core].core.cache[idx].addr == addr
    ) :: (
      && !v.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    )
  }

  ghost predicate L2AddrNotInCacheMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, addr: Address | (
      && L2AddrNotInCache(c, v, core, addr)
      && core < |v.tiles|
      && idx < |v.tiles[core].engine.cache|
      && v.tiles[core].engine.cache[idx].addr == addr
    ) :: (
      && !v.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    )
  }

  ghost predicate L2AddrNotInCacheMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, addr: Address | (
      && L2AddrNotInCache(c, v, core, addr)
      && core < |v.tiles|
      && idx < |v.tiles[core].proxy.cache|
      && v.tiles[core].proxy.cache[idx].addr == addr
    ) :: (
      && !v.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    )
  }
  
  // only true for same core
  ghost predicate L2DirectoryInIMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirIL2CacheEntry(c, v, core, idx1)
      && idx2 < |v.tiles[core].core.cache|
      && v.tiles[core].core.cache[idx2].addr == v.tiles[core].l2.cache[idx1].addr
    ) :: (
      && !v.tiles[core].core.cache[idx2].coh.HasMostRecentVal()
    )
  }

  ghost predicate L2DirectoryInIMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirIL2CacheEntry(c, v, core, idx1)
      && idx2 < |v.tiles[core].engine.cache|
      && v.tiles[core].engine.cache[idx2].addr == v.tiles[core].l2.cache[idx1].addr
    ) :: (
      && !v.tiles[core].engine.cache[idx2].coh.HasMostRecentVal()
    )
  }

  ghost predicate L2DirectoryInIMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirIL2CacheEntry(c, v, core, idx1)
      && idx2 < |v.tiles[core].proxy.cache|
      && v.tiles[core].proxy.cache[idx2].addr == v.tiles[core].l2.cache[idx1].addr
    ) :: (
      && !v.tiles[core].proxy.cache[idx2].coh.HasMostRecentVal()
    )
  }

  ghost predicate L2DirectoryInSMeansNoMInCore(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirSL2CacheEntry(c, v, core, idx1)
      && idx2 < |v.tiles[core].core.cache|
      && v.tiles[core].core.cache[idx2].addr == v.tiles[core].l2.cache[idx1].addr
    ) :: (
      && !v.tiles[core].core.cache[idx2].coh.M?
      && !v.tiles[core].core.cache[idx2].coh.IMA?
      && !v.tiles[core].core.cache[idx2].coh.SMA?
    )
  }

  ghost predicate L2DirectoryInSMeansNoMInEngine(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirSL2CacheEntry(c, v, core, idx1)
      && idx2 < |v.tiles[core].engine.cache|
      && v.tiles[core].engine.cache[idx2].addr == v.tiles[core].l2.cache[idx1].addr
    ) :: (
      && !v.tiles[core].engine.cache[idx2].coh.M?
      && !v.tiles[core].engine.cache[idx2].coh.IMA?
      && !v.tiles[core].engine.cache[idx2].coh.SMA?
    )
  }

  ghost predicate L3DirectoryInSMeansNoMInL2(c: Tako.Constants, v: Tako.Variables)
  {
    forall core1: nat, core2: nat, idx1: nat, idx2: nat | (
      && DirSL3CacheEntry(c, v, core1, idx1)
      && core2 < |v.tiles|
      && idx2 < |v.tiles[core2].l2.cache|
      && !v.tiles[core2].l2.cache[idx2].PendingCB?
      && v.tiles[core2].l2.cache[idx2].addr == v.tiles[core1].l3.cache[idx1].addr
    ) :: (
      && !v.tiles[core2].l2.cache[idx2].coh.M?
      && !v.tiles[core2].l2.cache[idx2].coh.IMA?
      && !v.tiles[core2].l2.cache[idx2].coh.SMA?
    )
  }

  ghost predicate L2DirectoryInSDAndMInCoreMeansFormerOwner(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirSDL2CacheEntry(c, v, core, idx1)
      && idx2 < |v.tiles[core].core.cache|
      && v.tiles[core].core.cache[idx2].addr == v.tiles[core].l2.cache[idx1].addr
      && v.tiles[core].core.cache[idx2].coh.M?
    ) :: (
      && v.tiles[core].l2.cache[idx1].dir.former_owner == Cache(core, L1)
    )
  }

  ghost predicate L2DirectoryInSDAndMInEngineMeansFormerOwner(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirSDL2CacheEntry(c, v, core, idx1)
      && idx2 < |v.tiles[core].engine.cache|
      && v.tiles[core].engine.cache[idx2].addr == v.tiles[core].l2.cache[idx1].addr
      && v.tiles[core].engine.cache[idx2].coh.M?
    ) :: (
      && v.tiles[core].l2.cache[idx1].dir.former_owner == Cache(core, eL1)
    )
  }

  ghost predicate L2DirectoryInMAndMInCoreMeansOwnerOrFwdGetMInFlight(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirML2CacheEntry(c, v, core, idx1)
      && idx2 < |v.tiles[core].core.cache|
      && v.tiles[core].core.cache[idx2].addr == v.tiles[core].l2.cache[idx1].addr
      && v.tiles[core].core.cache[idx2].coh.M?
    ) :: (
      || v.tiles[core].l2.cache[idx1].dir.owner == Cache(core, L1)
      // or there is a fwdgetm with the source being the owner
      || (exists dst : Location :: (
        && dst.Cache?
        && dst.level.Tier1()
        && dst.core == core
        && FwdGetMInFlight(c, v, v.tiles[core].l2.cache[idx1].addr, v.tiles[core].l2.cache[idx1].dir.owner, dst)
      ))
    )
  }

  ghost predicate L2DirectoryInMAndMInEngineMeansOwnerOrFwdGetMInFlight(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirML2CacheEntry(c, v, core, idx1)
      && idx2 < |v.tiles[core].engine.cache|
      && v.tiles[core].engine.cache[idx2].addr == v.tiles[core].l2.cache[idx1].addr
      && v.tiles[core].engine.cache[idx2].coh.M?
    ) :: (
      || v.tiles[core].l2.cache[idx1].dir.owner == Cache(core, eL1)
      // or there is a fwdgetm with the source being the owner
      || (exists dst : Location :: (
        && dst.Cache?
        && dst.level.Tier1()
        && dst.core == core
        && FwdGetMInFlight(c, v, v.tiles[core].l2.cache[idx1].addr, v.tiles[core].l2.cache[idx1].dir.owner, dst)
      ))
    )
  }
  
  ghost predicate MInCoreMeansMinL2(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyL1CacheEntry(c, v, core, idx2)
      && NonEmptyL2CacheEntry(c, v, core, idx1)
      && (
        || v.tiles[core].core.cache[idx2].coh.M?
        || v.tiles[core].core.cache[idx2].coh.IMA?
        || v.tiles[core].core.cache[idx2].coh.SMA?
      )
      && v.tiles[core].core.cache[idx2].addr == v.tiles[core].l2.cache[idx1].addr
    ) :: (
      && CohML2CacheEntry(c, v, core, idx1)
    )
  }

  ghost predicate MInEngineMeansMinL2(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyEL1CacheEntry(c, v, core, idx2)
      && NonEmptyL2CacheEntry(c, v, core, idx1)
      && (
        || v.tiles[core].engine.cache[idx2].coh.M?
        || v.tiles[core].engine.cache[idx2].coh.IMA?
        || v.tiles[core].engine.cache[idx2].coh.SMA?
      )
      && v.tiles[core].engine.cache[idx2].addr == v.tiles[core].l2.cache[idx1].addr
    ) :: (
      && CohML2CacheEntry(c, v, core, idx1)
    )
  }

  /*
  ghost predicate HavingDataInMMeansDirectoryinMorSDCore(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyL1CacheEntry(c, v, core, idx1) 
      && NonEmptyL2CacheEntry(c, v, core, idx2)
      && v.tiles[core].core.cache[idx1].addr == v.tiles[core].l2.cache[idx2].addr
      && v.tiles[core].core.cache[idx1].coh.M? 
    ) :: (
      || (
        && DirML2CacheEntry(c, v, core, idx2) // owner could be someone else, not necessarily you (FwdGetM en route)
        // cant guarantee that source of FwdGetM is the new owner either, as we can chain FwdGetMs
        // well, we can, but its not necessarily the same FwdGetM...
        && (
          // so either we are the owner,
          || v.tiles[core].l2.cache[idx2].dir.owner == Cache(core, L1)
          // or there is a fwdgetm with the source being the owner
          || (exists dst : Location :: (
            && dst.Cache?
            && dst.level.Tier1()
            && dst.core == core
            && FwdGetMInFlight(c, v, v.tiles[core].l2.cache[idx2].addr, v.tiles[core].l2.cache[idx2].dir.owner, dst)
          ))
        )
        && (DirMProxyOwnerL2CacheEntry(c, v, core, idx2) ==> DirtyL2CacheEntry(c, v, core, idx2))
      )
      || (
        && DirSDL2CacheEntry(c, v, core, idx2) // if in SD, FwdGetS is on its way
        && v.tiles[core].l2.cache[idx2].dir.former_owner == Cache(core, L1) // it is true when in M
      )
    )
  }

  ghost predicate HavingDataInMMeansDirectoryinMorSDEngine(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyEL1CacheEntry(c, v, core, idx1) 
      && NonEmptyL2CacheEntry(c, v, core, idx2)
      && v.tiles[core].engine.cache[idx1].addr == v.tiles[core].l2.cache[idx2].addr
      && v.tiles[core].engine.cache[idx1].coh.M? 
    ) :: (
      || (
        && DirML2CacheEntry(c, v, core, idx2) // owner could be someone else, not necessarily you (FwdGetM en route)
        // cant guarantee that source of FwdGetM is the new owner either, as we can chain FwdGetMs
        // well, we can, but its not necessarily the same FwdGetM...
        && (
          // so either we are the owner,
          || v.tiles[core].l2.cache[idx2].dir.owner == Cache(core, eL1)
          // or there is a fwdgetm with the source being the owner
          || (exists dst : Location :: (
            && dst.Cache?
            && dst.level.Tier1()
            && dst.core == core
            && FwdGetMInFlight(c, v, v.tiles[core].l2.cache[idx2].addr, v.tiles[core].l2.cache[idx2].dir.owner, dst)
          ))
        )
        && (DirMProxyOwnerL2CacheEntry(c, v, core, idx2) ==> DirtyL2CacheEntry(c, v, core, idx2))
      )
      || (
        && DirSDL2CacheEntry(c, v, core, idx2) // if in SD, FwdGetS is on its way
        && v.tiles[core].l2.cache[idx2].dir.former_owner == Cache(core, eL1)
      )
    )
  }
  */


  ghost predicate L1AddrNotMostRecentVal(c: Tako.Constants, v: Tako.Variables, core: nat, addr: Address)
  {
    (forall i: nat | NonEmptyL1CacheEntry(c, v, core, i) :: (
      || v.tiles[core].core.cache[i].addr != addr
      || !v.tiles[core].core.cache[i].coh.HasMostRecentVal()
    ))
  }

  ghost predicate EL1AddrNotMostRecentVal(c: Tako.Constants, v: Tako.Variables, core: nat, addr: Address)
  {
    (forall i: nat | NonEmptyEL1CacheEntry(c, v, core, i) :: (
      || v.tiles[core].engine.cache[i].addr != addr
      || !v.tiles[core].engine.cache[i].coh.HasMostRecentVal()
    ))
  }

  ghost predicate ProxyAddrNotMostRecentVal(c: Tako.Constants, v: Tako.Variables, core: nat, addr: Address)
  {
    (forall i: nat | NonEmptyProxyCacheEntry(c, v, core, i) :: (
      || v.tiles[core].proxy.cache[i].addr != addr
      || !v.tiles[core].proxy.cache[i].coh.HasMostRecentVal()
    ))
  }

  /*
  // be very careful here
  // some issues
  // 2. if we want l3addr->l2addr, we should weaken to allow l2 to have stuff in non loadable form
  // TODO: potentially add IMA as a carveout here too.
  ghost predicate L2AddrNotInCache(c: Tako.Constants, v: Tako.Variables, core: nat, addr: Address)
  {
    (forall i: nat | NonEmptyL2CacheEntry(c, v, core, i) :: (
      || v.tiles[core].l2.cache[i].addr != addr
      || v.tiles[core].l2.cache[i].PendingCB?
      || (v.tiles[core].l2.cache[i].L2Entry? && !v.tiles[core].l2.cache[i].coh.Loadable())
    ))
  }

  ghost predicate L3AddrNotInCache(c: Tako.Constants, v: Tako.Variables, core: nat, addr: Address)
  {
    (forall i: nat | NonEmptyL3CacheEntry(c, v, core, i) :: (
      || v.tiles[core].l3.cache[i].addr != addr
      || !v.tiles[core].l3.cache[i].L3Entry?
    ))
  }

  // same core doesn't have data in higher tiers. No guarantees about other cores
  ghost predicate L2AddrNotInCacheMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, addr: Address | (
      && L2AddrNotInCache(c, v, core, addr)
      && core < |v.tiles|
      && idx < |v.tiles[core].core.cache|
      && v.tiles[core].core.cache[idx].addr == addr
    ) :: (
      && !v.tiles[core].core.cache[idx].coh.HasMostRecentVal()
    )
  }

  ghost predicate L2AddrNotInCacheMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, addr: Address | (
      && L2AddrNotInCache(c, v, core, addr)
      && core < |v.tiles|
      && idx < |v.tiles[core].engine.cache|
      && v.tiles[core].engine.cache[idx].addr == addr
    ) :: (
      && !v.tiles[core].engine.cache[idx].coh.HasMostRecentVal()
    )
  }

  ghost predicate L2AddrNotInCacheMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, addr: Address | (
      && L2AddrNotInCache(c, v, core, addr)
      && core < |v.tiles|
      && idx < |v.tiles[core].proxy.cache|
      && v.tiles[core].proxy.cache[idx].addr == addr
    ) :: (
      && !v.tiles[core].proxy.cache[idx].coh.HasMostRecentVal()
    )
  }
  */

  ghost predicate MessageMetaAndTypeMatches(m: Message, addr: Address, src: Location, dst: Location, msg_type_matches: bool)
  {
    && m.CoherenceMsg?
    && msg_type_matches
    && m.meta.addr == addr
    && m.meta.src == src
    && m.meta.dst == dst
  }

  ghost opaque predicate InvAckInFlight(c: Tako.Constants, v: Tako.Variables, addr: Address, src: Location, dst: Location)
  {
    (exists m : Message :: (
      && m in v.network.inFlightMessages
      && m.CoherenceMsg?
      && MessageMetaAndTypeMatches(m, addr, src, dst, m.coh_msg.InvAck?)
    ))
    // invacks coming to T2 also in flight
    || (
      && dst.Cache?
      && dst.level.L2? // not needed strictly but may help eliminate cases
      && dst.core < |v.tiles|
      && |v.tiles[dst.core].l2.next_coh_msg_t2| == 2
      && v.tiles[dst.core].l2.next_coh_msg_t2[1].Some?
      && var m := v.tiles[dst.core].l2.next_coh_msg_t2[1].val;
      && m.CoherenceMsg?
      && MessageMetaAndTypeMatches(m, addr, src, dst, m.coh_msg.InvAck?)
    )
  }

  // ghost opaque predicate DataInFlightToT1(c: Tako.Constants, v: Tako.Variables, core: nat, addr: Address, val: Value)
  // {
  //   (exists m : Message :: (
  //     && DataMessage(m, addr, val)
  //     && m.meta.dst.Cache?
  //     && m.meta.dst.level.Tier1()
  //     && m.meta.dst.core == core
  //     && m.meta.addr == addr
  //   ))
  // }

  ghost opaque predicate PutMInFlight(c: Tako.Constants, v: Tako.Variables, addr: Address, src: Location, dst: Location, val: Value)
  {
    || (exists m : Message :: (
      && m in v.network.inFlightMessages
      && m.CoherenceMsg?
      && MessageMetaAndTypeMatches(m, addr, src, dst, m.coh_msg.PutM?)
      && m.coh_msg.val == val
    ))
    // PutM is at head of queue in L2
    || (
      && dst.Cache?
      && dst.level.L2? // not needed strictly but may help eliminate cases
      && dst.core < |v.tiles|
      && |v.tiles[dst.core].l2.next_coh_msg_t1| == 2
      && v.tiles[dst.core].l2.next_coh_msg_t1[0].Some?
      && var m := v.tiles[dst.core].l2.next_coh_msg_t1[0].val;
      && m.CoherenceMsg?
      && MessageMetaAndTypeMatches(m, addr, src, dst, m.coh_msg.PutM?)
      && m.coh_msg.val == val
    )
    // PutM is at head of queue in L3
    || (
      && dst.Cache?
      && dst.level.L3? // not needed strictly but may help eliminate cases
      && dst.core < |v.tiles|
      && |v.tiles[dst.core].l3.next_coh_msg| == 2
      && v.tiles[dst.core].l3.next_coh_msg[0].Some?
      && var m := v.tiles[dst.core].l3.next_coh_msg[0].val;
      && m.CoherenceMsg?
      && MessageMetaAndTypeMatches(m, addr, src, dst, m.coh_msg.PutM?)
      && m.coh_msg.val == val
    )
  }

  ghost opaque predicate GetMInFlight(c: Tako.Constants, v: Tako.Variables, addr: Address, src: Location, dst: Location)
  {
    || (exists m : Message :: (
      && m in v.network.inFlightMessages
      && m.CoherenceMsg?
      && MessageMetaAndTypeMatches(m, addr, src, dst, m.coh_msg.GetM?)
    ))
    // GetM is at head of queue in L2
    || (
      && dst.Cache?
      && dst.level.L2? // not needed strictly but may help eliminate cases
      && dst.core < |v.tiles|
      && |v.tiles[dst.core].l2.next_coh_msg_t1| == 2
      && v.tiles[dst.core].l2.next_coh_msg_t1[0].Some?
      && var m := v.tiles[dst.core].l2.next_coh_msg_t1[0].val;
      && m.CoherenceMsg?
      && MessageMetaAndTypeMatches(m, addr, src, dst, m.coh_msg.GetM?)
    )
    // GetM is at head of queue in L3
    || (
      && dst.Cache?
      && dst.level.L3? // not needed strictly but may help eliminate cases
      && dst.core < |v.tiles|
      && |v.tiles[dst.core].l3.next_coh_msg| == 2
      && v.tiles[dst.core].l3.next_coh_msg[0].Some?
      && var m := v.tiles[dst.core].l3.next_coh_msg[0].val;
      && m.CoherenceMsg?
      && MessageMetaAndTypeMatches(m, addr, src, dst, m.coh_msg.GetM?)
    )
  }

  ghost opaque predicate GetSInFlight(c: Tako.Constants, v: Tako.Variables, addr: Address, src: Location, dst: Location)
  {
    || (exists m : Message :: (
      && m in v.network.inFlightMessages
      && m.CoherenceMsg?
      && MessageMetaAndTypeMatches(m, addr, src, dst, m.coh_msg.GetS?)
    ))
    // GetS is at head of queue in L2
    || (
      && dst.Cache?
      && dst.level.L2? // not needed strictly but may help eliminate cases
      && dst.core < |v.tiles|
      && |v.tiles[dst.core].l2.next_coh_msg_t1| == 2
      && v.tiles[dst.core].l2.next_coh_msg_t1[0].Some?
      && var m := v.tiles[dst.core].l2.next_coh_msg_t1[0].val;
      && m.CoherenceMsg?
      && MessageMetaAndTypeMatches(m, addr, src, dst, m.coh_msg.GetS?)
    )
    // GetS is at head of queue in L3
    || (
      && dst.Cache?
      && dst.level.L3? // not needed strictly but may help eliminate cases
      && dst.core < |v.tiles|
      && |v.tiles[dst.core].l3.next_coh_msg| == 2
      && v.tiles[dst.core].l3.next_coh_msg[0].Some?
      && var m := v.tiles[dst.core].l3.next_coh_msg[0].val;
      && m.CoherenceMsg?
      && MessageMetaAndTypeMatches(m, addr, src, dst, m.coh_msg.GetS?)
    )
  }

  ghost opaque predicate FwdGetSInFlight(c: Tako.Constants, v: Tako.Variables, addr: Address, src: Location, dst: Location)
  {
    || (exists m : Message :: (
      && m in v.network.inFlightMessages
      && m.CoherenceMsg?
      && MessageMetaAndTypeMatches(m, addr, src, dst, m.coh_msg.FwdGetS?)
    ))
    // FwdGetS is at head of queue in L2 (from T3)
    || (
      && dst.Cache?
      && dst.level.L2? // not needed strictly but may help eliminate cases
      && dst.core < |v.tiles|
      && |v.tiles[dst.core].l2.next_coh_msg_t2| == 2
      && v.tiles[dst.core].l2.next_coh_msg_t2[0].Some?
      && var m := v.tiles[dst.core].l2.next_coh_msg_t2[0].val;
      && m.CoherenceMsg?
      && MessageMetaAndTypeMatches(m, addr, src, dst, m.coh_msg.FwdGetS?)
    )
  }

  ghost opaque predicate FwdGetMInFlight(c: Tako.Constants, v: Tako.Variables, addr: Address, src: Location, dst: Location)
  {
    || (exists m : Message :: (
      && m in v.network.inFlightMessages
      && m.CoherenceMsg?
      && MessageMetaAndTypeMatches(m, addr, src, dst, m.coh_msg.FwdGetM?)
    ))
    // FwdGetM is at head of queue in L2 (from T3)
    || (
      && dst.Cache?
      && dst.level.L2? // not needed strictly but may help eliminate cases
      && dst.core < |v.tiles|
      && |v.tiles[dst.core].l2.next_coh_msg_t2| == 2
      && v.tiles[dst.core].l2.next_coh_msg_t2[0].Some?
      && var m := v.tiles[dst.core].l2.next_coh_msg_t2[0].val;
      && m.CoherenceMsg?
      && MessageMetaAndTypeMatches(m, addr, src, dst, m.coh_msg.FwdGetM?)
    )
  }

  ghost opaque predicate DataInFlight(c: Tako.Constants, v: Tako.Variables, addr: Address, src: Location, dst: Location, val: Value)
  {
    || (exists m : Message :: (
      && m in v.network.inFlightMessages
      && m.CoherenceMsg?
      && MessageMetaAndTypeMatches(m, addr, src, dst, m.coh_msg.Data?)
      && m.coh_msg.val == val
    ))
    // Data is at head of queue in L2 (from T1)
    || (
      && dst.Cache?
      && dst.level.L2? // not needed strictly but may help eliminate cases
      && dst.core < |v.tiles|
      && |v.tiles[dst.core].l2.next_coh_msg_t1| == 2
      && v.tiles[dst.core].l2.next_coh_msg_t1[1].Some?
      && var m := v.tiles[dst.core].l2.next_coh_msg_t1[1].val;
      && m.CoherenceMsg?
      && MessageMetaAndTypeMatches(m, addr, src, dst, m.coh_msg.Data?)
      && m.coh_msg.val == val
    )
    // Data is at head of queue in L2 (from T3)
    || (
      && dst.Cache?
      && dst.level.L2? // not needed strictly but may help eliminate cases
      && dst.core < |v.tiles|
      && |v.tiles[dst.core].l2.next_coh_msg_t2| == 2
      && v.tiles[dst.core].l2.next_coh_msg_t2[1].Some?
      && var m := v.tiles[dst.core].l2.next_coh_msg_t2[1].val;
      && m.CoherenceMsg?
      && MessageMetaAndTypeMatches(m, addr, src, dst, m.coh_msg.Data?)
      && m.coh_msg.val == val
    )
    // Data is at head of queue in L3
    || (
      && dst.Cache?
      && dst.level.L3? // not needed strictly but may help eliminate cases
      && dst.core < |v.tiles|
      && |v.tiles[dst.core].l3.next_coh_msg| == 2
      && v.tiles[dst.core].l3.next_coh_msg[1].Some?
      && var m := v.tiles[dst.core].l3.next_coh_msg[1].val;
      && m.CoherenceMsg?
      && MessageMetaAndTypeMatches(m, addr, src, dst, m.coh_msg.Data?)
      && m.coh_msg.val == val
    )
  }

  ghost opaque predicate PutSInFlight(c: Tako.Constants, v: Tako.Variables, addr: Address, src: Location, dst: Location)
  {
    || (exists m : Message :: (
      && m in v.network.inFlightMessages
      && m.CoherenceMsg?
      && MessageMetaAndTypeMatches(m, addr, src, dst, m.coh_msg.PutS?)
    ))
    // PutS is at head of queue in L2
    || (
      && dst.Cache?
      && dst.level.L2? // not needed strictly but may help eliminate cases
      && dst.core < |v.tiles|
      && |v.tiles[dst.core].l2.next_coh_msg_t1| == 2
      && v.tiles[dst.core].l2.next_coh_msg_t1[0].Some?
      && var m := v.tiles[dst.core].l2.next_coh_msg_t1[0].val;
      && m.CoherenceMsg?
      && MessageMetaAndTypeMatches(m, addr, src, dst, m.coh_msg.PutS?)
    )
    // PutS is at head of queue in L3
    || (
      && dst.Cache?
      && dst.level.L3? // not needed strictly but may help eliminate cases
      && dst.core < |v.tiles|
      && |v.tiles[dst.core].l3.next_coh_msg| == 2
      && v.tiles[dst.core].l3.next_coh_msg[0].Some?
      && var m := v.tiles[dst.core].l3.next_coh_msg[0].val;
      && m.CoherenceMsg?
      && MessageMetaAndTypeMatches(m, addr, src, dst, m.coh_msg.PutS?)
    )
  }

  ghost predicate DataInFlightToT1MeansDirectoryNotInI(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr, val, src: Location, dst: Location | (
      && dst.Cache?
      && dst.level.Tier1()
      && DataInFlight(c, v, addr, src, dst, val) 
    ) :: (
      && (exists idx: nat :: 
        && NonEmptyNonPendingL2CacheEntry(c, v, dst.core, idx) && v.tiles[dst.core].l2.cache[idx].addr == addr
        && v.tiles[dst.core].l2.cache[idx].coh.Loadable()
        && !DirIL2CacheEntry(c, v, dst.core, idx) // not in I
      )
    )
  }

  ghost predicate DataInFlightToProxyMeansDirtyBitTracksInterveningWrite(c: Tako.Constants, v: Tako.Variables)
  {
    // this is only true for M data -- i.e FwdGetM response (not FwdGetS)
    forall val, core: nat, src: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v, core, idx)
      && DataInFlight(c, v, v.tiles[core].l2.cache[idx].addr, src, Cache(core, Proxy), val) 
      && AddrIsInEpoch(c, v, v.tiles[core].l2.cache[idx].addr)
    ) :: (
      && (DirtyL2CacheEntry(c, v, core, idx) ==> (
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.Some?
      ))
      && ((CleanL2CacheEntry(c, v, core, idx) && PrivateMorph(v.tiles[core].l2.cache[idx].addr)) ==> (
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.None?
      ))
    )
  }
  
  ghost predicate FwdGetMInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, dst: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v, core, idx)
      && FwdGetMInFlight(c, v, v.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
      && AddrIsInEpoch(c, v, v.tiles[core].l2.cache[idx].addr)
    ) :: (
      DirtyL2CacheEntry(c, v, core, idx)
    )
  }

  ghost predicate FwdGetSInFlightFromProxyMeansDirtyBitSet(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, dst: Location, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v, core, idx)
      && FwdGetSInFlight(c, v, v.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), dst) 
      && AddrIsInEpoch(c, v, v.tiles[core].l2.cache[idx].addr)
    ) :: (
      DirtyL2CacheEntry(c, v, core, idx)
    )
  }

  /*
  ghost predicate DataInFlightToT1AndDirectorySSDMeansDstIsSharer(c: Tako.Constants, v: Tako.Variables)
  {
    forall val, src: Location, dst: Location, idx: nat | (
      && dst.Cache?
      && dst.level.Tier1()
      && (DirSL2CacheEntry(c, v, dst.core, idx) || DirSDL2CacheEntry(c, v, dst.core, idx))
      && DataInFlight(c, v, v.tiles[dst.core].l2.cache[idx].addr, src, dst, val) 
    ) :: (
      dst in v.tiles[dst.core].l2.cache[idx].dir.sharers
    )
  }

  ghost predicate InvAckInFlightToT1MeansDirectoryNotInI(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr, src, dst: Location | (
      && dst.Cache?
      && dst.level.Tier1()
      && InvAckInFlight(c, v, addr, src, dst) 
    ) :: (
      && (exists idx: nat :: 
        && NonEmptyNonPendingL2CacheEntry(c, v, dst.core, idx)
        && v.tiles[dst.core].l2.cache[idx].addr == addr
        && v.tiles[dst.core].l2.cache[idx].coh.Loadable()
        && !DirIL2CacheEntry(c, v, dst.core, idx) // not in I
        // TODO: also potentially not in S, as we have to go through SD, which means all InvAcks should be in?
      )
    )
  }
  */
  // ghost predicate PutMInFlightMeansSourceIsEvictingCore(c: Tako.Constants, v: Tako.Variables)
  // {
  //   forall addr, val, dst: Location | (
  //     && dst.Cache?
  //     && dst.level.L2? // not needed strictly but may help eliminate cases
  //     && PutMInFlight(c, v, addr, Cache(dst.core, L1), dst, val) 
  //   ) :: (
  //     && (exists idx: nat :: 
  //         && NonEmptyL1CacheEntry(c, v, dst.core, idx)
  //         && v.tiles[dst.core].core.cache[idx].addr == addr
  //         && v.tiles[dst.core].core.cache[idx].coh.Evicting()
  //     )
  //   )
  // }

  // ghost predicate PutMInFlightMeansSourceIsEvictingEngine(c: Tako.Constants, v: Tako.Variables)
  // {
  //   forall addr, val, dst: Location | (
  //     && dst.Cache?
  //     && dst.level.L2? // not needed strictly but may help eliminate cases
  //     && PutMInFlight(c, v, addr, Cache(dst.core, eL1), dst, val) 
  //   ) :: (
  //     && (exists idx: nat :: 
  //         && NonEmptyEL1CacheEntry(c, v, dst.core, idx)
  //         && v.tiles[dst.core].engine.cache[idx].addr == addr
  //         && v.tiles[dst.core].engine.cache[idx].coh.Evicting()
  //     )
  //   )
  // }

  ghost predicate PutMInFlightMeansSourceIsEvicting(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr, val, src, dst: Location | (
      && dst.Cache?
      // && dst.level.L2? // not needed strictly but may help eliminate cases
      && PutMInFlight(c, v, addr, src, dst, val) 
    ) :: (
      && (src == Cache(dst.core, Proxy) ==> 
        (exists idx: nat :: 
          && NonEmptyProxyCacheEntry(c, v, dst.core, idx)
          && v.tiles[dst.core].proxy.cache[idx].addr == addr
          && v.tiles[dst.core].proxy.cache[idx].coh.Evicting()
        )
      )
      && (src == Cache(dst.core, L1) ==> 
        (exists idx: nat :: 
          && NonEmptyL1CacheEntry(c, v, dst.core, idx)
          && v.tiles[dst.core].core.cache[idx].addr == addr
          && v.tiles[dst.core].core.cache[idx].coh.Evicting()
        )
      )
      && (src == Cache(dst.core, eL1) ==> 
        (exists idx: nat :: 
          && NonEmptyEL1CacheEntry(c, v, dst.core, idx)
          && v.tiles[dst.core].engine.cache[idx].addr == addr
          && v.tiles[dst.core].engine.cache[idx].coh.Evicting()
        )
      )
      && (src.Cache? && src.level.L2? ==> 
        (exists idx: nat :: 
          && NonEmptyNonPendingL2CacheEntry(c, v, src.core, idx)
          && v.tiles[src.core].l2.cache[idx].addr == addr
          && v.tiles[src.core].l2.cache[idx].coh.Evicting()
        )
      )
    )
  }

  ghost predicate GetMInFlightMeansSourceIsTransitioningToM(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr, src, dst: Location | (
      && dst.Cache?
      // && dst.level.L2? // not needed strictly but may help eliminate cases
      && GetMInFlight(c, v, addr, src, dst) 
    ) :: (
      && (src == Cache(dst.core, Proxy) ==>
        (exists idx: nat :: 
          && NonEmptyProxyCacheEntry(c, v, dst.core, idx)
          && v.tiles[dst.core].proxy.cache[idx].addr == addr
          && (
            || v.tiles[dst.core].proxy.cache[idx].coh.IMAD?
            || v.tiles[dst.core].proxy.cache[idx].coh.SMAD?
          )
        )
      )
      && (src == Cache(dst.core, L1) ==>
        (exists idx: nat :: 
          && NonEmptyL1CacheEntry(c, v, dst.core, idx)
          && v.tiles[dst.core].core.cache[idx].addr == addr
          && (
            || v.tiles[dst.core].core.cache[idx].coh.IMAD?
            || v.tiles[dst.core].core.cache[idx].coh.SMAD?
          )
        )
      )
      && (src == Cache(dst.core, eL1) ==>
        (exists idx: nat :: 
          && NonEmptyEL1CacheEntry(c, v, dst.core, idx)
          && v.tiles[dst.core].engine.cache[idx].addr == addr
          && (
            || v.tiles[dst.core].engine.cache[idx].coh.IMAD?
            || v.tiles[dst.core].engine.cache[idx].coh.SMAD?
          )
        )
      )
      && (src.Cache? && src.level.L2? ==>
        (exists idx: nat :: 
          && NonEmptyNonPendingL2CacheEntry(c, v, src.core, idx)
          && v.tiles[src.core].l2.cache[idx].addr == addr
          && (
            || v.tiles[src.core].l2.cache[idx].coh.IMAD?
            || v.tiles[src.core].l2.cache[idx].coh.SMAD?
          )
        )
      )
    )
  }

  ghost predicate GetSInFlightToT2MeansSourceIsTransitioningToS(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr, src, dst: Location | (
      && dst.Cache?
      && dst.level.L2? // not needed strictly but may help eliminate cases
      && GetSInFlight(c, v, addr, src, dst) 
    ) :: (
      && (src == Cache(dst.core, Proxy) ==> 
        (exists idx: nat :: 
          && NonEmptyProxyCacheEntry(c, v, dst.core, idx)
          && v.tiles[dst.core].proxy.cache[idx].addr == addr
          && v.tiles[dst.core].proxy.cache[idx].coh.ISD?
        )
      )
      && (src == Cache(dst.core, L1) ==> 
        (exists idx: nat :: 
          && NonEmptyL1CacheEntry(c, v, dst.core, idx)
          && v.tiles[dst.core].core.cache[idx].addr == addr
          && v.tiles[dst.core].core.cache[idx].coh.ISD?
        )
      )
      && (src == Cache(dst.core, eL1) ==> 
        (exists idx: nat :: 
          && NonEmptyEL1CacheEntry(c, v, dst.core, idx)
          && v.tiles[dst.core].engine.cache[idx].addr == addr
          && v.tiles[dst.core].engine.cache[idx].coh.ISD?
        )
      )
    )
  }

  ghost predicate FwdGetSInFlightToT1MeansSourceIsTransitioningToS(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr, src, dst: Location | (
      && dst.Cache?
      && dst.level.Tier1() // not needed strictly but may help eliminate cases
      && FwdGetSInFlight(c, v, addr, src, dst) 
    ) :: (
      && (src == Cache(dst.core, Proxy) ==> 
        (exists idx: nat :: 
          && NonEmptyProxyCacheEntry(c, v, dst.core, idx)
          && v.tiles[dst.core].proxy.cache[idx].addr == addr
          && v.tiles[dst.core].proxy.cache[idx].coh.ISD?
        )
      )
      && (src == Cache(dst.core, L1) ==> 
        (exists idx: nat :: 
          && NonEmptyL1CacheEntry(c, v, dst.core, idx)
          && v.tiles[dst.core].core.cache[idx].addr == addr
          && v.tiles[dst.core].core.cache[idx].coh.ISD?
        )
      )
      && (src == Cache(dst.core, eL1) ==> 
        (exists idx: nat :: 
          && NonEmptyEL1CacheEntry(c, v, dst.core, idx)
          && v.tiles[dst.core].engine.cache[idx].addr == addr
          && v.tiles[dst.core].engine.cache[idx].coh.ISD?
        )
      )
    )
  }

  
  ghost predicate FwdGetSInFlightMeansSrcDstDifferent(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr, src, dst: Location | (
      && FwdGetSInFlight(c, v, addr, src, dst) 
    ) :: (
      src != dst
    )
  }

  ghost predicate FwdGetSInFlightMeansDirectoryIsSD(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr, src, dst: Location | (
      && dst.Cache?
      && FwdGetSInFlight(c, v, addr, src, dst) 
    ) :: (
      && (dst.level.Tier1() ==> (
        // directory is def Cache(dst.core, L2)
        && (exists idx: nat :: 
            && DirSDL2CacheEntry(c, v, dst.core, idx)
            && v.tiles[dst.core].l2.cache[idx].addr == addr
            && v.tiles[dst.core].l2.cache[idx].dir.former_owner == dst
        )
      ))
      && (dst.level.L2? ==> (
        && (exists idx: nat :: 
            && DirSDL3CacheEntry(c, v, c.addr_map(addr), idx)
            && v.tiles[c.addr_map(addr)].l3.cache[idx].addr == addr
            && v.tiles[c.addr_map(addr)].l3.cache[idx].dir.former_owner == dst
        )
      ))
    )
  }

  ghost predicate NoGetSAndReturningData(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr, src, dst, dst2, val :: (
      !(GetSInFlight(c, v, addr, src, dst) && DataInFlight(c, v, addr, dst2, src, val))
      // todo gets & fwdgets
      // fwdgets & data
    )
  }

  ghost predicate NoGetMAndReturningData(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr, src, dst, dst2, val :: (
      !(GetMInFlight(c, v, addr, src, dst) && DataInFlight(c, v, addr, dst2, src, val))
      // todo getm & fwdgetm
      // fwdgetm & data
    )
  }

  ghost predicate NoGetsAndDirML2(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat | (
      && DirML2CacheEntry(c, v, core, idx)
    ) :: (
      && !GetMInFlight(c, v, v.tiles[core].l2.cache[idx].addr, v.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2))
      && !GetSInFlight(c, v, v.tiles[core].l2.cache[idx].addr, v.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2))
    )
  }
  

  ghost predicate L1InCohMMeansAddrNotInOtherL1s(c: Tako.Constants, v: Tako.Variables)
  {
    forall core1: nat, core2: nat, idx: nat | (
      && CohML1CacheEntry(c, v, core1, idx)
    ) :: (
      // other L1s
      && (core1 != core2 ==> L1AddrNotMostRecentVal(c, v, core2, v.tiles[core1].core.cache[idx].addr))
      // all eL1s
      && EL1AddrNotMostRecentVal(c, v, core2, v.tiles[core1].core.cache[idx].addr)
      // all Proxys
      && ProxyAddrNotMostRecentVal(c, v, core2, v.tiles[core1].core.cache[idx].addr)
    )
  }

  
  ghost predicate L1InCohMMeansNoT1DataInFlight(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, src: Location, dst: Location, val: Value | (
      && CohML1CacheEntry(c, v, core, idx)
      && (
        || (src.Cache? && src.level.Tier1())
        || (dst.Cache? && dst.level.Tier1())
      )
    ) :: (
      !DataInFlight(c, v, v.tiles[core].core.cache[idx].addr, src, dst, val)
    )
  }

  ghost predicate EL1InCohMMeansAddrNotInOtherL1s(c: Tako.Constants, v: Tako.Variables)
  {
    forall core1: nat, core2: nat, idx: nat | (
      && CohMEL1CacheEntry(c, v, core1, idx)
    ) :: (
      // other EL1s
      && (core1 != core2 ==> EL1AddrNotMostRecentVal(c, v, core2, v.tiles[core1].engine.cache[idx].addr))
      // all L1s
      && L1AddrNotMostRecentVal(c, v, core2, v.tiles[core1].engine.cache[idx].addr)
      // all Proxys
      && ProxyAddrNotMostRecentVal(c, v, core2, v.tiles[core1].engine.cache[idx].addr)
    )
  }

  ghost predicate EL1InCohMMeansNoT1DataInFlight(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, src: Location, dst: Location, val: Value | (
      && CohMEL1CacheEntry(c, v, core, idx)
      && (
        || (src.Cache? && src.level.Tier1())
        || (dst.Cache? && dst.level.Tier1())
      )
    ) :: (
      !DataInFlight(c, v, v.tiles[core].engine.cache[idx].addr, src, dst, val)
    )
  }

  ghost predicate L2InCohMMeansAddrNotInOtherL2s(c: Tako.Constants, v: Tako.Variables)
  {
    forall core1: nat, core2: nat, idx: nat | (
      && CohML2CacheEntry(c, v, core1, idx)
      && core1 != core2
    ) :: (
      L2AddrNotInCache(c, v, core2, v.tiles[core1].l2.cache[idx].addr)
    )
  }

  /*
  ghost predicate PutSInFlightMeansSourceIsEvicting(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr, src, dst: Location | (
      && dst.Cache?
      && dst.level.L2? // not needed strictly but may help eliminate cases
      && PutSInFlight(c, v, addr, src, dst) 
    ) :: (
      && (src == Cache(dst.core, Proxy) ==> 
        (exists idx: nat :: 
          && NonEmptyProxyCacheEntry(c, v, dst.core, idx)
          && v.tiles[dst.core].proxy.cache[idx].addr == addr
          && v.tiles[dst.core].proxy.cache[idx].coh.Evicting()
          && !v.tiles[dst.core].proxy.cache[idx].coh.MIA?
          && !v.tiles[dst.core].proxy.cache[idx].coh.MIF?
        )
      )
      && (src == Cache(dst.core, L1) ==> 
        (exists idx: nat :: 
          && NonEmptyL1CacheEntry(c, v, dst.core, idx)
          && v.tiles[dst.core].core.cache[idx].addr == addr
          && v.tiles[dst.core].core.cache[idx].coh.Evicting()
          && !v.tiles[dst.core].core.cache[idx].coh.MIA?
          && !v.tiles[dst.core].core.cache[idx].coh.MIF?
        )
      )
      && (src == Cache(dst.core, eL1) ==> 
        (exists idx: nat :: 
          && NonEmptyEL1CacheEntry(c, v, dst.core, idx)
          && v.tiles[dst.core].engine.cache[idx].addr == addr
          && v.tiles[dst.core].engine.cache[idx].coh.Evicting()
          && !v.tiles[dst.core].engine.cache[idx].coh.MIA?
          && !v.tiles[dst.core].engine.cache[idx].coh.MIF?
        )
      )
    )
  }


  ghost predicate FwdGetSInFlightToT1MeansDirectoryIsSD(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr, src, dst: Location | (
      && dst.Cache?
      && dst.level.Tier1() // not needed strictly but may help eliminate cases
      && FwdGetSInFlight(c, v, addr, src, dst) 
    ) :: (
      // directory is def Cache(dst.core, L2)
      && (exists idx: nat :: 
          && DirSDL2CacheEntry(c, v, dst.core, idx)
          && v.tiles[dst.core].l2.cache[idx].addr == addr
          && v.tiles[dst.core].l2.cache[idx].dir.former_owner == dst
      )
      && (src == Cache(dst.core, Proxy) ==> 
        (exists idx: nat :: 
          && NonEmptyProxyCacheEntry(c, v, dst.core, idx)
          && v.tiles[dst.core].proxy.cache[idx].addr == addr
          && v.tiles[dst.core].proxy.cache[idx].coh.ISD?
        )
      )
      && (src == Cache(dst.core, L1) ==> 
        (exists idx: nat :: 
          && NonEmptyL1CacheEntry(c, v, dst.core, idx)
          && v.tiles[dst.core].core.cache[idx].addr == addr
          && v.tiles[dst.core].core.cache[idx].coh.ISD?
        )
      )
      && (src == Cache(dst.core, eL1) ==> 
        (exists idx: nat :: 
          && NonEmptyEL1CacheEntry(c, v, dst.core, idx)
          && v.tiles[dst.core].engine.cache[idx].addr == addr
          && v.tiles[dst.core].engine.cache[idx].coh.ISD?
        )
      )
    )
  }
  */

  ghost predicate FwdGetMInFlightToT1MeansSourceIsTransitioningToM(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr, src, dst: Location | (
      && dst.Cache?
      && dst.level.Tier1() // not needed strictly but may help eliminate cases
      && FwdGetMInFlight(c, v, addr, src, dst) 
    ) :: (
      // directory is def Cache(dst.core, L2)
      // could be SD or M can say similar things
      && (exists idx: nat :: 
          && CohML2CacheEntry(c, v, dst.core, idx)
          && v.tiles[dst.core].l2.cache[idx].addr == addr
      )
      && (src == Cache(dst.core, Proxy) ==> 
        (exists idx: nat :: 
          && NonEmptyProxyCacheEntry(c, v, dst.core, idx)
          && v.tiles[dst.core].proxy.cache[idx].addr == addr
          && (
            || v.tiles[dst.core].proxy.cache[idx].coh.IMAD?
            || v.tiles[dst.core].proxy.cache[idx].coh.SMAD?
          )
        )
      )
      && (src == Cache(dst.core, L1) ==> 
        (exists idx: nat :: 
          && NonEmptyL1CacheEntry(c, v, dst.core, idx)
          && v.tiles[dst.core].core.cache[idx].addr == addr
          && (
            || v.tiles[dst.core].core.cache[idx].coh.IMAD?
            || v.tiles[dst.core].core.cache[idx].coh.SMAD?
          )
        )
      )
      && (src == Cache(dst.core, eL1) ==> 
        (exists idx: nat :: 
          && NonEmptyEL1CacheEntry(c, v, dst.core, idx)
          && v.tiles[dst.core].engine.cache[idx].addr == addr
          && (
            || v.tiles[dst.core].engine.cache[idx].coh.IMAD?
            || v.tiles[dst.core].engine.cache[idx].coh.SMAD?
          )
        )
      )
    )
  }

  ghost predicate DataInFlightToT2FromT1MeansDirectoryInSD(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr, val, src: Location, dst: Location, idx: nat | (
      // TODO: and FwdGetS for that matter
      && src.Cache?
      && src.level.Tier1()
      && dst.Cache?
      && dst.level.L2?
      && DataInFlight(c, v, addr, src, dst, val) 
      && NonEmptyNonPendingL2CacheEntry(c, v, dst.core, idx)
      && v.tiles[dst.core].l2.cache[idx].addr == addr
    ) :: (
      DirSDL2CacheEntry(c, v, dst.core, idx)
    )
  }

  ghost predicate DataInFlightToT3FromT2MeansDirectoryInSD(c: Tako.Constants, v: Tako.Variables)
  {
    forall addr, val, src: Location, dst: Location, idx: nat | (
      // TODO: and FwdGetS for that matter
      && src.Cache?
      && src.level.L2?
      && dst.Cache?
      && dst.level.L3?
      && DataInFlight(c, v, addr, src, dst, val) 
      && NonEmptyNonPendingL3CacheEntry(c, v, dst.core, idx)
      && v.tiles[dst.core].l3.cache[idx].addr == addr
    ) :: (
      DirSDL3CacheEntry(c, v, dst.core, idx)
    )
  }

  ghost predicate L3AddrNotInCacheMeansL2AddrNotInCache(c: Tako.Constants, v: Tako.Variables)
  {
    forall core, addr | !PrivateMorph(addr) && L3AddrNotInCache(c, v, c.addr_map(addr), addr) :: (
      L2AddrNotInCache(c, v, core, addr)
    )
  }

  ghost predicate L3DirectoryInIMeansL2AddrNotInCache(c: Tako.Constants, v: Tako.Variables)
  {
    forall core1: nat, core2: nat, idx1: nat | DirIL3CacheEntry(c, v, core1, idx1) :: (
      L2AddrNotInCache(c, v, core2, v.tiles[core1].l3.cache[idx1].addr)
    )
  }

  /*
  ghost predicate L2CohSToMMeansL2DirSorI(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat | CohSToML2CacheEntry(c, v, core, idx) :: (
      && (
        || DirIL2CacheEntry(c, v, core, idx) 
        || DirSL2CacheEntry(c, v, core, idx)
        || DirSDProxyOwnerL2CacheEntry(c, v, core, idx)
        || DirMProxyOwnerL2CacheEntry(c, v, core, idx)
      ) 
      // && CleanL2CacheEntry(c, v, core, idx) // we know it is clean as well NO!
      // its not true that the data is clean...
      // scenario: L2 in coh M, dir in I, dirty
      // receives a fwdgets, downgrades to S, still dirty
    )
  }
  */

  ghost predicate L2NotDirIMeansLoadableCoh(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat | NonEmptyNonPendingL2CacheEntry(c, v, core, idx) && !DirIL2CacheEntry(c, v, core, idx)
     :: (
      && v.tiles[core].l2.cache[idx].coh.Loadable() 
    )
  }

  ghost predicate L2DirMorSDMeansL2CohM(c: Tako.Constants, v: Tako.Variables)
  {
    // we can only have DirM without proxy owner if we own the data in L2
    forall core: nat, idx: nat | (
      || (
        && DirML2CacheEntry(c, v, core, idx) 
        && v.tiles[core].l2.cache[idx].dir.owner != Cache(core, Proxy)
      )
      || (
        && DirSDL2CacheEntry(c, v, core, idx) 
        && v.tiles[core].l2.cache[idx].dir.former_owner != Cache(core, Proxy)
      )
    ) :: (
      CohML2CacheEntry(c, v, core, idx) 
      // strengthen: Proxy => loadable, nonproxy => M
    )
  }

  ghost predicate L2DirOwnerIsAlwaysTier1Cache(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat | (
      && DirML2CacheEntry(c, v, core, idx)
    ) :: (
      && v.tiles[core].l2.cache[idx].dir.owner.Cache?
      && v.tiles[core].l2.cache[idx].dir.owner.level.Tier1()
      && v.tiles[core].l2.cache[idx].dir.owner.core == core
    )
  }

  ghost predicate L2DirSharersAlwaysTier1Cache(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, loc: Location | (
      && (DirSL2CacheEntry(c, v, core, idx) || DirSDL2CacheEntry(c, v, core, idx))
      && loc in v.tiles[core].l2.cache[idx].dir.sharers
    ) :: (
      && loc.Cache?
      && loc.level.Tier1()
      && loc.core == core
    )
  }

  ghost predicate L3DirOwnerIsAlwaysTier2Cache(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat | (
      && DirML3CacheEntry(c, v, core, idx)
    ) :: (
      && v.tiles[core].l3.cache[idx].dir.owner.Cache?
      && v.tiles[core].l3.cache[idx].dir.owner.level.L2?
      // don't know which core
    )
  }

  ghost predicate L3DirSharersAlwaysTier2Cache(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, loc: Location | (
      && (DirSL3CacheEntry(c, v, core, idx) || DirSDL3CacheEntry(c, v, core, idx))
      && loc in v.tiles[core].l3.cache[idx].dir.sharers
    ) :: (
      && loc.Cache?
      && loc.level.L2?
    )
  }
  /*

  ghost predicate NotSharerSMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && (DirSL2CacheEntry(c, v, core, idx1) || DirSDL2CacheEntry(c, v, core, idx1)) 
      && !(Cache(core, L1) in v.tiles[core].l2.cache[idx1].dir.sharers)
      && idx2 < |v.tiles[core].core.cache|
      && v.tiles[core].core.cache[idx2].addr == v.tiles[core].l2.cache[idx1].addr
    ) :: (
      && !v.tiles[core].core.cache[idx2].coh.HasMostRecentVal()
    )
  }

  ghost predicate NotSharerSMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && (DirSL2CacheEntry(c, v, core, idx1) || DirSDL2CacheEntry(c, v, core, idx1)) 
      && !(Cache(core, eL1) in v.tiles[core].l2.cache[idx1].dir.sharers)
      && idx2 < |v.tiles[core].engine.cache|
      && v.tiles[core].engine.cache[idx2].addr == v.tiles[core].l2.cache[idx1].addr
    ) :: (
      && !v.tiles[core].engine.cache[idx2].coh.HasMostRecentVal()
    )
  }

  ghost predicate NotSharerSMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && (DirSL2CacheEntry(c, v, core, idx1) || DirSDL2CacheEntry(c, v, core, idx1)) 
      && !(Cache(core, Proxy) in v.tiles[core].l2.cache[idx1].dir.sharers)
      && idx2 < |v.tiles[core].proxy.cache|
      && v.tiles[core].proxy.cache[idx2].addr == v.tiles[core].l2.cache[idx1].addr
    ) :: (
      && !v.tiles[core].proxy.cache[idx2].coh.HasMostRecentVal()
    )
  }

  ghost predicate NotOwnerMAndNoFwdGetMMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirML2CacheEntry(c, v, core, idx1)
      && v.tiles[core].l2.cache[idx1].dir.owner != Cache(core, L1)
      && idx2 < |v.tiles[core].core.cache|
      && v.tiles[core].core.cache[idx2].addr == v.tiles[core].l2.cache[idx1].addr
      && (forall src : Location :: !FwdGetMInFlight(c, v, v.tiles[core].l2.cache[idx1].addr, src, Cache(core, L1)))
    ) :: (
      && !v.tiles[core].core.cache[idx2].coh.HasMostRecentVal()
    )
  }

  ghost predicate NotOwnerMAndNoFwdGetMMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirML2CacheEntry(c, v, core, idx1)
      && v.tiles[core].l2.cache[idx1].dir.owner != Cache(core, eL1)
      && idx2 < |v.tiles[core].engine.cache|
      && v.tiles[core].engine.cache[idx2].addr == v.tiles[core].l2.cache[idx1].addr
      && (forall src : Location :: !FwdGetMInFlight(c, v, v.tiles[core].l2.cache[idx1].addr, src, Cache(core, eL1)))
    ) :: (
      && !v.tiles[core].engine.cache[idx2].coh.HasMostRecentVal()
    )
  }

  ghost predicate NotOwnerMAndNoFwdGetMMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirML2CacheEntry(c, v, core, idx1)
      && v.tiles[core].l2.cache[idx1].dir.owner != Cache(core, Proxy)
      && idx2 < |v.tiles[core].proxy.cache|
      && v.tiles[core].proxy.cache[idx2].addr == v.tiles[core].l2.cache[idx1].addr
      && (forall src : Location :: !FwdGetMInFlight(c, v, v.tiles[core].l2.cache[idx1].addr, src, Cache(core, Proxy)))
    ) :: (
      && !v.tiles[core].proxy.cache[idx2].coh.HasMostRecentVal()
    )
  }
 
  ghost predicate PutSFromSharerMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirSL2CacheEntry(c, v, core, idx1)
      && PutSInFlight(c, v, v.tiles[core].l2.cache[idx1].addr, Cache(core, L1), Cache(core, L2))
      && (Cache(core, L1) in v.tiles[core].l2.cache[idx1].dir.sharers)
      && idx2 < |v.tiles[core].core.cache|
      && v.tiles[core].core.cache[idx2].addr == v.tiles[core].l2.cache[idx1].addr
    ) :: (
      && !v.tiles[core].core.cache[idx2].coh.HasMostRecentVal()
    )
  }
  
  ghost predicate PutSFromSharerMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirSL2CacheEntry(c, v, core, idx1)
      && PutSInFlight(c, v, v.tiles[core].l2.cache[idx1].addr, Cache(core, eL1), Cache(core, L2))
      && (Cache(core, eL1) in v.tiles[core].l2.cache[idx1].dir.sharers)
      && idx2 < |v.tiles[core].engine.cache|
      && v.tiles[core].engine.cache[idx2].addr == v.tiles[core].l2.cache[idx1].addr
    ) :: (
      && !v.tiles[core].engine.cache[idx2].coh.HasMostRecentVal()
    )
  }

  ghost predicate PutSFromSharerMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirSL2CacheEntry(c, v, core, idx1)
      && PutSInFlight(c, v, v.tiles[core].l2.cache[idx1].addr, Cache(core, Proxy), Cache(core, L2))
      && (Cache(core, Proxy) in v.tiles[core].l2.cache[idx1].dir.sharers)
      && idx2 < |v.tiles[core].proxy.cache|
      && v.tiles[core].proxy.cache[idx2].addr == v.tiles[core].l2.cache[idx1].addr
    ) :: (
      && !v.tiles[core].proxy.cache[idx2].coh.HasMostRecentVal()
    )
  }
  */

  ghost predicate PutMFromOwnerMeansNoLoadableInCore(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat, val: Value | (
      && DirML2CacheEntry(c, v, core, idx1)
      && PutMInFlight(c, v, v.tiles[core].l2.cache[idx1].addr, v.tiles[core].l2.cache[idx1].dir.owner, Cache(core, L2), val)
      && idx2 < |v.tiles[core].core.cache|
      && v.tiles[core].core.cache[idx2].addr == v.tiles[core].l2.cache[idx1].addr
    ) :: (
      && !v.tiles[core].core.cache[idx2].coh.HasMostRecentVal()
    )
  }

  ghost predicate PutMFromOwnerMeansNoLoadableInEngine(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat, val: Value | (
      && DirML2CacheEntry(c, v, core, idx1)
      && PutMInFlight(c, v, v.tiles[core].l2.cache[idx1].addr, v.tiles[core].l2.cache[idx1].dir.owner, Cache(core, L2), val)
      && idx2 < |v.tiles[core].engine.cache|
      && v.tiles[core].engine.cache[idx2].addr == v.tiles[core].l2.cache[idx1].addr
    ) :: (
      && !v.tiles[core].engine.cache[idx2].coh.HasMostRecentVal()
    )
  }
  /*
  ghost predicate PutMFromOwnerMeansNoLoadableInProxy(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat, val: Value | (
      && DirML2CacheEntry(c, v, core, idx1)
      && PutMInFlight(c, v, v.tiles[core].l2.cache[idx1].addr, v.tiles[core].l2.cache[idx1].dir.owner, Cache(core, L2), val)
      && idx2 < |v.tiles[core].proxy.cache|
      && v.tiles[core].proxy.cache[idx2].addr == v.tiles[core].l2.cache[idx1].addr
    ) :: (
      && !v.tiles[core].proxy.cache[idx2].coh.HasMostRecentVal()
    )
  }


  // needed to finish L2CohStoM reasoning
  // idea:
  // 1. !(getminflight && src == owner) needs to be proven at
  //   a. when src goes I-> IMAD/S->SMAD (producing GetM)
  //   b. when dir processes GetM and sets owner to src
  // b. will need a new inv:
  // 2. No 2 GetMs from same source in flight. needs to be proven at
  //   a. when src goes I-> IMAD/S->SMAD (producing GetM)
  // which will be proven by 3. GetMInFlight -> src in IMAD/SMAD (already exists)
  // a. will need a new inv: 
  // 4. (this one) When dir is M, then src can't be I/S needs to be proven at
  //   a. when src goes I/S (PutAck, FwdGetS, FwdGetM, Inv
  //   b. when dir processes GetM and sets owner to src
  // b. handled by 4. GetMInFlight -> src in IMAD/SMAD (already exists)
  // a. will need invs for these messages: PutAck in flight means dir !m with you being owner
  ghost predicate DirMMeansOwnerNotI(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && DirML2CacheEntry(c, v, core, idx1)
      && v.tiles[core].l2.cache[idx1].dir.owner == Cache(core, L1)
      && idx2 < |v.tiles[core].core.cache|
      && v.tiles[core].core.cache[idx2].addr == v.tiles[core].l2.cache[idx1].addr
    ) :: (
      && !v.tiles[core].core.cache[idx2].coh.I?
      && !v.tiles[core].core.cache[idx2].coh.S?
    )
  }

  ghost predicate DataFromOwnerMeansNoMInCore(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat, src: Location, val: Value | (
      && DirSDL2CacheEntry(c, v, core, idx1)
      && DataInFlight(c, v, v.tiles[core].l2.cache[idx1].addr, src, Cache(core, L2), val)
      && idx2 < |v.tiles[core].core.cache|
      && v.tiles[core].core.cache[idx2].addr == v.tiles[core].l2.cache[idx1].addr
    ) :: (
      && !v.tiles[core].core.cache[idx2].coh.M?
    )
  }

  ghost predicate DataFromOwnerMeansNoMInEngine(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat, src: Location, val: Value | (
      && DirSDL2CacheEntry(c, v, core, idx1)
      && DataInFlight(c, v, v.tiles[core].l2.cache[idx1].addr, src, Cache(core, L2), val)
      && idx2 < |v.tiles[core].engine.cache|
      && v.tiles[core].engine.cache[idx2].addr == v.tiles[core].l2.cache[idx1].addr
    ) :: (
      && !v.tiles[core].engine.cache[idx2].coh.M?
    )
  }

  ghost predicate DataToT2IsFromFormerOwner(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL2CacheEntry(c, v, core, idx)
      && src.Cache?
      && src.level.Tier1()
      && DataInFlight(c, v, v.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val)
    ) :: (
      && src == v.tiles[core].l2.cache[idx].dir.former_owner
    )
  }


  ghost predicate PutMFromOwnerL2MeansEpochHasWcb(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v, core, idx)
      && v.tiles[core].l2.cache[idx].dir.owner.Cache?
      && !v.tiles[core].l2.cache[idx].dir.owner.level.Proxy?
      && PutMInFlight(c, v, v.tiles[core].l2.cache[idx].addr, v.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && v.tiles[core].l2.cache[idx].addr.Morph?
    ) :: (
      && AddrIsInEpoch(c, v, v.tiles[core].l2.cache[idx].addr)
      && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.Some?
      && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.CBWrite()
      && var wval := if v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.Wcb? then v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.val else v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.wval;
      && wval == val
    )
  }

  ghost predicate DataFromOwnerL2MeansEpochHasWcb(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, src: Location, val: Value | (
      && DirSDL2CacheEntry(c, v, core, idx)
      && src.Cache?
      && src.level.Tier1()
      && !src.level.Proxy?
      && DataInFlight(c, v, v.tiles[core].l2.cache[idx].addr, src, Cache(core, L2), val)
      && v.tiles[core].l2.cache[idx].addr.Morph?
    ) :: (
      && AddrIsInEpoch(c, v, v.tiles[core].l2.cache[idx].addr)
      && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.Some?
      && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.CBWrite()
      && var wval := if v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.Wcb? then v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.val else v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.wval;
      && wval == val
    )
  }

  ghost predicate PutMFromProxyL2MeansEpochDataMatches(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, val: Value | (
      && DirML2CacheEntry(c, v, core, idx)
      && v.tiles[core].l2.cache[idx].dir.owner == Cache(core, Proxy)
      && PutMInFlight(c, v, v.tiles[core].l2.cache[idx].addr, v.tiles[core].l2.cache[idx].dir.owner, Cache(core, L2), val)
      && PrivateMorph(v.tiles[core].l2.cache[idx].addr)
    ) :: (
      && AddrIsInEpoch(c, v, v.tiles[core].l2.cache[idx].addr)
      && (DirtyL2CacheEntry(c, v, core, idx) ==> (
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.Some?
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.CBWrite()
        && var wval := if v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.Wcb? then v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.val else v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.wval;
        && wval == val
      ))
      && (CleanL2CacheEntry(c, v, core, idx) ==> (
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.None?
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].me.Me?
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].me.val == val
      ))
    )
  }

  ghost predicate DataFromProxyL2MeansEpochDataMatches(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat, val: Value | (
      && DirSDL2CacheEntry(c, v, core, idx)
      && DataInFlight(c, v, v.tiles[core].l2.cache[idx].addr, Cache(core, Proxy), Cache(core, L2), val)
      && PrivateMorph(v.tiles[core].l2.cache[idx].addr)
    ) :: (
      && AddrIsInEpoch(c, v, v.tiles[core].l2.cache[idx].addr)
      && (DirtyL2CacheEntry(c, v, core, idx) ==> (
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.Some?
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.CBWrite()
        && var wval := if v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.Wcb? then v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.val else v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.val.wval;
        && wval == val
      ))
      && (CleanL2CacheEntry(c, v, core, idx) ==> (
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].wcb.None?
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].me.Me?
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx].addr].me.val == val
      ))
    )
  }

  // UNUSED
  // ghost predicate WaitingForDataL2(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  // {
  //   && NonEmptyL2CacheEntry(c, v, core, idx)
  //   && v.tiles[core].l2.cache[idx].L2Entry?
  //   && (
  //     || v.tiles[core].l2.cache[idx].coh.IMAD?
  //     || v.tiles[core].l2.cache[idx].coh.ISD?
  //     || v.tiles[core].l2.cache[idx].coh.SMAD?
  //   )
  // }

  // ghost predicate WaitingForDataL2MeansDataIsClean(c: Tako.Constants, v: Tako.Variables)
  // {
  //   forall core: nat, idx: nat | WaitingForDataL2(c, v, core, idx) :: (
  //     !v.tiles[core].l2.cache[idx].dirty
  //   )
  // }




  ghost predicate HavingDataInMMeansDirectoryinMorSDCore(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyL1CacheEntry(c, v, core, idx1) 
      && NonEmptyL2CacheEntry(c, v, core, idx2)
      && v.tiles[core].core.cache[idx1].addr == v.tiles[core].l2.cache[idx2].addr
      && v.tiles[core].core.cache[idx1].coh.M? 
    ) :: (
      || (
        && DirML2CacheEntry(c, v, core, idx2) // owner could be someone else, not necessarily you (FwdGetM en route)
        // cant guarantee that source of FwdGetM is the new owner either, as we can chain FwdGetMs
        // well, we can, but its not necessarily the same FwdGetM...
        && (
          // so either we are the owner,
          || v.tiles[core].l2.cache[idx2].dir.owner == Cache(core, L1)
          // or there is a fwdgetm with the source being the owner
          || (exists dst : Location :: (
            && dst.Cache?
            && dst.level.Tier1()
            && dst.core == core
            && FwdGetMInFlight(c, v, v.tiles[core].l2.cache[idx2].addr, v.tiles[core].l2.cache[idx2].dir.owner, dst)
          ))
        )
        && (DirMProxyOwnerL2CacheEntry(c, v, core, idx2) ==> DirtyL2CacheEntry(c, v, core, idx2))
      )
      || (
        && DirSDL2CacheEntry(c, v, core, idx2) // if in SD, FwdGetS is on its way
        && v.tiles[core].l2.cache[idx2].dir.former_owner == Cache(core, L1)
      )
    )
  }

  ghost predicate HavingDataInMMeansDirectoryinMorSDEngine(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyEL1CacheEntry(c, v, core, idx1) 
      && NonEmptyL2CacheEntry(c, v, core, idx2)
      && v.tiles[core].engine.cache[idx1].addr == v.tiles[core].l2.cache[idx2].addr
      && v.tiles[core].engine.cache[idx1].coh.M? 
    ) :: (
      || (
        && DirML2CacheEntry(c, v, core, idx2) // owner could be someone else, not necessarily you (FwdGetM en route)
        // cant guarantee that source of FwdGetM is the new owner either, as we can chain FwdGetMs
        // well, we can, but its not necessarily the same FwdGetM...
        && (
          // so either we are the owner,
          || v.tiles[core].l2.cache[idx2].dir.owner == Cache(core, eL1)
          // or there is a fwdgetm with the source being the owner
          || (exists dst : Location :: (
            && dst.Cache?
            && dst.level.Tier1()
            && dst.core == core
            && FwdGetMInFlight(c, v, v.tiles[core].l2.cache[idx2].addr, v.tiles[core].l2.cache[idx2].dir.owner, dst)
          ))
        )
        && (DirMProxyOwnerL2CacheEntry(c, v, core, idx2) ==> DirtyL2CacheEntry(c, v, core, idx2))
      )
      || (
        && DirSDL2CacheEntry(c, v, core, idx2) // if in SD, FwdGetS is on its way
        && v.tiles[core].l2.cache[idx2].dir.former_owner == Cache(core, eL1)
      )
    )
  }

  // ghost predicate HavingDataInMMeansDirectoryinMorSDProxy(c: Tako.Constants, v: Tako.Variables)
  // {
  //   forall core: nat, idx1: nat, idx2: nat | (
  //     && NonEmptyProxyCacheEntry(c, v, core, idx1) 
  //     && NonEmptyL2CacheEntry(c, v, core, idx2)
  //     && v.tiles[core].proxy.cache[idx1].addr == v.tiles[core].l2.cache[idx2].addr
  //     && v.tiles[core].proxy.cache[idx1].coh.M? 
  //   ) :: (
  //     || (
  //       && DirML2CacheEntry(c, v, core, idx2) // owner could be someone else, not necessarily you (FwdGetM en route)
  //     )
  //     || (
  //       && DirSDL2CacheEntry(c, v, core, idx2) // if in SD, FwdGetS is on its way
  //       && v.tiles[core].l2.cache[idx2].dir.former_owner == Cache(core, Proxy)
  //     )
  //   )
  // }

  ghost predicate HavingDataInMMeansDirectoryinMorSDL2(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v, core, idx1)
      && NonEmptyL3CacheEntry(c, v, c.addr_map(v.tiles[core].l2.cache[idx1].addr), idx2)
      && v.tiles[core].l2.cache[idx1].addr == v.tiles[c.addr_map(v.tiles[core].l2.cache[idx1].addr)].l3.cache[idx2].addr
      && v.tiles[core].l2.cache[idx1].coh.M? 
    ) :: (
      || (
        && DirML3CacheEntry(c, v, c.addr_map(v.tiles[core].l2.cache[idx1].addr), idx2)
        && (
          // so either we are the owner,
          || v.tiles[c.addr_map(v.tiles[core].l2.cache[idx1].addr)].l3.cache[idx2].dir.owner == Cache(core, L2)
          // or there is a fwdgetm with the source being the owner
          || (exists dst : Location :: (
            && dst.Cache?
            && dst.level.L2?
            && FwdGetMInFlight(c, v, v.tiles[core].l2.cache[idx1].addr, v.tiles[c.addr_map(v.tiles[core].l2.cache[idx1].addr)].l3.cache[idx2].dir.owner, dst)
          ))
        )
      )
      || (
        && DirSDL3CacheEntry(c, v, c.addr_map(v.tiles[core].l2.cache[idx1].addr), idx2) // if in SD, FwdGetS is on its way
        && v.tiles[c.addr_map(v.tiles[core].l2.cache[idx1].addr)].l3.cache[idx2].dir.former_owner == Cache(core, L2)
      )
    )
  }

  // ghost predicate L2SharedCoherenceWithDirMMeansProxyIsOwner(c: Tako.Constants, v: Tako.Variables)
  // {
  //   forall core: nat, idx: nat | (
  //     && DirML2CacheEntry(c, v, core, idx)
  //     && v.tiles[core].l2.cache[idx].coh.Loadable()
  //     && !v.tiles[core].l2.cache[idx].coh.M?
  //   ) :: (
  //     && v.tiles[core].l2.cache[idx].dir.owner == Cache(core, Proxy)
  //   )
  // }
  */

  ghost predicate L2EvictingOrPreDataCoherenceMeansDirI(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v, core, idx)
      && (
        || v.tiles[core].l2.cache[idx].coh.Evicting()
        || v.tiles[core].l2.cache[idx].coh.PreData() // I excluded by nonempty
        || v.tiles[core].l2.cache[idx].coh.IMA?
      )
    ) :: (
      && DirIL2CacheEntry(c, v, core, idx)
      // && ((
      //   || v.tiles[core].l2.cache[idx].coh.PreData() // I excluded by nonempty
      //   || v.tiles[core].l2.cache[idx].coh.IMA?
      // ) ==> 
      //   CleanL2CacheEntry(c, v, core, idx)
      // )
    )
  }

  /*
  ghost predicate DirtyMorphAddressHasMostRecentWriteCore(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat | (
      && NonEmptyL1CacheEntry(c, v, core, idx)
      && v.tiles[core].core.cache[idx].dirty
      && v.tiles[core].core.cache[idx].coh.Loadable()
      && v.tiles[core].core.cache[idx].addr.Morph?
    ) :: (
      && AddrIsInEpoch(c, v, v.tiles[core].core.cache[idx].addr)
      && v.g.callback_epochs[v.tiles[core].core.cache[idx].addr].wcb.Some?
      && v.g.callback_epochs[v.tiles[core].core.cache[idx].addr].wcb.val.CBWrite()
      && var wval := if v.g.callback_epochs[v.tiles[core].core.cache[idx].addr].wcb.val.Wcb? then v.g.callback_epochs[v.tiles[core].core.cache[idx].addr].wcb.val.val else v.g.callback_epochs[v.tiles[core].core.cache[idx].addr].wcb.val.wval;
      && wval == v.tiles[core].core.cache[idx].coh.val
    )
  }
  
  ghost predicate DirtyMorphAddressHasMostRecentWriteEngine(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat | (
      && NonEmptyEL1CacheEntry(c, v, core, idx)
      && v.tiles[core].engine.cache[idx].dirty
      && v.tiles[core].engine.cache[idx].coh.Loadable()
      && v.tiles[core].engine.cache[idx].addr.Morph?
    ) :: (
      && AddrIsInEpoch(c, v, v.tiles[core].engine.cache[idx].addr)
      && v.g.callback_epochs[v.tiles[core].engine.cache[idx].addr].wcb.Some?
      && v.g.callback_epochs[v.tiles[core].engine.cache[idx].addr].wcb.val.CBWrite()
      && var wval := if v.g.callback_epochs[v.tiles[core].engine.cache[idx].addr].wcb.val.Wcb? then v.g.callback_epochs[v.tiles[core].engine.cache[idx].addr].wcb.val.val else v.g.callback_epochs[v.tiles[core].engine.cache[idx].addr].wcb.val.wval;
      && wval == v.tiles[core].engine.cache[idx].coh.val
    )
  }

  
  ghost predicate MStateMorphAddressHasMostRecentWriteProxy(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyProxyCacheEntry(c, v, core, idx1)
      && NonEmptyL2CacheEntry(c, v, core, idx2)
      && (
        || v.tiles[core].proxy.cache[idx1].coh.M?
        || v.tiles[core].proxy.cache[idx1].coh.IMA?
        || v.tiles[core].proxy.cache[idx1].coh.SMA?
      )
      && v.tiles[core].l2.cache[idx2].addr == v.tiles[core].proxy.cache[idx1].addr
      && PrivateMorph(v.tiles[core].proxy.cache[idx1].addr)
    ) :: (
      && AddrIsInEpoch(c, v, v.tiles[core].proxy.cache[idx1].addr)
      && (DirtyL2CacheEntry(c, v, core, idx2) ==> (
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx2].addr].wcb.Some?
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx2].addr].wcb.val.CBWrite()
        && var wval := if v.g.callback_epochs[v.tiles[core].l2.cache[idx2].addr].wcb.val.Wcb? then v.g.callback_epochs[v.tiles[core].l2.cache[idx2].addr].wcb.val.val else v.g.callback_epochs[v.tiles[core].l2.cache[idx2].addr].wcb.val.wval;
        && wval == v.tiles[core].proxy.cache[idx1].coh.val
      ))
      && (CleanL2CacheEntry(c, v, core, idx2) ==> (
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx2].addr].wcb.None?
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx2].addr].me.Me?
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx2].addr].me.val == v.tiles[core].proxy.cache[idx1].coh.val
      ))
    )
  }

  // how about: 
  // dir receives PutM, goes to I, sends out PutAck
  // someone else sends out GetM, receives data, then writes.
  // so not true in MIA
  // in order for someone else to write,

  // does the dst need to be the l1?
  // i think yes:
  // dir receives PutM, goes to I, sends out PutAck
  // someone else sends out GetM, receives data, then writes.
  // third party sends out GetS, dir Sends FwdGetS

  ghost predicate MEvictingMorphAddressWithMatchingDirOwnerHasMostRecentWriteCore(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyL1CacheEntry(c, v, core, idx1)
      && (
        || v.tiles[core].core.cache[idx1].coh.MIA?
        || v.tiles[core].core.cache[idx1].coh.MIF?
      )
      && (
        || (DirML2CacheEntry(c, v, core, idx2) && v.tiles[core].l2.cache[idx2].dir.owner == Cache(core, L1))
        || (DirSDL2CacheEntry(c, v, core, idx2) && v.tiles[core].l2.cache[idx2].dir.former_owner == Cache(core, L1))
      )
      && v.tiles[core].l2.cache[idx2].addr == v.tiles[core].core.cache[idx1].addr
      && v.tiles[core].core.cache[idx1].addr.Morph?
    ) :: (
      && AddrIsInEpoch(c, v, v.tiles[core].core.cache[idx1].addr)
      && v.g.callback_epochs[v.tiles[core].core.cache[idx1].addr].wcb.Some?
      && v.g.callback_epochs[v.tiles[core].core.cache[idx1].addr].wcb.val.CBWrite()
      && var wval := if v.g.callback_epochs[v.tiles[core].core.cache[idx1].addr].wcb.val.Wcb? then v.g.callback_epochs[v.tiles[core].core.cache[idx1].addr].wcb.val.val else v.g.callback_epochs[v.tiles[core].core.cache[idx1].addr].wcb.val.wval;
      && wval == v.tiles[core].core.cache[idx1].coh.val
    )
  }

  ghost predicate MEvictingMorphAddressWithMatchingDirOwnerHasMostRecentWriteEngine(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyEL1CacheEntry(c, v, core, idx1)
      && (
        || v.tiles[core].engine.cache[idx1].coh.MIA?
        || v.tiles[core].engine.cache[idx1].coh.MIF?
      )
      && (
        || (DirML2CacheEntry(c, v, core, idx2) && v.tiles[core].l2.cache[idx2].dir.owner == Cache(core, eL1))
        || (DirSDL2CacheEntry(c, v, core, idx2) && v.tiles[core].l2.cache[idx2].dir.former_owner == Cache(core, eL1))
      )
      && v.tiles[core].l2.cache[idx2].addr == v.tiles[core].engine.cache[idx1].addr
      && v.tiles[core].engine.cache[idx1].addr.Morph?
    ) :: (
      && AddrIsInEpoch(c, v, v.tiles[core].engine.cache[idx1].addr)
      && v.g.callback_epochs[v.tiles[core].engine.cache[idx1].addr].wcb.Some?
      && v.g.callback_epochs[v.tiles[core].engine.cache[idx1].addr].wcb.val.CBWrite()
      && var wval := if v.g.callback_epochs[v.tiles[core].engine.cache[idx1].addr].wcb.val.Wcb? then v.g.callback_epochs[v.tiles[core].engine.cache[idx1].addr].wcb.val.val else v.g.callback_epochs[v.tiles[core].engine.cache[idx1].addr].wcb.val.wval;
      && wval == v.tiles[core].engine.cache[idx1].coh.val
    )
  }

  ghost predicate MEvictingMorphAddressWithMatchingDirOwnerHasMostRecentWriteProxy(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx1: nat, idx2: nat | (
      && NonEmptyProxyCacheEntry(c, v, core, idx1)
      && NonEmptyL2CacheEntry(c, v, core, idx2)
      && (
        || v.tiles[core].proxy.cache[idx1].coh.MIA?
        || v.tiles[core].proxy.cache[idx1].coh.MIF?
      )
      && (
        || DirMProxyOwnerL2CacheEntry(c, v, core, idx2)
        || DirSDProxyOwnerL2CacheEntry(c, v, core, idx2)
      )
      && v.tiles[core].l2.cache[idx2].addr == v.tiles[core].proxy.cache[idx1].addr
      && PrivateMorph(v.tiles[core].proxy.cache[idx1].addr)
    ) :: (
      && AddrIsInEpoch(c, v, v.tiles[core].proxy.cache[idx1].addr)
      && (DirtyL2CacheEntry(c, v, core, idx2) ==> (
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx2].addr].wcb.Some?
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx2].addr].wcb.val.CBWrite()
        && var wval := if v.g.callback_epochs[v.tiles[core].l2.cache[idx2].addr].wcb.val.Wcb? then v.g.callback_epochs[v.tiles[core].l2.cache[idx2].addr].wcb.val.val else v.g.callback_epochs[v.tiles[core].l2.cache[idx2].addr].wcb.val.wval;
        && wval == v.tiles[core].proxy.cache[idx1].coh.val
      ))
      && (CleanL2CacheEntry(c, v, core, idx2) ==> (
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx2].addr].wcb.None?
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx2].addr].me.Me?
        && v.g.callback_epochs[v.tiles[core].l2.cache[idx2].addr].me.val == v.tiles[core].proxy.cache[idx1].coh.val
      ))
    )
  }

  ghost predicate L2InCohMMeansAddrNotInOtherL2s(c: Tako.Constants, v: Tako.Variables)
  {
    forall core1: nat, core2: nat, idx: nat | (
      && CohML2CacheEntry(c, v, core1, idx)
      && core1 != core2
    ) :: (
      L2AddrNotInCache(c, v, core2, v.tiles[core1].l2.cache[idx].addr)
    )
  }

  ghost predicate L1InCohMMeansAddrNotInOtherL1s(c: Tako.Constants, v: Tako.Variables)
  {
    forall core1: nat, core2: nat, idx: nat | (
      && CohML1CacheEntry(c, v, core1, idx)
    ) :: (
      // other L1s
      && (core1 != core2 ==> L1AddrNotMostRecentVal(c, v, core2, v.tiles[core1].core.cache[idx].addr))
      // all eL1s
      && EL1AddrNotMostRecentVal(c, v, core2, v.tiles[core1].core.cache[idx].addr)
      // all Proxys
      && ProxyAddrNotMostRecentVal(c, v, core2, v.tiles[core1].core.cache[idx].addr)
    )
  }

  ghost predicate EL1InCohMMeansAddrNotInOtherL1s(c: Tako.Constants, v: Tako.Variables)
  {
    forall core1: nat, core2: nat, idx: nat | (
      && CohMEL1CacheEntry(c, v, core1, idx)
    ) :: (
      // other EL1s
      && (core1 != core2 ==> EL1AddrNotMostRecentVal(c, v, core2, v.tiles[core1].engine.cache[idx].addr))
      // all L1s
      && L1AddrNotMostRecentVal(c, v, core2, v.tiles[core1].engine.cache[idx].addr)
      // all Proxys
      && ProxyAddrNotMostRecentVal(c, v, core2, v.tiles[core1].engine.cache[idx].addr)
    )
  }

  ghost predicate ProxyInCohMMeansAddrNotInOtherL1s(c: Tako.Constants, v: Tako.Variables)
  {
    forall core1: nat, core2: nat, idx: nat | (
      && CohMProxyCacheEntry(c, v, core1, idx)
    ) :: (
      // all EL1s
      && EL1AddrNotMostRecentVal(c, v, core2, v.tiles[core1].proxy.cache[idx].addr)
      // all L1s
      && L1AddrNotMostRecentVal(c, v, core2, v.tiles[core1].proxy.cache[idx].addr)
    )
  }
  */
  ghost predicate AllReqsToTier2HasTier1Source(c: Tako.Constants, v: Tako.Variables)
  {
    forall msg | (
      && msg in v.network.inFlightMessages 
      && msg.CoherenceMsg?
      && (msg.coh_msg.GetS? || msg.coh_msg.GetM? || msg.coh_msg.PutS? || msg.coh_msg.PutM?)
      && msg.meta.dst.Cache? 
      && msg.meta.dst.level.L2?
    ) :: (
      && msg.meta.src.Cache?
      && msg.meta.src.level.Tier1()
      && msg.meta.src.core == msg.meta.dst.core
    )
  }

  ghost predicate AllReqsToTier3HasTier2Source(c: Tako.Constants, v: Tako.Variables)
  {
    forall msg | (
      && msg in v.network.inFlightMessages 
      && msg.CoherenceMsg?
      && (msg.coh_msg.GetS? || msg.coh_msg.GetM? || msg.coh_msg.PutS? || msg.coh_msg.PutM?)
      && msg.meta.dst.Cache? 
      && msg.meta.dst.level.L3?
    ) :: (
      && msg.meta.src.Cache?
      && msg.meta.src.level.L2?
    )
  }

  ghost predicate AllPutAcksToTier2HasTier3Source(c: Tako.Constants, v: Tako.Variables)
  {
    forall msg | (
      && msg in v.network.inFlightMessages 
      && msg.CoherenceMsg?
      && (msg.coh_msg.PutAck? || msg.coh_msg.PutAckStale?)
      && msg.meta.dst.Cache? 
      && msg.meta.dst.level.L2?
    ) :: (
      && msg.meta.src.Cache?
      && msg.meta.src.level.L3?
    )
  }

  ghost predicate AllDataToTier2FromCache(c: Tako.Constants, v: Tako.Variables)
  {
    forall msg | (
      && msg in v.network.inFlightMessages 
      && msg.CoherenceMsg?
      && msg.coh_msg.Data?
      && msg.meta.dst.Cache? 
      && msg.meta.dst.level.L2?
    ) :: (
      && msg.meta.src.Cache?
      && (msg.meta.src.level.Tier1() ==> msg.meta.src.core == msg.meta.dst.core)
    )
  }

  ghost predicate AllDataToTier3FromTier2Cache(c: Tako.Constants, v: Tako.Variables)
  {
    forall msg | (
      && msg in v.network.inFlightMessages 
      && msg.CoherenceMsg?
      && msg.coh_msg.Data?
      && msg.meta.dst.Cache? 
      && msg.meta.dst.level.L3?
      && msg.meta.src.Cache?
    ) :: (
      && msg.meta.src.level.L2?
    )
  }

  ghost predicate AllFwdReqsToTier1HasTier1Source(c: Tako.Constants, v: Tako.Variables)
  {
    forall msg | (
      && msg in v.network.inFlightMessages 
      && msg.CoherenceMsg?
      && (msg.coh_msg.FwdGetS? || msg.coh_msg.FwdGetM? || msg.coh_msg.Inv?)
      && msg.meta.dst.Cache? 
      && msg.meta.dst.level.Tier1()
    ) :: (
      && msg.meta.src.Cache?
      && msg.meta.src.level.Tier1()
      && msg.meta.src.core == msg.meta.dst.core
    )
  }

  ghost predicate AllFwdReqsFromTier1HasTier1Dst(c: Tako.Constants, v: Tako.Variables)
  {
    forall msg | (
      && msg in v.network.inFlightMessages 
      && msg.CoherenceMsg?
      && (msg.coh_msg.FwdGetS? || msg.coh_msg.FwdGetM? || msg.coh_msg.Inv?)
      && msg.meta.src.Cache?
      && msg.meta.src.level.Tier1()
    ) :: (
      && msg.meta.dst.Cache? 
      && msg.meta.dst.level.Tier1()
      && msg.meta.dst.core == msg.meta.src.core
    )
  }

  ghost predicate AllFwdReqsToTier2HasTier2Source(c: Tako.Constants, v: Tako.Variables)
  {
    forall msg | (
      && (
        || msg in v.network.inFlightMessages
        || (
          && msg.meta.dst.Cache?
          && msg.meta.dst.level.L2?
          && msg.meta.dst.core < |v.tiles|
          && |v.tiles[msg.meta.dst.core].l2.next_coh_msg_t2| == 2
          && v.tiles[msg.meta.dst.core].l2.next_coh_msg_t2[0].Some?
          && msg == v.tiles[msg.meta.dst.core].l2.next_coh_msg_t2[0].val
        )
      )
      && msg.CoherenceMsg?
      && (msg.coh_msg.FwdGetS? || msg.coh_msg.FwdGetM? || msg.coh_msg.Inv? || msg.coh_msg.InvAck?)
      && msg.meta.dst.Cache? 
      && msg.meta.dst.level.L2?
    ) :: (
      && msg.meta.src.Cache?
      && msg.meta.src.level.L2?
    )
  }

  ghost predicate PreMStateMeansNotDirtyCore(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat | (
      && NonEmptyL1CacheEntry(c, v, core, idx)
      && (
        || v.tiles[core].core.cache[idx].coh.PreData()
        || v.tiles[core].core.cache[idx].coh.IMA?
        || v.tiles[core].core.cache[idx].coh.SMA?
        || v.tiles[core].core.cache[idx].coh.SMAD?
      )
    ) :: (
      !v.tiles[core].core.cache[idx].dirty
    )
  }

  ghost predicate PreMStateMeansNotDirtyEngine(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat | (
      && NonEmptyEL1CacheEntry(c, v, core, idx)
      && (
        || v.tiles[core].engine.cache[idx].coh.PreData()
        || v.tiles[core].engine.cache[idx].coh.IMA?
        || v.tiles[core].engine.cache[idx].coh.SMA?
        || v.tiles[core].engine.cache[idx].coh.SMAD?
      )
    ) :: (
      !v.tiles[core].engine.cache[idx].dirty
    )
  }

  ghost predicate PreMStateMeansNotDirtyL2(c: Tako.Constants, v: Tako.Variables)
  {
    forall core: nat, idx: nat | (
      && NonEmptyNonPendingL2CacheEntry(c, v, core, idx)
      && (
        || v.tiles[core].l2.cache[idx].coh.PreData()
        || v.tiles[core].l2.cache[idx].coh.IMA?
        || v.tiles[core].l2.cache[idx].coh.SMA?
        || v.tiles[core].l2.cache[idx].coh.SMAD?
      )
    ) :: (
      !v.tiles[core].l2.cache[idx].dirty
    )
  }

  
  // ghost predicate EachAddrInL3BoundMemMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables)
  // {
  //   forall msg | InFlightMemoryResponse(c, v, msg) :: (
  //     && msg.meta.dst.Cache?
  //     && msg.meta.dst.level.L3?
  //     && c.addr_map(msg.meta.addr) == msg.meta.dst.core
  //     && msg.meta.addr.Regular?
  //   )
  // }


  ////////////////////////////////////////////////////////////////////
  // Address uniqueness In Cache Invariants
  ////////////////////////////////////////////////////////////////////

  ghost predicate NonEmptyL1CacheEntry(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  {
    && core < |v.tiles|
    && idx < |v.tiles[core].core.cache|
    && !v.tiles[core].core.cache[idx].coh.I?
  }
  
  ghost predicate L1AddressesUnique(c: Tako.Constants, v: Tako.Variables)
  {
    && (forall core: nat, idx1: nat, idx2: nat | (
        && NonEmptyL1CacheEntry(c, v, core, idx1)
        && NonEmptyL1CacheEntry(c, v, core, idx2)
        && v.tiles[core].core.cache[idx1].addr == v.tiles[core].core.cache[idx2].addr
      ) :: (
      idx1 == idx2
      )
    )
  }

  ghost predicate NonEmptyEL1CacheEntry(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  {
    && core < |v.tiles|
    && idx < |v.tiles[core].engine.cache|
    && !v.tiles[core].engine.cache[idx].coh.I?
  }

  ghost predicate EL1AddressesUnique(c: Tako.Constants, v: Tako.Variables)
  {
    && (forall core: nat, idx1: nat, idx2: nat | (
        && NonEmptyEL1CacheEntry(c, v, core, idx1)
        && NonEmptyEL1CacheEntry(c, v, core, idx2)
        && v.tiles[core].engine.cache[idx1].addr == v.tiles[core].engine.cache[idx2].addr
      ) :: (
      idx1 == idx2
      )
    )
  }

  ghost predicate NonEmptyProxyCacheEntry(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  {
    && core < |v.tiles|
    && idx < |v.tiles[core].proxy.cache|
    && !v.tiles[core].proxy.cache[idx].coh.I?
  }

  ghost predicate ProxyAddressesUnique(c: Tako.Constants, v: Tako.Variables)
  {
    && (forall core: nat, idx1: nat, idx2: nat | (
        && NonEmptyProxyCacheEntry(c, v, core, idx1)
        && NonEmptyProxyCacheEntry(c, v, core, idx2)
        && v.tiles[core].proxy.cache[idx1].addr == v.tiles[core].proxy.cache[idx2].addr
      ) :: (
      idx1 == idx2
      )
    )
  }

  ghost predicate NonEmptyL2CacheEntry(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  {
    && core < |v.tiles|
    && idx < |v.tiles[core].l2.cache|
    && (v.tiles[core].l2.cache[idx].L2Entry? ==> !v.tiles[core].l2.cache[idx].coh.I?)
  }

  ghost predicate NonEmptyNonPendingL2CacheEntry(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  {
    && NonEmptyL2CacheEntry(c, v, core, idx)
    && v.tiles[core].l2.cache[idx].L2Entry?
  }

  ghost predicate L2AddressesUnique(c: Tako.Constants, v: Tako.Variables)
  {
    && (forall core: nat, idx1: nat, idx2: nat | (
        && NonEmptyL2CacheEntry(c, v, core, idx1)
        && NonEmptyL2CacheEntry(c, v, core, idx2)
        && v.tiles[core].l2.cache[idx1].addr == v.tiles[core].l2.cache[idx2].addr
      ) :: (
      idx1 == idx2
      )
    )
  }
  
  ghost predicate NonEmptyL3CacheEntry(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  {
    && core < |v.tiles|
    && idx < |v.tiles[core].l3.cache|
    && !v.tiles[core].l3.cache[idx].Empty?
  }

  ghost predicate NonEmptyNonPendingL3CacheEntry(c: Tako.Constants, v: Tako.Variables, core: nat, idx: nat)
  {
    && core < |v.tiles|
    && idx < |v.tiles[core].l3.cache|
    && v.tiles[core].l3.cache[idx].L3Entry?
  }

  ghost predicate L3AddressesUnique(c: Tako.Constants, v: Tako.Variables)
  {
    && (forall core: nat, idx1: nat, idx2: nat | (
        && NonEmptyL3CacheEntry(c, v, core, idx1)
        && NonEmptyL3CacheEntry(c, v, core, idx2)
        && v.tiles[core].l3.cache[idx1].addr == v.tiles[core].l3.cache[idx2].addr
      ) :: (
      idx1 == idx2
      )
    )
  }

  // ghost function SumOfTokens<T>(items: set<(T, nat)>) : nat
  // {
  //     if items == {}
  //     then 0
  //     else
  //     var x :| x in items;
  //     SumOfTokens(items - {x}) + x.1
  // }


  // ghost predicate NumberOfTokensAlwaysMatches(c: Tako.Constants, v: Tako.Variables)
  // {
  //   && forall addr: Address | addr in v.token_counter :: (
  //     && v.token_counter[addr].total_tokens == SumOfTokens(v.token_counter[addr].token_tracker.Items)
  //   )
  //   // && v.g.tokens >= 0
  //   // && v.g.tokens == (v.g.callback_epochs.Count() + v.network.inFlightMessages.Count())
  //   // && (forall addr: Address | AddrIsInEpoch(c, v, addr) ==> (
  //   //   && v.g.callback_epochs[addr].wcb.Count() + v.g.callback_epochs[addr].me.Count() <= 1
  //   // ))
  // }

  // lemma Test(c: Tako.Constants, v: Tako.Variables)
  //   requires Tako.Init(c, v)
  //   ensures NumberOfTokensAlwaysMatches(c, v)
  // {
  // }

  // SWMR Invariants
  // ghost predicate SWMR_T1(c: Tako.Constants, v: Tako.Variables)
  // {
  //   true
  //   // && NonEmptyL2CacheEntry(c, v, core, idx)
  //   // && v.tiles[core].l2.cache[idx].L2Entry?
  //   // && v.tiles[core].l2.cache[idx].coh.T1()
  //   // && !v.tiles[core].l2.cache[idx].dirty
  //   // && v.tiles[core].l2.cache[idx].dir.owner == Cache(core, L1)
  // }

  // the question is: how do we get around the fact that processing data in the core and transitioning to loadable
  // is a viable transition?

  // going back, maybe its something like OnEvictInProgress => cur owners structure doesn't have core
  // does reading data put us in cur owners structure tho? then we still need to deal with this transition in core
  // loadable in core <=> core in cur owners structure

  // goal: no inv about data

  // however, when proving OnEvictInProgress => cur owners structure doesn't have core, we will run into
  // scenario about reading data and getting added to cur owners
  // the issue we are running into is figuring out the notion of when epochs are set in a protocol with transient states...


  // option 1: this transition is when we go to current owner
  // benefit here: we get the iff with the state of the curr owner
  // issue is what state are we in while data and invs are in flight?

  // option 2: we set with the directory. As soon as dir says you are owner, you are.
  // this fails however, because engine can perf store after core becomes owner by stalling the FwdGetM.

  // so the data in flight proof is not necessary because...
  // data in flight has
  // dir I <==> tokens == T
  // M <=> your tokens == T
  // total tokens == T
  // loadable ==> your tokens > 0
  // tokens > 0 ==> InEpoch
  //                && None? => val matches me
  //                && Some? => val matches wcb
  

  // independent proof: dirty ==> some, non
}