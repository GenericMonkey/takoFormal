include "../../model/types.s.dfy"
include "../../model/tako_spec.i.dfy"
include "../../model/tako.i.dfy"

include "refinement_defns.i.dfy"

module RefinementInitProof {
  import opened TakoRefinementDefns
  import opened Execution

  lemma InitAbstractionCorrect(c: Tako.Constants, v: Tako.Variables)
    requires Tako.Init(c, v)
    ensures TakoSpec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
  {
    reveal Program.Program.WF;
  }

  lemma InvPerfStoreHoldsInitially(c: Tako.Constants, v: Tako.Variables)
    requires Tako.Init(c, v)
    ensures InvPerfStore(c, v)
  {}

  lemma InvCorrectCoreHoldsInitially(c: Tako.Constants, v: Tako.Variables)
    requires Tako.Init(c, v)
    ensures InvCorrectCore(c, v)
  {}

  lemma InvAddressesUniqueHoldsInitially(c: Tako.Constants, v: Tako.Variables)
    requires Tako.Init(c, v)
    ensures InvAddressesUnique(c, v)
  {}

  lemma InvCallbackProgressHoldsInitially(c: Tako.Constants, v: Tako.Variables)
    requires Tako.Init(c, v)
    ensures InvCallbackProgress(c, v)
  {
    reveal CallbackPresent;
    reveal InFlightOnMissRequest;
    reveal InFlightOnMissResponse;
    reveal InFlightOnEvictRequest;
    reveal InFlightOnWritebackRequest;
    reveal L2PendingCallbackForAddr;
    reveal L3PendingCallbackForAddr;
  }

  lemma InvStartCallbackHoldsInitially(c: Tako.Constants, v: Tako.Variables)
    requires Tako.Init(c, v)
    ensures InvStartCallback(c, v)
  {}

  lemma InvEpochsHoldsInitially(c: Tako.Constants, v: Tako.Variables)
    requires Tako.Init(c, v)
    ensures InvEpochs(c, v)
  {
    reveal Program.Program.WF;
    reveal UnstartedCallbackPresent;
    reveal InFlightOnMissRequest;
    reveal InFlightOnEvictRequest;
    reveal InFlightOnEvictRequestForAddr;
    reveal UnstartedOnEvictEntryForAddr;
    reveal InFlightOnWritebackRequest;
    reveal InFlightOnWritebackRequestForAddr;
    reveal UnstartedOnWritebackEntryForAddr;
    reveal L2PendingCallbackForAddr;
    reveal L3PendingCallbackForAddr;
    reveal MorphAddrIsInL2CacheEntry;
    reveal MorphAddrIsInL3CacheEntry;
  }

  lemma InvDirtyBitHoldsInitially(c: Tako.Constants, v: Tako.Variables)
    requires Tako.Init(c, v)
    ensures InvDirtyBit(c, v)
  {}

  lemma InvCoherenceStateHoldsInitially(c: Tako.Constants, v: Tako.Variables)
    requires Tako.Init(c, v)
    ensures InvCoherenceState(c, v)
  {}

  lemma InvWFMessagesHoldsInitially(c: Tako.Constants, v: Tako.Variables)
    requires Tako.Init(c, v)
    ensures InvWFMessages(c, v)
  {}
  
  lemma InvCoherenceMessagesHoldsInitially(c: Tako.Constants, v: Tako.Variables)
    requires Tako.Init(c, v)
    ensures InvCoherenceMessages(c, v)
  {
    reveal InvAckInFlight;
    reveal DataInFlight;
    reveal PutMInFlight;
    reveal PutSInFlight;
    reveal GetMInFlight;
    reveal GetSInFlight;
    reveal FwdGetSInFlight;
    reveal FwdGetMInFlight;
  }

  lemma InvPerfLoadHoldsInitially(c: Tako.Constants, v: Tako.Variables)
    requires Tako.Init(c, v)
    ensures InvPerfLoad(c, v)
  {}

  lemma InvHoldsInitially(c: Tako.Constants, v: Tako.Variables)
    requires Tako.Init(c, v)
    ensures Inv(c, v)
  {
    InvAddressesUniqueHoldsInitially(c, v);
    InvPerfLoadHoldsInitially(c, v);
    InvPerfStoreHoldsInitially(c, v);
    InvCorrectCoreHoldsInitially(c, v);
    InvCallbackProgressHoldsInitially(c, v);
    InvStartCallbackHoldsInitially(c, v);
    InvEpochsHoldsInitially(c, v);
    InvDirtyBitHoldsInitially(c, v);
    InvWFMessagesHoldsInitially(c, v);
    InvCoherenceStateHoldsInitially(c, v);
    InvCoherenceMessagesHoldsInitially(c, v);
  }
}