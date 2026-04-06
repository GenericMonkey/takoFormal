include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module EngReqPropertiesProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes
  import opened CacheTypes
  import Program

  ///////////////////////////////////////////////////////////////////////////////////
  // EachAddrInEngineBoundMsgHasCorrectCore
  ///////////////////////////////////////////////////////////////////////////////////
  lemma ProxyNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    ensures EachAddrInEngineBoundMsgHasCorrectCore(c, v')
  {}

  lemma CoreNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    ensures EachAddrInEngineBoundMsgHasCorrectCore(c, v')
  {}

  lemma EngineReceiveCallbackReqNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    ensures EachAddrInEngineBoundMsgHasCorrectCore(c, v')
  {}

  lemma EngineCacheCommunicationNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    ensures EachAddrInEngineBoundMsgHasCorrectCore(c, v')
  {}

  lemma L2CacheCommunicationNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    ensures EachAddrInEngineBoundMsgHasCorrectCore(c, v')
  {}

  lemma L2DirectoryNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    ensures EachAddrInEngineBoundMsgHasCorrectCore(c, v')
  {}

  lemma L2ScheduleCallbackNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    ensures EachAddrInEngineBoundMsgHasCorrectCore(c, v')
  {}

  lemma L2ReceiveOnMissDataNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    ensures EachAddrInEngineBoundMsgHasCorrectCore(c, v')
  {}

  lemma L2ReceiveCoherenceMessageNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    ensures EachAddrInEngineBoundMsgHasCorrectCore(c, v')
  {}

  lemma L3ReceiveCoherenceMessageNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    ensures EachAddrInEngineBoundMsgHasCorrectCore(c, v')
  {}

  lemma L3ScheduleCallbackNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    ensures EachAddrInEngineBoundMsgHasCorrectCore(c, v')
  {}

  lemma L3ReceiveOnMissDataNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    ensures EachAddrInEngineBoundMsgHasCorrectCore(c, v')
  {}

  lemma L3ReqMemoryNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    ensures EachAddrInEngineBoundMsgHasCorrectCore(c, v')
  {}

  lemma L3RespMemoryNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    ensures EachAddrInEngineBoundMsgHasCorrectCore(c, v')
  {}

  lemma L3DirectoryNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    ensures EachAddrInEngineBoundMsgHasCorrectCore(c, v')
  {}

  lemma NoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgHasCorrectCore(c, v)
    requires EngReqsInNetworkAreDiffThanCurrentCallbacks(c, v)
    ensures EachAddrInEngineBoundMsgHasCorrectCore(c, v')
  {
    match step {
      case MemoryStep(msgOps) => {
        assert EachAddrInEngineBoundMsgHasCorrectCore(c, v');
      }
      case TileStep(tile_idx, tile_step, msgOps) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            match l3_step {
              case ReceiveOnMissDataStep(_) => {
                L3ReceiveOnMissDataNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L3ScheduleCallbackNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L3ReceiveCoherenceMessageNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L3DirectoryNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c, v, v', step);
              }
              case ReqMemoryStep(_,_) => {
                L3ReqMemoryNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c, v, v', step);
              }
              case RespMemoryStep(_) => {
                L3RespMemoryNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c, v, v', step);
              }
            }
          }
          case EngineStep(eng_step) => {
            if eng_step.ReceiveCallbackReqStep? {
              EngineReceiveCallbackReqNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c, v, v', step);
            } else if eng_step.CacheCommunicationStep? {
              EngineCacheCommunicationNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c, v, v', step);
            } else {
              assert false; // No other EngineStep should be here
            }
          }
          case ProxyStep(proxy_step) => {
            ProxyNoOpPreservesEachAddrInEngineBoundMsgHasCorrectCore(c, v, v', step);
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesEachAddrInEngineBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires InvCorrectCore(c, v)
    ensures EachAddrInEngineBoundMsgHasCorrectCore(c, v')
  {}

  lemma StartEndCBPreservesEachAddrInEngineBoundMsgHasCorrectCore(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires InvCorrectCore(c, v)
    ensures EachAddrInEngineBoundMsgHasCorrectCore(c, v')
  {}

  ///////////////////////////////////////////////////////////////////////////////////
  // EachAddrInEngineBoundMsgInWorkingSet
  ///////////////////////////////////////////////////////////////////////////////////
  lemma ProxyNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires EachAddrInEngineBoundMsgInWorkingSet(c, v)
    ensures EachAddrInEngineBoundMsgInWorkingSet(c, v')
  {}

  lemma CoreNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires EachAddrInEngineBoundMsgInWorkingSet(c, v)
    ensures EachAddrInEngineBoundMsgInWorkingSet(c, v')
  {}

  lemma EngineNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires EachAddrInEngineBoundMsgInWorkingSet(c, v)
    ensures EachAddrInEngineBoundMsgInWorkingSet(c, v')
  {}

  lemma L2CacheCommunicationNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgInWorkingSet(c, v)
    ensures EachAddrInEngineBoundMsgInWorkingSet(c, v')
  {
    reveal Program.Program.WF;
  }

  lemma L2DirectoryNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgInWorkingSet(c, v)
    ensures EachAddrInEngineBoundMsgInWorkingSet(c, v')
  {
    reveal Program.Program.WF;
  }

  lemma L2ScheduleCallbackNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgInWorkingSet(c, v)
    ensures EachAddrInEngineBoundMsgInWorkingSet(c, v')
  {
    reveal Program.Program.WF;
  }

  lemma L2ReceiveCoherenceMessageNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgInWorkingSet(c, v)
    ensures EachAddrInEngineBoundMsgInWorkingSet(c, v')
  {
    reveal Program.Program.WF;
  }

  lemma L2ReceiveOnMissDataNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgInWorkingSet(c, v)
    ensures EachAddrInEngineBoundMsgInWorkingSet(c, v')
  {
    reveal Program.Program.WF;
  }

  lemma L3RespMemoryNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgInWorkingSet(c, v)
    ensures EachAddrInEngineBoundMsgInWorkingSet(c, v')
  {
    reveal Program.Program.WF;
  }

  lemma L3ReqMemoryNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgInWorkingSet(c, v)
    ensures EachAddrInEngineBoundMsgInWorkingSet(c, v')
  {
    reveal Program.Program.WF;
  }

  lemma L3ScheduleCallbackNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgInWorkingSet(c, v)
    ensures EachAddrInEngineBoundMsgInWorkingSet(c, v')
  {
    reveal Program.Program.WF;
  }

  lemma L3ReceiveOnMissDataNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgInWorkingSet(c, v)
    ensures EachAddrInEngineBoundMsgInWorkingSet(c, v')
  {
    reveal Program.Program.WF;
  }

  lemma L3ReceiveCoherenceMessageNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgInWorkingSet(c, v)
    ensures EachAddrInEngineBoundMsgInWorkingSet(c, v')
  {
    reveal Program.Program.WF;
  }

  lemma L3DirectoryNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgInWorkingSet(c, v)
    ensures EachAddrInEngineBoundMsgInWorkingSet(c, v')
  {
    reveal Program.Program.WF;
  }

  lemma NoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires L2PrivateMorphAddressesAreCorrectCore(c, v)
    requires L3MorphAddressesAreCorrectCore(c, v)
    requires EachAddrInEngineBoundMsgInWorkingSet(c, v)
    ensures EachAddrInEngineBoundMsgInWorkingSet(c, v')
  {
    match step {
      case MemoryStep(msgOps) => {
        assert EachAddrInEngineBoundMsgInWorkingSet(c, v');
      }
      case TileStep(tile_idx, tile_step, msgOps) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            match l3_step {
              case RespMemoryStep(_) => {
                L3RespMemoryNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c, v, v', step);
              }
              case ReqMemoryStep(_,_) => {
                L3ReqMemoryNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L3ScheduleCallbackNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L3ReceiveOnMissDataNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L3DirectoryNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L3ReceiveCoherenceMessageNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c, v, v', step);
              }
            }
          }
          case EngineStep(eng_step) => {
            EngineNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c, v, v', step);
          }
          case ProxyStep(proxy_step) => {
            ProxyNoOpPreservesEachAddrInEngineBoundMsgInWorkingSet(c, v, v', step);
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesEachAddrInEngineBoundMsgInWorkingSet(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires EachAddrInEngineBoundMsgInWorkingSet(c, v)
    ensures EachAddrInEngineBoundMsgInWorkingSet(c, v')
  {}

  lemma StartEndCBPreservesEachAddrInEngineBoundMsgInWorkingSet(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EachAddrInEngineBoundMsgInWorkingSet(c, v)
    ensures EachAddrInEngineBoundMsgInWorkingSet(c, v')
  {}

}