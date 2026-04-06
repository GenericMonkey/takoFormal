include "../../../model/types.s.dfy"
include "../../../model/tako_spec.i.dfy"
include "../../../model/tako.i.dfy"
include "../refinement_defns.i.dfy"

module CohMsgWellFormedProof {
  import opened Types
  import opened RefinementTypes
  import opened MessageType
  import opened TakoRefinementDefns
  import opened Execution
  import opened EngineTypes
  import opened CacheTypes

  lemma NoOpPreservesL2DirOwnerIsAlwaysTier1Cache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires v.WF(c)
    requires L2QueueHeadsWellformed(c, v)
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    ensures L2DirOwnerIsAlwaysTier1Cache(c, v')
  {}
  
  lemma PerformNextInstPreservesL2DirOwnerIsAlwaysTier1Cache(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    ensures L2DirOwnerIsAlwaysTier1Cache(c, v')
  {}

  lemma StartEndCBPreservesL2DirOwnerIsAlwaysTier1Cache(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    ensures L2DirOwnerIsAlwaysTier1Cache(c, v')
  {}

  lemma CoreNoOpPreservesL2DirSharersAlwaysTier1Cache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires v.WF(c)
    requires L2QueueHeadsWellformed(c, v)
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires L2DirSharersAlwaysTier1Cache(c, v)
    ensures L2DirSharersAlwaysTier1Cache(c, v')
  {}
  
  lemma EngineNoOpPreservesL2DirSharersAlwaysTier1Cache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires v.WF(c)
    requires L2QueueHeadsWellformed(c, v)
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires L2DirSharersAlwaysTier1Cache(c, v)
    ensures L2DirSharersAlwaysTier1Cache(c, v')
  {}
  
  lemma ProxyNoOpPreservesL2DirSharersAlwaysTier1Cache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires v.WF(c)
    requires L2QueueHeadsWellformed(c, v)
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires L2DirSharersAlwaysTier1Cache(c, v)
    ensures L2DirSharersAlwaysTier1Cache(c, v')
  {}

  lemma L2NoOpPreservesL2DirSharersAlwaysTier1Cache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires v.WF(c)
    requires L2QueueHeadsWellformed(c, v)
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires L2DirSharersAlwaysTier1Cache(c, v)
    ensures L2DirSharersAlwaysTier1Cache(c, v')
  {}

  lemma L3NoOpPreservesL2DirSharersAlwaysTier1Cache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires v.WF(c)
    requires L2QueueHeadsWellformed(c, v)
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires L2DirSharersAlwaysTier1Cache(c, v)
    ensures L2DirSharersAlwaysTier1Cache(c, v')
  {}

  lemma MemoryNoOpPreservesL2DirSharersAlwaysTier1Cache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires v.WF(c)
    requires L2QueueHeadsWellformed(c, v)
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires L2DirSharersAlwaysTier1Cache(c, v)
    ensures L2DirSharersAlwaysTier1Cache(c, v')
  {}

  lemma NoOpPreservesL2DirSharersAlwaysTier1Cache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires v.WF(c)
    requires L2QueueHeadsWellformed(c, v)
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires L2DirSharersAlwaysTier1Cache(c, v)
    ensures L2DirSharersAlwaysTier1Cache(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesL2DirSharersAlwaysTier1Cache(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesL2DirSharersAlwaysTier1Cache(c, v, v', step);
          }
          case EngineStep(_) => {
            EngineNoOpPreservesL2DirSharersAlwaysTier1Cache(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesL2DirSharersAlwaysTier1Cache(c, v, v', step);
          }
          case L2Step(_) => {
            L2NoOpPreservesL2DirSharersAlwaysTier1Cache(c, v, v', step);
          }
          case L3Step(_) => {
            L3NoOpPreservesL2DirSharersAlwaysTier1Cache(c, v, v', step);
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesL2DirSharersAlwaysTier1Cache(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires L2DirSharersAlwaysTier1Cache(c, v)
    ensures L2DirSharersAlwaysTier1Cache(c, v')
  {}

  lemma StartEndCBPreservesL2DirSharersAlwaysTier1Cache(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires L2DirSharersAlwaysTier1Cache(c, v)
    ensures L2DirSharersAlwaysTier1Cache(c, v')
  {}

  lemma NoOpPreservesL3DirOwnerIsAlwaysTier2Cache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires v.WF(c)
    requires L3QueueHeadsWellformed(c, v)
    requires L3DirOwnerIsAlwaysTier2Cache(c, v)
    ensures L3DirOwnerIsAlwaysTier2Cache(c, v')
  {}

  lemma PerformNextInstPreservesL3DirOwnerIsAlwaysTier2Cache(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires L3DirOwnerIsAlwaysTier2Cache(c, v)
    ensures L3DirOwnerIsAlwaysTier2Cache(c, v')
  {}

  lemma StartEndCBPreservesL3DirOwnerIsAlwaysTier2Cache(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires L3DirOwnerIsAlwaysTier2Cache(c, v)
    ensures L3DirOwnerIsAlwaysTier2Cache(c, v')
  {}

  lemma TileNoOpPreservesL3DirSharersAlwaysTier2Cache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires v.WF(c)
    requires L3QueueHeadsWellformed(c, v)
    requires L3DirOwnerIsAlwaysTier2Cache(c, v)
    requires L3DirSharersAlwaysTier2Cache(c, v)
    ensures L3DirSharersAlwaysTier2Cache(c, v')
  {}

  lemma MemoryNoOpPreservesL3DirSharersAlwaysTier2Cache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires L3DirSharersAlwaysTier2Cache(c, v)
    ensures L3DirSharersAlwaysTier2Cache(c, v')
  {}

  lemma NoOpPreservesL3DirSharersAlwaysTier2Cache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires v.WF(c)
    requires L3QueueHeadsWellformed(c, v)
    requires L3DirOwnerIsAlwaysTier2Cache(c, v)
    requires L3DirSharersAlwaysTier2Cache(c, v)
    ensures L3DirSharersAlwaysTier2Cache(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesL3DirSharersAlwaysTier2Cache(c, v, v', step);
      }
      case TileStep(_,_,_) => {
        TileNoOpPreservesL3DirSharersAlwaysTier2Cache(c, v, v', step);
      }
    }
  }

  lemma PerformNextInstPreservesL3DirSharersAlwaysTier2Cache(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires L3DirSharersAlwaysTier2Cache(c, v)
    ensures L3DirSharersAlwaysTier2Cache(c, v')
  {}

  lemma StartEndCBPreservesL3DirSharersAlwaysTier2Cache(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires L3DirSharersAlwaysTier2Cache(c, v)
    ensures L3DirSharersAlwaysTier2Cache(c, v')
  {}

  
  lemma L2DirectoryNoOpPreservesAllFwdReqsToTier1HasTier1Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires v.WF(c)
    requires L2QueueHeadsWellformed(c, v)
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires L2DirSharersAlwaysTier1Cache(c, v)
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    ensures AllFwdReqsToTier1HasTier1Source(c, v')
  {}

  lemma L2CacheCommunicationNoOpPreservesAllFwdReqsToTier1HasTier1Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    ensures AllFwdReqsToTier1HasTier1Source(c, v')
  {}

  lemma L2ReceiveCoherenceMessageNoOpPreservesAllFwdReqsToTier1HasTier1Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    ensures AllFwdReqsToTier1HasTier1Source(c, v')
  {}

  lemma L2ScheduleCallbackNoOpPreservesAllFwdReqsToTier1HasTier1Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    ensures AllFwdReqsToTier1HasTier1Source(c, v')
  {}

  lemma L2ReceiveOnMissDataNoOpPreservesAllFwdReqsToTier1HasTier1Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    ensures AllFwdReqsToTier1HasTier1Source(c, v')
  {}

  lemma L3DirectoryNoOpPreservesAllFwdReqsToTier1HasTier1Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires L3DirOwnerIsAlwaysTier2Cache(c, v)
    requires L3DirSharersAlwaysTier2Cache(c, v)
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    ensures AllFwdReqsToTier1HasTier1Source(c, v')
  {}

  lemma L3ReceiveCoherenceMessageNoOpPreservesAllFwdReqsToTier1HasTier1Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    ensures AllFwdReqsToTier1HasTier1Source(c, v')
  {}

  lemma L3ReceiveOnMissDataNoOpPreservesAllFwdReqsToTier1HasTier1Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    ensures AllFwdReqsToTier1HasTier1Source(c, v')
  {}

  lemma L3ScheduleCallbackNoOpPreservesAllFwdReqsToTier1HasTier1Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    ensures AllFwdReqsToTier1HasTier1Source(c, v')
  {}

  lemma L3ReqMemoryNoOpPreservesAllFwdReqsToTier1HasTier1Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    ensures AllFwdReqsToTier1HasTier1Source(c, v')
  {}

  lemma L3RespMemoryNoOpPreservesAllFwdReqsToTier1HasTier1Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    ensures AllFwdReqsToTier1HasTier1Source(c, v')
  {}

  lemma CoreNoOpPreservesAllFwdReqsToTier1HasTier1Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    ensures AllFwdReqsToTier1HasTier1Source(c, v')
  {}

  lemma EngineNoOpPreservesAllFwdReqsToTier1HasTier1Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    ensures AllFwdReqsToTier1HasTier1Source(c, v')
  {}

  lemma ProxyNoOpPreservesAllFwdReqsToTier1HasTier1Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    ensures AllFwdReqsToTier1HasTier1Source(c, v')
  {}

  lemma MemoryNoOpPreservesAllFwdReqsToTier1HasTier1Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    ensures AllFwdReqsToTier1HasTier1Source(c, v')
  {}

  lemma NoOpPreservesAllFwdReqsToTier1HasTier1Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires v.WF(c)
    requires L2QueueHeadsWellformed(c, v)
    requires L3DirOwnerIsAlwaysTier2Cache(c, v)
    requires L3DirSharersAlwaysTier2Cache(c, v)
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires L2DirSharersAlwaysTier1Cache(c, v)
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    ensures AllFwdReqsToTier1HasTier1Source(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesAllFwdReqsToTier1HasTier1Source(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesAllFwdReqsToTier1HasTier1Source(c, v, v', step);
          }
          case EngineStep(_) => {
            EngineNoOpPreservesAllFwdReqsToTier1HasTier1Source(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesAllFwdReqsToTier1HasTier1Source(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesAllFwdReqsToTier1HasTier1Source(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesAllFwdReqsToTier1HasTier1Source(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesAllFwdReqsToTier1HasTier1Source(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesAllFwdReqsToTier1HasTier1Source(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesAllFwdReqsToTier1HasTier1Source(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            match l3_step {
              case DirectoryStep(_,_,_) => {
                L3DirectoryNoOpPreservesAllFwdReqsToTier1HasTier1Source(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L3ReceiveCoherenceMessageNoOpPreservesAllFwdReqsToTier1HasTier1Source(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L3ScheduleCallbackNoOpPreservesAllFwdReqsToTier1HasTier1Source(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L3ReceiveOnMissDataNoOpPreservesAllFwdReqsToTier1HasTier1Source(c, v, v', step);
              }
              case ReqMemoryStep(_,_) => {
                L3ReqMemoryNoOpPreservesAllFwdReqsToTier1HasTier1Source(c, v, v', step);
              }
              case RespMemoryStep(_) => {
                L3RespMemoryNoOpPreservesAllFwdReqsToTier1HasTier1Source(c, v, v', step);
              }
            }
          }
        }
      }
    }
  }

  lemma StartEndCBPreservesAllFwdReqsToTier1HasTier1Source(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    ensures AllFwdReqsToTier1HasTier1Source(c, v')
  {}

  lemma PerformNextInstPreservesAllFwdReqsToTier1HasTier1Source(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    ensures AllFwdReqsToTier1HasTier1Source(c, v')
  {}
  
  lemma L2DirectoryNoOpPreservesAllFwdReqsToTier2HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires v.WF(c)
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires L2DirSharersAlwaysTier1Cache(c, v)
    requires AllFwdReqsToTier2HasTier2Source(c, v)
    ensures AllFwdReqsToTier2HasTier2Source(c, v')
  {}

  lemma L2CacheCommunicationNoOpPreservesAllFwdReqsToTier2HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires AllFwdReqsToTier2HasTier2Source(c, v)
    ensures AllFwdReqsToTier2HasTier2Source(c, v')
  {}

  lemma L2ReceiveCoherenceMessageNoOpPreservesAllFwdReqsToTier2HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires AllFwdReqsToTier2HasTier2Source(c, v)
    ensures AllFwdReqsToTier2HasTier2Source(c, v')
  {}

  lemma L2ScheduleCallbackNoOpPreservesAllFwdReqsToTier2HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires AllFwdReqsToTier2HasTier2Source(c, v)
    ensures AllFwdReqsToTier2HasTier2Source(c, v')
  {}

  lemma L2ReceiveOnMissDataNoOpPreservesAllFwdReqsToTier2HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires AllFwdReqsToTier2HasTier2Source(c, v)
    ensures AllFwdReqsToTier2HasTier2Source(c, v')
  {}

  lemma L3DirectoryNoOpPreservesAllFwdReqsToTier2HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires L3QueueHeadsWellformed(c, v)
    requires L3DirOwnerIsAlwaysTier2Cache(c, v)
    requires L3DirSharersAlwaysTier2Cache(c, v)
    requires AllFwdReqsToTier2HasTier2Source(c, v)
    ensures AllFwdReqsToTier2HasTier2Source(c, v')
  {}

  lemma L3ReceiveCoherenceMessageNoOpPreservesAllFwdReqsToTier2HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires AllFwdReqsToTier2HasTier2Source(c, v)
    ensures AllFwdReqsToTier2HasTier2Source(c, v')
  {}

  lemma L3ReceiveOnMissDataNoOpPreservesAllFwdReqsToTier2HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires AllFwdReqsToTier2HasTier2Source(c, v)
    ensures AllFwdReqsToTier2HasTier2Source(c, v')
  {}

  lemma L3ScheduleCallbackNoOpPreservesAllFwdReqsToTier2HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires AllFwdReqsToTier2HasTier2Source(c, v)
    ensures AllFwdReqsToTier2HasTier2Source(c, v')
  {}

  lemma L3ReqMemoryNoOpPreservesAllFwdReqsToTier2HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires AllFwdReqsToTier2HasTier2Source(c, v)
    ensures AllFwdReqsToTier2HasTier2Source(c, v')
  {}

  lemma L3RespMemoryNoOpPreservesAllFwdReqsToTier2HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires AllFwdReqsToTier2HasTier2Source(c, v)
    ensures AllFwdReqsToTier2HasTier2Source(c, v')
  {}

  lemma CoreNoOpPreservesAllFwdReqsToTier2HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    requires AllFwdReqsToTier2HasTier2Source(c, v)
    ensures AllFwdReqsToTier2HasTier2Source(c, v')
  {}

  lemma EngineNoOpPreservesAllFwdReqsToTier2HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    requires AllFwdReqsToTier2HasTier2Source(c, v)
    ensures AllFwdReqsToTier2HasTier2Source(c, v')
  {}

  lemma ProxyNoOpPreservesAllFwdReqsToTier2HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    requires AllFwdReqsToTier2HasTier2Source(c, v)
    ensures AllFwdReqsToTier2HasTier2Source(c, v')
  {}

  lemma MemoryNoOpPreservesAllFwdReqsToTier2HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires AllFwdReqsToTier2HasTier2Source(c, v)
    ensures AllFwdReqsToTier2HasTier2Source(c, v')
  {}

  lemma NoOpPreservesAllFwdReqsToTier2HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires v.WF(c)
    requires L3QueueHeadsWellformed(c, v)
    requires L3DirOwnerIsAlwaysTier2Cache(c, v)
    requires L3DirSharersAlwaysTier2Cache(c, v)
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires L2DirSharersAlwaysTier1Cache(c, v)
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    requires AllFwdReqsToTier2HasTier2Source(c, v)
    ensures AllFwdReqsToTier2HasTier2Source(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesAllFwdReqsToTier2HasTier2Source(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesAllFwdReqsToTier2HasTier2Source(c, v, v', step);
          }
          case EngineStep(_) => {
            EngineNoOpPreservesAllFwdReqsToTier2HasTier2Source(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesAllFwdReqsToTier2HasTier2Source(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesAllFwdReqsToTier2HasTier2Source(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesAllFwdReqsToTier2HasTier2Source(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesAllFwdReqsToTier2HasTier2Source(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesAllFwdReqsToTier2HasTier2Source(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesAllFwdReqsToTier2HasTier2Source(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            match l3_step {
              case DirectoryStep(_,_,_) => {
                L3DirectoryNoOpPreservesAllFwdReqsToTier2HasTier2Source(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L3ReceiveCoherenceMessageNoOpPreservesAllFwdReqsToTier2HasTier2Source(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L3ScheduleCallbackNoOpPreservesAllFwdReqsToTier2HasTier2Source(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L3ReceiveOnMissDataNoOpPreservesAllFwdReqsToTier2HasTier2Source(c, v, v', step);
              }
              case ReqMemoryStep(_,_) => {
                L3ReqMemoryNoOpPreservesAllFwdReqsToTier2HasTier2Source(c, v, v', step);
              }
              case RespMemoryStep(_) => {
                L3RespMemoryNoOpPreservesAllFwdReqsToTier2HasTier2Source(c, v, v', step);
              }
            }
          }
        }
      }
    }
  }

  lemma StartEndCBPreservesAllFwdReqsToTier2HasTier2Source(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires AllFwdReqsToTier2HasTier2Source(c, v)
    ensures AllFwdReqsToTier2HasTier2Source(c, v')
  {}

  lemma PerformNextInstPreservesAllFwdReqsToTier2HasTier2Source(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires AllFwdReqsToTier2HasTier2Source(c, v)
    ensures AllFwdReqsToTier2HasTier2Source(c, v')
  {}

  lemma L2DirectoryNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires v.WF(c)
    requires L2QueueHeadsWellformed(c, v)
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires L2DirSharersAlwaysTier1Cache(c, v)
    requires AllFwdReqsFromTier1HasTier1Dst(c, v)
    ensures AllFwdReqsFromTier1HasTier1Dst(c, v')
  {}

  lemma L2CacheCommunicationNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires AllFwdReqsFromTier1HasTier1Dst(c, v)
    ensures AllFwdReqsFromTier1HasTier1Dst(c, v')
  {}

  lemma L2ReceiveCoherenceMessageNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires AllFwdReqsFromTier1HasTier1Dst(c, v)
    ensures AllFwdReqsFromTier1HasTier1Dst(c, v')
  {}

  lemma L2ScheduleCallbackNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires AllFwdReqsFromTier1HasTier1Dst(c, v)
    ensures AllFwdReqsFromTier1HasTier1Dst(c, v')
  {}

  lemma L2ReceiveOnMissDataNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires AllFwdReqsFromTier1HasTier1Dst(c, v)
    ensures AllFwdReqsFromTier1HasTier1Dst(c, v')
  {}

  lemma L3DirectoryNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires L3QueueHeadsWellformed(c, v)
    requires L3DirOwnerIsAlwaysTier2Cache(c, v)
    requires L3DirSharersAlwaysTier2Cache(c, v)
    requires AllFwdReqsFromTier1HasTier1Dst(c, v)
    ensures AllFwdReqsFromTier1HasTier1Dst(c, v')
  {}

  lemma L3ReceiveCoherenceMessageNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires AllFwdReqsFromTier1HasTier1Dst(c, v)
    ensures AllFwdReqsFromTier1HasTier1Dst(c, v')
  {}

  lemma L3ReceiveOnMissDataNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires AllFwdReqsFromTier1HasTier1Dst(c, v)
    ensures AllFwdReqsFromTier1HasTier1Dst(c, v')
  {}

  lemma L3ScheduleCallbackNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires AllFwdReqsFromTier1HasTier1Dst(c, v)
    ensures AllFwdReqsFromTier1HasTier1Dst(c, v')
  {}

  lemma L3ReqMemoryNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires AllFwdReqsFromTier1HasTier1Dst(c, v)
    ensures AllFwdReqsFromTier1HasTier1Dst(c, v')
  {}

  lemma L3RespMemoryNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep? 
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires AllFwdReqsFromTier1HasTier1Dst(c, v)
    ensures AllFwdReqsFromTier1HasTier1Dst(c, v')
  {}

  lemma CoreNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires AllFwdReqsFromTier1HasTier1Dst(c, v)
    ensures AllFwdReqsFromTier1HasTier1Dst(c, v')
  {}

  lemma EngineNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires AllFwdReqsFromTier1HasTier1Dst(c, v)
    ensures AllFwdReqsFromTier1HasTier1Dst(c, v')
  {}

  lemma ProxyNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires AllFwdReqsFromTier1HasTier1Dst(c, v)
    ensures AllFwdReqsFromTier1HasTier1Dst(c, v')
  {}

  lemma MemoryNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires AllFwdReqsFromTier1HasTier1Dst(c, v)
    ensures AllFwdReqsFromTier1HasTier1Dst(c, v')
  {}

  lemma NoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires v.WF(c)
    requires L2QueueHeadsWellformed(c, v)
    requires L3QueueHeadsWellformed(c, v)
    requires L3DirOwnerIsAlwaysTier2Cache(c, v)
    requires L3DirSharersAlwaysTier2Cache(c, v)
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires L2DirSharersAlwaysTier1Cache(c, v)
    requires AllFwdReqsFromTier1HasTier1Dst(c, v)
    ensures AllFwdReqsFromTier1HasTier1Dst(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c, v, v', step);
          }
          case EngineStep(_) => {
            EngineNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            match l3_step {
              case DirectoryStep(_,_,_) => {
                L3DirectoryNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L3ReceiveCoherenceMessageNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L3ScheduleCallbackNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L3ReceiveOnMissDataNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c, v, v', step);
              }
              case ReqMemoryStep(_,_) => {
                L3ReqMemoryNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c, v, v', step);
              }
              case RespMemoryStep(_) => {
                L3RespMemoryNoOpPreservesAllFwdReqsFromTier1HasTier1Dst(c, v, v', step);
              }
            }
          }
        }
      }
    }
  }

  lemma StartEndCBPreservesAllFwdReqsFromTier1HasTier1Dst(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires AllFwdReqsFromTier1HasTier1Dst(c, v)
    ensures AllFwdReqsFromTier1HasTier1Dst(c, v')
  {}

  lemma PerformNextInstPreservesAllFwdReqsFromTier1HasTier1Dst(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires AllFwdReqsFromTier1HasTier1Dst(c, v)
    ensures AllFwdReqsFromTier1HasTier1Dst(c, v')
  {}

  lemma ProxyNoOpPreservesMemMessagesWellformed(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires v.WF(c)
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    requires MemMessagesWellformed(c, v)
    ensures MemMessagesWellformed(c, v')
  {}

  lemma CoreNoOpPreservesMemMessagesWellformed(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires v.WF(c)
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    requires MemMessagesWellformed(c, v)
    ensures MemMessagesWellformed(c, v')
  {}

  lemma EngineNoOpPreservesMemMessagesWellformed(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires v.WF(c)
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    requires MemMessagesWellformed(c, v)
    ensures MemMessagesWellformed(c, v')
  {}

  lemma L2ReceiveCoherenceMessageNoOpPreservesMemMessagesWellformed(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires MemMessagesWellformed(c, v)
    ensures MemMessagesWellformed(c, v')
  {}

  lemma L2ScheduleCallbackMessageNoOpPreservesMemMessagesWellformed(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires MemMessagesWellformed(c, v)
    ensures MemMessagesWellformed(c, v')
  {}

  lemma L2ReceiveOnMissDataNoOpPreservesMemMessagesWellformed(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires MemMessagesWellformed(c, v)
    ensures MemMessagesWellformed(c, v')
  {}

  lemma L2CacheCommunicationNoOpPreservesMemMessagesWellformed(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires v.WF(c)
    requires L2QueueHeadsWellformed(c, v)
    requires AllFwdReqsToTier2HasTier2Source(c, v)
    requires MemMessagesWellformed(c, v)
    ensures MemMessagesWellformed(c, v')
  {}

  lemma L2DirectoryNoOpPreservesMemMessagesWellformed(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires v.WF(c)
    requires L2QueueHeadsWellformed(c, v)
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires L2DirSharersAlwaysTier1Cache(c, v)
    requires MemMessagesWellformed(c, v)
    ensures MemMessagesWellformed(c, v')
  {}

  lemma L3ReceiveCoherenceMessageNoOpPreservesMemMessagesWellformed(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveCoherenceMessageStep?
    requires MemMessagesWellformed(c, v)
    ensures MemMessagesWellformed(c, v')
  {}

  lemma L3ScheduleCallbackMessageNoOpPreservesMemMessagesWellformed(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ScheduleCallbackStep?
    requires MemMessagesWellformed(c, v)
    ensures MemMessagesWellformed(c, v')
  {}

  lemma L3ReceiveOnMissDataNoOpPreservesMemMessagesWellformed(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReceiveOnMissDataStep?
    requires MemMessagesWellformed(c, v)
    ensures MemMessagesWellformed(c, v')
  {}

  lemma L3ReqMemoryNoOpPreservesMemMessagesWellformed(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.ReqMemoryStep?
    requires v.WF(c)
    requires MemMessagesWellformed(c, v)
    ensures MemMessagesWellformed(c, v')
  {}

  lemma L3RespMemoryNoOpPreservesMemMessagesWellformed(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.RespMemoryStep?
    requires v.WF(c)
    requires MemMessagesWellformed(c, v)
    ensures MemMessagesWellformed(c, v')
  {}

  lemma L3DirectoryNoOpPreservesMemMessagesWellformed(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires step.tile_step.l3_step.DirectoryStep?
    requires v.WF(c)
    requires L3QueueHeadsWellformed(c, v)
    requires L3DirOwnerIsAlwaysTier2Cache(c, v)
    requires L3DirSharersAlwaysTier2Cache(c, v)
    requires MemMessagesWellformed(c, v)
    ensures MemMessagesWellformed(c, v')
  {}

  lemma MemoryNoOpPreservesMemMessagesWellformed(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires v.WF(c)
    requires MemMessagesWellformed(c, v)
    ensures MemMessagesWellformed(c, v')
  {}

  lemma NoOpPreservesMemMessagesWellformed(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires v.WF(c)
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    requires AllFwdReqsToTier2HasTier2Source(c, v)
    requires L2QueueHeadsWellformed(c, v)
    requires L2DirOwnerIsAlwaysTier1Cache(c, v)
    requires L2DirSharersAlwaysTier1Cache(c, v)
    requires L3QueueHeadsWellformed(c, v)
    requires L3DirOwnerIsAlwaysTier2Cache(c, v)
    requires L3DirSharersAlwaysTier2Cache(c, v)
    requires MemMessagesWellformed(c, v)
    ensures MemMessagesWellformed(c, v')
  {
    match step {
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesMemMessagesWellformed(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesMemMessagesWellformed(c, v, v', step);
          }
          case EngineStep(_) => {
            EngineNoOpPreservesMemMessagesWellformed(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesMemMessagesWellformed(c, v, v', step);
              }
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesMemMessagesWellformed(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesMemMessagesWellformed(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackMessageNoOpPreservesMemMessagesWellformed(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesMemMessagesWellformed(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            match l3_step {
              case DirectoryStep(_,_,_) => {
                L3DirectoryNoOpPreservesMemMessagesWellformed(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L3ReceiveCoherenceMessageNoOpPreservesMemMessagesWellformed(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L3ScheduleCallbackMessageNoOpPreservesMemMessagesWellformed(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L3ReceiveOnMissDataNoOpPreservesMemMessagesWellformed(c, v, v', step);
              }
              case ReqMemoryStep(_,_) => {
                L3ReqMemoryNoOpPreservesMemMessagesWellformed(c, v, v', step);
              }
              case RespMemoryStep(_) => {
                L3RespMemoryNoOpPreservesMemMessagesWellformed(c, v, v', step);
              }
            }
          }
        }
      }
      case MemoryStep(_) => {
        MemoryNoOpPreservesMemMessagesWellformed(c, v, v', step);
      }
    }
  }

  lemma PerformNextInstPreservesMemMessagesWellformed(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires MemMessagesWellformed(c, v)
    ensures MemMessagesWellformed(c, v')
  {}

  lemma StartEndCBPreservesMemMessagesWellformed(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires EachAddrInEngineIsInCorrectCore(c, v)
    requires MemMessagesWellformed(c, v)
    ensures MemMessagesWellformed(c, v')
  {}

  lemma NoOpPreservesL2QueueHeadsWellformed(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires AllReqsToTier2HasTier1Source(c, v)
    requires AllFwdReqsToTier2HasTier2Source(c, v)
    requires AllPutAcksToTier2HasTier3Source(c, v)
    requires AllDataToTier2FromCache(c, v)
    requires L2QueueHeadsWellformed(c, v)
    ensures L2QueueHeadsWellformed(c, v')
  {}

  lemma PerformNextInstPreservesL2QueueHeadsWellformed(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires L2QueueHeadsWellformed(c, v)
    ensures L2QueueHeadsWellformed(c, v')
  {}

  lemma StartEndCBPreservesL2QueueHeadsWellformed(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires L2QueueHeadsWellformed(c, v)
    ensures L2QueueHeadsWellformed(c, v')
  {}

  lemma NoOpPreservesL3QueueHeadsWellformed(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires AllReqsToTier3HasTier2Source(c, v)
    requires AllDataToTier3FromTier2Cache(c, v)
    requires L3QueueHeadsWellformed(c, v)
    ensures L3QueueHeadsWellformed(c, v')
  {
  }

  lemma PerformNextInstPreservesL3QueueHeadsWellformed(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires L3QueueHeadsWellformed(c, v)
    ensures L3QueueHeadsWellformed(c, v')
  {}

  lemma StartEndCBPreservesL3QueueHeadsWellformed(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires L3QueueHeadsWellformed(c, v)
    ensures L3QueueHeadsWellformed(c, v')
  {}

  lemma MemoryNoOpPreservesAllReqsToTier2HasTier1Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires v.WF(c)
    requires AllReqsToTier2HasTier1Source(c, v)
    ensures AllReqsToTier2HasTier1Source(c, v')
  {}

  lemma CoreNoOpPreservesAllReqsToTier2HasTier1Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires v.WF(c)
    requires AllReqsToTier2HasTier1Source(c, v)
    ensures AllReqsToTier2HasTier1Source(c, v')
  {}

  lemma EngineNoOpPreservesAllReqsToTier2HasTier1Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires v.WF(c)
    requires AllReqsToTier2HasTier1Source(c, v)
    ensures AllReqsToTier2HasTier1Source(c, v')
  {}

  lemma ProxyNoOpPreservesAllReqsToTier2HasTier1Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires v.WF(c)
    requires AllReqsToTier2HasTier1Source(c, v)
    ensures AllReqsToTier2HasTier1Source(c, v')
  {}

  lemma L2NoOpPreservesAllReqsToTier2HasTier1Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires v.WF(c)
    requires AllReqsToTier2HasTier1Source(c, v)
    ensures AllReqsToTier2HasTier1Source(c, v')
  {}

  lemma L3NoOpPreservesAllReqsToTier2HasTier1Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires v.WF(c)
    requires AllReqsToTier2HasTier1Source(c, v)
    ensures AllReqsToTier2HasTier1Source(c, v')
  {}

  lemma NoOpPreservesAllReqsToTier2HasTier1Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires v.WF(c)
    requires AllReqsToTier2HasTier1Source(c, v)
    ensures AllReqsToTier2HasTier1Source(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesAllReqsToTier2HasTier1Source(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesAllReqsToTier2HasTier1Source(c, v, v', step);
          }
          case EngineStep(_) => {
            EngineNoOpPreservesAllReqsToTier2HasTier1Source(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesAllReqsToTier2HasTier1Source(c, v, v', step);
          }
          case L2Step(_) => {
            L2NoOpPreservesAllReqsToTier2HasTier1Source(c, v, v', step);
          }
          case L3Step(l3_step) => {
            L3NoOpPreservesAllReqsToTier2HasTier1Source(c, v, v', step);
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesAllReqsToTier2HasTier1Source(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires AllReqsToTier2HasTier1Source(c, v)
    ensures AllReqsToTier2HasTier1Source(c, v')
  {}

  lemma StartEndCBPreservesAllReqsToTier2HasTier1Source(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires AllReqsToTier2HasTier1Source(c, v)
    ensures AllReqsToTier2HasTier1Source(c, v')
  {}

  lemma MemoryNoOpPreservesAllReqsToTier3HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires v.WF(c)
    requires AllReqsToTier3HasTier2Source(c, v)
    ensures AllReqsToTier3HasTier2Source(c, v')
  {}

  lemma CoreNoOpPreservesAllReqsToTier3HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires v.WF(c)
    requires AllReqsToTier3HasTier2Source(c, v)
    ensures AllReqsToTier3HasTier2Source(c, v')
  {}

  lemma EngineNoOpPreservesAllReqsToTier3HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires v.WF(c)
    requires AllReqsToTier3HasTier2Source(c, v)
    ensures AllReqsToTier3HasTier2Source(c, v')
  {}

  lemma ProxyNoOpPreservesAllReqsToTier3HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires v.WF(c)
    requires AllReqsToTier3HasTier2Source(c, v)
    ensures AllReqsToTier3HasTier2Source(c, v')
  {}

  lemma L2ReceiveCoherenceMessageNoOpPreservesAllReqsToTier3HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires v.WF(c)
    requires AllReqsToTier3HasTier2Source(c, v)
    ensures AllReqsToTier3HasTier2Source(c, v')
  {}

  lemma L2ScheduleCallbackNoOpPreservesAllReqsToTier3HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires v.WF(c)
    requires AllReqsToTier3HasTier2Source(c, v)
    ensures AllReqsToTier3HasTier2Source(c, v')
  {}

  lemma L2ReceiveOnMissDataNoOpPreservesAllReqsToTier3HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires v.WF(c)
    requires AllReqsToTier3HasTier2Source(c, v)
    ensures AllReqsToTier3HasTier2Source(c, v')
  {}

  lemma L2CacheCommunicationNoOpPreservesAllReqsToTier3HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires v.WF(c)
    requires AllReqsToTier3HasTier2Source(c, v)
    ensures AllReqsToTier3HasTier2Source(c, v')
  {}

  lemma L2DirectoryNoOpPreservesAllReqsToTier3HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires v.WF(c)
    requires AllReqsToTier3HasTier2Source(c, v)
    ensures AllReqsToTier3HasTier2Source(c, v')
  {}

  lemma L3NoOpPreservesAllReqsToTier3HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires v.WF(c)
    requires AllReqsToTier3HasTier2Source(c, v)
    ensures AllReqsToTier3HasTier2Source(c, v')
  {}

  lemma NoOpPreservesAllReqsToTier3HasTier2Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires v.WF(c)
    requires AllReqsToTier3HasTier2Source(c, v)
    ensures AllReqsToTier3HasTier2Source(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesAllReqsToTier3HasTier2Source(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesAllReqsToTier3HasTier2Source(c, v, v', step);
          }
          case EngineStep(_) => {
            EngineNoOpPreservesAllReqsToTier3HasTier2Source(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesAllReqsToTier3HasTier2Source(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesAllReqsToTier3HasTier2Source(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesAllReqsToTier3HasTier2Source(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesAllReqsToTier3HasTier2Source(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesAllReqsToTier3HasTier2Source(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesAllReqsToTier3HasTier2Source(c, v, v', step);
              }
            }
          }
          case L3Step(l3_step) => {
            L3NoOpPreservesAllReqsToTier3HasTier2Source(c, v, v', step);
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesAllReqsToTier3HasTier2Source(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires AllReqsToTier3HasTier2Source(c, v)
    ensures AllReqsToTier3HasTier2Source(c, v')
  {}

  lemma StartEndCBPreservesAllReqsToTier3HasTier2Source(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires AllReqsToTier3HasTier2Source(c, v)
    ensures AllReqsToTier3HasTier2Source(c, v')
  {}

  lemma MemoryNoOpPreservesAllPutAcksToTier2HasTier3Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires v.WF(c)
    requires MemMessagesWellformed(c, v)
    requires AllPutAcksToTier2HasTier3Source(c, v)
    ensures AllPutAcksToTier2HasTier3Source(c, v')
  {}

  lemma CoreNoOpPreservesAllPutAcksToTier2HasTier3Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires AllPutAcksToTier2HasTier3Source(c, v)
    ensures AllPutAcksToTier2HasTier3Source(c, v')
  {}

  lemma EngineCacheCommunicationNoOpPreservesAllPutAcksToTier2HasTier3Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.CacheCommunicationStep?
    requires AllPutAcksToTier2HasTier3Source(c, v)
    ensures AllPutAcksToTier2HasTier3Source(c, v')
  {}

  lemma EngineReceiveCallbackReqNoOpPreservesAllPutAcksToTier2HasTier3Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires step.tile_step.eng_step.ReceiveCallbackReqStep?
    requires AllPutAcksToTier2HasTier3Source(c, v)
    ensures AllPutAcksToTier2HasTier3Source(c, v')
  {}

  lemma ProxyNoOpPreservesAllPutAcksToTier2HasTier3Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires AllPutAcksToTier2HasTier3Source(c, v)
    ensures AllPutAcksToTier2HasTier3Source(c, v')
  {}

  lemma L2ReceiveCoherenceMessageNoOpPreservesAllPutAcksToTier2HasTier3Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires AllPutAcksToTier2HasTier3Source(c, v)
    ensures AllPutAcksToTier2HasTier3Source(c, v')
  {}

  lemma L2ScheduleCallbackNoOpPreservesAllPutAcksToTier2HasTier3Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires AllPutAcksToTier2HasTier3Source(c, v)
    ensures AllPutAcksToTier2HasTier3Source(c, v')
  {}

  lemma L2ReceiveOnMissDataNoOpPreservesAllPutAcksToTier2HasTier3Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires L2QueueHeadsWellformed(c, v)
    requires AllPutAcksToTier2HasTier3Source(c, v)
    ensures AllPutAcksToTier2HasTier3Source(c, v')
  {}

  lemma L2CacheCommunicationNoOpPreservesAllPutAcksToTier2HasTier3Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires AllPutAcksToTier2HasTier3Source(c, v)
    ensures AllPutAcksToTier2HasTier3Source(c, v')
  {}

  lemma L2DirectoryNoOpPreservesAllPutAcksToTier2HasTier3Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires L2QueueHeadsWellformed(c, v)
    requires AllPutAcksToTier2HasTier3Source(c, v)
    ensures AllPutAcksToTier2HasTier3Source(c, v')
  {}

  lemma L3NoOpPreservesAllPutAcksToTier2HasTier3Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires L3QueueHeadsWellformed(c, v)
    requires AllPutAcksToTier2HasTier3Source(c, v)
    ensures AllPutAcksToTier2HasTier3Source(c, v')
  {}

  lemma NoOpPreservesAllPutAcksToTier2HasTier3Source(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires v.WF(c)
    requires MemMessagesWellformed(c, v)
    requires L2QueueHeadsWellformed(c, v)
    requires L3QueueHeadsWellformed(c, v)
    requires AllPutAcksToTier2HasTier3Source(c, v)
    ensures AllPutAcksToTier2HasTier3Source(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesAllPutAcksToTier2HasTier3Source(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesAllPutAcksToTier2HasTier3Source(c, v, v', step);
          }
          case EngineStep(eng_step) => {
            if eng_step.ReceiveCallbackReqStep? {
              EngineReceiveCallbackReqNoOpPreservesAllPutAcksToTier2HasTier3Source(c, v, v', step);
            } else if eng_step.CacheCommunicationStep? {
              EngineCacheCommunicationNoOpPreservesAllPutAcksToTier2HasTier3Source(c, v, v', step);
            }
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesAllPutAcksToTier2HasTier3Source(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesAllPutAcksToTier2HasTier3Source(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesAllPutAcksToTier2HasTier3Source(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesAllPutAcksToTier2HasTier3Source(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesAllPutAcksToTier2HasTier3Source(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesAllPutAcksToTier2HasTier3Source(c, v, v', step);
              }
            }
          }
          case L3Step(_) => {
            L3NoOpPreservesAllPutAcksToTier2HasTier3Source(c, v, v', step);
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesAllPutAcksToTier2HasTier3Source(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires AllPutAcksToTier2HasTier3Source(c, v)
    ensures AllPutAcksToTier2HasTier3Source(c, v')
  {}

  lemma StartEndCBPreservesAllPutAcksToTier2HasTier3Source(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires AllPutAcksToTier2HasTier3Source(c, v)
    ensures AllPutAcksToTier2HasTier3Source(c, v')
  {}

  lemma MemoryNoOpPreservesAllDataToTier2FromCache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires v.WF(c)
    requires MemMessagesWellformed(c, v)
    requires AllDataToTier2FromCache(c, v)
    ensures AllDataToTier2FromCache(c, v')
  {}

  lemma CoreNoOpPreservesAllDataToTier2FromCache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires v.WF(c)
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    requires AllDataToTier2FromCache(c, v)
    ensures AllDataToTier2FromCache(c, v')
  {}

  lemma EngineNoOpPreservesAllDataToTier2FromCache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires v.WF(c)
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    requires AllDataToTier2FromCache(c, v)
    ensures AllDataToTier2FromCache(c, v')
  {}

  lemma ProxyNoOpPreservesAllDataToTier2FromCache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires v.WF(c)
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    requires AllDataToTier2FromCache(c, v)
    ensures AllDataToTier2FromCache(c, v')
  {}


  lemma L2ReceiveCoherenceMessageNoOpPreservesAllDataToTier2FromCache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires AllDataToTier2FromCache(c, v)
    ensures AllDataToTier2FromCache(c, v')
  {}

  lemma L2ScheduleCallbackNoOpPreservesAllDataToTier2FromCache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires AllDataToTier2FromCache(c, v)
    ensures AllDataToTier2FromCache(c, v')
  {}

  lemma L2ReceiveOnMissDataNoOpPreservesAllDataToTier2FromCache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires AllDataToTier2FromCache(c, v)
    ensures AllDataToTier2FromCache(c, v')
  {}

  lemma L2CacheCommunicationNoOpPreservesAllDataToTier2FromCache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires v.WF(c)
    requires L2QueueHeadsWellformed(c, v)
    requires AllDataToTier2FromCache(c, v)
    ensures AllDataToTier2FromCache(c, v')
  {}

  lemma L2DirectoryNoOpPreservesAllDataToTier2FromCache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires v.WF(c)
    requires L2QueueHeadsWellformed(c, v)
    requires AllDataToTier2FromCache(c, v)
    ensures AllDataToTier2FromCache(c, v')
  {}

  lemma L3NoOpPreservesAllDataToTier2FromCache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires L3QueueHeadsWellformed(c, v)
    requires AllDataToTier2FromCache(c, v)
    ensures AllDataToTier2FromCache(c, v')
  {}

  lemma NoOpPreservesAllDataToTier2FromCache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires v.WF(c)
    requires MemMessagesWellformed(c, v)
    requires L2QueueHeadsWellformed(c, v)
    requires L3QueueHeadsWellformed(c, v)
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    requires AllDataToTier2FromCache(c, v)
    ensures AllDataToTier2FromCache(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesAllDataToTier2FromCache(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesAllDataToTier2FromCache(c, v, v', step);
          }
          case EngineStep(eng_step) => {
            EngineNoOpPreservesAllDataToTier2FromCache(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesAllDataToTier2FromCache(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesAllDataToTier2FromCache(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesAllDataToTier2FromCache(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesAllDataToTier2FromCache(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesAllDataToTier2FromCache(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesAllDataToTier2FromCache(c, v, v', step);
              }
            }
          }
          case L3Step(_) => {
            L3NoOpPreservesAllDataToTier2FromCache(c, v, v', step);
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesAllDataToTier2FromCache(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires AllDataToTier2FromCache(c, v)
    ensures AllDataToTier2FromCache(c, v')
  {}

  lemma StartEndCBPreservesAllDataToTier2FromCache(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires AllDataToTier2FromCache(c, v)
    ensures AllDataToTier2FromCache(c, v')
  {}

  lemma MemoryNoOpPreservesAllDataToTier3FromTier2Cache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.MemoryStep?
    requires v.WF(c)
    requires MemMessagesWellformed(c, v)
    requires AllDataToTier3FromTier2Cache(c, v)
    ensures AllDataToTier3FromTier2Cache(c, v')
  {}

  lemma CoreNoOpPreservesAllDataToTier3FromTier2Cache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    requires v.WF(c)
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    requires AllDataToTier3FromTier2Cache(c, v)
    ensures AllDataToTier3FromTier2Cache(c, v')
  {}

  lemma EngineNoOpPreservesAllDataToTier3FromTier2Cache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    requires v.WF(c)
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    requires AllDataToTier3FromTier2Cache(c, v)
    ensures AllDataToTier3FromTier2Cache(c, v')
  {}

  lemma ProxyNoOpPreservesAllDataToTier3FromTier2Cache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    requires v.WF(c)
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    requires AllDataToTier3FromTier2Cache(c, v)
    ensures AllDataToTier3FromTier2Cache(c, v')
  {}

  lemma L2ReceiveCoherenceMessageNoOpPreservesAllDataToTier3FromTier2Cache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveCoherenceMessageStep?
    requires AllDataToTier3FromTier2Cache(c, v)
    ensures AllDataToTier3FromTier2Cache(c, v')
  {}

  lemma L2ScheduleCallbackNoOpPreservesAllDataToTier3FromTier2Cache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ScheduleCallbackStep?
    requires AllDataToTier3FromTier2Cache(c, v)
    ensures AllDataToTier3FromTier2Cache(c, v')
  {}

  lemma L2ReceiveOnMissDataNoOpPreservesAllDataToTier3FromTier2Cache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.ReceiveOnMissDataStep?
    requires AllDataToTier3FromTier2Cache(c, v)
    ensures AllDataToTier3FromTier2Cache(c, v')
  {}

  lemma L2CacheCommunicationNoOpPreservesAllDataToTier3FromTier2Cache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.CacheCommunicationStep?
    requires v.WF(c)
    requires L2QueueHeadsWellformed(c, v)
    requires AllDataToTier3FromTier2Cache(c, v)
    ensures AllDataToTier3FromTier2Cache(c, v')
  {}

  lemma L2DirectoryNoOpPreservesAllDataToTier3FromTier2Cache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    requires step.tile_step.l2_step.DirectoryStep?
    requires v.WF(c)
    requires L2QueueHeadsWellformed(c, v)
    requires AllDataToTier3FromTier2Cache(c, v)
    ensures AllDataToTier3FromTier2Cache(c, v')
  {}

  lemma L3NoOpPreservesAllDataToTier3FromTier2Cache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    requires L3QueueHeadsWellformed(c, v)
    requires AllDataToTier3FromTier2Cache(c, v)
    ensures AllDataToTier3FromTier2Cache(c, v')
  {}

  lemma NoOpPreservesAllDataToTier3FromTier2Cache(c: Tako.Constants, v: Tako.Variables, v' : Tako.Variables, step: Tako.Step)
    requires Tako.NextStep(c, v, v', step, NoOp)
    requires v.WF(c)
    requires MemMessagesWellformed(c, v)
    requires L2QueueHeadsWellformed(c, v)
    requires L3QueueHeadsWellformed(c, v)
    requires AllFwdReqsToTier1HasTier1Source(c, v)
    requires AllDataToTier3FromTier2Cache(c, v)
    ensures AllDataToTier3FromTier2Cache(c, v')
  {
    match step {
      case MemoryStep(_) => {
        MemoryNoOpPreservesAllDataToTier3FromTier2Cache(c, v, v', step);
      }
      case TileStep(_,tile_step,_) => {
        match tile_step {
          case CoreStep(_) => {
            CoreNoOpPreservesAllDataToTier3FromTier2Cache(c, v, v', step);
          }
          case EngineStep(eng_step) => {
            EngineNoOpPreservesAllDataToTier3FromTier2Cache(c, v, v', step);
          }
          case ProxyStep(_) => {
            ProxyNoOpPreservesAllDataToTier3FromTier2Cache(c, v, v', step);
          }
          case L2Step(l2_step) => {
            match l2_step {
              case CacheCommunicationStep(_,_,_,_) => {
                L2CacheCommunicationNoOpPreservesAllDataToTier3FromTier2Cache(c, v, v', step);
              }
              case ReceiveOnMissDataStep(_) => {
                L2ReceiveOnMissDataNoOpPreservesAllDataToTier3FromTier2Cache(c, v, v', step);
              }
              case DirectoryStep(_,_,_) => {
                L2DirectoryNoOpPreservesAllDataToTier3FromTier2Cache(c, v, v', step);
              }
              case ScheduleCallbackStep(_,_,_) => {
                L2ScheduleCallbackNoOpPreservesAllDataToTier3FromTier2Cache(c, v, v', step);
              }
              case ReceiveCoherenceMessageStep() => {
                L2ReceiveCoherenceMessageNoOpPreservesAllDataToTier3FromTier2Cache(c, v, v', step);
              }
            }
          }
          case L3Step(_) => {
            L3NoOpPreservesAllDataToTier3FromTier2Cache(c, v, v', step);
          }
        }
      }
    }
  }

  lemma PerformNextInstPreservesAllDataToTier3FromTier2Cache(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires step.TileStep?
    requires step.tile_step.CoreStep? || step.tile_step.EngineStep?
    requires step.tile_step.CoreStep? ==> step.tile_step.core_step.NextInstStep?
    requires step.tile_step.EngineStep? ==> step.tile_step.eng_step.NextInstStep?
    requires AllDataToTier3FromTier2Cache(c, v)
    ensures AllDataToTier3FromTier2Cache(c, v')
  {}

  lemma StartEndCBPreservesAllDataToTier3FromTier2Cache(c: Tako.Constants, v: Tako.Variables, v': Tako.Variables, step: Tako.Step, re: RefinementEvent)
    requires Tako.NextStep(c, v, v', step, re)
    requires re == StartOnEvict
      || re == StartOnMiss
      || re == StartOnWriteback
      || re == EndOnEvict
      || re == EndOnMiss
      || re == EndOnWriteback
    requires AllDataToTier3FromTier2Cache(c, v)
    ensures AllDataToTier3FromTier2Cache(c, v')
  {}
}