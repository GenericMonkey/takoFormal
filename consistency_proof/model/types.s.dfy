module Types {
  type CoreId = nat
  datatype Option<T> =
    | None
    | Some(val: T)

  datatype MorphType =
      | Shared
      | Private(idx: nat) // index of the core that owns the morph

  datatype MorphData =
    | Phantom
    // | Real

  datatype Address =
    | Regular(idx: nat, atomic: bool)
    | Morph(idx: nat, morphType: MorphType, morphData: MorphData, atomic: bool)

  // denotes a value from/to memory.
  datatype Value =
    | Just(val : int)// , origin: Option<InstLoc>)       // return "just" the value for real non-morph
    | Transform(vals : seq<Value>) //return the "transformed" contents for a morph.
    // Internally build a sequence of the requests/values you read to track dependencies in your value
  {
    // ghost predicate MatchingVal(other: Value)
    // {
    //   match this {
    //     case Just(v, _) => other.Just? && other.val == v
    //     case Transform(vals) =>
    //       match other {
    //         case Transform(other_vals) => |vals| == |other_vals| && (forall i: nat | i < |vals| :: vals[i].MatchingVal(other_vals[i]))
    //         case _ => false
    //       }
    //   }
    // }
  }
  
  datatype Register = 
    | Register(idx: nat) // infinite registerfile
    | EvictReg() // dedicated register to hold evicted values

  datatype ConstReg =
    | Const(val: int)
    | Reg(reg: Register)

  datatype InstLoc =
    | Core(core: CoreId, idx: nat)
    | Callback(addr: Address, idx: nat)

}

module CacheTypes {
  import opened Types

  datatype CacheLevel =
    | L1
    | eL1
    | Proxy
    | L2
    | L3
  {
    ghost predicate Tier1() {
      this.L1? || this.eL1? || this.Proxy?
    }
  }

  datatype Location =
    | Cache(core: CoreId, level: CacheLevel)
    | Engine(core: CoreId) // messages sent to CB Buffer
    | Mem() // messages sent to memory

  datatype CohMsg =
    | GetM
    | GetS
    | PutM(val: Value)
    | PutS
    | PutAck
    | PutAckStale
    | FwdGetM
    | FwdGetS
    | Inv
    | InvAck
    | Data(val: Value, ack_count: nat)
  {
    ghost predicate IsChildToParent() {
      this.GetM? || this.GetS? || this.PutM? || this.PutS? || this.Data?
    }
    ghost predicate IsParentToChild() {
      this.PutAck? || this.Data?
    }
    ghost predicate IsChildToChild() {
      this.FwdGetM? || this.FwdGetS? || this.Inv? || this.InvAck? || this.Data?
    }
    // data can be sent
    // - parent to child (dir has it)
    // - child to parent (FwdGetS)
    // - child to child (FwdGetM)
  }


}

module EngineTypes {
  import opened Types

  datatype EngineRequest =
    | OnMiss(idx: nat) // location to write result to
    | OnEvict(val: Value) // value of evicted block
    | OnWriteBack(val: Value) // value of evicted block

  datatype EngineResponse =
    | OnMissData(idx: nat, val: Value)

}

module RefinementTypes {
  datatype RefinementEvent =
    | PerformLoad
    | PerformStore
    | PerformFlush
    | PerformRMW
    | PerformBranch
    | StartOnMiss
    | StartOnEvict
    | StartOnWriteback
    | EndOnMiss
    | EndOnEvict
    | EndOnWriteback
    | NoOp
}