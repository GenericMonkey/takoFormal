include "types.s.dfy"

module Program {
  import opened Types
  datatype Instruction =
    | Load(addr: Address, reg: Register)
    | Store(addr: Address, val: ConstReg)
    | Flush(addr: Address)
    | RMW(addr: Address, wval: ConstReg, reg: Register)
    | Branch(reg: Register, compval: Value, target: nat)
  {
    ghost predicate HasAddress() {
      this.Load? || this.Store? || this.Flush? || this.RMW?
    }
    
    ghost predicate HasWriteReg() {
      this.Load? || this.RMW?
    }
  }



  type Thread = seq<Instruction>

  datatype Program = Program(
      threads: seq<Thread>,
      onMissCBs: map<Address, Thread>,
      onEvictCBs: map<Address, Thread>,
      onWBCBs: map<Address, Thread>
  ) {
    ghost opaque predicate WF() {
      && AllExistingThreadsNonEmpty()
      && AtomicInstructionsOnlyReferenceAtomicAddrs()

      && AllMorphAddressesHaveCallback()
      && AllCallbacksAreForMorphs()

      // can't have private morph addrs in CBs, and can't have shared morph addrs in CBs for shared addrs.
      && PrivateMorphsOnlyReferenceSharedMorphs()
      && SharedMorphsOnlyReferenceRegularAddrs()

      // can't reference private morph addrs if that core doesn't have ownership of that addr.
      && PrivateMorphAddrsAccessedOnlyInCorrectCore()

      // all registers written to are normal 
      && RegisterInstructionsWriteToRegularRegisters()

      // all flushes are for morph addresses
      && AllFlushInstructionsAreForMorphAddresses()
      // TODO: determine if additional constraints necessary here
      && true
    }

    ghost predicate AllExistingThreadsNonEmpty()
    {
      && (forall i: nat | i < |threads| :: |threads[i]| > 0)
    }

    ghost predicate AtomicInstructionsOnlyReferenceAtomicAddrs()
    {
      && (forall i: nat, inst : Instruction | i < |threads| && inst in threads[i] ::
        && (inst.RMW? ==> inst.addr.atomic)
        && (inst.Load? ==> !inst.addr.atomic)
        && (inst.Store? ==> !inst.addr.atomic)
      )

      && (forall addr: Address, inst : Instruction | addr in onMissCBs && inst in onMissCBs[addr] ::
        && (inst.RMW? ==> inst.addr.atomic)
        && (inst.Load? ==> !inst.addr.atomic)
        && (inst.Store? ==> !inst.addr.atomic)
      )

      && (forall addr: Address, inst : Instruction | addr in onEvictCBs && inst in onEvictCBs[addr] ::
        && (inst.RMW? ==> inst.addr.atomic)
        && (inst.Load? ==> !inst.addr.atomic)
        && (inst.Store? ==> !inst.addr.atomic)
      )

      && (forall addr: Address, inst : Instruction | addr in onWBCBs && inst in onWBCBs[addr] ::
        && (inst.RMW? ==> inst.addr.atomic)
        && (inst.Load? ==> !inst.addr.atomic)
        && (inst.Store? ==> !inst.addr.atomic)
      )
    }

    ghost predicate RegisterInstructionsWriteToRegularRegisters()
    {
      && (forall i: nat, inst : Instruction | i < |threads| && inst in threads[i] && inst.HasWriteReg() ::
        inst.reg.Register?
      )

      && (forall addr: Address, inst : Instruction | addr in onMissCBs && inst in onMissCBs[addr] && inst.HasWriteReg() ::
        inst.reg.Register?
      )

      && (forall addr: Address, inst : Instruction | addr in onEvictCBs && inst in onEvictCBs[addr] && inst.HasWriteReg() ::
        inst.reg.Register?
      )

      && (forall addr: Address, inst : Instruction | addr in onWBCBs && inst in onWBCBs[addr] && inst.HasWriteReg() ::
        inst.reg.Register?
      )
    }

    ghost predicate AllMorphAddressesHaveCallback() {
      // for every address mentioned that is a morph, callbacks exist (even if empty)
      && (forall i: nat, inst : Instruction | i < |threads| && inst in threads[i] ::
        inst.HasAddress() && inst.addr.Morph? ==> (
          && inst.addr in onMissCBs
          && inst.addr in onEvictCBs
          && inst.addr in onWBCBs
        )
      )
      && (forall addr: Address, inst : Instruction | addr in onMissCBs && inst in onMissCBs[addr] ::
        inst.HasAddress() && inst.addr.Morph? ==> (
          && inst.addr in onMissCBs
          && inst.addr in onEvictCBs
          && inst.addr in onWBCBs
        )
      )
      && (forall addr: Address, inst : Instruction | addr in onEvictCBs && inst in onEvictCBs[addr] ::
        inst.HasAddress() && inst.addr.Morph? ==> (
          && inst.addr in onMissCBs
          && inst.addr in onEvictCBs
          && inst.addr in onWBCBs
        )
      )
      && (forall addr: Address, inst : Instruction | addr in onWBCBs && inst in onWBCBs[addr] ::
        inst.HasAddress() && inst.addr.Morph? ==> (
          && inst.addr in onMissCBs
          && inst.addr in onEvictCBs
          && inst.addr in onWBCBs
        )
      )

    }

    ghost predicate AllCallbacksAreForMorphs() {
      && (forall addr: Address | addr in onMissCBs :: addr.Morph?)
      && (forall addr: Address | addr in onEvictCBs :: addr.Morph?)
      && (forall addr: Address | addr in onWBCBs :: addr.Morph?)
    }

    ghost predicate PrivateMorphsOnlyReferenceSharedMorphs()
      requires AllCallbacksAreForMorphs()
    {
      && (forall addr: Address, inst : Instruction | addr in onMissCBs && inst in onMissCBs[addr] ::
        inst.HasAddress() && addr.morphType.Private? ==> (inst.addr.Regular? || inst.addr.morphType.Shared?)
      )
      && (forall addr: Address, inst : Instruction | addr in onEvictCBs && inst in onEvictCBs[addr] ::
        inst.HasAddress() && addr.morphType.Private? ==> (inst.addr.Regular? || inst.addr.morphType.Shared?)
      )
      && (forall addr: Address, inst : Instruction | addr in onWBCBs && inst in onWBCBs[addr] ::
        inst.HasAddress() && addr.morphType.Private? ==> (inst.addr.Regular? || inst.addr.morphType.Shared?)
      )
    }

    ghost predicate SharedMorphsOnlyReferenceRegularAddrs()
      requires AllCallbacksAreForMorphs()
    {
      && (forall addr: Address, inst : Instruction | addr in onMissCBs && inst in onMissCBs[addr] ::
        inst.HasAddress() && addr.morphType.Shared? ==> inst.addr.Regular?
      )
      && (forall addr: Address, inst : Instruction | addr in onEvictCBs && inst in onEvictCBs[addr] ::
        inst.HasAddress() && addr.morphType.Shared? ==> inst.addr.Regular?
      )
      && (forall addr: Address, inst : Instruction | addr in onWBCBs && inst in onWBCBs[addr] ::
        inst.HasAddress() && addr.morphType.Shared? ==> inst.addr.Regular?
      )
    }

    ghost predicate PrivateMorphAddrsAccessedOnlyInCorrectCore()
    {
      && (forall i: nat, inst : Instruction | i < |threads| && inst in threads[i] :: (
        inst.HasAddress() && inst.addr.Morph? && inst.addr.morphType.Private? ==> (
          && inst.addr.morphType.idx == i
        )
      ))
    }

    ghost predicate AllFlushInstructionsAreForMorphAddresses()
    {
      && (forall i: nat, inst : Instruction | i < |threads| && inst in threads[i] && inst.Flush? ::
        inst.addr.Morph?
      )
    }

    ghost function WorkingSet() : (res: set<Address>)
    {
      (set i: nat, inst : Instruction | i < |threads| && inst in threads[i] && inst.HasAddress() :: inst.addr)
      +
      (set addr: Address, inst : Instruction | addr in onMissCBs && inst in onMissCBs[addr] && inst.HasAddress() :: inst.addr)
      +
      (set addr: Address, inst : Instruction | addr in onEvictCBs && inst in onEvictCBs[addr] && inst.HasAddress() :: inst.addr)
      +
      (set addr: Address, inst : Instruction | addr in onWBCBs && inst in onWBCBs[addr] && inst.HasAddress() :: inst.addr)

    }
  }

  // predicate ValidCoreId
}
