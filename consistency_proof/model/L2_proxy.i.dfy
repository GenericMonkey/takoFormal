include "types.s.dfy"
include "program.i.dfy"
include "network.i.dfy"
include "MSI.i.dfy"

module Proxy {
  import opened Types
  import opened CacheTypes
  import opened Program

  import opened MessageType
  import Network

  import MSI.Controller

  datatype Constants = Constants(
    working_set: set<Address>, // set of addresses accessed by cache
    cache_size: nat,
    locs: Controller.Constants
  ) {
    ghost predicate WF(i: CoreId, p: Program) {
      && cache_size > 0
      && locs.loc == Cache(i, Proxy)
      && locs.dir_loc == Cache(i, L2)
      && working_set == p.WorkingSet()
    }
  }

  datatype ProxyEntry = ProxyEntry(addr : Address, coh: Controller.Variables)


  datatype Variables = Variables(
    cache: seq<ProxyEntry>
  ) {
    ghost predicate WF(c: Constants) {
      && c.locs.loc.Cache?
      && |cache| == c.cache_size
    }
  }
  // Invariant (enforced or assumed)
  // entries in cache are either empty or data (no Allocated or CallbackRunning)

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && (forall i: nat | i < |v.cache| :: v.cache[i].coh.I?)
  }

  datatype Step =
    | CacheCommunicationStep(step: Controller.Step, idx: nat, addr: Address) // perform a cache communication step



  ghost predicate NextStep(c : Constants, v: Variables, v': Variables, step : Step, msgOps: Network.MessageOps)
  {
    match step
      case CacheCommunicationStep(step, idx, addr) => CacheCommunication(c, v, v', msgOps, step, idx, addr)
  }


  /////////////////////
  // UTILITY FUNCTIONS
  /////////////////////
  ghost predicate AddrNotInCache(c: Constants, v: Variables, addr: Address)
  {
    && (forall i: nat | i < |v.cache| && !v.cache[i].coh.I? :: v.cache[i].addr != addr)
  }


  ghost predicate CacheCommunication(c: Constants, v: Variables, v': Variables, msgOps: Network.MessageOps, step: Controller.Step, idx: nat, addr: Address)
  {
    && v.WF(c)
    && v'.WF(c)
    && idx < |v.cache|
    // all other entries are the same
    && (forall i: nat | i < |v.cache| && i != idx :: v.cache[i] == v'.cache[i])
    // update address afterwards to keep same address
    // need it even if evicting for transient states like IIA etc
    && v'.cache[idx].addr == addr
    // index validation
    && (match step
      // TODO: this won't affect deadlock or correctness, but
      // should we somehow restrict this to only be for when we need to get out of the 
      // SMAD hierarchy deadlock a-la Hieragen?
      // No deadlocks caused by sending out "unserviceable" GetMs here because we only
      // need data in L2 to be in S to allow GetMs to be serviced here.
      case GetSStep() => (
        // addr is not in the cache
        && AddrNotInCache(c, v, addr)
        && addr in c.working_set
        && (addr.Morph? && addr.morphType.Private? ==> (addr.morphType.idx == c.locs.loc.core))
      )
      case GetMStep() => (
        // index is empty or shared
        && (match v.cache[idx].coh
          case S(_) => (v.cache[idx].addr == addr)
          case I => (
            && AddrNotInCache(c, v, addr)
            && addr in c.working_set
            && (addr.Morph? && addr.morphType.Private? ==> (addr.morphType.idx == c.locs.loc.core))
          )
          case _ => false
        )
      )
      case EvictStep() => (
        // only restriction is that addr matches
        // S M enforcement handled by NextStep
        && v.cache[idx].addr == addr
      )
      case RecvMsgStep() => (
        // match addr going to recvmessage step with index
        // addr matching the msg is handled by NextStep
        && v.cache[idx].addr == addr
      )
    )
    && Controller.NextStep(c.locs, v.cache[idx].coh, v'.cache[idx].coh, msgOps, step, addr)
  }
}