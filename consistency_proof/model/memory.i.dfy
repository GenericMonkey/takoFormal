include "types.s.dfy"
include "network.i.dfy"

module Memory {
  import opened Types
  import opened CacheTypes
  import opened EngineTypes

  import opened MessageType
  import Network


  datatype Constants = Constants(
    mem_size: nat
  ) {
    ghost predicate WF() {
      && mem_size > 0
    }
  }


  datatype Variables = Variables(
    memory: seq<Value>
  ) {
    ghost predicate WF(c: Constants) {
      && |memory| == c.mem_size
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    // mem initialized to 0
    && (forall i: nat | i < |v.memory| :: v.memory[i] == Just(0/*, None*/))
  }

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, msgOps: Network.MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && msgOps.recv.Some?
    && var msg := msgOps.recv.val;
    && msg.meta.addr.Regular?
    && msg.meta.dst == Mem()
    && msg.meta.addr.idx < |v.memory|
    && msg.CoherenceMsg?
    && (match msg.coh_msg
      case PutM(val) => (
        && v'.memory[msg.meta.addr.idx] == val
        && (forall i: nat | i < |v.memory| && i != msg.meta.addr.idx :: v'.memory[i] == v.memory[i])
        && msgOps.send == multiset{
          CoherenceMsg(PutAck, Metadata(msg.meta.addr, Mem(), msg.meta.src))
        }
      )
      case GetM() => (
        && v'.memory == v.memory
        && msgOps.send == multiset{
          CoherenceMsg(CohMsg.Data(v.memory[msg.meta.addr.idx], 0), Metadata(msg.meta.addr, Mem(), msg.meta.src))
        }
      )
      case _ => false
    )
  }



}