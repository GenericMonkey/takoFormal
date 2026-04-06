include "types.s.dfy"
// stolen from course
// the network promises to deliver messages at most once.

// This module isn't part of Types because Types is trusted but this module
// needn't be.
module MessageType {
  import opened Types
  import opened CacheTypes
  import opened EngineTypes
  // a full list of messages that can be sent by the system
  datatype Metadata = Metadata(addr: Address, src: Location, dst: Location)

  datatype Message =
    | CoherenceMsg(coh_msg: CohMsg, meta: Metadata)
    | EngineRequest(engine_req: EngineRequest, meta: Metadata)
    | EngineResponse(engine_resp: EngineResponse, meta: Metadata)

}

// Read this Network carefully. Unlike prior exercises, here we use a Network
// that delivers each message at most once.
module Network {
  import opened MessageType
  import opened Types

  type HostId = nat

  datatype MessageOps = MessageOps(recv: Option<Message>, send: multiset<Message>)

  datatype Constants = Constants  // no constants for network

  // Network state is the multiset of messages in flight. Delivering a message
  // removes it from the multiset. It's a multiset because, if the same message
  // is sent twice, we can't disappear one of them.
  datatype Variables = Variables(
    inFlightMessages:multiset<Message>,
    inFlightEngReqs: map<Address, seq<Message>>,
    deliveredMessages:multiset<Message>
  )

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.inFlightMessages == multiset{}
    && v.inFlightEngReqs == map[]
    && v.deliveredMessages == multiset{}
  }

  ghost predicate UniqueAddrsOnSend(msgs: multiset<Message>)
  {
    forall m1, m2 | m1 in msgs && m1.EngineRequest? && m2 in msgs && m2.EngineRequest? && m1.meta.addr == m2.meta.addr :: m1 == m2
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    requires UniqueAddrsOnSend(msgOps.send)
  {
    // Only allow receipt of a message if we've seen it has been sent.
    && (msgOps.recv.Some? ==> (
      && (!msgOps.recv.val.EngineRequest? ==> msgOps.recv.val in v.inFlightMessages)
      && (msgOps.recv.val.EngineRequest? ==>
        (
          // for engine requests, maintain FIFO per address
          && msgOps.recv.val.meta.addr in v.inFlightEngReqs
          && |v.inFlightEngReqs[msgOps.recv.val.meta.addr]| > 0 
          && msgOps.recv.val == v.inFlightEngReqs[msgOps.recv.val.meta.addr][0]
        )
      )
    ))
    && var newEngReqs := set m | m in msgOps.send && m.EngineRequest?;
    && var newMsgs := multiset(set m | m in msgOps.send && !m.EngineRequest?);
    // Record the sent message, if there was one.
    && v'.inFlightMessages ==
      v.inFlightMessages
        // remove a message "used up" by receipt
        - (if msgOps.recv.None? || msgOps.recv.val.EngineRequest? then multiset{} else multiset{ msgOps.recv.val })
        // add a new message supplied by send
        + (newMsgs)
    && var removeOld := if (msgOps.recv.None? || !msgOps.recv.val.EngineRequest?) then 
        // remove a message "used up" by receipt
        v.inFlightEngReqs
      else
        v.inFlightEngReqs[msgOps.recv.val.meta.addr := v.inFlightEngReqs[msgOps.recv.val.meta.addr][1..]];
    && v'.inFlightEngReqs == removeOld
        // add a new message supplied by send
        + (map m | m in newEngReqs :: m.meta.addr := (if m.meta.addr in v.inFlightEngReqs then v.inFlightEngReqs[m.meta.addr] else []) + [m])
    // track delivered messages
    && v'.deliveredMessages ==
      v.deliveredMessages
        // add used up message to delivered
        + (if msgOps.recv.None? then multiset{} else multiset{ msgOps.recv.val })
  }
}