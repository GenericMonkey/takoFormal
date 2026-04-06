include "types.s.dfy"
include "network.i.dfy"

module MSI {

  module Controller {
    import opened Types
    import opened Network
    import opened MessageType
    import opened CacheTypes

    datatype Constants = Constants(
      loc: Location, // who are we?
      dir_loc: Location // who is our directory?
    )

    datatype Variables =
      | I()
      | ISD()
      | IMAD(ack_cnt: nat)
      | IMA(ack_cnt: nat, total_acks: nat, val: Value)
      | S(val: Value)
      | SMAD(ack_cnt: nat, val: Value)
      | SMA(ack_cnt: nat, total_acks: nat, val: Value)
      | M(val: Value)
      | MIA(val: Value)
      | MIF(val: Value)
      | SIA()
      | SII()
      | IIA()
    {
      // todo: might be useless
      ghost predicate HasVal() {
        && (match this
          case S(_) => true
          case M(_) => true
          case IMA(_, _, _) => true
          case SMA(_, _, _) => true
          case SMAD(_, _) => true
          case MIA(_) => true
          case _ => false
        )
      }

      ghost predicate Loadable() {
        && (match this
          case S(_) | SMAD(_, _) | SMA(_, _, _) | M(_) => true
          case _ => false
        )
      }

      ghost predicate HasMostRecentVal() {
        || this.Loadable()
        || this.IMA?
      }

      ghost predicate Evicting() {
        && (match this
          case MIA(_) | SIA() | IIA() | MIF(_) | SII() => true
          case _ => false
        )
      }

      ghost predicate PreData() {
        && (match this
          case IMAD(_) | ISD() | I() => true
          case _ => false
        )
      }
    }

    datatype Step =
      | GetSStep()
      | GetMStep()
      | EvictStep()
      | RecvMsgStep()


    predicate NextStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, step: Step, addr: Address)
    {
      match step
        case GetSStep() => DoGetS(c, v, v', msgOps, addr)
        case GetMStep() => DoGetM(c, v, v', msgOps, addr)
        case EvictStep() => DoEviction(c, v, v', msgOps, addr)
        case RecvMsgStep() => DoRecvMsg(c, v, v', msgOps, addr)
    }

    predicate DoGetS(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, addr: Address)
    {
      && v.I?
      && v'.ISD?
      && msgOps.recv.None?
      && msgOps.send == multiset{ CoherenceMsg(CohMsg.GetS, Metadata(addr, c.loc, c.dir_loc)) }
    }

    predicate DoGetM(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, addr: Address)
    {
      && (match v
        case I() => v' == IMAD(0)
        case S(val) => v' == SMAD(1, val) // already has ack from self
        case _ => false
      )
      && msgOps.recv.None?
      && msgOps.send == multiset{ CoherenceMsg(CohMsg.GetM, Metadata(addr, c.loc, c.dir_loc)) }
    }

    predicate DoEviction(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, addr: Address)
    {
      && msgOps.recv.None?
      && (match v
        case M(val) => (
          && v' == MIA(val)
          && msgOps.send == multiset{ CoherenceMsg(CohMsg.PutM(val), Metadata(addr, c.loc, c.dir_loc)) }
        )
        case S(_) => (
          && v' == SIA()
          && msgOps.send == multiset{ CoherenceMsg(CohMsg.PutS, Metadata(addr, c.loc, c.dir_loc)) }
        )
        case _ => false
      )
    }


    predicate DoRecvMsg(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, addr: Address)
    {
      && msgOps.recv.Some?
      && msgOps.recv.val.CoherenceMsg?
      && var msg := msgOps.recv.val;
      && addr == msg.meta.addr
      && msg.meta.dst == c.loc // intended recipient
      && (match v
        case ISD => (
          && msg.coh_msg.Data?
          && v' == S(msg.coh_msg.val)
          && msgOps.send == multiset{}
        )
        case IMAD(ack_cnt) => (
          && msgOps.send == multiset{}
          && (match msg.coh_msg
            case Data(val, total_acks) => (
              && (v' == if msg.meta.src == c.dir_loc then
                          if ack_cnt == total_acks then M(val) else IMA(ack_cnt, total_acks, val)
                        else
                          M(val)
              )
            )
            case InvAck() => (
              && v' == IMAD(ack_cnt + 1)
            )
            case _ => false
          )
        )
        case IMA(ack_cnt, total_acks, val) => (
          && msgOps.send == multiset{}
          && msg.coh_msg.InvAck?
          && v' == if ack_cnt + 1 == total_acks then M(val) else IMA(ack_cnt + 1, total_acks, val)
        )
        case S(val) => (
          && msg.coh_msg.Inv?
          // send inv ack, dst is orig src (directory updates this)
          && msgOps.send == multiset{ CoherenceMsg(CohMsg.InvAck, Metadata(msg.meta.addr, msg.meta.dst, msg.meta.src)) }
          // to I
          && v' == I()
        )
        case SMAD(ack_cnt, val) => (
          && (match msg.coh_msg
            case Data(d_val, total_acks) => (
              && msgOps.send == multiset{}
              && d_val == val  // TODO: this should be provable
              && (v' == if ack_cnt == total_acks then M(val) else SMA(ack_cnt, total_acks, val))
            )
            case InvAck() => (
              && msgOps.send == multiset{}
              && v' == SMAD(ack_cnt + 1, val)
            )
            case Inv() => (
              && v' == IMAD(ack_cnt)
              && msgOps.send == multiset{ CoherenceMsg(CohMsg.InvAck, Metadata(msg.meta.addr, msg.meta.dst, msg.meta.src)) }
            )
            case _ => false
          )
        )
        case SMA(ack_cnt, total_acks, val) => (
          && msgOps.send == multiset{}
          && msg.coh_msg.InvAck?
          && v' == if ack_cnt + 1 == total_acks then M(val) else SMA(ack_cnt + 1, total_acks, val)
        )
        case M(val) => (
          && (match msg.coh_msg
            case FwdGetM() => (
              // need to send data to new owner
              // data is coming from owner: IMAD will go to M, SMAD will go to SMA.
              // we init SMAD with 1 from self, so the 1 here will match that
              && msgOps.send == multiset{ CoherenceMsg(CohMsg.Data(val, 1), Metadata(msg.meta.addr, msg.meta.dst, msg.meta.src)) }
              // to I
              && v' == I()
            )
            case FwdGetS() => (
              // ack_cnt doesn't matter here either (receiver will go ISD -> S)
              // need to send data to owner and dir...
              && msgOps.send == multiset{
                CoherenceMsg(CohMsg.Data(val, 0), Metadata(msg.meta.addr, msg.meta.dst, msg.meta.src)),
                CoherenceMsg(CohMsg.Data(val, 0), Metadata(msg.meta.addr, msg.meta.dst, c.dir_loc))
              }
              // to S
              && v' == S(val)
            )
            case _ => false
          )
        )
        case MIA(val) => (
          && (match msg.coh_msg
            case FwdGetM() => (
              // data is coming from owner: IMAD will go to M, SMAD will go to SMA.
              // we init SMAD with 1 from self, so the 1 here will match that
              && msgOps.send == multiset{ CoherenceMsg(CohMsg.Data(val, 1), Metadata(msg.meta.addr, msg.meta.dst, msg.meta.src)) }
              && v' == IIA()
            )
            case FwdGetS() => (
              // ack_cnt doesn't matter here either (receiver will go ISD -> S)
              // need to send data to owner and dir...
              && msgOps.send == multiset{
                CoherenceMsg(CohMsg.Data(val, 0), Metadata(msg.meta.addr, msg.meta.dst, msg.meta.src)),
                CoherenceMsg(CohMsg.Data(val, 0), Metadata(msg.meta.addr, msg.meta.dst, c.dir_loc))
              }
              && v' == SIA()
            )
            case PutAck() => (
              && msgOps.send == multiset{}
              && v' == I()
            )
            case PutAckStale() => (
              && msgOps.send == multiset{}
              && v' == MIF(val)
            )
            case _ => false
          )
        )
        // exists if PutAck beats the Fwd. after processing, go to I
        case MIF(val) => (
          && (match msg.coh_msg
            case FwdGetM() => (
              // data is coming from owner: IMAD will go to M, SMAD will go to SMA.
              // we init SMAD with 1 from self, so the 1 here will match that
              && msgOps.send == multiset{ CoherenceMsg(CohMsg.Data(val, 1), Metadata(msg.meta.addr, msg.meta.dst, msg.meta.src)) }
              && v' == I()
            )
            case FwdGetS() => (
              // ack_cnt doesn't matter here either (receiver will go ISD -> S)
              // need to send data to owner and dir...
              && msgOps.send == multiset{
                CoherenceMsg(CohMsg.Data(val, 0), Metadata(msg.meta.addr, msg.meta.dst, msg.meta.src)),
                CoherenceMsg(CohMsg.Data(val, 0), Metadata(msg.meta.addr, msg.meta.dst, c.dir_loc))
              }
              && v' == I()
            )
            case _ => false
          )
        )
        case SIA() => (
          && (match msg.coh_msg
            case PutAck() => (
              && msgOps.send == multiset{}
              && v' == I()
            )
            case PutAckStale() => (
              && msgOps.send == multiset{}
              && v' == SII()
            )
            case Inv() => (
              && v' == IIA()
              && msgOps.send == multiset{ CoherenceMsg(CohMsg.InvAck, Metadata(msg.meta.addr, msg.meta.dst, msg.meta.src)) }
            )
            case _ => false
          )
        )
        // exists in case PutAck beats the Inv. after processing, go to I
        case SII() => (
          && (match msg.coh_msg
            case Inv() => (
              && v' == I()
              && msgOps.send == multiset{ CoherenceMsg(CohMsg.InvAck, Metadata(msg.meta.addr, msg.meta.dst, msg.meta.src)) }
            )
            case _ => false
          )
        )
        case IIA() => (
          && (match msg.coh_msg
            case PutAck() => (
              && msgOps.send == multiset{}
              && v' == I()
            )
            // TODO: think about this case
            case PutAckStale() => (
              && msgOps.send == multiset{}
              && v' == I()
            )
            case _ => false
          )
        )
        case I() => false
      )
    }

  }

  module Directory {

    import opened Types
    import opened Network
    import opened MessageType
    import opened CacheTypes


    datatype Step =
      | RecvMsgStep()

    datatype Constants = Constants(
      loc: Location
    )

    datatype Variables =
      | I(val: Value)
      | S(sharers: set<Location>, val: Value)
      | M(owner: Location)
      | SD(sharers: set<Location>, former_owner: Location)
    {
      ghost predicate HasVal() {
        && (match this
          case S(_, _) => true
          case I(_) => true
          case _ => false
        )
      }
    }


    predicate NextStep(c: Constants, v: Variables, v': Variables, msgOps: MessageOps, step: Step)
    {
      match step
        case RecvMsgStep() => DoRecvMsg(c, v, v', msgOps)
    }

    predicate DoRecvMsg(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
      && msgOps.recv.Some?
      && msgOps.recv.val.CoherenceMsg?
      && var msg := msgOps.recv.val;
      && msg.meta.dst == c.loc // intended recipient
      && (match v
        case I(val) => (
          && (match msg.coh_msg
            case GetM() => (
              && v' == M(msg.meta.src)
              && msgOps.send == multiset{ CoherenceMsg(CohMsg.Data(val, 0), Metadata(msg.meta.addr, msg.meta.dst, msg.meta.src)) }
            )
            case GetS() => (
              && v' == S({msg.meta.src}, val)
              && msgOps.send == multiset{ CoherenceMsg(CohMsg.Data(val, 0), Metadata(msg.meta.addr, msg.meta.dst, msg.meta.src)) }
            )
            case PutS() => (
              && v' == v // no change
              && msgOps.send == multiset{ CoherenceMsg(CohMsg.PutAck, Metadata(msg.meta.addr, msg.meta.dst, msg.meta.src)) }
            )
            // ignore inc data
            case PutM(_) => (
              && v' == v // no change
              && msgOps.send == multiset{ CoherenceMsg(CohMsg.PutAck, Metadata(msg.meta.addr, msg.meta.dst, msg.meta.src)) }
            )
            case _ => false
          )
        )
        case S(sharers, val) => (
          && (match msg.coh_msg
            case GetM() => (
              && v' == M(msg.meta.src)
              && msgOps.send ==
                // ack count is |sharers|, if this is S -> M promotion one free inv is handled in controller
                multiset{ CoherenceMsg(CohMsg.Data(val, |sharers|), Metadata(msg.meta.addr, msg.meta.dst, msg.meta.src)) }
                // inv to all sharers (except the potential requestor)
                + multiset(set x | x in sharers && x != msg.meta.src :: CoherenceMsg(CohMsg.Inv, Metadata(msg.meta.addr, msg.meta.src, x)))
            )
            case GetS() => (
              && v' == S(sharers + {msg.meta.src}, val)
              //count doesn't matter here
              && msgOps.send == multiset{ CoherenceMsg(CohMsg.Data(val, 0), Metadata(msg.meta.addr, msg.meta.dst, msg.meta.src)) }
            )
            case PutS() => (
              && v' == (if sharers - {msg.meta.src} == {} then
                    I(val)
                 else
                    S(sharers - {msg.meta.src}, val)
              )
              && msgOps.send == multiset{ CoherenceMsg(CohMsg.PutAck, Metadata(msg.meta.addr, msg.meta.dst, msg.meta.src)) }
            )
            // ignore inc data
            case PutM(_) => (
              // w/o point to point, can have PutM be the last one
              && v' == (if sharers - {msg.meta.src} == {} then
                    I(val)
                 else
                    S(sharers - {msg.meta.src}, val)
              )
              && msgOps.send == multiset{ CoherenceMsg(CohMsg.PutAck, Metadata(msg.meta.addr, msg.meta.dst, msg.meta.src)) }
            )
            case _ => false
          )
        )
        case M(owner) => (
          && (match msg.coh_msg
            case GetM() => (
              // new owner
              && v' == M(msg.meta.src)
              // spoof fwdgetm source as original src
              && msgOps.send == multiset{ CoherenceMsg(CohMsg.FwdGetM, Metadata(msg.meta.addr, msg.meta.src, owner)) }
            )
            case GetS() => (
              && v' == SD({owner, msg.meta.src}, owner)
              //count doesn't matter here
              // spoof fwdgets source as original src
              && msgOps.send == multiset{ CoherenceMsg(CohMsg.FwdGetS, Metadata(msg.meta.addr, msg.meta.src, owner)) }
            )
            case PutS() => (
              && v' == v
              && msgOps.send == multiset{ CoherenceMsg(CohMsg.PutAckStale, Metadata(msg.meta.addr, msg.meta.dst, msg.meta.src)) }
            )
            case PutM(data) => (
              && v' == (if msg.meta.src == owner then I(data) else v)
              && var msgtype := (if msg.meta.src == owner then CohMsg.PutAck else CohMsg.PutAckStale);
              && msgOps.send == multiset{ CoherenceMsg(msgtype, Metadata(msg.meta.addr, msg.meta.dst, msg.meta.src)) }
            )
            case _ => false
          )
        )
        case SD(sharers, former_owner) => (
          && (match msg.coh_msg
            case PutS() => (
              && v' == SD(sharers - {msg.meta.src}, former_owner)
              && var msgtype := (if msg.meta.src in sharers then CohMsg.PutAck else CohMsg.PutAckStale);
              && msgOps.send == multiset{ CoherenceMsg(msgtype, Metadata(msg.meta.addr, msg.meta.dst, msg.meta.src)) }
            )
            // ignore inc data
            case PutM(_) => (
              && v' == SD(sharers - {msg.meta.src}, former_owner)
              && msgOps.send == multiset{ CoherenceMsg(CohMsg.PutAckStale, Metadata(msg.meta.addr, msg.meta.dst, msg.meta.src)) }
            )
            case Data(val, _) => (
              // guaranteed to be coming from former owner
              && msg.meta.src == former_owner
              && v' == (if sharers != {} then S(sharers, val) else I(val))
              && msgOps.send == multiset{}
            )
            case _ => false
          )
        )
      )
    }

  }

}