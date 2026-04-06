include "types.s.dfy"
include "core.i.dfy"
include "L2.i.dfy"
include "L3.i.dfy"
include "L2_proxy.i.dfy"
include "engine.i.dfy"
include "memory.i.dfy"
include "program.i.dfy"
include "execution.i.dfy"

module Tile {
  import opened Types
  import opened Core
  import opened L2
  import opened Engine
  import opened L3
  import opened Proxy
  import opened Network
  import opened Program

  datatype Constants = Constants(
    coreid: CoreId,
    core: Core.Constants,
    l2: L2.Constants,
    proxy: Proxy.Constants,
    l3: L3.Constants,
    engine: Engine.Constants
  ) {
    ghost predicate WF(i: CoreId, p: Program, addr_map: Address -> CoreId) {
      && coreid == i
      && core.WF(i, p)
      && l2.WF(i, p, addr_map)
      && proxy.WF(i, p)
      && l3.WF(i, p, addr_map)
      && engine.WF(i, p)
    }
  }

  datatype Variables = Variables(
    core: Core.Variables,
    l2: L2.Variables,
    proxy: Proxy.Variables,
    l3: L3.Variables,
    engine: Engine.Variables
  ) {
    ghost predicate WF(c: Constants) {
      && core.WF(c.core)
      && l2.WF(c.l2)
      && proxy.WF(c.proxy)
      && l3.WF(c.l3)
      && engine.WF(c.engine)
    }
  }

  datatype Step =
    | CoreStep(core_step: Core.Step)
    | L2Step(l2_step: L2.Step)
    | ProxyStep(proxy_step: Proxy.Step)
    | L3Step(l3_step: L3.Step)
    | EngineStep(eng_step: Engine.Step)

  ghost predicate Init(c: Constants, v: Variables) {
    && Core.Init(c.core, v.core)
    && L2.Init(c.l2, v.l2)
    && Proxy.Init(c.proxy, v.proxy)
    && L3.Init(c.l3, v.l3)
    && Engine.Init(c.engine, v.engine)
  }

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: Network.MessageOps, flushed: bool)
  {
    && match step {
      case CoreStep(core_step) => (
        && Core.NextStep(c.core, v.core, v'.core, core_step, msgOps, flushed)
        && v.l2 == v'.l2
        && v.proxy == v'.proxy
        && v.l3 == v'.l3
        && v.engine == v'.engine
      )
      case L2Step(l2_step) => (
        && v.core == v'.core
        && L2.NextStep(c.l2, v.l2, v'.l2, l2_step, msgOps)
        && v.proxy == v'.proxy
        && v.l3 == v'.l3
        && v.engine == v'.engine
      )
      case ProxyStep(proxy_step) => (
        && v.core == v'.core
        && v.l2 == v'.l2
        && Proxy.NextStep(c.proxy, v.proxy, v'.proxy, proxy_step, msgOps)
        && v.l3 == v'.l3
        && v.engine == v'.engine
      )
      case L3Step(l3_step) => (
        && v.core == v'.core
        && v.l2 == v'.l2
        && v.proxy == v'.proxy
        && L3.NextStep(c.l3, v.l3, v'.l3, l3_step, msgOps)
        && v.engine == v'.engine
      )
      case EngineStep(eng_step) => (
        && v.core == v'.core
        && v.l2 == v'.l2
        && v.proxy == v'.proxy
        && v.l3 == v'.l3
        && Engine.NextStep(c.engine, v.engine, v'.engine, eng_step, msgOps)
      )
    }
  }
}

module Tako {
  import opened Types
  import opened RefinementTypes
  import opened Tile
  import opened Network
  import opened Memory
  import opened Program
  import opened Execution

  datatype Constants = Constants(
    program: Program,
    addr_map: Address -> CoreId,
    tiles: seq<Tile.Constants>,
    network: Network.Constants,
    memory: Memory.Constants
  ) {
    ghost predicate WF() {
      && (forall addr: Address :: addr_map(addr) < |tiles|)
      && program.WF()
      && memory.WF()
      && |tiles| >= |program.threads|
      && (forall i: nat | i < |tiles| :: tiles[i].WF(i, program, addr_map))
    }
  }
  datatype GhostRefinementData = GhostRefinementData(
    execution: Execution,
    writes_to_addr: map<Address, seq<Event>>,
    callback_epochs: map<Address, Epoch>,
    pcs: imap<ThreadId, RuntimeData>
  )

  datatype Variables = Variables(
    tiles: seq<Tile.Variables>,
    memory: Memory.Variables,
    network: Network.Variables,
    ghost g : GhostRefinementData
  ) {
    ghost predicate WF(c: Constants) {
      && c.WF()
      && |tiles| == |c.tiles|
      && (forall i: nat | i < |tiles| :: tiles[i].WF(c.tiles[i]))
      && memory.WF(c.memory)
    }
  }

  datatype Step =
    | TileStep(tile_idx: nat, tile_step: Tile.Step, msgOps: Network.MessageOps)
    | MemoryStep(msgOps: Network.MessageOps)

  ghost predicate OneTileChanged(c: Constants, v: Variables, v': Variables, idx: nat)
    requires idx < |c.tiles|
    requires v.WF(c) && v'.WF(c)
  {
    && (forall i: nat | i < |c.tiles| && i != idx :: v.tiles[i] == v'.tiles[i])
  }

  ghost predicate Init(c: Constants, v: Variables) {
    && v.WF(c)
    && (forall i: nat | i < |c.tiles| :: Tile.Init(c.tiles[i], v.tiles[i]))
    && Memory.Init(c.memory, v.memory)
    && Network.Init(c.network, v.network)
    && v.g.execution.Init(c.program)
    && v.g.writes_to_addr ==
      (map addr: Address | addr in c.program.WorkingSet() && addr.Regular? ::
        [W(addr, Just(0), ThreadInfo(Initial(), Start()))]
      )
    && v.g.callback_epochs ==
      (map addr: Address | addr in c.program.WorkingSet() && addr.Morph? ::
        Out(0)
      )
    && v.g.pcs == (imap id : ThreadId | (
      && id.CoreId?
      && id.id < |c.tiles|
      && |c.tiles[id.id].core.insts| > 0
    ) ::
      RuntimeData(
        PC(v.tiles[id.id].core.pc, v.tiles[id.id].core.count),
        v.tiles[id.id].core.regs,
        seq(
          |v.tiles[id.id].core.results|,
          (i: nat)
            requires i < |v.tiles[id.id].core.results|
          => (
            v.tiles[id.id].core.results[i].1
          )
        )
      )
    )
  }

  ghost predicate UpdateExecution(c: Constants, v: Variables, v': Variables, step: Step, re: RefinementEvent)
    requires v.WF(c) && v'.WF(c)
    requires NextStepReal(c, v, v', step)
  {
    match step {
      case TileStep(tile_idx, tile_step, _) => (
        match tile_step {
          case CoreStep(core_step) => (
            match core_step {
              case NextInstStep(inst, idx) => (
                && var id: ThreadId := CoreId(tile_idx);
                && var pc: PC := PC(v.tiles[tile_idx].core.pc, v.tiles[tile_idx].core.count);
                && var cache := v.tiles[tile_idx].core.cache;
                && var vals' := seq(
                  |v'.tiles[tile_idx].core.results|,
                  (i: nat)
                    requires i < |v'.tiles[tile_idx].core.results|
                  => (
                    v'.tiles[tile_idx].core.results[i].1
                  )
                );
                && var regs' := v'.tiles[tile_idx].core.regs;
                && var pc' := v'.tiles[tile_idx].core.pc;
                && var count' := v'.tiles[tile_idx].core.count;
                && id in v.g.pcs
                && match inst {
                  case Load(addr, reg) => (
                    && re == PerformLoad
                    && var r := (if addr.Regular? then
                          R(addr, cache[idx].coh.val, ThreadInfo(id, pc))
                        else
                          Rcb(addr, cache[idx].coh.val, ThreadInfo(id, pc)));
                    && v'.g.writes_to_addr == v.g.writes_to_addr
                    && v'.g.execution.pre == v.g.execution.pre.(events := v.g.execution.pre.events + {r})
                    && (if addr.Regular? then (
                      && addr in v.g.writes_to_addr
                      && |v.g.writes_to_addr[addr]| > 0
                      && var w := v.g.writes_to_addr[addr][|v.g.writes_to_addr[addr]| -1];
                      && v'.g.execution.wit == v.g.execution.wit.(
                        rf := v.g.execution.wit.rf + {(w, r)}
                      )
                    ) else (
                      && v'.g.execution.wit == v.g.execution.wit.(
                          cbo := v.g.execution.wit.cbo
                            + (set e_o: Event | e_o in v.g.execution.CBEventsToAddr(addr) :: (e_o, r))
                      )
                    ))
                    && v'.g.callback_epochs == v.g.callback_epochs
                    && v'.g.pcs == v.g.pcs[id := RuntimeData(pc.(pc := pc'), regs', vals')]
                  )
                  case Store(addr, val) => (
                    && re == PerformStore
                    && var wval_real := if val.Reg? then v.tiles[tile_idx].core.regs[val.reg] else Just(val.val/*, Some(Core(c.locs.loc.core, v.pc))*/);
                    && var w := (if addr.Regular? then
                          W(addr, wval_real, ThreadInfo(id, pc))
                        else
                          Wcb(addr, wval_real, ThreadInfo(id, pc)));
                    && (if addr.Regular? then
                      && addr in v.g.writes_to_addr
                      && v'.g.writes_to_addr == v.g.writes_to_addr[addr := v.g.writes_to_addr[addr] + [w]]
                    else
                      && v'.g.writes_to_addr == v.g.writes_to_addr
                    )
                    && v'.g.execution.pre == v.g.execution.pre.(events := v.g.execution.pre.events + {w})
                    && (if addr.Regular? then (
                      && v'.g.execution.wit == v.g.execution.wit.(
                            mo := v.g.execution.wit.mo
                              + (set w_o: Event | w_o in v.g.execution.WritesToAddr(addr) :: (w_o, w))
                      )
                    ) else (
                      && v'.g.execution.wit == v.g.execution.wit.(
                          cbo := v.g.execution.wit.cbo
                            + (set e_o: Event | e_o in v.g.execution.CBEventsToAddr(addr) :: (e_o, w))
                      )
                    ))
                    && (if addr.Regular? then (
                      v'.g.callback_epochs == v.g.callback_epochs
                    ) else (
                      && addr in v.g.callback_epochs
                      && v.g.callback_epochs[addr].In? // TODO: this should be provable
                      && v'.g.callback_epochs == v.g.callback_epochs[addr := In(v.g.callback_epochs[addr].epoch, v.g.callback_epochs[addr].me, Some(w))]
                    ))
                    && v'.g.pcs == v.g.pcs[id := RuntimeData(pc.(pc := pc'), regs', vals')]
                  )
                  case Flush(addr) => (
                    && re == PerformFlush
                    && var f := F(addr, ThreadInfo(id, pc));
                    && v'.g.writes_to_addr == v.g.writes_to_addr
                    && v'.g.execution.pre == v.g.execution.pre.(events := v.g.execution.pre.events + {f})
                    && v'.g.execution.wit == v.g.execution.wit.(
                        cbo := v.g.execution.wit.cbo
                          + (set e_o: Event | e_o in v.g.execution.CBEventsToAddr(addr) :: (e_o, f))
                    )
                    && v'.g.callback_epochs == v.g.callback_epochs
                    && v'.g.pcs == v.g.pcs[id := RuntimeData(pc.(pc := pc'), regs', vals')]
                  )
                  case RMW(addr, wval, reg) => (
                    && re == PerformRMW
                    && var wval_real := if wval.Reg? then v.tiles[tile_idx].core.regs[wval.reg] else Just(wval.val/*, Some(Core(c.locs.loc.core, v.pc))*/);
                    && var rmw := (if addr.Regular? then
                          Event.RMW(addr, cache[idx].coh.val, wval_real, ThreadInfo(id, pc))
                        else
                          RMWcb(addr, cache[idx].coh.val, wval_real, ThreadInfo(id, pc)));
                    && (if addr.Regular? then
                      && addr in v.g.writes_to_addr
                      && v'.g.writes_to_addr == v.g.writes_to_addr[addr := v.g.writes_to_addr[addr] + [rmw]]
                    else
                      && v'.g.writes_to_addr == v.g.writes_to_addr
                    )
                    && v'.g.execution.pre == v.g.execution.pre.(events := v.g.execution.pre.events + {rmw})
                    && (if addr.Regular? then (
                      && addr in v.g.writes_to_addr
                      && |v.g.writes_to_addr[addr]| > 0
                      && var w := v.g.writes_to_addr[addr][|v.g.writes_to_addr[addr]| -1];
                      && v'.g.execution.wit == v.g.execution.wit.(
                        rf := v.g.execution.wit.rf + {(w, rmw)},
                        mo := v.g.execution.wit.mo
                          + (set w_o: Event | w_o in v.g.execution.WritesToAddr(addr) :: (w_o, rmw))
                      )
                    ) else (
                      && v'.g.execution.wit == v.g.execution.wit.(
                          cbo := v.g.execution.wit.cbo
                            + (set e_o: Event | e_o in v.g.execution.CBEventsToAddr(addr) :: (e_o, rmw))
                      )
                    ))
                    && (if addr.Regular? then (
                      v'.g.callback_epochs == v.g.callback_epochs
                    ) else (
                      && addr in v.g.callback_epochs
                      && v.g.callback_epochs[addr].In? // TODO: this should be provable
                      && v'.g.callback_epochs == v.g.callback_epochs[addr := In(v.g.callback_epochs[addr].epoch, v.g.callback_epochs[addr].me, Some(rmw))]
                    ))
                    && v'.g.pcs == v.g.pcs[id := RuntimeData(pc.(pc := pc'), regs', vals')]
                  )
                  case Branch(reg, compval, target) => (
                    && re == PerformBranch
                    && v'.g.writes_to_addr == v.g.writes_to_addr
                    && v'.g.execution == v.g.execution
                    && v'.g.callback_epochs == v.g.callback_epochs
                    && v'.g.pcs == v.g.pcs[id := RuntimeData(pc.(pc := pc', count := count'), regs', vals')]
                  )
                }
              )
              case _ => (
                // no update here (cache coms)
                && v.g == v'.g
                && re == NoOp
              )
            }
          )
          case EngineStep(eng_step) => (
            match eng_step {
              case NextInstStep(idx, inst, c_idx) => (
                && var addr := v.tiles[tile_idx].engine.buffer[idx].addr;
                && addr in v.g.callback_epochs
                && var cb_type := EngReqToCBType(v.tiles[tile_idx].engine.buffer[idx].cb_type);
                && var id: ThreadId := CallbackId(addr, cb_type, v.g.callback_epochs[addr].epoch);
                && var pc: PC := PC(v.tiles[tile_idx].engine.buffer[idx].pc, v.tiles[tile_idx].engine.buffer[idx].count);
                && var cache := v.tiles[tile_idx].engine.cache;
                && var vals' := v'.tiles[tile_idx].engine.buffer[idx].values;
                && var regs' := v'.tiles[tile_idx].engine.buffer[idx].regs;
                && var pc' := v'.tiles[tile_idx].engine.buffer[idx].pc;
                && var count' := v'.tiles[tile_idx].engine.buffer[idx].count;
                && id in v.g.pcs // TODO: in theory provable
                && match inst {
                  case Load(addr, reg) => (
                    && re == PerformLoad
                    && var r := (if addr.Regular? then
                          R(addr, cache[c_idx].coh.val, ThreadInfo(id, pc))
                        else
                          Rcb(addr, cache[c_idx].coh.val, ThreadInfo(id, pc)));
                    && v'.g.writes_to_addr == v.g.writes_to_addr
                    && v'.g.execution.pre == v.g.execution.pre.(events := v.g.execution.pre.events + {r})
                    && (if addr.Regular? then (
                      && addr in v.g.writes_to_addr
                      && |v.g.writes_to_addr[addr]| > 0
                      && var w := v.g.writes_to_addr[addr][|v.g.writes_to_addr[addr]| -1];
                      && v'.g.execution.wit == v.g.execution.wit.(
                        rf := v.g.execution.wit.rf + {(w, r)}
                      )
                    ) else (
                      && v'.g.execution.wit == v.g.execution.wit.(
                          cbo := v.g.execution.wit.cbo
                            + (set e_o: Event | e_o in v.g.execution.CBEventsToAddr(addr) :: (e_o, r))
                      )
                    ))
                    && v'.g.callback_epochs == v.g.callback_epochs
                    && v'.g.pcs == v.g.pcs[id := RuntimeData(pc.(pc := pc'), regs', vals')]
                  )
                  case Store(addr, val) => (
                    && re == PerformStore
                    && var wval_real := if val.Reg? then v.tiles[tile_idx].engine.buffer[idx].regs[val.reg] else Just(val.val/*, Some(Core(c.locs.loc.core, v.pc))*/);
                    && var w := (if addr.Regular? then
                          W(addr, wval_real, ThreadInfo(id, pc))
                        else
                          Wcb(addr, wval_real, ThreadInfo(id, pc)));
                    && (if addr.Regular? then
                      && addr in v.g.writes_to_addr
                      && v'.g.writes_to_addr == v.g.writes_to_addr[addr := v.g.writes_to_addr[addr] + [w]]
                    else
                      && v'.g.writes_to_addr == v.g.writes_to_addr
                    )
                    && v'.g.execution.pre == v.g.execution.pre.(events := v.g.execution.pre.events + {w})
                    && (if addr.Regular? then (
                      && v'.g.execution.wit == v.g.execution.wit.(
                            mo := v.g.execution.wit.mo
                              + (set w_o: Event | w_o in v.g.execution.WritesToAddr(addr) :: (w_o, w))
                      )
                    ) else (
                      && v'.g.execution.wit == v.g.execution.wit.(
                          cbo := v.g.execution.wit.cbo
                            + (set e_o: Event | e_o in v.g.execution.CBEventsToAddr(addr) :: (e_o, w))
                      )
                    ))
                    && (if addr.Regular? then (
                      v'.g.callback_epochs == v.g.callback_epochs
                    ) else (
                      && addr in v.g.callback_epochs
                      && v.g.callback_epochs[addr].In? // TODO: this should be provable
                      && v'.g.callback_epochs == v.g.callback_epochs[addr := In(v.g.callback_epochs[addr].epoch, v.g.callback_epochs[addr].me, Some(w))]
                    ))
                    && v'.g.pcs == v.g.pcs[id := RuntimeData(pc.(pc := pc'), regs', vals')]
                  )
                  case Flush(addr) => (
                    && false // no flushes in callbacks
                  )
                  case RMW(addr, wval, reg) => (
                    && re == PerformRMW
                    && var wval_real := if wval.Reg? then v.tiles[tile_idx].engine.buffer[idx].regs[wval.reg] else Just(wval.val/*, Some(Core(c.locs.loc.core, v.pc))*/);
                    && var rmw := (if addr.Regular? then
                          Event.RMW(addr, cache[c_idx].coh.val, wval_real, ThreadInfo(id, pc))
                        else
                          RMWcb(addr, cache[c_idx].coh.val, wval_real, ThreadInfo(id, pc)));
                    && (if addr.Regular? then
                      && addr in v.g.writes_to_addr
                      && v'.g.writes_to_addr == v.g.writes_to_addr[addr := v.g.writes_to_addr[addr] + [rmw]]
                    else
                      && v'.g.writes_to_addr == v.g.writes_to_addr
                    )
                    && v'.g.execution.pre == v.g.execution.pre.(events := v.g.execution.pre.events + {rmw})
                    && (if addr.Regular? then (
                      && addr in v.g.writes_to_addr
                      && |v.g.writes_to_addr[addr]| > 0
                      && var w := v.g.writes_to_addr[addr][|v.g.writes_to_addr[addr]| -1];
                      && v'.g.execution.wit == v.g.execution.wit.(
                        rf := v.g.execution.wit.rf + {(w, rmw)},
                        mo := v.g.execution.wit.mo
                          + (set w_o: Event | w_o in v.g.execution.WritesToAddr(addr) :: (w_o, rmw))
                      )
                    ) else (
                      && v'.g.execution.wit == v.g.execution.wit.(
                          cbo := v.g.execution.wit.cbo
                            + (set e_o: Event | e_o in v.g.execution.CBEventsToAddr(addr) :: (e_o, rmw))
                      )
                    ))
                    && (if addr.Regular? then (
                      v'.g.callback_epochs == v.g.callback_epochs
                    ) else (
                      && addr in v.g.callback_epochs
                      && v.g.callback_epochs[addr].In? // TODO: this should be provable
                      && v'.g.callback_epochs == v.g.callback_epochs[addr := In(v.g.callback_epochs[addr].epoch, v.g.callback_epochs[addr].me, Some(rmw))]
                    ))
                    && v'.g.pcs == v.g.pcs[id := RuntimeData(pc.(pc := pc'), regs', vals')]
                  )
                  case Branch(reg, compval, target) => (
                    && re == PerformBranch
                    && v'.g.writes_to_addr == v.g.writes_to_addr
                    && v'.g.execution == v.g.execution
                    && v'.g.callback_epochs == v.g.callback_epochs
                    && v'.g.pcs == v.g.pcs[id := RuntimeData(pc.(pc := pc', count := count'), regs', vals')]
                  )
                }
              )
              case StartCallbackStep(idx) => (
                && var addr := v.tiles[tile_idx].engine.buffer[idx].addr;
                && addr in v.g.callback_epochs
                && var cb_type := v.tiles[tile_idx].engine.buffer[idx].cb_type;
                && var id: ThreadId := CallbackId(addr, EngReqToCBType(cb_type), v.g.callback_epochs[addr].epoch);
                && var s := if cb_type.OnMiss? then Ms(addr, ThreadInfo(id, Start())) else
                  Es(addr, cb_type.val, cb_type.OnWriteBack?, ThreadInfo(id, Start()));
                && v'.g.writes_to_addr == v.g.writes_to_addr
                && v'.g.execution.pre == v.g.execution.pre.(events := v.g.execution.pre.events + {s})
                && v'.g.execution.wit == v.g.execution.wit.(
                    cbo := v.g.execution.wit.cbo
                      + (set e_o: Event | e_o in v.g.execution.CBEventsToAddr(addr) :: (e_o, s))
                )
                && var epoch' := if cb_type.OnMiss? then Miss(v.g.callback_epochs[addr].epoch) else Evict(v.g.callback_epochs[addr].epoch, cb_type.val, cb_type.OnWriteBack?);
                && v'.g.callback_epochs == v.g.callback_epochs[addr := epoch']
                && var pc := PC(v.tiles[tile_idx].engine.buffer[idx].pc, v.tiles[tile_idx].engine.buffer[idx].count);
                && var regs := v.tiles[tile_idx].engine.buffer[idx].regs;
                && var vals := v.tiles[tile_idx].engine.buffer[idx].values;
                && v'.g.pcs == v.g.pcs[id := RuntimeData(pc, regs, vals)]
                && re == if cb_type.OnMiss? then
                            StartOnMiss
                          else if cb_type.OnEvict? then
                            StartOnEvict
                          else
                            StartOnWriteback
              )
              case FinishCallbackStep(idx) => (
                && var entry := v.tiles[tile_idx].engine.buffer[idx];
                && entry.addr in v.g.callback_epochs
                && var cb_type := EngReqToCBType(entry.cb_type);
                && var id: ThreadId := CallbackId(entry.addr, cb_type, v.g.callback_epochs[entry.addr].epoch);
                && id in v.g.pcs
                && var e := if cb_type.OnMiss? then Me(entry.addr, Transform(entry.values), ThreadInfo(id, End())) else
                  Ee(entry.addr, entry.cb_type.OnWriteBack?, ThreadInfo(id, End()));
                && v'.g.writes_to_addr == v.g.writes_to_addr
                && v'.g.execution.pre == v.g.execution.pre.(events := v.g.execution.pre.events + {e})
                && v'.g.execution.wit == v.g.execution.wit.(
                    cbo := v.g.execution.wit.cbo
                      + (set e_o: Event | e_o in v.g.execution.CBEventsToAddr(entry.addr) :: (e_o, e))
                )
                && var epoch' := if cb_type.OnMiss? then In(v.g.callback_epochs[entry.addr].epoch, e, None) else Out(v.g.callback_epochs[entry.addr].epoch + 1);
                && v'.g.callback_epochs == v.g.callback_epochs[entry.addr := epoch']
                && v'.g.pcs == v.g.pcs[id := RuntimeData(End(), v.g.pcs[id].regs, v.g.pcs[id].vals)]
                && re == if cb_type.OnMiss? then
                            EndOnMiss
                          else if cb_type.OnEvict? then
                            EndOnEvict
                          else
                            EndOnWriteback
              )
              case _ => (
                // no change for other engine steps
                // (receive callback + cache comms)
                && v.g == v'.g
                && re == NoOp
              )
            }
          )
          case L2Step(_) => (
            && v.g == v'.g
            && re == NoOp
          )
          case L3Step(l3_step) => (
            && v.g == v'.g
            && re == NoOp
          )
          case ProxyStep(_) => (
            // no change for L2, L3, proxy
            && v.g == v'.g
            && re == NoOp
          )
        }
      )
      case MemoryStep(msgOps) => (
        // nothing commits with a memory step
        && v.g == v'.g
        && re == NoOp
      )
    }
  }

  ghost predicate NextStepReal(c: Constants, v: Variables, v': Variables, step: Step)
    requires v.WF(c) && v'.WF(c)
  {
    && match step {
      case TileStep(tile_idx, tile_step, msgOps) => (
        && tile_idx < |c.tiles|
        && OneTileChanged(c, v, v', tile_idx)
        && v.memory == v'.memory
        && var flushed := if tile_step.CoreStep? && tile_step.core_step.NextInstStep? && tile_step.core_step.inst.HasAddress() then (
          // overapprox: not in any L2 (technically just need not in same core)
          && (forall i : nat | i < |c.tiles| :: L2.AddrHasNoActiveCacheEntry(c.tiles[i].l2, v.tiles[i].l2, tile_step.core_step.inst.addr))
          // overapprox: not in any L3 (technically just need for addr_map's core)
          && (forall i : nat | i < |c.tiles| :: L3.AddrHasNoActiveCacheEntry(c.tiles[i].l3, v.tiles[i].l3, tile_step.core_step.inst.addr))
          // no in flight requests to engine (OnMiss is ruled out by PendingCB in cache, but need to rule out OnEvict/OnWB in flight)
          && (tile_step.core_step.inst.addr in v.network.inFlightEngReqs ==> |v.network.inFlightEngReqs[tile_step.core_step.inst.addr]| == 0)
          // not in any engine waiting for eviction
          && (forall i : nat | i < |c.tiles| :: Engine.AddrNotPendingCallback(c.tiles[i].engine, v.tiles[i].engine, tile_step.core_step.inst.addr))
        ) else false;
        && Tile.NextStep(c.tiles[tile_idx], v.tiles[tile_idx], v'.tiles[tile_idx], tile_step, msgOps, flushed)
      )
      case MemoryStep(msgOps) => (
        // memory advances, no core
        && v.tiles == v'.tiles
        && Memory.NextStep(c.memory, v.memory, v'.memory, msgOps)
      )
    }

  }

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, re: RefinementEvent) {
    && v.WF(c)
    && v'.WF(c)
    && NextStepReal(c, v, v', step)
    && UpdateExecution(c, v, v', step, re)
    && assert Network.UniqueAddrsOnSend(step.msgOps.send) by {
      NextStepSendsHaveUniqueAddress(c, v, v', step);
    }
    // network advances
    && Network.Next(c.network, v.network, v'.network, step.msgOps)
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, re: RefinementEvent)
  {
    exists step :: NextStep(c, v, v', step, re)
  }

  lemma CoreNextStepSendsHaveUniqueAddress(c: Constants, v: Variables, v': Variables, step: Step)
    requires v.WF(c) && v'.WF(c)
    requires NextStepReal(c, v, v', step)
    requires step.TileStep?
    requires step.tile_step.CoreStep?
    ensures Network.UniqueAddrsOnSend(step.msgOps.send)
  {
    assert Network.UniqueAddrsOnSend(step.msgOps.send);
  }

  lemma ProxyNextStepSendsHaveUniqueAddress(c: Constants, v: Variables, v': Variables, step: Step)
    requires v.WF(c) && v'.WF(c)
    requires NextStepReal(c, v, v', step)
    requires step.TileStep?
    requires step.tile_step.ProxyStep?
    ensures Network.UniqueAddrsOnSend(step.msgOps.send)
  {
    assert Network.UniqueAddrsOnSend(step.msgOps.send);
  }

  lemma EngineNextStepSendsHaveUniqueAddress(c: Constants, v: Variables, v': Variables, step: Step)
    requires v.WF(c) && v'.WF(c)
    requires NextStepReal(c, v, v', step)
    requires step.TileStep?
    requires step.tile_step.EngineStep?
    ensures Network.UniqueAddrsOnSend(step.msgOps.send)
  {
    assert Network.UniqueAddrsOnSend(step.msgOps.send);
  }

  lemma L2NextStepSendsHaveUniqueAddress(c: Constants, v: Variables, v': Variables, step: Step)
    requires v.WF(c) && v'.WF(c)
    requires NextStepReal(c, v, v', step)
    requires step.TileStep?
    requires step.tile_step.L2Step?
    ensures Network.UniqueAddrsOnSend(step.msgOps.send)
  {
    assert Network.UniqueAddrsOnSend(step.msgOps.send);
  }

  lemma L3NextStepSendsHaveUniqueAddress(c: Constants, v: Variables, v': Variables, step: Step)
    requires v.WF(c) && v'.WF(c)
    requires NextStepReal(c, v, v', step)
    requires step.TileStep?
    requires step.tile_step.L3Step?
    ensures Network.UniqueAddrsOnSend(step.msgOps.send)
  {
    assert Network.UniqueAddrsOnSend(step.msgOps.send);
  }

  lemma MemoryNextStepSendsHaveUniqueAddress(c: Constants, v: Variables, v': Variables, step: Step)
    requires v.WF(c) && v'.WF(c)
    requires NextStepReal(c, v, v', step)
    requires step.MemoryStep?
    ensures Network.UniqueAddrsOnSend(step.msgOps.send)
  {
    assert Network.UniqueAddrsOnSend(step.msgOps.send);
  }

  lemma NextStepSendsHaveUniqueAddress(c: Constants, v: Variables, v': Variables, step: Step)
    requires v.WF(c) && v'.WF(c)
    requires NextStepReal(c, v, v', step)
    ensures Network.UniqueAddrsOnSend(step.msgOps.send)
  {
    match step {
      case TileStep(tile_idx, tile_step, msgOps) => {
        match tile_step {
          case CoreStep(core_step) => {
            CoreNextStepSendsHaveUniqueAddress(c, v, v', step);
          }
          case EngineStep(eng_step) => {
            EngineNextStepSendsHaveUniqueAddress(c, v, v', step);
          }
          case L2Step(l2_step) => {
            L2NextStepSendsHaveUniqueAddress(c, v, v', step);
          }
          case L3Step(l3_step) => {
            L3NextStepSendsHaveUniqueAddress(c, v, v', step);
          }
          case ProxyStep(proxy_step) => {
            ProxyNextStepSendsHaveUniqueAddress(c, v, v', step);
          }
        }
      }
      case MemoryStep(msgOps) => {
        MemoryNextStepSendsHaveUniqueAddress(c, v, v', step);
      }
    }
  }
}