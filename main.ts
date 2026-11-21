// main.ts -- Sokoban solver for make.fun "sokoban-solver-01-run-20261121".
//
// Idea: every level is a 1-wide hallway plus 1-4 rooms (3-4 boxes each,
// one door each). A box pushed out of a room into the hallway can never
// come back, so each room is solved on its own and the level optimum is
// the sum of the room optima. Each room is solved push-optimally with A*
// over pushes (player walks are filled in afterwards by BFS), using a
// min-matching heuristic and corner / wall-run / 2x2 deadlock pruning.
// Rooms are stitched together with hallway walks; every room but the
// last is solved with the extra condition that the player can walk back
// out through its door, and the room where that costs the most pushes
// is solved last (where it costs nothing).
//
// Pure Node stdlib, no network, no clock, no randomness: two runs write
// the same bytes. One run answers all 5 instances well inside the 60 s
// wall. Plain JavaScript in a .ts file (no TypeScript-only syntax), so
// Node runs it as-is.

const fs = require("node:fs");
const path = require("node:path");

// The harness mounts the input/output trees at /input and /output in its
// container, and passes the same locations through MAKEFUN_INPUT_DIR /
// MAKEFUN_OUTPUT_DIR when it runs a bot directly on a machine instead
// (the kit's own template reads them exactly this way). These are only
// directory locations, never a source of variation: the same input always
// yields the same output.
const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR || "/input";
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR || "/output";
const IDS = ["i001", "i002", "i003", "i004", "i005"];

// [dx, dy, letter]. This fixed order keeps every BFS deterministic.
const DIRS = [
  { dx: 0, dy: -1, ch: "u" },
  { dx: 0, dy: 1, ch: "d" },
  { dx: -1, dy: 0, ch: "l" },
  { dx: 1, dy: 0, ch: "r" },
];

// Work caps are counted in expansions, never in seconds: a run cut off
// by the clock would answer differently from one execution to the next.
const ASTAR_MAX_EXPANSIONS = 1000000;
const GREEDY_MAX_EXPANSIONS = 500000;

// ---------------------------------------------------------------- parsing

function parseLevel(text) {
  const lines = text.split("\n");
  while (lines.length > 0 && lines[lines.length - 1] === "") lines.pop();
  const h = lines.length;
  let w = 0;
  for (const l of lines) w = Math.max(w, l.length);
  const at = (x, y) => {
    if (y < 0 || y >= h) return "#";
    const line = lines[y];
    if (x < 0 || x >= line.length) return "#";
    return line[x];
  };
  const id = (x, y) => y * w + x;
  const floor = new Set();
  const goals = new Set();
  const boxes = new Set();
  let player = -1;
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      const c = at(x, y);
      if (c === "#") continue;
      const cell = id(x, y);
      floor.add(cell);
      if (c === "." || c === "*" || c === "+") goals.add(cell);
      if (c === "$" || c === "*") boxes.add(cell);
      if (c === "@" || c === "+") player = cell;
    }
  }
  return { w, h, at, id, floor, goals, boxes, player };
}

// Split the floor into the hallway (the player's row) and the rooms
// (the connected components left when the hallway row is removed).
// Each room has exactly one door cell: a room cell next to a hallway cell.
function detectRooms(level) {
  const { w, floor, player, id } = level;
  const hallY = Math.floor(player / w);
  const hall = new Set();
  for (const c of floor) if (Math.floor(c / w) === hallY) hall.add(c);
  const rest = new Set([...floor].filter((c) => !hall.has(c)));
  const rooms = [];
  const seen = new Set();
  const sortedRest = [...rest].sort((a, b) => a - b);
  for (const start of sortedRest) {
    if (seen.has(start)) continue;
    const comp = [];
    const q = [start];
    seen.add(start);
    for (let qi = 0; qi < q.length; qi++) {
      const c = q[qi];
      comp.push(c);
      const x = c % w;
      const y = Math.floor(c / w);
      for (const d of DIRS) {
        const n = id(x + d.dx, y + d.dy);
        if (rest.has(n) && !seen.has(n)) {
          seen.add(n);
          q.push(n);
        }
      }
    }
    comp.sort((a, b) => a - b);
    const doors = comp
      .filter((c) => {
        const x = c % w;
        const y = Math.floor(c / w);
        return DIRS.some((d) => hall.has(id(x + d.dx, y + d.dy)));
      })
      .sort((a, b) => a - b);
    rooms.push({ cells: comp, doors });
  }
  return { hall, rooms };
}

// ------------------------------------------------------------------- heap

// Binary min-heap ordered by (f, h, seq): seq breaks ties in insertion
// order, so the search is fully deterministic.
class Heap {
  constructor() {
    this.a = [];
  }
  get size() {
    return this.a.length;
  }
  push(node) {
    const a = this.a;
    a.push(node);
    let i = a.length - 1;
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (cmpNode(a[p], a[i]) <= 0) break;
      const t = a[p];
      a[p] = a[i];
      a[i] = t;
      i = p;
    }
  }
  pop() {
    const a = this.a;
    const top = a[0];
    const last = a.pop();
    if (a.length > 0) {
      a[0] = last;
      let i = 0;
      for (;;) {
        const l = 2 * i + 1;
        const r = l + 1;
        let m = i;
        if (l < a.length && cmpNode(a[l], a[m]) < 0) m = l;
        if (r < a.length && cmpNode(a[r], a[m]) < 0) m = r;
        if (m === i) break;
        const t = a[m];
        a[m] = a[i];
        a[i] = t;
        i = m;
      }
    }
    return top;
  }
}

function cmpNode(a, b) {
  if (a.f !== b.f) return a.f - b.f;
  if (a.h !== b.h) return a.h - b.h;
  return a.seq - b.seq;
}

// ------------------------------------------------------------- room model

// Build everything a room search needs. Local indices 0..n-1 are the room
// cells; local index n is the entry cell (the hallway cell next to the
// door), which the player may walk on but boxes may never enter.
function buildRoom(level, comp, door) {
  const { w, id, goals, boxes } = level;
  const n = comp.length;
  const ENTRY = n;
  const index = new Map();
  comp.forEach((c, i) => index.set(c, i));
  const cellX = new Array(n);
  const cellY = new Array(n);
  comp.forEach((c, i) => {
    cellX[i] = c % w;
    cellY[i] = Math.floor(c / w);
  });
  // The entry cell: the hallway neighbour of the door (first, sorted).
  let entry = -1;
  {
    const dx = door % w;
    const dy = Math.floor(door / w);
    const cands = [];
    for (const d of DIRS) {
      const nc = id(dx + d.dx, dy + d.dy);
      if (Math.floor(nc / w) === Math.floor(level.player / w) && level.floor.has(nc)) cands.push(nc);
    }
    cands.sort((a, b) => a - b);
    entry = cands[0];
  }
  const entryX = entry % w;
  const entryY = Math.floor(entry / w);

  // Walk neighbours for every walk cell (room cells + entry cell).
  // localAt(x, y): room index, or ENTRY for the entry cell, else -1.
  const localAt = (x, y) => {
    if (x === entryX && y === entryY) return ENTRY;
    return index.has(id(x, y)) ? index.get(id(x, y)) : -1;
  };
  const walkNb = [];
  for (let i = 0; i < n; i++) {
    const list = [];
    for (let di = 0; di < 4; di++) {
      const d = DIRS[di];
      const to = localAt(cellX[i] + d.dx, cellY[i] + d.dy);
      if (to >= 0) list.push({ to, dir: di });
    }
    walkNb.push(list);
  }
  {
    const list = [];
    for (let di = 0; di < 4; di++) {
      const d = DIRS[di];
      const to = localAt(entryX + d.dx, entryY + d.dy);
      if (to >= 0 && to !== ENTRY) list.push({ to, dir: di });
    }
    walkNb.push(list);
  }

  // All-pairs shortest paths over room cells (boxes move only there).
  const dist = [];
  for (let s = 0; s < n; s++) {
    const row = new Array(n).fill(Infinity);
    row[s] = 0;
    const q = [s];
    for (let qi = 0; qi < q.length; qi++) {
      const u = q[qi];
      for (const e of walkNb[u]) {
        if (e.to < n && row[e.to] === Infinity) {
          row[e.to] = row[u] + 1;
          q.push(e.to);
        }
      }
    }
    dist.push(row);
  }

  const goalList = comp
    .filter((c) => goals.has(c))
    .map((c) => index.get(c))
    .sort((a, b) => a - b);
  const goalSet = new Set(goalList);
  let goalMask = 0n;
  for (const g of goalList) goalMask |= 1n << BigInt(g);
  const startBoxes = comp.filter((c) => boxes.has(c)).map((c) => index.get(c));
  let startMask = 0n;
  for (const b of startBoxes) startMask |= 1n << BigInt(b);

  // A cell is blocked for a box when the player cannot stand there and
  // a box cannot sit there: a wall, another room's floor, or a hallway
  // cell. The entry cell is NOT blocked: the player stands on it to push
  // a box off the door cell back into the room (i001 starts with a box
  // on its door cell, which is movable exactly this way).
  const blockedForBox = (x, y) => {
    const gid = id(x, y);
    return !index.has(gid) && gid !== entry;
  };

  // Static dead cells: corners, and closed wall runs with no goal.
  const dead = new Array(n).fill(false);
  for (let i = 0; i < n; i++) {
    if (goalSet.has(i)) continue;
    const x = cellX[i];
    const y = cellY[i];
    const up = blockedForBox(x, y - 1);
    const down = blockedForBox(x, y + 1);
    const left = blockedForBox(x - 1, y);
    const right = blockedForBox(x + 1, y);
    if ((up || down) && (left || right)) dead[i] = true;
  }
  // Wall runs: maximal runs of room cells sharing a blocked side, closed
  // at both ends by blocked cells, holding no goal -> every cell dead.
  const markRun = (cells) => {
    if (cells.length === 0) return;
    if (cells.some((c) => goalSet.has(c))) return;
    for (const c of cells) dead[c] = true;
  };
  const runsAlong = (blockedSide, along) => {
    // blockedSide: "up" | "down" | "left" | "right"; along: "h" | "v".
    const groups = new Map();
    for (let i = 0; i < n; i++) {
      if (goalSet.has(i)) continue;
      const x = cellX[i];
      const y = cellY[i];
      let blocked = false;
      if (blockedSide === "up") blocked = blockedForBox(x, y - 1);
      if (blockedSide === "down") blocked = blockedForBox(x, y + 1);
      if (blockedSide === "left") blocked = blockedForBox(x - 1, y);
      if (blockedSide === "right") blocked = blockedForBox(x + 1, y);
      if (!blocked) continue;
      const key = along === "h" ? y : x;
      if (!groups.has(key)) groups.set(key, []);
      groups.get(key).push(i);
    }
    for (const list of groups.values()) {
      list.sort((a, b) => (along === "h" ? cellX[a] - cellX[b] : cellY[a] - cellY[b]));
      let run = [list[0]];
      const flush = () => {
        // Closed when the cells just past both ends are blocked for boxes.
        const first = run[0];
        const last = run[run.length - 1];
        let closed = false;
        if (along === "h") {
          closed =
            blockedForBox(cellX[first] - 1, cellY[first]) &&
            blockedForBox(cellX[last] + 1, cellY[last]);
        } else {
          closed =
            blockedForBox(cellX[first], cellY[first] - 1) &&
            blockedForBox(cellX[last], cellY[last] + 1);
        }
        if (closed) markRun(run);
        run = [];
      };
      for (let k = 1; k < list.length; k++) {
        const prev = list[k - 1];
        const cur = list[k];
        const adjacent =
          along === "h"
            ? cellX[cur] === cellX[prev] + 1 && cellY[cur] === cellY[prev]
            : cellY[cur] === cellY[prev] + 1 && cellX[cur] === cellX[prev];
        if (adjacent) run.push(cur);
        else {
          flush();
          run = [cur];
        }
      }
      flush();
    }
  };
  runsAlong("up", "h");
  runsAlong("down", "h");
  runsAlong("left", "v");
  runsAlong("right", "v");

  // 2x2 blocks: four cells forming a square, each a room cell or blocked
  // for boxes, none a goal. Dead when every room cell in it holds a box.
  const quads = [];
  {
    let minX = Infinity;
    let maxX = -Infinity;
    let minY = Infinity;
    let maxY = -Infinity;
    for (let i = 0; i < n; i++) {
      minX = Math.min(minX, cellX[i]);
      maxX = Math.max(maxX, cellX[i]);
      minY = Math.min(minY, cellY[i]);
      maxY = Math.max(maxY, cellY[i]);
    }
    for (let y = minY; y < maxY; y++) {
      for (let x = minX; x < maxX; x++) {
        const cells = [
          [x, y],
          [x + 1, y],
          [x, y + 1],
          [x + 1, y + 1],
        ];
        let ok = true;
        const roomCells = [];
        for (const [cx, cy] of cells) {
          const gid = id(cx, cy);
          if (index.has(gid)) {
            const li = index.get(gid);
            if (goalSet.has(li)) {
              ok = false;
              break;
            }
            roomCells.push(li);
          } else if (gid === entry || level.floor.has(gid)) {
            // The player can stand here (entry cell, hallway, another
            // room), so a box in this square can be pushed out of it:
            // not a frozen block.
            ok = false;
            break;
          }
          // Otherwise a wall (or out of bounds): blocking, fine.
        }
        if (ok && roomCells.length > 0) quads.push(roomCells);
      }
    }
  }

  return {
    n,
    ENTRY,
    entry,
    door,
    cells: comp,
    cellX,
    cellY,
    walkNb,
    dist,
    goalList,
    goalSet,
    goalMask,
    startMask,
    dead,
    quads,
    localAt,
  };
}

// ------------------------------------------------------------ room search

function bitsOf(mask, n) {
  const out = [];
  for (let i = 0; i < n; i++) if ((mask >> BigInt(i)) & 1n) out.push(i);
  return out;
}

// Cells the player can reach from `from`, walking over walk cells while
// treating boxes (mask) as obstacles. Returns a Uint8Array over walk
// cells (0..n, n = ENTRY).
function reachableRegion(room, mask, from) {
  const seen = new Uint8Array(room.n + 1);
  seen[from] = 1;
  const q = [from];
  for (let qi = 0; qi < q.length; qi++) {
    const u = q[qi];
    for (const e of room.walkNb[u]) {
      if (seen[e.to]) continue;
      if (e.to < room.n && ((mask >> BigInt(e.to)) & 1n)) continue;
      seen[e.to] = 1;
      q.push(e.to);
    }
  }
  return seen;
}

function minSetBit(seen) {
  for (let i = 0; i < seen.length; i++) if (seen[i]) return i;
  return -1;
}

// Minimum over assignments of the sum of shortest-path distances from
// each box to a distinct goal. Admissible: one push moves one box one
// step, so the remaining pushes are at least this sum. Infinity when
// some box cannot reach any goal.
function heuristic(room, mask) {
  const bs = bitsOf(mask, room.n);
  const gs = room.goalList;
  if (bs.length !== gs.length) return Infinity;
  const k = bs.length;
  if (k === 0) return 0;
  let best = Infinity;
  const used = new Array(k).fill(false);
  const assign = (i, cost) => {
    if (cost >= best) return;
    if (i === k) {
      best = cost;
      return;
    }
    for (let j = 0; j < k; j++) {
      if (used[j]) continue;
      const d = room.dist[bs[i]][gs[j]];
      if (d === Infinity) continue;
      used[j] = true;
      assign(i + 1, cost + d);
      used[j] = false;
    }
  };
  assign(0, 0);
  return best;
}

function isDead(room, mask) {
  const bs = bitsOf(mask, room.n);
  for (const b of bs) if (room.dead[b]) return true;
  for (const quad of room.quads) {
    let all = true;
    for (const c of quad) {
      if (!((mask >> BigInt(c)) & 1n)) {
        all = false;
        break;
      }
    }
    if (all) return true;
  }
  return false;
}

// A* (greedy=false) or greedy best-first (greedy=true) over pushes.
// State = (box mask, canonical player = smallest cell of the player's
// reachable region). The canonical player is valid because every future
// push depends only on which cells the player can reach, not on where
// exactly the player stands inside that region.
function searchRoom(room, requireExit, greedy, maxExpansions) {
  const { n, ENTRY, goalMask, startMask } = room;
  const startRegion = reachableRegion(room, startMask, ENTRY);
  const startCanon = minSetBit(startRegion);
  const h0 = heuristic(room, startMask);
  if (h0 === Infinity) return { status: "unsolvable", expansions: 0 };
  if (startMask === goalMask && (!requireExit || startRegion[ENTRY])) {
    return { status: "ok", pushes: [], count: 0, expansions: 0 };
  }
  const keyOf = (mask, canon) => mask.toString(36) + ":" + canon;
  const open = new Heap();
  const gScore = new Map();
  const parent = new Map();
  let seq = 0;
  const startKey = keyOf(startMask, startCanon);
  gScore.set(startKey, 0);
  open.push({ f: greedy ? h0 : h0, h: h0, g: 0, seq: seq++, mask: startMask, canon: startCanon });
  let expansions = 0;
  while (open.size > 0) {
    const node = open.pop();
    const nodeKey = keyOf(node.mask, node.canon);
    if (node.g > (gScore.has(nodeKey) ? gScore.get(nodeKey) : Infinity)) continue;
    expansions++;
    if (expansions > maxExpansions) return { status: "cap", expansions };
    const region = reachableRegion(room, node.mask, node.canon);
    if (node.mask === goalMask && (!requireExit || region[ENTRY])) {
      const pushes = [];
      let k = nodeKey;
      while (parent.has(k)) {
        const p = parent.get(k);
        pushes.push({ box: p.box, dir: p.dir });
        k = p.prev;
      }
      pushes.reverse();
      return { status: "ok", pushes, count: node.g, expansions };
    }
    const boxes = bitsOf(node.mask, n);
    for (const b of boxes) {
      const bx = room.cellX[b];
      const by = room.cellY[b];
      for (let di = 0; di < 4; di++) {
        const d = DIRS[di];
        const dest = room.localAt(bx + d.dx, by + d.dy);
        if (dest < 0 || dest >= n) continue; // not a room cell
        if ((node.mask >> BigInt(dest)) & 1n) continue; // occupied
        const behind = room.localAt(bx - d.dx, by - d.dy);
        if (behind < 0) continue;
        if (!region[behind]) continue; // player cannot get behind the box
        const newMask = (node.mask & ~(1n << BigInt(b))) | (1n << BigInt(dest));
        if (isDead(room, newMask)) continue;
        const h = heuristic(room, newMask);
        if (h === Infinity) continue;
        const newRegion = reachableRegion(room, newMask, b);
        const newCanon = minSetBit(newRegion);
        const nk = keyOf(newMask, newCanon);
        const ng = node.g + 1;
        const prevG = gScore.has(nk) ? gScore.get(nk) : Infinity;
        if (greedy && gScore.has(nk)) continue; // greedy never reopens
        if (ng < prevG) {
          gScore.set(nk, ng);
          parent.set(nk, { prev: nodeKey, box: b, dir: di });
          const f = greedy ? h : ng + h;
          open.push({ f, h, g: ng, seq: seq++, mask: newMask, canon: newCanon });
        }
      }
    }
  }
  return { status: "unsolvable", expansions };
}

function solveRoom(room, requireExit) {
  const res = searchRoom(room, requireExit, false, ASTAR_MAX_EXPANSIONS);
  if (res.status === "ok") return res;
  if (res.status === "cap") {
    const g = searchRoom(room, requireExit, true, GREEDY_MAX_EXPANSIONS);
    if (g.status === "ok") return g;
    return { status: "cap", expansions: res.expansions + g.expansions };
  }
  return res;
}

// ------------------------------------------------------------ move stitching

// BFS walk over the whole level floor, avoiding the given box cells.
// Returns the list of direction indices from `from` to `to`, or null.
function walkPath(level, boxSet, from, to) {
  if (from === to) return [];
  const { w, id, floor } = level;
  const prev = new Map();
  prev.set(from, -1);
  const q = [from];
  for (let qi = 0; qi < q.length; qi++) {
    const c = q[qi];
    const x = c % w;
    const y = Math.floor(c / w);
    for (let di = 0; di < 4; di++) {
      const d = DIRS[di];
      const nc = id(x + d.dx, y + d.dy);
      if (!floor.has(nc) || boxSet.has(nc) || prev.has(nc)) continue;
      prev.set(nc, { from: c, dir: di });
      if (nc === to) {
        const path = [];
        let cur = nc;
        while (prev.get(cur) !== -1) {
          const step = prev.get(cur);
          path.push(step.dir);
          cur = step.from;
        }
        path.reverse();
        return path;
      }
      q.push(nc);
    }
  }
  return null;
}

// BFS walk inside one room's walk area (room cells + entry cell),
// avoiding the room's current boxes (local indices). Returns the list
// of direction indices from `fromLocal` to `toLocal`, or null.
function roomWalkPath(room, boxMask, fromLocal, toLocal) {
  if (fromLocal === toLocal) return [];
  const prev = new Map();
  prev.set(fromLocal, -1);
  const q = [fromLocal];
  for (let qi = 0; qi < q.length; qi++) {
    const u = q[qi];
    for (const e of room.walkNb[u]) {
      if (prev.has(e.to)) continue;
      if (e.to < room.n && ((boxMask >> BigInt(e.to)) & 1n)) continue;
      prev.set(e.to, { from: u, dir: e.dir });
      if (e.to === toLocal) {
        const path = [];
        let cur = toLocal;
        while (prev.get(cur) !== -1) {
          const step = prev.get(cur);
          path.push(step.dir);
          cur = step.from;
        }
        path.reverse();
        return path;
      }
      q.push(e.to);
    }
  }
  return null;
}

// Solve one level, returning the LURD move string ("" when unsolvable).
function solveLevel(level) {
  const { rooms } = detectRooms(level);
  if (rooms.length === 0) return "";
  const models = rooms.map((r) => {
    const door = r.doors[0];
    return buildRoom(level, r.cells, door);
  });
  // Per room: free optimum and exit-compatible optimum.
  const results = models.map((room) => {
    const exit = solveRoom(room, true);
    let free = null;
    if (exit.status === "ok") {
      // The start heuristic is a lower bound on the free optimum; when
      // the exit solution meets it, it is free-optimal too.
      const h0 = heuristic(room, room.startMask);
      if (exit.count === h0) {
        free = exit;
      } else {
        free = solveRoom(room, false);
        if (free.status !== "ok") free = exit; // keep the working one
      }
    } else {
      free = solveRoom(room, false);
    }
    return { room, free, exit };
  });
  // Any room without a working solution makes the level unsolvable.
  for (const r of results) {
    if (!r.free || r.free.status !== "ok") return "";
  }
  // The last room is the one where requiring an exit costs the most.
  let lastIdx = 0;
  let bestSaving = -Infinity;
  results.forEach((r, i) => {
    const freeLen = r.free.count;
    const exitLen = r.exit && r.exit.status === "ok" ? r.exit.count : Infinity;
    const saving = exitLen - freeLen;
    if (saving > bestSaving) {
      bestSaving = saving;
      lastIdx = i;
    }
  });

  const moves = [];
  let playerGlobal = level.player;
  const boxSet = new Set(level.boxes);
  const order = results.map((_, i) => i).filter((i) => i !== lastIdx);
  order.push(lastIdx);
  for (const idx of order) {
    const { room, free, exit } = results[idx];
    const useExit = idx !== lastIdx && exit && exit.status === "ok";
    const sol = useExit ? exit : free;
    // Walk through the hallway to this room's entry cell.
    const walk = walkPath(level, boxSet, playerGlobal, room.entry);
    if (walk === null) return "";
    for (const di of walk) moves.push(DIRS[di].ch);
    playerGlobal = room.entry;
    // Replay the room's pushes.
    let mask = room.startMask;
    let playerLocal = room.ENTRY;
    for (const push of sol.pushes) {
      const b = push.box;
      const d = DIRS[push.dir];
      const behind = room.localAt(room.cellX[b] - d.dx, room.cellY[b] - d.dy);
      const toWalk = roomWalkPath(room, mask, playerLocal, behind);
      if (toWalk === null) return "";
      for (const di of toWalk) moves.push(DIRS[di].ch);
      moves.push(d.ch);
      // Update the global box set and the local state.
      const oldGlobal = room.cells[b];
      const destLocal = room.localAt(room.cellX[b] + d.dx, room.cellY[b] + d.dy);
      const destGlobal = room.cells[destLocal];
      boxSet.delete(oldGlobal);
      boxSet.add(destGlobal);
      mask = (mask & ~(1n << BigInt(b))) | (1n << BigInt(destLocal));
      playerLocal = b;
      playerGlobal = oldGlobal;
    }
    // Walk back out through the door, unless this is the last room.
    if (idx !== lastIdx) {
      const out = roomWalkPath(room, mask, playerLocal, room.ENTRY);
      if (out === null) return "";
      for (const di of out) moves.push(DIRS[di].ch);
      playerGlobal = room.entry;
    }
  }
  return moves.join("");
}

// ------------------------------------------------------------------- main

function main() {
  for (const id of IDS) {
    const text = fs.readFileSync(path.join(INPUT_DIR, id, "level.txt"), "utf8");
    const level = parseLevel(text);
    const moves = solveLevel(level);
    const outDir = path.join(OUTPUT_DIR, id);
    fs.mkdirSync(outDir, { recursive: true });
    fs.writeFileSync(path.join(outDir, "solution.txt"), moves, "utf8");
    process.stdout.write(id + ": " + moves.length + " moves\n");
  }
}

main();
