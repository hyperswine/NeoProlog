#!/usr/bin/env python3
"""Check the complete examples against independent, finite Python models.

python3 test/example_programs.py /path/to/infera --all-modes

CLI startup is included in the reported elapsed time; this is an acceptance
runner, not a VM benchmark. Loaded-query measurements live in core-major.
No third-party Python packages are required.
"""
import argparse
import ast
from collections import deque
import heapq
import itertools
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ("sudoku4", "river_crossing", "job_shop", "route_planning", "supply_packing")


def require(condition, message):
    if not condition:
        raise AssertionError(message)


class Runner:
    def __init__(self, binary, directory, env):
        self.binary, self.directory, self.env = binary, directory, env
        self.queries = 0

    def run(self, path, *args):
        result = subprocess.run(
            [str(self.binary), str(path), *args, "+RTS", "-N1", "-RTS"],
            input=":quit\n", capture_output=True, text=True, timeout=30,
            cwd=self.directory, env=self.env)
        require(result.returncode == 0, result.stdout + result.stderr)
        require(not re.search(r"Error:|search depth limit", result.stdout + result.stderr, re.I),
                result.stdout + result.stderr)
        return result.stdout

    def query(self, name, goal):
        source = (ROOT / "examples" / (name + ".nprolog")).read_text()
        # These examples deliberately put all demonstrations after all clauses.
        # Splitting at the first entry removes multiline queries as one block.
        require("\n> " in source, "missing demo boundary: " + name)
        program = source.split("\n> ", 1)[0]
        path = self.directory / (name + ".nprolog")
        path.write_text(program + "\n> " + goal + "?\n")
        stdout = self.run(path)
        matches = re.findall(r"^Result = (.+)$", stdout, re.M)
        require(len(matches) == 1, "expected one collected ground result: " + stdout)
        # The test protocol only admits lists, integers and lowercase atoms.
        # Quote atoms for literal_eval; reject residual constraints/other terms.
        value = matches[0]
        require(re.fullmatch(r"[\[\], 0-9a-z_\-]+", value) is not None,
                "unexpected result syntax: " + value)
        quoted = re.sub(r"\b[a-z][a-z_]*\b", lambda m: repr(m.group()), value)
        self.queries += 1
        return ast.literal_eval(quoted)


def frozen(value):
    return tuple(map(frozen, value)) if isinstance(value, list) else value


def same_set(actual, expected, label):
    values = [frozen(value) for value in actual]
    target = {frozen(value) for value in expected}
    require(len(values) == len(set(values)), label + ": duplicate answers")
    require(set(values) == target, label + ": incomplete or incorrect answer set")


def sudoku_oracle():
    # Assemble rows from permutations, pruning columns and completed boxes.
    rows = list(itertools.permutations(range(1, 5)))
    def extend(board):
        if len(board) == 4:
            yield tuple(board)
            return
        for row in rows:
            if any(row[c] in [r[c] for r in board] for c in range(4)):
                continue
            if len(board) % 2 and any(
                    len(set(board[-1][c:c+2] + row[c:c+2])) != 4 for c in (0, 2)):
                continue
            yield from extend(board + [row])
    return list(extend([]))


def check_sudoku(runner):
    grids = sudoku_oracle()
    require(len(grids) == 288, "independent Sudoku enumeration failed")
    same_set(runner.query("sudoku4", "findall Grid (sudoku Grid) Result"), grids, "Sudoku")
    clues = [[1,0,0,4], [0,4,1,0], [2,0,4,0], [0,3,0,1]]
    expected = [g for g in grids if all(not clues[r][c] or clues[r][c] == g[r][c]
                                      for r in range(4) for c in range(4))]
    require(len(expected) == 1, "gentle Sudoku should have a unique solution")
    same_set(runner.query("sudoku4", "findall Grid (puzzle gentle Grid, sudoku Grid) Result"),
             expected, "Sudoku clues")
    require(runner.query("sudoku4", "findall Grid (puzzle impossible Grid, sudoku Grid) Result") == [],
            "contradictory Sudoku unexpectedly solved")


def river_oracle():
    start, goal = (0, 0, 0, 0), (1, 1, 1, 1)
    queue, found = deque([(start, (), frozenset([start]))]), []
    while queue:
        state, moves, seen = queue.popleft()
        if found and len(moves) > len(found[0]):
            break
        if state == goal:
            found.append(moves)
            continue
        for passenger, name in enumerate(("alone", "wolf", "goat", "cabbage")):
            if passenger and state[passenger] != state[0]:
                continue
            next_state = list(state)
            next_state[0] ^= 1
            if passenger:
                next_state[passenger] ^= 1
            f, w, g, c = next_state
            nxt = tuple(next_state)
            if (w == g != f) or (g == c != f) or nxt in seen:
                continue
            queue.append((nxt, moves + (name,), seen | {nxt}))
    return found


def check_river(runner):
    plans = river_oracle()
    require(len(plans) == 2 and all(len(p) == 7 for p in plans), "independent BFS failed")
    same_set(runner.query("river_crossing", "findall Moves (crossing 7 Moves) Result"), plans, "river")
    require(runner.query("river_crossing", "findall Moves (crossing 6 Moves) Result") == [],
            "river solved in fewer crossings than BFS")
    chosen = runner.query("river_crossing", "findall Moves (shortest Moves) Result")
    require(len(chosen) == 1 and tuple(chosen[0]) in plans, "shortest river plan is invalid")


DURATIONS = (3, 2, 2, 1, 2, 1)  # A, B, C, D, E, F
PRECEDENCE = ((0, 2), (1, 3), (4, 5))
MACHINES = ((0, 3, 4), (2, 1, 5))
JOB_PLAN = ("[op frame_cut cutter A 3,op frame_drill drill C 2,"
            "op bracket_drill drill B 2,op bracket_cut cutter D 1,"
            "op panel_cut cutter E 2,op panel_drill drill F 1]")


def job_optimum():
    # Enumerate machine orders, then longest paths through each precedence DAG.
    # This does not enumerate time assignments or reuse the CLP formulation.
    best = None
    for orders in itertools.product(*(itertools.permutations(m) for m in MACHINES)):
        edges = list(PRECEDENCE) + [pair for order in orders for pair in zip(order, order[1:])]
        starts, remaining = [0] * 6, set(range(6))
        while remaining:
            ready = [v for v in remaining if all(a not in remaining for a, b in edges if b == v)]
            if not ready:
                break  # Cyclic machine order is infeasible.
            for v in ready:
                starts[v] = max([starts[a] + DURATIONS[a] for a, b in edges if b == v] or [0])
                remaining.remove(v)
        if not remaining:
            finish = max(s + d for s, d in zip(starts, DURATIONS))
            best = finish if best is None else min(best, finish)
    require(best is not None, "independent job-shop model has no solution")
    return best


def check_jobs(runner):
    optimum = job_optimum()
    require(optimum == 6, "unexpected independent workshop optimum")
    for horizon in (5, 6, 9):
        answers = runner.query("job_shop", "findall [Finish,A,B,C,D,E,F] (job_shop "
                               + str(horizon) + " " + JOB_PLAN + " Finish) Result")
        if horizon < optimum:
            require(answers == [], "impossible workshop deadline accepted")
            continue
        require(len(answers) == 1, "optimizer must return one workshop plan")
        finish, *starts = answers[0]
        require(len(starts) == 6 and all(type(x) is int and x >= 0 for x in starts), "invalid start times")
        require(finish == optimum == max(s + d for s, d in zip(starts, DURATIONS)), "wrong makespan")
        require(all(starts[a] + DURATIONS[a] <= starts[b] for a, b in PRECEDENCE), "precedence violation")
        require(all(starts[a] + DURATIONS[a] <= starts[b] or starts[b] + DURATIONS[b] <= starts[a]
                    for machine in MACHINES for a, b in itertools.combinations(machine, 2)), "machine overlap")


ROADS = (("depot", "market", 4), ("depot", "station", 2), ("station", "market", 1),
         ("market", "park", 3), ("station", "park", 7), ("park", "clinic", 2),
         ("market", "clinic", 9), ("station", "depot", 2), ("park", "station", 1),
         ("clinic", "depot", 8))


def routes(closed):
    def walk(path, cost):
        if path[-1] == "clinic":
            yield [cost, path]
        else:
            for a, b, weight in ROADS:
                if a == path[-1] and b not in path and (a, b) not in closed:
                    yield from walk(path + [b], cost + weight)
    return list(walk(["depot"], 0))


def shortest_distance(closed):
    queue, visited = [(0, "depot")], set()
    while queue:
        distance, node = heapq.heappop(queue)
        if node == "clinic":
            return distance
        if node in visited:
            continue
        visited.add(node)
        for a, b, cost in ROADS:
            if a == node and (a, b) not in closed:
                heapq.heappush(queue, (distance + cost, b))
    return None


def check_routes(runner):
    for closed in (set(), {("station", "market")}, {("park", "clinic"), ("market", "clinic")}):
        term = "[" + ",".join("closed " + a + " " + b for a, b in sorted(closed)) + "]"
        expected = routes(closed)
        same_set(runner.query("route_planning", "findall [Cost,Path] (route depot clinic "
                              + term + " Path Cost) Result"), expected, "all routes")
        best = runner.query("route_planning", "findall [Cost,Path] (best_route depot clinic "
                            + term + " Path Cost) Result")
        distance = shortest_distance(closed)
        require(best == [] if distance is None else
                len(best) == 1 and best[0] in expected and best[0][0] == distance, "wrong shortest route")
    nodes = runner.query("route_planning", "findall Node (reachable depot Node) Result")
    same_set(nodes, ["depot", "market", "station", "park", "clinic"], "tabled closure")
    require(runner.query("route_planning", "findall Path (best_route depot island [] Path _) Result") == [],
            "unreachable island unexpectedly reached")


ITEMS = ((3, 2, 8, 2), (2, 3, 5, 3), (4, 5, 10, 1), (2, 1, 4, 2))
PACK = "[take water A,take food B,take radio C,take blanket D]"


def check_packing(runner):
    possibilities = []
    for quantities in itertools.product(*(range(stock + 1) for _, _, _, stock in ITEMS)):
        totals = [sum(q * item[k] for q, item in zip(quantities, ITEMS)) for k in range(3)]
        possibilities.append(totals + list(quantities))
    for capacity, budget in ((0, 0), (3, 8), (10, 8), (10, 100), (100, 100), (8, 4)):
        feasible = [p for p in possibilities if p[0] <= capacity and p[1] <= budget]
        optimum = max(p[2] for p in feasible)
        answers = runner.query("supply_packing", "findall [Weight,Price,Value,A,B,C,D] (best_pack "
                               + f"{capacity} {budget} " + PACK + " Weight Price Value) Result")
        require(len(answers) == 1 and answers[0] in feasible and answers[0][2] == optimum,
                f"invalid or suboptimal packing for {capacity}, {budget}")
    require(runner.query("supply_packing", "findall Vars (packing_model 3 8 "
                         "[take water _,take food _,take radio 1,take blanket _] Vars _ _ _, label Vars) Result") == [],
            "overweight required radio accepted")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    parser.add_argument("--all-modes", action="store_true")
    args = parser.parse_args()
    binary = args.binary.resolve()
    diagnostics = subprocess.run([str(binary), "check", "--json",
                                  *(str(ROOT / "examples" / (name + ".nprolog")) for name in EXAMPLES),
                                  "+RTS", "-N1", "-RTS"], capture_output=True, text=True, timeout=30, cwd=ROOT)
    require(diagnostics.returncode == 0, diagnostics.stdout + diagnostics.stderr)
    require(all(d["severity"] == "information" for d in json.loads(diagnostics.stdout)),
            "examples must have no diagnostic warnings or errors: " + diagnostics.stdout)
    modes = [("1", "1"), ("0", "1"), ("1", "0"), ("0", "0")] if args.all_modes else [("1", "1")]
    for jit, stream in modes:
        start = time.monotonic()
        with tempfile.TemporaryDirectory(prefix="infera-examples-") as directory:
            runner = Runner(binary, Path(directory), {**os.environ, "INFERA_JIT": jit, "INFERA_CORE_STREAM": stream})
            for name in EXAMPLES:
                output = runner.run(ROOT / "examples" / (name + ".nprolog"))
                require("\nfalse." not in output, "demonstration failed: " + name)
            for check in (check_sudoku, check_river, check_jobs, check_routes, check_packing):
                check(runner)
            print(json.dumps({"status": "ok", "jit": jit, "stream": stream,
                              "independent_queries": runner.queries, "demo_programs": len(EXAMPLES),
                              "elapsed_seconds": round(time.monotonic() - start, 3)}), flush=True)


if __name__ == "__main__":
    main()
