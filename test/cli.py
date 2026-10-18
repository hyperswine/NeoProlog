"""Exercise the real compiler CLI contract, including imported locations."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile

binary = str(Path(sys.argv[1]).resolve())

with tempfile.TemporaryDirectory(prefix="infera-cli-") as tmp:
    root = Path(tmp).resolve()

    def check(source, expected_code=None, success=False):
        target = root / "main.nprolog"
        target.write_text(source)
        result = subprocess.run([binary, "check", "--json", str(target)], cwd=root,
                                capture_output=True, text=True, timeout=20)
        rows = json.loads(result.stdout)
        assert (result.returncode == 0) == success, (result, rows)
        if expected_code:
            assert any(d["code"] == expected_code for d in rows), rows
        for d in rows:
            assert d["severity"] in ("error", "warning", "information")
            assert d["range"]["start"]["line"] >= 0
            assert d["range"]["start"]["character"] >= 0
        return rows

    assert check("p 1.\n> p 1?\n", success=True) == []
    rows = check("p 1.\n\nbad <- missing 1.\n", "undefined-predicate")
    assert rows[0]["range"]["start"] == {"line": 2, "character": 0}, rows
    assert rows[0]["range"]["end"] == {"line": 2, "character": 17}, rows
    prefix = 'p "😀".\t'
    rows = check(prefix + "bad <- missing.\n", "undefined-predicate")
    assert rows[0]["range"]["start"]["character"] == len(prefix.encode("utf-16-le")) // 2, rows
    check("p 1.\nbad <- p.\n", "wrong-arity")
    check("p : det (int: <=).\n", "declaration-without-clauses")
    check('p : det (int: <=).\np 1.\n> p "bad"?\n', "call-sort-mismatch")
    check("p X.\n", "singleton-variable", success=True)
    check("p : det (int: <=).\np 2.\n> p (1 + 1)?\n", success=True)
    check("p X <- call X.\n", success=True)
    rows = check("walk X <- walk X, true.\n", "perf-non-tail-recursion", success=True)
    suggestion = next(d for d in rows if d["code"] == "perf-non-tail-recursion")
    assert suggestion["severity"] == "information", rows
    assert suggestion["range"] == {"start": {"line": 0, "character": 10},
                                   "end": {"line": 0, "character": 14}}, rows
    target = root / "main.nprolog"
    text_check = subprocess.run([binary, "check", str(target)], cwd=root,
                                capture_output=True, text=True, timeout=20)
    assert text_check.returncode == 0 and "information [perf-non-tail-recursion]" in text_check.stderr
    assert ": ok" in text_check.stdout, text_check
    check("fresh <- label [X].\n", "perf-unbounded-labeling", success=True)
    for goal in ["once missing", "not missing", "findall X (missing X) _",
                 "forall true missing", "call missing", "phrase missing []", "minimize C (missing C)"]:
        check(f"bad <- {goal}.\n", "undefined-predicate")
    rows = check("p 1.\n> p [1, ?\n", "load-error")
    assert rows[0]["range"]["start"]["line"] == 1, rows
    imported = root / "lib.nprolog"
    imported.write_text("greet <- missing.\n")
    (root / "neoprolog.conf").write_text(f"lib#test {imported}\n")
    rows = check('<- import "lib#test".\n> lib:greet?\n', "undefined-predicate")
    assert rows[0]["file"] == str(imported), rows
    imported.write_text("greet.\n")
    check('<- import "lib#test".\n> lib:greet?\n', success=True)
    imported.write_text("walk X <- walk X, true.\n")
    rows = check('<- import "lib#test".\n> lib:walk 1?\n', "perf-non-tail-recursion", success=True)
    suggestion = next(d for d in rows if d["code"] == "perf-non-tail-recursion")
    assert suggestion["file"] == str(imported), rows
    assert suggestion["range"]["start"] == {"line": 0, "character": 10}, rows
    imported.write_text("greet <- .\n")
    rows = check('<- import "lib#test".\n', "load-error")
    assert rows[0]["file"] == str(imported), rows

    result = subprocess.run([binary, "check", "--json"], capture_output=True, text=True)
    assert result.returncode != 0 and "Usage:" in result.stderr, result
    print("CLI diagnostics acceptance passed")

    # Live checking uses the same compiler path and never writes source files.
    target = root / "unsaved.nprolog"
    target.write_text("disk_only.\n")
    source = 'p "😀".\tbad <- missing.\n'
    target_on_disk = target.read_text()
    stdin_result = subprocess.run([binary, "check", "--json", "--stdin", str(target)],
                                  input=source, cwd=root, capture_output=True, text=True)
    assert stdin_result.returncode == 1, stdin_result
    target.write_text(source)
    disk_result = subprocess.run([binary, "check", "--json", str(target)], cwd=root,
                                 capture_output=True, text=True)
    assert json.loads(stdin_result.stdout) == json.loads(disk_result.stdout)
    target.write_text(target_on_disk)
    before = target.read_text()
    result = subprocess.run([binary, "check", "--json", "--stdin", str(target)], input="live.\n",
                            cwd=root, capture_output=True, text=True)
    assert result.returncode == 0 and json.loads(result.stdout) == [], result
    assert target.read_text() == before
    new_file = root / "not-yet-saved.nprolog"
    result = subprocess.run([binary, "check", "--json", "--stdin", str(new_file)], input="new.\n",
                            cwd=root, capture_output=True, text=True)
    assert result.returncode == 0 and not new_file.exists(), result
    imported.write_text("greet.\n")
    snapshot = root / "snapshot with spaces"
    snapshot.write_text("greet <- missing.\n")
    result = subprocess.run([binary, "check", "--json", "--stdin", str(target),
                             "--buffer", str(imported), str(snapshot)],
                            input='<- import "lib#test".\nmain <- lib:greet.\n', cwd=root,
                            capture_output=True, text=True)
    rows = json.loads(result.stdout)
    assert result.returncode == 1 and rows[0]["file"] == str(imported), (result, rows)
    assert rows[0]["code"] == "undefined-predicate" and imported.read_text() == "greet.\n", rows
    for args in [["--stdin"], ["--stdin", str(target), "--buffer", str(imported)]]:
        result = subprocess.run([binary, "check", "--json", *args], input="new.\n",
                                capture_output=True, text=True)
        assert result.returncode == 1 and "Usage:" in result.stderr, result
    print("Live-buffer diagnostics acceptance passed")

    # The tracing consumer uses the same answer stream. Events are opt-in and
    # CLI tracing leaves ordinary answer/output text on stdout.
    traced_file = root / "trace.infera"
    traced_source = "<- notable.\nroot X <- choose X.\nchoose a.\nchoose b.\n"
    traced_file.write_text(traced_source + "> root X?\n")
    for arguments in [["--trace", str(traced_file), "root X?"],
                      ["--trace", str(traced_file)]]:
        result = subprocess.run([binary, *arguments], cwd=root, capture_output=True,
                                text=True, timeout=20)
        assert result.returncode == 0, result
        assert result.stdout.splitlines() == ["X = a", "X = b"], result
        for port in ["Call", "Exit", "Redo"]:
            assert port in result.stderr, result
        assert str(traced_file) in result.stderr and "root/1" in result.stderr, result
        assert "Call" not in result.stdout, result

    result = subprocess.run([binary], cwd=root,
                            input=f":load {traced_file}\n:trace root X?\n:quit\n",
                            capture_output=True, text=True, timeout=20)
    assert result.returncode == 0 and "Call root" in result.stdout, result
    assert "Exit root" in result.stdout and "X = a" in result.stdout and "X = b" in result.stdout, result
    result = subprocess.run([binary], cwd=root,
                            input="p a.\np b.\n:trace p X?\n:quit\n",
                            capture_output=True, text=True, timeout=20)
    assert result.returncode == 0 and "<repl>:" in result.stdout, result
    assert "X = a" in result.stdout and "X = b" in result.stdout, result

    traced_file.write_text("<- notable.\nouter <- inner.\ninner <-\n  X is 1 / 0.\n")
    result = subprocess.run([binary, "--trace", str(traced_file), "outer?"], cwd=root,
                            capture_output=True, text=True, timeout=20)
    assert result.returncode == 1 and "Exception" in result.stderr, result
    assert "division by zero" in result.stderr and f"{traced_file}:4:" in result.stderr, result
    assert "outer/0" in result.stderr and "inner/0" in result.stderr, result
    assert result.stdout == "", result
    imported.write_text("greet <-\n  X is 1 / 0.\n")
    traced_file.write_text('<- import "lib#test".\n> lib:greet?\n')
    result = subprocess.run([binary, "--trace", str(traced_file)], cwd=root,
                            capture_output=True, text=True, timeout=20)
    assert result.returncode == 1 and f"{imported}:2:" in result.stderr, result
    imported.write_text("greet : table.\ngreet <- helper.\nhelper <-\n  X is 1 / 0.\n")
    result = subprocess.run([binary, "--trace", str(traced_file)], cwd=root,
                            capture_output=True, text=True, timeout=20)
    assert result.returncode == 1 and f"{imported}:4:" in result.stderr, result
    assert "lib:helper/0" in result.stderr and "lib:greet/0" in result.stderr, result

    traced_file.write_text("p a.\n")
    result = subprocess.run([binary, "--trace", str(traced_file)], cwd=root,
                            capture_output=True, text=True, timeout=20)
    assert result.returncode == 1 and "No inline query" in result.stderr, result
    for arguments in [["--trace"], ["--trace", str(traced_file), "p X?", "extra"]]:
        result = subprocess.run([binary, *arguments], cwd=root, capture_output=True,
                                text=True, timeout=20)
        assert result.returncode == 1 and "Usage:" in result.stderr, result
    print("Trace CLI, REPL and located runtime-error acceptance passed")

    # DCG newline helpers and flags-only dynamic declarations are current syntax.
    assert not [d for d in check("grid_row _ -> [].\ngrid [] -> [].\ngrid [Row | Rows] -> grid_row Row, nl, grid Rows.\n", success=True)
                if d["severity"] == "error"]
    assert not [d for d in check("best_so_far : dynamic.\n", success=True) if d["severity"] == "error"]
    rows = check("say <- nl.\n", "unsafe-call")
    assert any("say : unsafe." in d["message"] for d in rows), rows

    examples = Path(__file__).resolve().parent.parent / "examples"
    (root / "neoprolog.conf").write_text(
        f"facts#f12568529f605753c20ea9210f40d00b8318ebc4 {examples / 'facts.nprolog'}\n")
    for example in sorted(examples.glob("*.nprolog")):
        result = subprocess.run([binary, "check", "--json", str(example)], cwd=root,
                                capture_output=True, text=True, timeout=20)
        errors = [d for d in json.loads(result.stdout) if d["severity"] == "error"]
        if example.name == "v2_decls.nprolog":
            # This example intentionally demonstrates two invalid sort calls.
            assert len(errors) == 2 and all(d["code"] == "call-sort-mismatch" for d in errors), errors
            assert result.returncode == 1
        else:
            assert result.returncode == 0 and not errors, (example, result, errors)
    print("Shipped-example diagnostics acceptance passed")

    # The classic example programs print the answers their comments describe.
    # Timetable checks avoid the exact slots, which depend on labeling order.
    classics = {
        "queens.nprolog": ["Qs = [2, 4, 6, 1, 3, 5]", "N = 92, F = 12",
                           "   9        352           46"],
        "blocks.nprolog": ["Moves = [move c a table, move b table c, move a table b]",
                           "trade: 5 moves", "N = 13\n", "N = 73\n", "N = 501\n"],
        "timetable.nprolog": ["N = 6, Rooms = [0]", "smith    6 lessons  [maths, physics]",
                              "> checked\ntrue."],
        "stable_matching.nprolog": [
            "leads propose, 18 offers: ada-nia ben-lea cal-ola dan-jo eli-ivy finn-mia gus-pam hal-kim",
            "follows propose, 15 offers: ada-jo ben-lea cal-ivy dan-pam eli-mia finn-nia gus-ola hal-kim",
            "], N = 7\n", "no elective: [eli]", "> fair_admission\ntrue.",
            "S = cara\nS = eli\nS = gus\n"],
        "database_access.nprolog": [
            "none: 148 reachable states", "careless: 365 reachable states",
            "readers_first: 397 reachable states", "turnstile: 787 reachable states",
            "an update is lost:", "deadlock:", "readers can keep writer 1 out forever:",
            "a waiting writer is never overtaken forever"],
    }
    for name, expected in classics.items():
        result = subprocess.run([binary, str(examples / name)], cwd=examples.parent, input="",
                                capture_output=True, text=True, timeout=120)
        output = result.stdout + result.stderr
        assert result.returncode == 0 and "Error" not in output and "raised an error" not in output, (name, result)
        missing = [text for text in expected if text not in result.stdout]
        assert not missing, (name, missing, result.stdout)
    print("Classic example answers acceptance passed")

    # A fresh checkout uses the tracked relative-path map, without a local registration.
    project = root / "portable-project"
    (project / "examples").mkdir(parents=True)
    (project / "infera.conf").write_text((examples.parent / "infera.conf").read_text())
    for name in ["facts.nprolog", "facts2.nprolog"]:
        (project / "examples" / name).write_text((examples / name).read_text())
    portable = project / "examples" / "facts2.nprolog"
    result = subprocess.run([binary, "check", "--json", str(portable)], cwd=project,
                            capture_output=True, text=True, timeout=20)
    assert result.returncode == 0 and not [d for d in json.loads(result.stdout)
                                          if d["severity"] == "error"], result
    result = subprocess.run([binary, str(portable)], cwd=project, input="",
                            capture_output=True, text=True, timeout=20)
    assert result.returncode == 0 and "R = 24" in result.stdout, result

    # Import IDs remain exact keys; a filename match does not rescue a stale ID.
    stale = project / "stale.nprolog"
    stale.write_text('<- import "facts#not-registered".\n')
    result = subprocess.run([binary, "check", "--json", str(stale)], cwd=project,
                            capture_output=True, text=True, timeout=20)
    assert result.returncode == 1 and any(d["code"] == "load-error" for d in json.loads(result.stdout)), result

    # Registration writes its own path-derived key, which can be imported directly.
    result = subprocess.run([binary, "reg", str(project / "examples" / "facts.nprolog")], cwd=project,
                            capture_output=True, text=True, timeout=20)
    assert result.returncode == 0, result
    key = (project / "neoprolog.conf").read_text().split()[0]
    assert key.startswith("facts#")
    fresh = project / "fresh.nprolog"
    fresh.write_text(f'<- import "{key}".\n> facts:factorial 5 Result?\n')
    result = subprocess.run([binary, str(fresh)], cwd=project, input="",
                            capture_output=True, text=True, timeout=20)
    assert result.returncode == 0 and "Result = 120" in result.stdout, result
    print("DCG newline, dynamic declaration and portable module acceptance passed")
