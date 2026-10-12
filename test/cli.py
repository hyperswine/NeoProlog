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
            assert d["severity"] in ("error", "warning")
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
