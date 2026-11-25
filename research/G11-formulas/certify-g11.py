"""Generate LRAT proofs for the G11 rectangle exclusions and check them in Lean."""

from argparse import ArgumentParser
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from tempfile import TemporaryDirectory
import hashlib
import json
import re
import subprocess
import sys

base = Path(__file__).resolve().parent
spec = spec_from_file_location("shared", base / "g11-shared-or.py")
shared = module_from_spec(spec)
sys.dont_write_bytecode = True
spec.loader.exec_module(shared)


def dimacs(clauses):
    highest = max(abs(literal) for clause in clauses for literal in clause)
    lines = [f"p cnf {highest} {len(clauses)}"]
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in clauses)
    return ("\n".join(lines) + "\n").encode()


def problems(signatures):
    if signatures is None:
        for mask in sorted(range(1, 2048), key=lambda s: (s.bit_count(), s)):
            if mask.bit_count() >= 2:
                yield str(mask), lambda mask=mask: shared.build(mask, linear_cells=True)
        return
    rows = [(1 << a) | (1 << b) for a, b in shared.kw.edges]
    columns, patterns = shared.kw.structure(shared.kw.edges)
    for key, cost in json.loads(signatures.read_bytes())["unresolved"].items():
        word = int(key, 16)
        yes = [i for i in range(len(rows)) if word >> i & 1]
        no = [j for j in range(len(columns)) if not word >> (len(rows) + j) & 1]
        yield key, lambda a=yes, b=no, t=cost: shared.build_for(
            rows, columns, patterns, a, b, 22 - t, linear_cells=True
        )


def verify(clauses, folder, solver, checker):
    problem = folder / "problem.cnf"
    proof = folder / "proof.lrat"
    data = dimacs(clauses)
    problem.write_bytes(data)
    proof.unlink(missing_ok=True)
    run = subprocess.run(
        [solver, "--quiet", "--lrat", "--no-binary", problem, proof],
        capture_output=True
    )
    if run.returncode != 20:
        raise RuntimeError((run.returncode, run.stdout[-350:], run.stderr[-350:]))
    checked = subprocess.run([checker, problem, proof], capture_output=True, text=True, check=True)
    match = re.fullmatch(r"Checked (\d+) LRAT actions\.\s*", checked.stdout)
    if not match:
        raise RuntimeError("Unexpected checker response: " + checked.stdout)
    return {"cnf_sha256": hashlib.sha256(data).hexdigest(), "actions": int(match[1])}


def checkpoint(path, records):
    tmp = path.with_suffix(".tmp")
    tmp.write_bytes(json.dumps(records, separators=(",", ":")).encode())
    tmp.replace(path)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("cadical", type=Path)
    parser.add_argument("checker", type=Path)
    parser.add_argument("out", type=Path)
    parser.add_argument("--mixed", type=Path, help="classify the listed mixed-gate signatures")
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--limit", type=int, default=0, help="stop after this many new SAT certificates")
    args = parser.parse_args()
    results = json.loads(args.out.read_bytes()) if args.resume else {}
    checked = 0
    with TemporaryDirectory() as directory:
        for key, build in problems(args.mixed):
            if key in results:
                continue
            clauses = build()
            if isinstance(clauses, str):
                results[key] = {"reason": clauses}
            else:
                results[key] = verify(clauses, Path(directory), args.cadical.resolve(), args.checker.resolve())
                checked += 1
            if len(results) % 10 == 0:
                checkpoint(args.out, results)
            if len(results) % 60 == 0:
                print(len(results), "cases", sum("actions" in r for r in results.values()), "LRAT certificates", flush=True)
            if args.limit and checked >= args.limit:
                break
    checkpoint(args.out, results)
    print(len(results), "cases checked", sum(r.get("actions", 0) for r in results.values()), "LRAT actions", flush=True)


if __name__ == "__main__":
    main()
