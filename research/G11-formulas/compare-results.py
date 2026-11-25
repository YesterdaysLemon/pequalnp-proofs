"""Validate that proof replay agrees with the published classifications."""
import json
from pathlib import Path
import sys


def compare(mode, results, quick=False):
    here = Path(__file__).resolve().parent
    if mode == "or":
        expected_keys = {str(mask) for mask in range(1, 2048) if mask.bit_count() >= 2}
        def expected(key):
            return "certified" if published[key]["status"] == "UNSAT" else published[key]["status"]
        published = json.loads((here / "or-discovery.json").read_bytes())
    else:
        published = json.loads((here / "mixed-discovery.json").read_bytes())
        expected_keys = set(published)
        def expected(key):
            return "certified" if published[key]["status"] == "UNSAT" else published[key]["status"]
    if set(published) != expected_keys or (not quick and set(results) != expected_keys):
        raise RuntimeError("Expected and recorded cases differ")
    for key, record in results.items():
        if key not in expected_keys or record.get("reason", "certified") != expected(key):
            raise RuntimeError("Status mismatch for " + key)
        if "reason" not in record and (record.get("actions", 0) <= 0 or len(record.get("cnf_sha256", "")) != 64):
            raise RuntimeError("Incomplete certificate record for " + key)
    if not results:
        raise RuntimeError("Empty replay")
    print("Compared", len(results), "cases against the published classifications.")


if __name__ == "__main__":
    compare(sys.argv[1], json.loads(Path(sys.argv[2]).read_bytes()), sys.argv[3:] == ["--quick"])
