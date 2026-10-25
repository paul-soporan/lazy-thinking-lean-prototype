#!/usr/bin/env python3
"""Build, execute, audit, and check expected failures (Python standard library)."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shlex
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
NEGATIVE_CASES = [
    ("UnknownHelpers", "SplitContract left right"),
    ("BadCombine", "GuardOnSplit leftHalf rightHalf Separated"),
    ("FixedBaseline", "CombineContract concatenate"),
    ("PlainOnly", "CombineContract concatenate"),
    ("NoTransport", "GuardTransport Separated"),
    ("MissingSplitGuard", "GuardOnSplit minimumLeft minimumRight Separated"),
    ("NoProgress", "SplitContract rawMinimumLeft rawMinimumRight"),
    ("UntrustedFact", "CombineContract concatenate"),
]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def events(output: str, channel: str) -> list[dict]:
    prefix = f"[{channel}] "
    return [json.loads(line[len(prefix):]) for line in output.splitlines()
            if line.startswith(prefix)]


def audit(output: str, expected: int) -> list[dict]:
    rows = []
    pattern = r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))"
    for match in re.finditer(pattern, output):
        names = [name.strip() for name in (match.group(2) or "").split(",") if name.strip()]
        require(set(names) <= ALLOWED_AXIOMS,
                f"Unapproved proof dependency in {match.group(1)}: {names}")
        rows.append({"theorem": match.group(1), "axioms": names})
    require(len(rows) == expected, f"Expected {expected} audit entries, found {len(rows)}")
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", action="store_true", help="Write logs and JSON into docs/results")
    parser.add_argument("--lake-command", default="lake", help="Command prefix, split without a shell")
    args = parser.parse_args()
    lake = shlex.split(args.lake_command)
    require(bool(lake), "The Lake command cannot be empty")
    destination = ROOT / "docs" / "results"
    if args.report:
        destination.mkdir(parents=True, exist_ok=True)

    def run(label: str, arguments: list[str], *, failure: bool = False) -> str:
        result = subprocess.run(lake + arguments, cwd=ROOT, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=240)
        if args.report:
            (destination / f"{label}.log").write_text(result.stdout, encoding="utf-8")
        if failure:
            require(result.returncode != 0 and "unsolved goals" in result.stdout,
                    f"{label}: expected unresolved proof obligations\n{result.stdout}")
        else:
            require(result.returncode == 0, f"{label} failed:\n{result.stdout}")
        print(f"PASS: {label}", flush=True)
        return result.stdout

    version = run("version", ["env", "lean", "--version"]).strip()
    require("version 4.24.0" in version, f"Wrong pinned toolchain: {version}")
    run("build", ["build", "LazyThinking", "lazy-thinking-demo", "lazy-thinking-tests"])
    output = run("execution", ["exe", "lazy-thinking-tests"])
    require("2742 specification checks" in output, "Executable did not finish the complete corpus")
    run("demo", ["exe", "lazy-thinking-demo"])

    baseline = run("baseline", ["env", "lean", "Examples.lean"])
    baseline_events = events(baseline, "LazyThinking")
    require(bool(baseline_events) and baseline_events[-1]["stage"] == "complete",
            "Fixed-rule baseline failed to complete")
    audit(baseline, 2)

    expanded = run("experiments", ["env", "lean", "Experiments.lean"])
    search_events = events(expanded, "LazyThinking.Search")
    groups, current = [], []
    for event in search_events:
        current.append(event)
        if event["stage"] == "complete":
            groups.append(current)
            current = []
    require(not current and len(groups) == 3, "Expected three completed search experiments")
    selected = [group[-1]["candidate"] for group in groups]
    require(selected == ["unconditional", "separated", "unconditional"],
            f"Unexpected candidate selection: {selected}")
    require(any(event["stage"] == "candidate_unresolved" and
                event["candidate"] == "unconditional" for event in groups[1]),
            "Guarded success must follow an unresolved unconditional candidate")
    audit(expanded, 4)

    proof_audit = audit(run("axioms", ["env", "lean", "Audit.lean"]), 23)
    failures = []
    for name, required_goal in NEGATIVE_CASES:
        output = run(name, ["env", "lean", f"tests/{name}.lean"], failure=True)
        channel = "LazyThinking" if name == "FixedBaseline" else "LazyThinking.Search"
        trace = events(output, channel)
        require(bool(trace) and trace[-1]["stage"] == "unresolved",
                f"{name}: missing final unresolved event")
        unresolved = [event for event in trace if event["stage"] in
                      {"unresolved", "candidate_unresolved"}]
        require(any(required_goal in goal for event in unresolved for goal in event["goals"]),
                f"{name}: missing expected premise {required_goal}")
        failures.append({"name": name, "expected_unproved_premise": required_goal, "events": trace})

    hashes = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
              for path in sorted(ROOT.rglob("*.lean")) if ".lake" not in path.parts}
    report = {
        "lean_version": version,
        "project_version": "0.2.0",
        "runtime_inputs_per_program": 1371,
        "runtime_specification_checks": 2742,
        "selected_candidates": selected,
        "positive_search_events": groups,
        "fixed_rule_events": baseline_events,
        "expected_failure_cases": failures,
        "audited_theorems": proof_audit,
        "allowed_foundational_axioms": sorted(ALLOWED_AXIOMS),
        "source_sha256": hashes,
    }
    if args.report:
        (destination / "summary.json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n",
                                                  encoding="utf-8")
    print("PASS: 3 candidate-selection runs, 8 expected failures, 23 audited theorem dependencies.")
    print("PASS: all checks completed; expected failures remain unproved, not admitted.")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, subprocess.TimeoutExpired) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
