#!/usr/bin/env python3
"""validate_seismic_reaching.py

Run the seismic validation end-to-end:

1) Fetch a real `validation_bundle.json` via `scripts/seismic_bridge.py`.
2) Build the Lean executable `seismic_validate_demo`.
3) Run the executable on the bundle and write the JSON output.

This is a convenience wrapper around the manual workflow described in
`WIP/meristor_alternative_source.md`.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys


def run_checked(cmd: list[str], *, cwd: str | None = None) -> None:
    p = subprocess.run(cmd, cwd=cwd)
    if p.returncode != 0:
        raise RuntimeError(f"command failed ({p.returncode}): {' '.join(cmd)}")


def run_capture(cmd: list[str], *, cwd: str | None = None) -> str:
    p = subprocess.run(cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if p.returncode != 0:
        raise RuntimeError(
            json.dumps(
                {
                    "cmd": cmd,
                    "returncode": p.returncode,
                    "stdout": p.stdout,
                    "stderr": p.stderr,
                },
                indent=2,
            )
        )
    return p.stdout


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--stations",
        default="IU.ANMO,IU.HRV,IU.COLA,II.BFO,IU.CTAO,IU.SNZO",
        help="Comma-separated station list",
    )
    ap.add_argument("--min-magnitude", type=float, default=6.0)
    ap.add_argument("--days-back", type=int, default=30)
    ap.add_argument("--max-events", type=int, default=3)
    ap.add_argument("--bundle", default="data/seismic/validation_bundle.json")
    ap.add_argument("--out", default="results/seismic_validation/lean_output.json")
    args = ap.parse_args()

    os.makedirs(os.path.dirname(args.bundle), exist_ok=True)
    os.makedirs(os.path.dirname(args.out), exist_ok=True)

    run_checked(
        [
            sys.executable,
            "scripts/seismic_bridge.py",
            "--stations",
            args.stations,
            "--min-magnitude",
            str(args.min_magnitude),
            "--days-back",
            str(args.days_back),
            "--max-events",
            str(args.max_events),
            "--output",
            args.bundle,
        ]
    )

    run_checked(["bash", "-lc", "cd lean && lake build --wfail seismic_validate_demo"])
    out = run_capture(["bash", "-lc", f"cd lean && lake exe seismic_validate_demo -- ../{args.bundle}"])
    with open(args.out, "w", encoding="utf-8") as f:
        f.write(out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

