#!/usr/bin/env python3
"""Run expanded seismic validation across multiple parameter sets.

This script is intentionally self-contained and writes results under:

  results/seismic_validation/<config-name>/

Each config directory contains:
- bundle.json
- lean_output.json
- validation_report.json (from generate_validation_report.py)
- validation_summary.md

and the top-level comparison report:

  results/seismic_validation/expanded_comparison.md
"""

from __future__ import annotations

import json
import math
import subprocess
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
RESEARCHER_BUNDLE = ROOT / "RESEARCHER_BUNDLE"
LEAN_EXE = RESEARCHER_BUNDLE / ".lake" / "build" / "bin" / "seismic_validate_demo"


EXPANDED_STATIONS = [
    # Original 6
    "IU.ANMO",
    "IU.HRV",
    "IU.COLA",
    "II.BFO",
    "IU.CTAO",
    "IU.SNZO",
    # Additional global coverage
    "IU.TATO",
    "IU.MAJO",
    "II.BORG",
    "IU.KONO",
    "IU.SJG",
    "II.SACV",
    "IU.CASY",
    "IU.QSPA",
    "IU.MBWA",
    "II.PALK",
]


CONFIGS: list[dict[str, Any]] = [
    {
        "name": "baseline",
        "stations": ["IU.ANMO", "IU.HRV", "IU.COLA", "II.BFO", "IU.CTAO", "IU.SNZO"],
        "min_magnitude": 6.0,
        "days_back": 30,
        "max_events": 3,
    },
    {
        "name": "expanded_stations",
        "stations": EXPANDED_STATIONS,
        "min_magnitude": 6.0,
        "days_back": 30,
        "max_events": 5,
    },
    {
        "name": "lower_magnitude",
        "stations": ["IU.ANMO", "IU.HRV", "IU.COLA", "II.BFO", "IU.CTAO", "IU.SNZO"],
        "min_magnitude": 5.5,
        "days_back": 30,
        "max_events": 5,
    },
    {
        "name": "extended_time",
        "stations": ["IU.ANMO", "IU.HRV", "IU.COLA", "II.BFO", "IU.CTAO", "IU.SNZO"],
        "min_magnitude": 6.0,
        "days_back": 90,
        "max_events": 20,
    },
    {
        "name": "comprehensive",
        "stations": EXPANDED_STATIONS,
        "min_magnitude": 5.5,
        "days_back": 90,
        "max_events": 30,
    },
]


@dataclass
class RunResult:
    config: str
    status: str
    error: str | None = None
    n_events: int | None = None
    n_pairs: int | None = None
    accuracy: float | None = None
    false_negative_rate: float | None = None
    false_positive_rate: float | None = None
    mean_abs_timing_error_s: float | None = None
    std_abs_timing_error_s: float | None = None
    max_abs_timing_error_s: float | None = None


def _run(cmd: list[str], *, cwd: Path | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=str(cwd) if cwd is not None else None,
        check=False,
        text=True,
        capture_output=True,
    )


def ensure_lean_exe() -> None:
    if LEAN_EXE.exists():
        return
    print("[info] Building seismic_validate_demo (first run)")
    proc = _run(["lake", "build", "--wfail", "seismic_validate_demo"], cwd=RESEARCHER_BUNDLE)
    if proc.returncode != 0:
        raise RuntimeError(f"lake build failed:\n{proc.stdout}\n{proc.stderr}")
    if not LEAN_EXE.exists():
        raise RuntimeError("expected seismic_validate_demo binary not found after build")


def compute_metrics(lean_output_path: Path) -> dict[str, float]:
    out = json.loads(lean_output_path.read_text())
    pairs = out.get("pairs", [])
    valid = [p for p in pairs if p.get("waveform_ok") is True]

    # In this pipeline, `should_reach` acts as the label (arrival predicted by the external
    # travel-time model). `did_reach` is the observation result from the Lean-side detector.
    tp = sum(1 for p in valid if p.get("should_reach") is True and p.get("did_reach") is True)
    tn = sum(1 for p in valid if p.get("should_reach") is False and p.get("did_reach") is False)
    fp = sum(1 for p in valid if p.get("should_reach") is False and p.get("did_reach") is True)
    fn = sum(1 for p in valid if p.get("should_reach") is True and p.get("did_reach") is False)

    denom = max(1, len(valid))
    accuracy = (tp + tn) / denom

    fnr = fn / (fn + tp) if (fn + tp) else float("nan")
    fpr = fp / (fp + tn) if (fp + tn) else float("nan")

    abs_err_s: list[float] = []
    for p in valid:
        if not (p.get("should_reach") is True and p.get("did_reach") is True):
            continue
        err_ms = p.get("timing_error_ms")
        if err_ms is None:
            continue
        abs_err_s.append(abs(float(err_ms)) / 1000.0)

    mean_abs = float("nan")
    std_abs = float("nan")
    max_abs = float("nan")
    if abs_err_s:
        mean_abs = sum(abs_err_s) / len(abs_err_s)
        if len(abs_err_s) >= 2:
            mu = mean_abs
            std_abs = math.sqrt(sum((x - mu) ** 2 for x in abs_err_s) / len(abs_err_s))
        else:
            std_abs = 0.0
        max_abs = max(abs_err_s)

    return {
        "n_pairs": float(len(valid)),
        "accuracy": accuracy,
        "false_negative_rate": fnr,
        "false_positive_rate": fpr,
        "mean_abs_timing_error_s": mean_abs,
        "std_abs_timing_error_s": std_abs,
        "max_abs_timing_error_s": max_abs,
    }


def run_config(cfg: dict[str, Any]) -> RunResult:
    name = str(cfg["name"])
    out_dir = ROOT / "results" / "seismic_validation" / name
    out_dir.mkdir(parents=True, exist_ok=True)
    bundle_path = out_dir / "bundle.json"

    station_list = cfg["stations"]
    if not isinstance(station_list, list) or not station_list:
        return RunResult(config=name, status="config_error", error="stations must be a non-empty list")

    stations_arg = ",".join(station_list)

    fetch_cmd = [
        sys.executable,
        str(ROOT / "scripts" / "seismic_bridge.py"),
        "--stations",
        stations_arg,
        "--min-magnitude",
        str(cfg.get("min_magnitude", 6.0)),
        "--days-back",
        str(cfg.get("days_back", 30)),
        "--max-events",
        str(cfg.get("max_events", 3)),
        "--output",
        str(bundle_path),
    ]
    if cfg.get("max_magnitude") is not None:
        fetch_cmd.extend(["--max-magnitude", str(cfg["max_magnitude"])])

    proc = _run(fetch_cmd, cwd=ROOT)
    if proc.returncode != 0:
        return RunResult(config=name, status="fetch_failed", error=proc.stderr.strip() or proc.stdout.strip())

    try:
        bridge_out = json.loads(proc.stdout.strip() or "{}")
        n_events = int(bridge_out.get("n_events"))
    except Exception:
        n_events = None

    ensure_lean_exe()
    lean_output_path = out_dir / "lean_output.json"
    validate_proc = _run([str(LEAN_EXE), str(bundle_path)], cwd=ROOT)
    if validate_proc.returncode != 0:
        return RunResult(config=name, status="validation_failed", error=validate_proc.stderr.strip())
    lean_output_path.write_text(validate_proc.stdout)

    rep_proc = _run(
        [
            sys.executable,
            str(ROOT / "scripts" / "generate_validation_report.py"),
            "--bundle",
            str(bundle_path),
            "--lean-output",
            str(lean_output_path),
            "--output-dir",
            str(out_dir),
        ],
        cwd=ROOT,
    )
    if rep_proc.returncode != 0:
        return RunResult(config=name, status="report_failed", error=rep_proc.stderr.strip() or rep_proc.stdout.strip())

    try:
        metrics = compute_metrics(lean_output_path)
    except Exception as e:
        return RunResult(config=name, status="parse_failed", error=str(e))

    result = RunResult(
        config=name,
        status="success",
        n_events=n_events,
        n_pairs=int(metrics["n_pairs"]),
        accuracy=float(metrics["accuracy"]),
        false_negative_rate=float(metrics["false_negative_rate"]),
        false_positive_rate=float(metrics["false_positive_rate"]),
        mean_abs_timing_error_s=float(metrics["mean_abs_timing_error_s"]),
        std_abs_timing_error_s=float(metrics["std_abs_timing_error_s"]),
        max_abs_timing_error_s=float(metrics["max_abs_timing_error_s"]),
    )

    (out_dir / "metrics.json").write_text(json.dumps(result.__dict__, indent=2, sort_keys=True) + "\n")
    return result


def format_pct(x: float | None) -> str:
    if x is None or math.isnan(x):
        return "n/a"
    return f"{x * 100:.2f}%"


def format_s(x: float | None) -> str:
    if x is None or math.isnan(x):
        return "n/a"
    return f"{x:.1f}s"


def main() -> int:
    results: list[RunResult] = []
    for cfg in CONFIGS:
        name = cfg.get("name")
        print(f"\n=== Running config: {name} ===")
        res = run_config(cfg)
        results.append(res)
        print(f"status={res.status}")
        if res.error:
            print(res.error)

    out_dir = ROOT / "results" / "seismic_validation"
    out_dir.mkdir(parents=True, exist_ok=True)

    all_json = [r.__dict__ for r in results]
    (out_dir / "all_results.json").write_text(json.dumps(all_json, indent=2, sort_keys=True) + "\n")

    now = datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")
    lines = [
        "# Expanded Seismic Validation Report",
        "",
        f"Generated: {now}",
        "",
        "| Config | Status | Events | Pairs | Accuracy | FNR | FPR | Mean |Δt| | Std |Δt| | Max |Δt| |",
        "|--------|--------|--------|-------|----------|-----|-----|----------|---------|---------|",
    ]
    for r in results:
        lines.append(
            "| "
            + " | ".join(
                [
                    r.config,
                    r.status,
                    str(r.n_events) if r.n_events is not None else "n/a",
                    str(r.n_pairs) if r.n_pairs is not None else "n/a",
                    format_pct(r.accuracy),
                    format_pct(r.false_negative_rate),
                    format_pct(r.false_positive_rate),
                    format_s(r.mean_abs_timing_error_s),
                    format_s(r.std_abs_timing_error_s),
                    format_s(r.max_abs_timing_error_s),
                ]
            )
            + " |"
        )

    lines += [
        "",
        "## Notes",
        "",
        "- `should_reach` (from ak135 travel-time prediction) is treated as the label.",
        "- `did_reach` (from Lean STA/LTA detector) is the observation result.",
        "- `FNR` is the rate of predicted arrivals that were not detected.",
        "- `FPR` is the rate of detections when `should_reach = false`.",
    ]

    (out_dir / "expanded_comparison.md").write_text("\n".join(lines) + "\n")
    print(f"\nWrote: {out_dir / 'expanded_comparison.md'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

