#!/usr/bin/env python3
"""billiard_calibration.py

Generate calibration datasets for a simple 1D elastic billiard system.

The intent is to measure how observation parameters (precision/noise) induce an information gap
relative to known ground truth dynamics.

This implementation is stdlib-only (no numpy).
"""

from __future__ import annotations

import argparse
import json
import math
import random
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal


@dataclass
class Ball:
    pos: float
    vel: float
    mass: float = 1.0


@dataclass
class BilliardState:
    balls: list[Ball]
    time: float = 0.0
    table_left: float = 0.0
    table_right: float = 1.0


EventType = Literal["wall", "collision", "none"]


def collide(b1: Ball, b2: Ball) -> tuple[Ball, Ball]:
    """1D elastic collision (conservation of momentum + energy)."""
    m1, m2 = b1.mass, b2.mass
    v1, v2 = b1.vel, b2.vel
    v1p = ((m1 - m2) * v1 + 2.0 * m2 * v2) / (m1 + m2)
    v2p = ((m2 - m1) * v2 + 2.0 * m1 * v1) / (m1 + m2)
    return Ball(b1.pos, v1p, m1), Ball(b2.pos, v2p, m2)


def time_to_wall(b: Ball, left: float, right: float) -> float:
    if b.vel > 0:
        return (right - b.pos) / b.vel if b.pos < right else 0.0
    if b.vel < 0:
        return (b.pos - left) / (-b.vel) if b.pos > left else 0.0
    return math.inf


def next_event(state: BilliardState, eps: float = 1e-12) -> tuple[float, EventType, tuple[int, int] | int | None]:
    """Return (dt, event_type, payload).

    Payload:
    - wall: index of ball
    - collision: (i, j)
    - none: None
    """
    balls = state.balls

    best_dt = math.inf
    best_type: EventType = "none"
    best_payload: tuple[int, int] | int | None = None

    for i, b in enumerate(balls):
        dt_wall = time_to_wall(b, state.table_left, state.table_right)
        if dt_wall >= -eps and dt_wall < best_dt:
            best_dt = max(0.0, dt_wall)
            best_type = "wall"
            best_payload = i

    for i in range(len(balls)):
        for j in range(i + 1, len(balls)):
            bi, bj = balls[i], balls[j]
            if bi.pos >= bj.pos:
                continue
            dv = bi.vel - bj.vel
            if dv <= eps:
                continue
            dt_col = (bj.pos - bi.pos) / dv
            if dt_col >= -eps and dt_col < best_dt:
                best_dt = max(0.0, dt_col)
                best_type = "collision"
                best_payload = (i, j)

    return best_dt, best_type, best_payload


def advance(state: BilliardState, dt: float) -> BilliardState:
    balls = [Ball(b.pos + b.vel * dt, b.vel, b.mass) for b in state.balls]
    return BilliardState(balls=balls, time=state.time + dt, table_left=state.table_left, table_right=state.table_right)


def step_to_next_event(state: BilliardState, remaining: float) -> BilliardState:
    dt, etype, payload = next_event(state)
    if dt is math.inf or dt >= remaining:
        return advance(state, remaining)

    s = advance(state, dt)
    if etype == "wall" and isinstance(payload, int):
        balls = list(s.balls)
        b = balls[payload]
        balls[payload] = Ball(b.pos, -b.vel, b.mass)
        return BilliardState(balls=balls, time=s.time, table_left=s.table_left, table_right=s.table_right)

    if etype == "collision" and isinstance(payload, tuple):
        i, j = payload
        balls = list(s.balls)
        b1, b2 = balls[i], balls[j]
        nb1, nb2 = collide(b1, b2)
        balls[i] = nb1
        balls[j] = nb2
        return BilliardState(balls=balls, time=s.time, table_left=s.table_left, table_right=s.table_right)

    return s


def evolve(state: BilliardState, total_time: float, *, max_steps: int = 100000) -> list[BilliardState]:
    """Evolve by `total_time`, returning a trajectory including the initial state."""
    traj = [state]
    t_rem = total_time
    steps = 0
    cur = state
    while t_rem > 0 and steps < max_steps:
        cur = step_to_next_event(cur, t_rem)
        traj.append(cur)
        t_rem = total_time - (cur.time - state.time)
        steps += 1
        if t_rem < 1e-12:
            break
    return traj


def observe_positions(state: BilliardState, *, precision: int, noise_std: float) -> dict:
    def round_to(x: float, decimals: int) -> float:
        factor = 10**decimals
        return round(x * factor) / factor

    pos = []
    for b in state.balls:
        x = b.pos + (random.gauss(0.0, noise_std) if noise_std > 0 else 0.0)
        pos.append(round_to(x, precision))
    return {
        "positions": pos,
        "precision": precision,
        "noise_std": noise_std,
        "timestamp": round_to(state.time, precision),
    }


def rms_error(a: list[float], b: list[float]) -> float:
    n = min(len(a), len(b))
    if n == 0:
        return float("nan")
    return math.sqrt(sum((a[i] - b[i]) ** 2 for i in range(n)) / n)


def run_calibration_experiment(
    *,
    initial_state: BilliardState,
    evolution_time: float,
    precision_levels: list[int],
    noise_levels: list[float],
    num_samples: int,
) -> dict:
    traj = evolve(initial_state, evolution_time)

    if len(traj) <= 1:
        sample_idx = [0]
    else:
        sample_idx = [
            int(round(i * (len(traj) - 1) / max(1, num_samples - 1))) for i in range(num_samples)
        ]
    sampled = [traj[i] for i in sample_idx]

    true_final = [b.pos for b in traj[-1].balls]
    results = {
        "initial_state": asdict(initial_state),
        "evolution_time": evolution_time,
        "ground_truth": {
            "final_positions": true_final,
            "final_velocities": [b.vel for b in traj[-1].balls],
        },
        "calibration_runs": [],
    }

    for precision in precision_levels:
        for noise_std in noise_levels:
            obs = [observe_positions(s, precision=precision, noise_std=noise_std) for s in sampled]
            obs_final = obs[-1]["positions"]
            results["calibration_runs"].append(
                {
                    "precision": precision,
                    "noise_std": noise_std,
                    "rms_error": rms_error(true_final, obs_final),
                    "observations": obs,
                }
            )
    return results


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--num-balls", type=int, default=3)
    ap.add_argument("--evolution-time", type=float, default=10.0)
    ap.add_argument("--output", default="data/billiard/calibration_results.json")
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--num-samples", type=int, default=100)
    args = ap.parse_args()

    random.seed(args.seed)

    balls = [
        Ball(pos=random.uniform(0.1, 0.9), vel=random.uniform(-1.0, 1.0))
        for _ in range(max(1, args.num_balls))
    ]
    balls.sort(key=lambda b: b.pos)
    init = BilliardState(balls=balls)

    results = run_calibration_experiment(
        initial_state=init,
        evolution_time=args.evolution_time,
        precision_levels=[1, 2, 3, 4, 5],
        noise_levels=[0.0, 0.001, 0.01, 0.1],
        num_samples=max(2, args.num_samples),
    )

    out_path = Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n")
    print(f"Calibration results saved to {out_path}")

    print("\nCalibration Summary:")
    print("Precision | Noise Std | RMS Error")
    print("-" * 40)
    for run in results["calibration_runs"]:
        print(f"    {run['precision']}     |   {run['noise_std']:.3f}   | {run['rms_error']:.6f}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

