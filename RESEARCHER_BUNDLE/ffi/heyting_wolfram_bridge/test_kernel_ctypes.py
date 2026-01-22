#!/usr/bin/env python3

from __future__ import annotations

import argparse
import ctypes
import pathlib
import sys


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Sanity-check HeytingLean-exported kernel shared library via ctypes."
    )
    parser.add_argument("--lib", required=True, help="Path to libheyting_kernel.so")
    parser.add_argument(
        "--expected",
        required=True,
        help=(
            "Path to expected.txt emitted by lambda_kernel_export "
            "(2 lines: heyting_add1(41), then heyting_add2(20,22))."
        ),
    )
    args = parser.parse_args()

    lib_path = pathlib.Path(args.lib)
    expected_path = pathlib.Path(args.expected)
    if not lib_path.is_file():
        print(f"E: missing shared library: {lib_path}", file=sys.stderr)
        return 1
    if not expected_path.is_file():
        print(f"E: missing expected output file: {expected_path}", file=sys.stderr)
        return 1

    expected_lines = [
        line.strip()
        for line in expected_path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    if len(expected_lines) < 2:
        print(
            f"E: expected.txt should have at least 2 non-empty lines; got {len(expected_lines)}",
            file=sys.stderr,
        )
        return 1
    try:
        expected_add1 = int(expected_lines[0])
        expected_add2 = int(expected_lines[1])
    except ValueError:
        print(f"E: expected.txt lines are not integers: {expected_lines[:2]!r}", file=sys.stderr)
        return 1

    try:
        lib = ctypes.CDLL(str(lib_path))
    except OSError as e:
        print(f"E: failed to load {lib_path}: {e}", file=sys.stderr)
        return 1

    try:
        add1 = lib.heyting_add1
    except AttributeError:
        print("E: missing symbol: heyting_add1", file=sys.stderr)
        return 1

    add1.argtypes = [ctypes.c_longlong]
    add1.restype = ctypes.c_longlong

    try:
        add2 = lib.heyting_add2
    except AttributeError:
        print("E: missing symbol: heyting_add2", file=sys.stderr)
        return 1

    add2.argtypes = [ctypes.c_longlong, ctypes.c_longlong]
    add2.restype = ctypes.c_longlong

    # The exported demo is Nat→Nat; keep inputs nonnegative.
    test_inputs = [0, 1, 2, 41, 123, 1024]
    for x in test_inputs:
        y = int(add1(x))
        if y != x + 1:
            print(f"E: heyting_add1({x}) = {y}, expected {x + 1}", file=sys.stderr)
            return 1

    # Cross-check against the `expected.txt` baseline from the generated C driver.
    y41 = int(add1(41))
    if y41 != expected_add1:
        print(
            f"E: heyting_add1(41) = {y41}, expected.txt says {expected_add1}",
            file=sys.stderr,
        )
        return 1

    test_pairs = [(0, 0), (1, 0), (0, 1), (2, 3), (20, 22), (123, 456)]
    for x, y in test_pairs:
        z = int(add2(x, y))
        if z != x + y:
            print(f"E: heyting_add2({x}, {y}) = {z}, expected {x + y}", file=sys.stderr)
            return 1

    z_demo = int(add2(20, 22))
    if z_demo != expected_add2:
        print(
            f"E: heyting_add2(20, 22) = {z_demo}, expected.txt says {expected_add2}",
            file=sys.stderr,
        )
        return 1

    print("ok: ctypes sanity checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
