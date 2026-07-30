#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Analyze one llvm-snippy RTL simulation log.

The Snippy RTL runner writes a minimal per-run result.json first:

  {
    "layout": "...",
    "iteration": 0,
    "snippy_seed": 123,
    "test_run_dir": ".../ibex_make_out/run/tests/snippy_<layout>.<seed>",
    "log_file": ".../rtl_sim_stdstreams.log"
  }

This script reads that file, checks the canonical Ibex stdstreams log and updates
the same result.json with the final PASS/FAIL status. It also updates the
aggregate snippy_summary.json.
"""

from __future__ import annotations

import argparse
import contextlib
import datetime as _datetime
import fcntl
import json
from pathlib import Path
from typing import Any


PASS_MARKER = "PASSED"
FAIL_MARKER = "FAILED"


@contextlib.contextmanager
def locked_file(lock_path: Path):
    """Take an exclusive advisory lock for aggregate summary updates."""
    lock_path.parent.mkdir(parents=True, exist_ok=True)

    with lock_path.open("w", encoding="utf-8") as lock_file:
        fcntl.flock(lock_file.fileno(), fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(lock_file.fileno(), fcntl.LOCK_UN)


def utc_now_iso() -> str:
    return _datetime.datetime.now(_datetime.UTC).isoformat(timespec="seconds")


def load_json_file(path: Path) -> dict[str, Any]:
    try:
        with path.open("r", encoding="utf-8") as input_file:
            data = json.load(input_file)
    except (OSError, json.JSONDecodeError):
        return {}

    if not isinstance(data, dict):
        return {}

    return data


def read_text_if_exists(path: Path) -> tuple[str, str | None]:
    if not path.exists():
        return "", f"Log file not found: {path}"

    try:
        return path.read_text(encoding="utf-8", errors="replace"), None
    except OSError as err:
        return "", f"Failed to read log file {path}: {err}"


def analyze_log(log_path: Path | None) -> str:
    """Return PASS or FAIL for one simulation log."""
    if log_path is None:
        return "FAIL"

    contents, read_error = read_text_if_exists(log_path)

    if read_error is not None:
        return "FAIL"

    passed_marker_found = PASS_MARKER in contents
    failed_marker_found = FAIL_MARKER in contents

    if passed_marker_found and not failed_marker_found:
        return "PASS"

    return "FAIL"


def empty_summary() -> dict[str, Any]:
    return {
        "totals": {
            "passed": 0,
            "failed": 0,
            "total": 0,
            "status": "FAIL",
        },
        "layouts": {},
        "results": [],
        "generated_at": None,
    }


def load_summary(summary_json: Path) -> dict[str, Any]:
    if not summary_json.exists():
        return empty_summary()

    data = load_json_file(summary_json)

    if not data:
        broken_path = summary_json.with_suffix(summary_json.suffix + ".broken")
        try:
            summary_json.replace(broken_path)
        except OSError:
            pass

        return empty_summary()

    data.setdefault(
        "totals",
        {
            "passed": 0,
            "failed": 0,
            "total": 0,
            "status": "FAIL",
        },
    )
    data.setdefault("layouts", {})
    data.setdefault("results", [])
    data.setdefault("generated_at", None)

    return data


def recompute_summary(results: list[dict[str, Any]]) -> dict[str, Any]:
    layouts: dict[str, dict[str, Any]] = {}

    for result in results:
        layout = str(result["layout"])
        status = str(result["status"])

        layout_summary = layouts.setdefault(
            layout,
            {
                "passed": 0,
                "failed": 0,
                "total": 0,
                "status": "FAIL",
            },
        )

        layout_summary["total"] += 1
        if status == "PASS":
            layout_summary["passed"] += 1
        else:
            layout_summary["failed"] += 1

    for layout_summary in layouts.values():
        layout_summary["status"] = (
            "PASS"
            if layout_summary["total"] > 0 and layout_summary["failed"] == 0
            else "FAIL"
        )

    passed = sum(1 for result in results if result["status"] == "PASS")
    failed = sum(1 for result in results if result["status"] != "PASS")
    total = len(results)

    totals = {
        "passed": passed,
        "failed": failed,
        "total": total,
        "status": "PASS" if total > 0 and failed == 0 else "FAIL",
    }

    return {
        "totals": totals,
        "layouts": layouts,
        "results": results,
        "generated_at": utc_now_iso(),
    }


def result_sort_key(result: dict[str, Any]) -> tuple[str, int]:
    layout = str(result.get("layout", ""))

    try:
        iteration = int(result.get("iteration", -1))
    except (TypeError, ValueError):
        iteration = -1

    return layout, iteration


def write_json(path: Path, data: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)

    tmp_path = path.with_suffix(path.suffix + ".tmp")
    with tmp_path.open("w", encoding="utf-8") as output:
        json.dump(data, output, indent=2)
        output.write("\n")

    tmp_path.replace(path)


def update_aggregate_summary(
    *,
    summary_json: Path,
    result: dict[str, Any],
) -> dict[str, Any]:
    lock_path = summary_json.with_suffix(summary_json.suffix + ".lock")

    with locked_file(lock_path):
        current_summary = load_summary(summary_json)
        results = current_summary.get("results", [])

        if not isinstance(results, list):
            results = []

        current_key = (result["layout"], result["iteration"])
        filtered_results = [
            old_result
            for old_result in results
            if (old_result.get("layout"), old_result.get("iteration")) != current_key
        ]

        filtered_results.append(result)
        filtered_results.sort(key=result_sort_key)

        new_summary = recompute_summary(filtered_results)
        write_json(summary_json, new_summary)

        return new_summary


def normalize_result(raw_result: dict[str, Any], status: str) -> dict[str, Any]:
    """Keep only the fields that should be stored in per-run and summary JSON."""
    return {
        "layout": raw_result["layout"],
        "iteration": int(raw_result["iteration"]),
        "status": status,
        "snippy_seed": int(raw_result["snippy_seed"]),
        "test_run_dir": raw_result["test_run_dir"],
        "log_file": raw_result["log_file"],
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Analyze one llvm-snippy RTL simulation log."
    )

    parser.add_argument(
        "--result-json",
        required=True,
        type=Path,
        help="Per-run JSON produced by run_snippy_rtl.py and updated here.",
    )
    parser.add_argument(
        "--summary-json",
        required=True,
        type=Path,
        help="Aggregate JSON summary path.",
    )

    return parser.parse_args()


def main() -> int:
    args = parse_args()

    raw_result = load_json_file(args.result_json)

    required_fields = [
        "layout",
        "iteration",
        "snippy_seed",
        "test_run_dir",
        "log_file",
    ]

    missing_fields = [
        field for field in required_fields
        if field not in raw_result or raw_result[field] in (None, "")
    ]

    if missing_fields:
        result = {
            "layout": str(raw_result.get("layout", "unknown")),
            "iteration": int(raw_result.get("iteration", -1)),
            "status": "FAIL",
            "snippy_seed": int(raw_result.get("snippy_seed", -1)),
            "test_run_dir": str(raw_result.get("test_run_dir", "")),
            "log_file": str(raw_result.get("log_file", "")),
        }
    else:
        log_file = Path(str(raw_result["log_file"]))
        status = analyze_log(log_file)
        result = normalize_result(raw_result, status)

    write_json(args.result_json, result)

    summary = update_aggregate_summary(
        summary_json=args.summary_json,
        result=result,
    )

    layout_summary = summary["layouts"][result["layout"]]
    totals = summary["totals"]

    print(
        f"Snippy: {result['layout']}[{result['iteration']}] "
        f"{result['status']}"
    )
    print(
        f"Layout: {layout_summary['passed']} passed, "
        f"{layout_summary['failed']} failed -> {layout_summary['status']}"
    )
    print(
        f"All: {totals['passed']} passed, "
        f"{totals['failed']} failed -> {totals['status']}"
    )

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
