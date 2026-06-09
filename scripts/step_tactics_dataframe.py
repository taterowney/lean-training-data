#!/usr/bin/env python3

"""Cache per-tactic step data and expose it as a Pandas dataframe.

This script wraps:

    lake exe step_tactics <module>

That command emits newline-delimited JSON records with fields:

    {
      "module": "<mod>",
      "declaration": "<decl>",
      "tactic": "<tactic source>",
      "tactic_kind": "<syntax kind>",
      "context": ["h0: ...", ...],
      "goal_before": "...",
      "goal_after": "..."
    }

The script streams those records to disk (so large traces don't have to fit
in memory), then loads them into a Pandas dataframe and pickles it for fast
later access.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    import pandas as pd


def require_pandas():
    try:
        import pandas as pd
    except ModuleNotFoundError as exc:
        raise SystemExit(
            "pandas is required to use this script. Install it with "
            "`python3 -m pip install pandas`."
        ) from exc
    return pd


def cache_stem(module: str) -> str:
    return f"step_tactics.{module}"


def run_step_tactics(module: str, output_path: Path, cwd: Path) -> None:
    """Stream `lake exe step_tactics <module>` stdout to `output_path` line by line.

    Each stdout line from Lean is one compact JSON record. We write them through
    to a `.part` file and flush per line, so progress is visible on disk while
    the subprocess is still running. Lean's stderr is forwarded to our stderr
    so the caller sees per-module progress markers.
    """
    cmd = ["lake", "exe", "step_tactics", module]
    tmp_path = output_path.with_suffix(output_path.suffix + ".part")
    print(f"writing to {tmp_path}", file=sys.stderr, flush=True)

    proc = subprocess.Popen(
        cmd,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=None,  # inherit so progress markers stream to our terminal
        text=True,
        bufsize=1,  # line-buffered
    )
    assert proc.stdout is not None

    count = 0
    try:
        with tmp_path.open("w") as out:
            for line in proc.stdout:
                out.write(line)
                out.flush()
                count += 1
                if count % 100 == 0:
                    print(f"[step_tactics] {count} records", file=sys.stderr, flush=True)
        returncode = proc.wait()
    except BaseException:
        proc.kill()
        proc.wait()
        raise

    if returncode != 0:
        raise SystemExit(
            f"`{' '.join(cmd)}` exited with status {returncode}. "
            f"Partial output left at {tmp_path}."
        )

    print(f"[step_tactics] wrote {count} records", file=sys.stderr, flush=True)
    tmp_path.replace(output_path)


def load_step_records(raw_path: Path) -> list[dict[str, object]]:
    records: list[dict[str, object]] = []
    with raw_path.open() as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            try:
                records.append(json.loads(line))
            except json.JSONDecodeError:
                continue
    return records


def build_step_dataframe(records: list[dict[str, object]]) -> "pd.DataFrame":
    pd = require_pandas()
    if not records:
        return pd.DataFrame(
            columns=[
                "module",
                "declaration",
                "tactic",
                "tactic_kind",
                "context",
                "goal_before",
                "goal_after",
            ]
        )
    df = pd.DataFrame.from_records(records)
    for column in (
        "module",
        "declaration",
        "tactic",
        "tactic_kind",
        "goal_before",
        "goal_after",
    ):
        if column not in df.columns:
            df[column] = ""
    if "context" not in df.columns:
        df["context"] = [[] for _ in range(len(df))]
    return df[
        [
            "module",
            "declaration",
            "tactic",
            "tactic_kind",
            "context",
            "goal_before",
            "goal_after",
        ]
    ]


def ensure_cached_records(
    module: str,
    cache_dir: Path,
    repo_root: Path,
    force: bool = False,
) -> Path:
    cache_dir.mkdir(parents=True, exist_ok=True)
    raw_path = cache_dir / f"{cache_stem(module)}.ndjson"
    if force or not raw_path.exists():
        run_step_tactics(module=module, output_path=raw_path, cwd=repo_root)
    return raw_path


def get_step_tactics_dataframe(
    module: str,
    cache_dir: Path,
    repo_root: Path,
    force: bool = False,
) -> "pd.DataFrame":
    pd = require_pandas()
    pickle_path = cache_dir / f"{cache_stem(module)}.pkl"
    raw_path = ensure_cached_records(
        module=module,
        cache_dir=cache_dir,
        repo_root=repo_root,
        force=force,
    )

    if pickle_path.exists() and not force:
        return pd.read_pickle(pickle_path)

    records = load_step_records(raw_path)
    df = build_step_dataframe(records)
    df.to_pickle(pickle_path)
    return df


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Cache the output of `lake exe step_tactics` and load it as a "
            "Pandas dataframe of (module, declaration, tactic, ...) rows."
        )
    )
    parser.add_argument(
        "--module",
        default="Mathlib",
        help="Root module to trace (passed to `lake exe step_tactics`).",
    )
    parser.add_argument(
        "--cache-dir",
        type=Path,
        default=Path("out/step_tactics"),
        help="Directory for the ndjson + pickle caches.",
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="Re-run `lake exe step_tactics` and rebuild the dataframe.",
    )
    parser.add_argument(
        "--head",
        type=int,
        default=0,
        help="If > 0, print the first N rows of the dataframe.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    repo_root = Path(__file__).resolve().parents[1]
    cache_dir = args.cache_dir
    if not cache_dir.is_absolute():
        cache_dir = repo_root / cache_dir

    df = get_step_tactics_dataframe(
        module=args.module,
        cache_dir=cache_dir,
        repo_root=repo_root,
        force=args.force,
    )

    print(f"module: {args.module}")
    print(f"rows: {len(df)}")
    print(f"unique_declarations: {df['declaration'].nunique() if len(df) else 0}")
    print(f"unique_modules: {df['module'].nunique() if len(df) else 0}")

    if len(df):
        top_kinds = df["tactic_kind"].value_counts().head(10)
        print("top_tactic_kinds:")
        for kind, count in top_kinds.items():
            print(f"  {count:>8d}  {kind}")

    if args.head > 0 and len(df):
        print(df.head(args.head).to_string(index=False))


if __name__ == "__main__":
    main()
