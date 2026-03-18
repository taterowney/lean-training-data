#!/usr/bin/env python3

"""Cache declaration dependency data and score declarations by dependency rarity.

This script wraps:

    lake exe declinfo decl-frequencies

In the current Lean implementation, that command emits newline-delimited JSON
records with fields:

    {"declaration": "<decl>", "dependencies": ["<dep1>", ...]}

The script caches those records to disk, derives a Pandas dataframe of
dependency frequencies, and uses it to score a declaration by summing the
reciprocals of each dependency's relative frequency.
"""

from __future__ import annotations

import argparse
import json
import subprocess
from collections import Counter
from pathlib import Path
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    import pandas as pd


DEFAULT_EXCLUDE_ROOTS = "Lean,Init,Std,Batteries,Qq,Aesop,_private"


def require_pandas():
    try:
        import pandas as pd
    except ModuleNotFoundError as exc:
        raise SystemExit(
            "pandas is required to use this script. Install it with "
            "`python3 -m pip install pandas`."
        ) from exc
    return pd


def cache_stem(project: str, include_private: bool, exclude_roots: str) -> str:
    suffix = "with_private" if include_private else "without_private"
    sanitized_excludes = exclude_roots.replace(",", "_").replace("/", "_")
    return f"{project}.{suffix}.exclude_{sanitized_excludes}"


def run_decl_frequencies(
    project: str,
    exclude_roots: str,
    include_private: bool,
    cwd: Path,
) -> str:
    cmd = [
        "lake",
        "exe",
        "declinfo",
        "decl-frequencies",
        "--project",
        project,
        "--exclude-roots",
        exclude_roots,
    ]
    if include_private:
        cmd.append("--include-private")

    completed = subprocess.run(
        cmd,
        cwd=cwd,
        check=True,
        capture_output=True,
        text=True,
    )
    return completed.stdout


def load_dependency_records(raw_path: Path) -> list[dict[str, object]]:
    records: list[dict[str, object]] = []
    with raw_path.open() as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            records.append(json.loads(line))
    return records


def build_frequency_dataframe(records: list[dict[str, object]]) -> "pd.DataFrame":
    pd = require_pandas()
    counter: Counter[str] = Counter()
    for record in records:
        counter.update(record["dependencies"])

    total_frequency = sum(counter.values())
    rows = [
        {
            "dependency": dependency,
            "frequency": frequency,
            "relative_frequency": frequency / total_frequency if total_frequency else 0.0,
        }
        for dependency, frequency in counter.items()
    ]

    return (
        pd.DataFrame(rows)
        .sort_values(["frequency", "dependency"], ascending=[False, True])
        .reset_index(drop=True)
    )


def ensure_cached_records(
    project: str,
    exclude_roots: str,
    include_private: bool,
    cache_dir: Path,
    repo_root: Path,
    force: bool = False,
) -> Path:
    cache_dir.mkdir(parents=True, exist_ok=True)
    stem = cache_stem(project, include_private, exclude_roots)
    raw_path = cache_dir / f"{stem}.ndjson"

    if force or not raw_path.exists():
        stdout = run_decl_frequencies(
            project=project,
            exclude_roots=exclude_roots,
            include_private=include_private,
            cwd=repo_root,
        )
        raw_path.write_text(stdout)

    return raw_path


def get_decl_frequencies_dataframe(
    project: str,
    exclude_roots: str,
    include_private: bool,
    cache_dir: Path,
    repo_root: Path,
    force: bool = False,
) -> tuple["pd.DataFrame", list[dict[str, object]]]:
    pd = require_pandas()
    stem = cache_stem(project, include_private, exclude_roots)
    pickle_path = cache_dir / f"{stem}.pkl"
    raw_path = ensure_cached_records(
        project=project,
        exclude_roots=exclude_roots,
        include_private=include_private,
        cache_dir=cache_dir,
        repo_root=repo_root,
        force=force,
    )
    records = load_dependency_records(raw_path)

    if pickle_path.exists() and not force:
        return pd.read_pickle(pickle_path), records

    df = build_frequency_dataframe(records)
    df.to_pickle(pickle_path)
    return df, records


def build_dependency_index(records: list[dict[str, object]]) -> dict[str, list[str]]:
    return {
        str(record["declaration"]): [str(dep) for dep in record["dependencies"]]
        for record in records
    }


def reciprocal_relative_frequency_sum(
    declaration: str,
    df: "pd.DataFrame",
    dependency_index: dict[str, list[str]],
) -> tuple[float, list[dict[str, float | str]]]:
    try:
        dependencies = dependency_index[declaration]
    except KeyError as exc:
        raise SystemExit(f"Declaration not found in cached data: {declaration}") from exc

    if not dependencies:
        return 0.0, []

    frequency_map = df.set_index("dependency")[["frequency", "relative_frequency"]].to_dict("index")
    missing = [dep for dep in dependencies if dep not in frequency_map]
    if missing:
        raise SystemExit(
            "Some dependencies were missing from the frequency dataframe: "
            + ", ".join(missing[:10])
        )

    details: list[dict[str, float | str]] = []
    total = 0.0
    for dep in dependencies:
        relative_frequency = float(frequency_map[dep]["relative_frequency"])
        reciprocal = 1.0 / relative_frequency
        total += reciprocal
        details.append(
            {
                "dependency": dep,
                "frequency": float(frequency_map[dep]["frequency"]),
                "relative_frequency": relative_frequency,
                "reciprocal_relative_frequency": reciprocal,
            }
        )

    return total, details


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Given a declaration name, load cached dependency data from "
            "`lake exe declinfo decl-frequencies` and sum the reciprocals of "
            "the relative frequencies of its dependencies."
        )
    )
    parser.add_argument("declaration", help="Fully qualified declaration name to score.")
    parser.add_argument("--project", default="Mathlib")
    parser.add_argument("--exclude-roots", default=DEFAULT_EXCLUDE_ROOTS)
    parser.add_argument("--include-private", action="store_true")
    parser.add_argument("--cache-dir", type=Path, default=Path("out/decl_frequencies"))
    parser.add_argument("--force", action="store_true")
    parser.add_argument(
        "--show-dependencies",
        action="store_true",
        help="Print per-dependency scoring details.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    repo_root = Path(__file__).resolve().parents[1]
    cache_dir = args.cache_dir
    if not cache_dir.is_absolute():
        cache_dir = repo_root / cache_dir

    df, records = get_decl_frequencies_dataframe(
        project=args.project,
        exclude_roots=args.exclude_roots,
        include_private=args.include_private,
        cache_dir=cache_dir,
        repo_root=repo_root,
        force=args.force,
    )
    dependency_index = build_dependency_index(records)
    total, details = reciprocal_relative_frequency_sum(args.declaration, df, dependency_index)

    print(f"declaration: {args.declaration}")
    print(f"dependency_count: {len(details)}")
    print(f"reciprocal_relative_frequency_sum: {total}")

    if args.show_dependencies and details:
        pd = require_pandas()
        details_df = pd.DataFrame(details).sort_values(
            ["reciprocal_relative_frequency", "dependency"],
            ascending=[False, True],
        )
        print(details_df.to_string(index=False))


if __name__ == "__main__":
    main()
