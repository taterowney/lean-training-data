#!/usr/bin/env python3

"""Pick k representative declarations by embedding their types and running
k-medoids with cosine similarity.

Pipeline:
  1. Load the cached `step_tactics` dataframe (see step_tactics_dataframe.py).
  2. Reduce it to one row per declaration, taking the *type* of the
     declaration to be the initial goal (the `goal_before` of its first
     tactic step).
  3. Filter the resulting (declaration, type) pairs through a user-supplied
     boolean predicate. The predicate may be supplied programmatically via
     `select_representative_types(...)` or from the CLI via
     `--predicate-module path/to/file.py --predicate-fn my_pred`.
  4. Embed the types with the same MLX embedding pipeline used in
     `embed_tsne_viz.py` (vectors are L2-normalised, so cosine similarity
     equals the dot product).
  5. Run k-medoids with cosine distance and return the medoids as the
     representative samples.

The predicate receives a single argument:

    predicate(row) -> bool

where `row` is a dict with keys {"declaration", "type", "module"}.
"""

from __future__ import annotations

import argparse
import importlib.util
import sys
from pathlib import Path
from typing import Callable, Iterable, Sequence, TYPE_CHECKING

import numpy as np

from embedding_utils import embed_texts
from step_tactics_dataframe import get_step_tactics_dataframe

if TYPE_CHECKING:
    import pandas as pd


Predicate = Callable[[dict], bool]


def declaration_types(df: "pd.DataFrame") -> "pd.DataFrame":
    """Reduce a step-tactics dataframe to one row per declaration.

    The "type" of a declaration is the `goal_before` of its first tactic
    step (the initial proof obligation).
    """
    if len(df) == 0:
        import pandas as pd

        return pd.DataFrame(columns=["module", "declaration", "type"])

    # Preserve original ordering — the first occurrence per declaration is
    # treated as the initial goal / type.
    first = df.drop_duplicates(subset=["declaration"], keep="first")
    out = first[["module", "declaration", "goal_before"]].rename(
        columns={"goal_before": "type"}
    )
    return out.reset_index(drop=True)


def filter_rows(types_df: "pd.DataFrame", predicate: Predicate) -> "pd.DataFrame":
    mask = types_df.apply(
        lambda row: bool(predicate(row.to_dict())), axis=1
    )
    return types_df[mask].reset_index(drop=True)


def cosine_distance_matrix(embeddings: np.ndarray) -> np.ndarray:
    """Pairwise cosine distance for L2-normalised vectors."""
    sims = embeddings @ embeddings.T
    np.clip(sims, -1.0, 1.0, out=sims)
    dists = 1.0 - sims
    np.fill_diagonal(dists, 0.0)
    # Numerical floor.
    np.clip(dists, 0.0, None, out=dists)
    return dists


def kmedoids(
    distances: np.ndarray,
    k: int,
    max_iter: int = 100,
    random_state: int = 42,
) -> tuple[np.ndarray, np.ndarray]:
    """Simple alternating (Voronoi-style) k-medoids.

    Returns (medoid_indices, labels) where `labels[i]` is the index into
    `medoid_indices` of the cluster point i is assigned to.
    """
    n = distances.shape[0]
    if k <= 0:
        raise ValueError("k must be positive.")
    if k >= n:
        return np.arange(n), np.arange(n)

    rng = np.random.default_rng(random_state)

    # k-means++ style seeding on the precomputed distance matrix.
    medoids = np.empty(k, dtype=np.int64)
    medoids[0] = int(rng.integers(0, n))
    closest = distances[medoids[0]].copy()
    for i in range(1, k):
        probs = closest ** 2
        total = probs.sum()
        if total <= 0:
            medoids[i] = int(rng.integers(0, n))
        else:
            medoids[i] = int(rng.choice(n, p=probs / total))
        closest = np.minimum(closest, distances[medoids[i]])

    labels = np.argmin(distances[medoids], axis=0)

    for _ in range(max_iter):
        new_medoids = medoids.copy()
        for c in range(k):
            members = np.where(labels == c)[0]
            if members.size == 0:
                continue
            sub = distances[np.ix_(members, members)]
            costs = sub.sum(axis=1)
            new_medoids[c] = members[int(np.argmin(costs))]

        new_labels = np.argmin(distances[new_medoids], axis=0)
        if np.array_equal(new_medoids, medoids) and np.array_equal(
            new_labels, labels
        ):
            medoids = new_medoids
            labels = new_labels
            break
        medoids = new_medoids
        labels = new_labels

    return medoids, labels


def select_representative_types(
    df: "pd.DataFrame",
    predicate: Predicate,
    k: int,
    *,
    model_name: str | None = None,
    max_length: int = 512,
    random_state: int = 42,
) -> "pd.DataFrame":
    """End-to-end: filter declarations, embed their types, and pick k medoids.

    Returns a dataframe with the medoid rows plus a `cluster_size` column
    counting how many filtered declarations each medoid represents.
    """
    import pandas as pd

    types_df = declaration_types(df)
    filtered = filter_rows(types_df, predicate)
    if len(filtered) == 0:
        raise SystemExit("No declarations matched the predicate.")
    if k > len(filtered):
        raise SystemExit(
            f"k={k} exceeds the {len(filtered)} declarations matching the predicate."
        )

    embed_kwargs: dict = {"max_length": max_length}
    if model_name is not None:
        embed_kwargs["model_name"] = model_name
    _, embeddings = embed_texts(filtered["type"].tolist(), **embed_kwargs)

    distances = cosine_distance_matrix(embeddings)
    medoids, labels = kmedoids(distances, k=k, random_state=random_state)

    representatives = filtered.iloc[medoids].copy().reset_index(drop=True)
    cluster_sizes = np.bincount(labels, minlength=k)
    representatives["cluster_size"] = cluster_sizes
    return representatives


def load_predicate_from_module(module_path: Path, fn_name: str) -> Predicate:
    spec = importlib.util.spec_from_file_location(
        f"_predicate_module_{module_path.stem}", module_path
    )
    if spec is None or spec.loader is None:
        raise SystemExit(f"Could not load predicate module: {module_path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    if not hasattr(module, fn_name):
        raise SystemExit(
            f"Module {module_path} has no attribute `{fn_name}`."
        )
    fn = getattr(module, fn_name)
    if not callable(fn):
        raise SystemExit(f"`{fn_name}` in {module_path} is not callable.")
    return fn


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--module",
        default="Mathlib",
        help="Lean module passed to step_tactics_dataframe.",
    )
    parser.add_argument(
        "--cache-dir",
        type=Path,
        default=Path("out/step_tactics"),
        help="Directory containing the cached step_tactics ndjson/pickle.",
    )
    parser.add_argument("--force", action="store_true")
    parser.add_argument("-k", type=int, required=True, help="Number of representatives.")
    parser.add_argument(
        "--predicate-module",
        type=Path,
        help="Python file defining the boolean filter function.",
    )
    parser.add_argument(
        "--predicate-fn",
        default="predicate",
        help="Name of the predicate callable inside --predicate-module.",
    )
    parser.add_argument("--embedding-model", default=None)
    parser.add_argument("--max-length", type=int, default=512)
    parser.add_argument("--random-state", type=int, default=42)
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="Optional CSV path to write the representatives to.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    repo_root = Path(__file__).resolve().parents[1]
    cache_dir = args.cache_dir
    if not cache_dir.is_absolute():
        cache_dir = repo_root / cache_dir

    if args.predicate_module is None:
        predicate: Predicate = lambda row: row["module"].startswith("Mathlib.Data.Set")
    else:
        predicate = load_predicate_from_module(
            args.predicate_module, args.predicate_fn
        )

    df = get_step_tactics_dataframe(
        module=args.module,
        cache_dir=cache_dir,
        repo_root=repo_root,
        force=args.force,
    )

    reps = select_representative_types(
        df=df,
        predicate=predicate,
        k=args.k,
        model_name=args.embedding_model,
        max_length=args.max_length,
        random_state=args.random_state,
    )

    print(f"representatives: {len(reps)}")
    print(reps.to_string(index=False))
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        reps.to_csv(args.output, index=False)
        print(f"wrote: {args.output}")


if __name__ == "__main__":
    main()
