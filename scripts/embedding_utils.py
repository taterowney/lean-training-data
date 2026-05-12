"""Shared embedding utilities using MLX embedding models.

Vectors returned by `embed_texts` are L2-normalised, so cosine similarity
equals the dot product.
"""

from __future__ import annotations

from typing import Iterable

import numpy as np
import mlx.core as mx
from mlx_embeddings.utils import load

DEFAULT_MODEL = "mlx-community/Qwen3-Embedding-0.6B-4bit-DWQ"


def _encode_text(tokenizer, text: str, max_length: int):
    """Encode one text with mlx-embeddings-compatible tokenizer APIs."""
    if hasattr(tokenizer, "encode"):
        try:
            return tokenizer.encode(
                text,
                return_tensors="mlx",
                truncation=True,
                max_length=max_length,
            )
        except TypeError:
            # Match mlx-embeddings README usage for wrappers with a narrower signature.
            return tokenizer.encode(text, return_tensors="mlx")

    base_tokenizer = getattr(tokenizer, "tokenizer", None)
    if base_tokenizer is not None and hasattr(base_tokenizer, "encode"):
        try:
            return base_tokenizer.encode(
                text,
                return_tensors="mlx",
                truncation=True,
                max_length=max_length,
            )
        except TypeError:
            return base_tokenizer.encode(text, return_tensors="mlx")

    raise TypeError("Tokenizer does not expose a supported `encode` method.")


def _mlx_to_numpy(arr: mx.array) -> np.ndarray:
    """Convert an MLX array to NumPy robustly across dtype/buffer edge cases."""
    # Prefer documented MLX API: array.astype(...)
    if hasattr(arr, "astype"):
        arr = arr.astype(mx.float32)
    else:
        # Compatibility fallback for MLX variants that expose module-level astype.
        arr = mx.astype(arr, mx.float32)
    mx.eval(arr)
    try:
        return np.asarray(arr, dtype=np.float32)
    except RuntimeError:
        # Fallback for PEP 3118 buffer incompatibilities seen with some MLX dtypes/layouts.
        return np.asarray(arr.tolist(), dtype=np.float32)


def embed_texts(
    texts: Iterable[str],
    model_name: str = DEFAULT_MODEL,
    max_length: int = 512,
) -> tuple[list[str], np.ndarray]:
    """Embed texts with an MLX embedding model and return normalized vectors."""
    text_list = list(texts)
    if not text_list:
        raise ValueError("No input texts were provided.")

    model, tokenizer = load(model_name)

    all_embeddings: list[np.ndarray] = []

    # Use single-item encode/model forward for broad compatibility across TokenizerWrapper variants.
    for text in text_list:
        input_ids = _encode_text(tokenizer, text, max_length=max_length)
        outputs = model(input_ids)
        embeds_np = _mlx_to_numpy(outputs.text_embeds)
        all_embeddings.append(embeds_np)

    embeddings = np.vstack(all_embeddings)
    norms = np.linalg.norm(embeddings, axis=1, keepdims=True)
    embeddings = embeddings / np.clip(norms, 1e-12, None)
    return text_list, embeddings


def embed_labeled_texts(
    labeled_texts: Iterable[tuple[str, str]],
    model_name: str = DEFAULT_MODEL,
    max_length: int = 512,
) -> tuple[list[str], list[str], np.ndarray]:
    """Embed labeled text pairs and return labels, texts, and embeddings."""
    labels: list[str] = []
    texts: list[str] = []
    for label, text in labeled_texts:
        labels.append(label)
        texts.append(text)

    text_list, embeddings = embed_texts(texts=texts, model_name=model_name, max_length=max_length)
    return labels, text_list, embeddings
