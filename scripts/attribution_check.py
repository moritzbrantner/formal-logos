"""Shape of the optional claim `attribution` field (#989), checked by `check`.

The pre-push attribution self-check itself is `truth attribution-check --base
<merge-base>` (#954 B5; truth/README.md); its Python implementation was retired
in #954 R2. This module keeps only the field validation that `scripts/corpus.py
check` still runs until R3."""

from __future__ import annotations

from typing import Any

ATTRIBUTION_PREFIX = "The passage states "
MIN_ATTRIBUTION_CHARS = 40


class AttributionError(Exception):
    pass


def validate_attribution(where: str, claim: dict[str, Any]) -> None:
    """Shape of an optional `attribution` field (checked by `check`)."""
    if "attribution" not in claim:
        return
    value = claim["attribution"]
    if (
        not isinstance(value, str)
        or not value.startswith(ATTRIBUTION_PREFIX)
        or len(value.strip()) < MIN_ATTRIBUTION_CHARS
    ):
        raise AttributionError(
            f"{where}: attribution must be one sentence starting {ATTRIBUTION_PREFIX!r} that says what the "
            f"passage states and that it is the premise (at least {MIN_ATTRIBUTION_CHARS} characters)"
        )
