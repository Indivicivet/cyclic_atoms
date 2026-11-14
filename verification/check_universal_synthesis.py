"""Compute the full synthesizable support for each binary feed pair."""

import chemistry.closed_reactions as closed
import chemistry.synthesis as synthesis


def closure(feeds, channels):
    available = set(feeds)
    while True:
        following = available | {
            m
            for left, right in channels
            for inputs, outputs in ((left, right), (right, left))
            if set(inputs) <= available
            for m in outputs
        }
        if following == available:
            return available
        available = following


if __name__ == "__main__":
    species = closed.catalog()
    channels = tuple(
        (left, right)
        for left, right in closed.reactions(species)
        if len(left) == len(right) == 2
    )
    for omitted in synthesis.FEEDS:
        feeds = tuple(m for m in synthesis.FEEDS if m != omitted)
        available = closure(feeds, channels)
        missing = sorted(set(species) - available)
        if missing:
            raise ValueError(f"unreachable formulas from {feeds}: {missing}")
        print("FEEDS", feeds, "REACHED", len(available), "MISSING", missing)
