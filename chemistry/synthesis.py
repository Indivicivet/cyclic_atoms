"""Shortest closed-endpoint syntheses from unlimited binary feedstocks."""

import json
from collections import Counter, deque
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix

import chemistry.closed_reactions as closed

FEEDS = ((5, 3, 0), (7, 0, 3), (0, 7, 5))
TARGET = (35, 14, 5)


def type_search(species, channels, feeds):
    """BFS over synthesizable species, counting each new reversible type once.

    Unlimited feed allows any established intermediate to be remade arbitrarily
    often. Once a type fires, all species on both its sides are established;
    reusing that type cannot add a new species to this support search.
    """
    masks = {m: 1 << i for i, m in enumerate(species)}
    initial = sum(masks[m] for m in feeds)
    target = masks[TARGET]
    actions = tuple(
        (sum(masks[m] for m in set(side)), sum(masks[m] for m in set(left + right)), i)
        for i, (left, right) in enumerate(channels)
        for side in (left, right)
    )
    parents = {initial: None}
    queue = deque([initial])
    while queue:
        state = queue.popleft()
        if state & target:
            plan = []
            while parents[state] is not None:
                previous, channel = parents[state]
                plan.append(channel)
                state = previous
            return list(reversed(plan)), len(parents)
        for required, added, channel in actions:
            if state & required == required and state | added != state:
                following = state | added
                if following not in parents:
                    parents[following] = (state, channel)
                    queue.append(following)
    raise ValueError("target is unreachable")


def schedule(directions, counts, feeds):
    """Find an executable ordering of a fixed integer reaction multiset."""

    active = [i for i, count in enumerate(counts) if count]
    # Restrict the recursion to the nonzero reaction counts.
    reduced = tuple(directions[i] for i in active)

    def order(remaining, stock):
        if not any(remaining):
            return []
        for i, count in enumerate(remaining):
            if count:
                left, right = reduced[i]
                needed = Counter(m for m in left if m not in feeds)
                if all(stock[m] >= n for m, n in needed.items()):
                    following = stock.copy()
                    following.subtract(needed)
                    following.update(m for m in right if m not in feeds)
                    rest = order(
                        remaining[:i] + (count - 1,) + remaining[i + 1 :], following
                    )
                    if rest is not None:
                        return [active[i]] + rest
        return None

    return order(tuple(counts[i] for i in active), Counter())


def event_search(species, channels, feeds):
    directions = tuple(
        direction
        for left, right in channels
        for direction in ((left, right), (right, left))
    )
    internal = [m for m in species if m not in feeds]
    matrix = lil_matrix((len(internal), len(directions)))
    rows = {m: i for i, m in enumerate(internal)}
    for j, (left, right) in enumerate(directions):
        for molecule, count in Counter(right).items():
            if molecule in rows:
                matrix[rows[molecule], j] += count
        for molecule, count in Counter(left).items():
            if molecule in rows:
                matrix[rows[molecule], j] -= count
    lower = np.zeros(len(internal))
    lower[rows[TARGET]] = 1
    result = milp(
        np.ones(len(directions)),
        integrality=np.ones(len(directions)),
        bounds=Bounds(0, 50),
        constraints=LinearConstraint(matrix.tocsc(), lower, np.inf),
        options={"time_limit": 120, "mip_rel_gap": 0},
    )
    if not result.success:
        raise RuntimeError(result.message)
    # Any solution with fewer than 50 total events has every count below 50,
    # so this finite variable bound cannot exclude a better solution here.
    if result.fun >= 50:
        raise ValueError("increase the count bound before claiming optimality")
    counts = np.rint(result.x).astype(int)
    plan = schedule(directions, counts, feeds)
    return {
        "lower_bound": int(round(result.fun)),
        "executable": plan is not None,
        "steps": [directions[i] for i in plan] if plan is not None else None,
        "flow": [(directions[i], int(n)) for i, n in enumerate(counts) if n],
    }


def expand_types(channels, plan, feeds):
    """Build a finite batch for a support plan, without borrowing intermediates."""
    available = set(feeds)
    producers = {}
    oriented = []
    for channel in plan:
        left, right = channels[channel]
        if not set(left) <= available:
            left, right = right, left
        if not set(left) <= available:
            raise ValueError("type plan has unavailable inputs")
        for molecule in set(right) - available:
            producers[molecule] = len(oriented)
        oriented.append((left, right))
        available.update(right)
    stock = Counter()
    steps = []

    def produce(molecule, count):
        if molecule in feeds:
            return
        while stock[molecule] < count:
            left, right = oriented[producers[molecule]]
            needed = Counter(m for m in left if m not in feeds)
            # Make later intermediates first: producing earlier species cannot
            # consume them. This avoids quietly borrowing a missing input.
            for precursor in sorted(needed, key=producers.__getitem__, reverse=True):
                produce(precursor, needed[precursor])
            if any(stock[m] < n for m, n in needed.items()):
                raise ValueError("preparation consumed a required intermediate")
            stock.subtract(needed)
            stock.update(m for m in right if m not in feeds)
            steps.append((left, right))

    produce(TARGET, 1)
    return oriented, steps


def audit(steps, feeds):
    """Replay a recipe and find finite initial feed counts; forbid other loans."""
    stock = Counter()
    initial = Counter()
    for left, right in steps:
        needed = Counter(left)
        for molecule in feeds:
            shortage = max(0, needed[molecule] - stock[molecule])
            initial[molecule] += shortage
            stock[molecule] += shortage
        if any(stock[m] < n for m, n in needed.items()):
            raise ValueError("recipe borrows an unavailable intermediate")
        stock.subtract(needed)
        stock.update(right)
    if stock[TARGET] < 1:
        raise ValueError("recipe does not produce MAX")
    return {
        "initial": [(m, n) for m, n in initial.items() if n],
        "final": [(m, n) for m, n in stock.items() if n],
    }


def main():
    species = closed.catalog()
    channels = closed.reactions(species)
    results = []
    for feeds in (
        (FEEDS[0], FEEDS[1]),
        (FEEDS[0], FEEDS[2]),
        (FEEDS[1], FEEDS[2]),
        FEEDS,
    ):
        events = event_search(species, channels, feeds)
        if not events["executable"]:
            raise ValueError("stoichiometric optimum could not be scheduled")
        types, states = type_search(species, channels, feeds)
        oriented, steps = expand_types(channels, types, feeds)
        print(
            "Supply",
            feeds,
            "events",
            events["lower_bound"],
            "types",
            len(types),
            flush=True,
        )
        results.append(
            {
                "feeds": feeds,
                "events": events,
                "type_count": len(types),
                "type_plan": oriented,
                "type_steps": steps,
                "searched_support_states": states,
                "event_batch": audit(events["steps"], feeds),
                "type_batch": audit(steps, feeds),
            }
        )
    output = Path(__file__).parent / "output" / "synthesis.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
