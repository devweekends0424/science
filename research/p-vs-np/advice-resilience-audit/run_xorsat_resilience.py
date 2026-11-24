"""Measure advice resilience on random 3-XOR-SAT instances.

Unlike 3-SAT (where literal polarity biases can leak planted solutions),
balanced 3-XOR-SAT has zero single-variable polarity bias, making structural
majority advice ineffective while still solvable in P via Gaussian elimination
over GF(2) (or exponentially hard for pure DPLL without XOR reasoning).
"""
from __future__ import annotations

import json
import math
from pathlib import Path
import random
import statistics


def generate_planted_3xorsat(n: int, m: int, rng: random.Random) -> tuple[list[tuple[tuple[int, int, int], int]], list[int]]:
    sol = [rng.choice([0, 1]) for _ in range(n)]
    eqs: list[tuple[tuple[int, int, int], int]] = []
    for _ in range(m):
        vs = tuple(sorted(rng.sample(range(n), 3)))
        rhs = sol[vs[0]] ^ sol[vs[1]] ^ sol[vs[2]]
        eqs.append((vs, rhs))
    return eqs, sol


def dpll_xor(eqs: list[tuple[tuple[int, int, int], int]], assign: dict[int, int], n: int, bias: dict[int, int] | None = None) -> tuple[bool, int]:
    nodes = 1
    # Check satisfied / falsified equations
    for vs, rhs in eqs:
        if all(v in assign for v in vs):
            if (assign[vs[0]] ^ assign[vs[1]] ^ assign[vs[2]]) != rhs:
                return False, nodes
    if len(assign) == n:
        return True, nodes

    for v in range(n):
        if v not in assign:
            first_val = bias[v] if (bias and v in bias) else 0
            for val in (first_val, 1 - first_val):
                assign[v] = val
                ok, sub = dpll_xor(eqs, assign, n, bias)
                nodes += sub
                if ok:
                    return True, nodes
                del assign[v]
            return False, nodes
    return False, nodes


def xor_structural_bias(eqs: list[tuple[tuple[int, int, int], int]], n: int, k: int) -> dict[int, int]:
    # In XOR-SAT, count rhs=1 vs rhs=0 occurrences per variable as a naive structural proxy
    score = {v: 0 for v in range(n)}
    for vs, rhs in eqs:
        delta = 1 if rhs == 1 else -1
        for v in vs:
            score[v] += delta
    ranked = sorted(range(n), key=lambda v: abs(score[v]), reverse=True)[:k]
    return {v: (1 if score[v] >= 0 else 0) for v in ranked}


def run_xor_benchmark(n: int, m: int, k: int, instances: int, seed: int) -> dict:
    rng = random.Random(seed)
    no_guide, oracle_k, struct_k = [], [], []
    for _ in range(instances):
        eqs, sol = generate_planted_3xorsat(n, m, rng)
        _, n0 = dpll_xor(eqs, {}, n)
        _, n_ora = dpll_xor(eqs, {}, n, bias={v: sol[v] for v in range(k)})
        _, n_str = dpll_xor(eqs, {}, n, bias=xor_structural_bias(eqs, n, k))
        no_guide.append(n0)
        oracle_k.append(n_ora)
        struct_k.append(n_str)

    base = statistics.mean(no_guide)
    out = {"n": n, "m": m, "k_bits": k, "instances": instances}
    for name, vals in (("no_guide", no_guide), ("oracle_k", oracle_k), ("structural_k", struct_k)):
        mval = statistics.mean(vals)
        red = (1.0 - mval / base) * 100.0 if base > 0 else 0.0
        gain = (math.log2(base / mval) / k) if (name != "no_guide" and mval > 0 and base > 0) else 0.0
        out[name] = {
            "mean_nodes": round(mval, 3),
            "reduction_pct": round(red, 2),
            "log2_gain_per_bit": round(gain, 4),
        }
    return out


def main() -> None:
    out_dir = Path("/Users/akasha/ai/science/experiments/pnp_advice_efficiency")
    report = {
        "experiment": "3xorsat_advice_resilience",
        "rounds": [
            run_xor_benchmark(n=14, m=20, k=4, instances=30, seed=20261124),
            run_xor_benchmark(n=16, m=24, k=4, instances=30, seed=20261125),
        ],
    }
    (out_dir / "xorsat_results.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
