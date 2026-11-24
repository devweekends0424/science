"""Measure exploration reduction per advice bit and advice-resilient hardness.

Compares:
1. No guide (baseline DPLL)
2. Oracle guide (k exact solution bits)
3. Structural majority guide (k global polarity bias bits)
across:
- Planted 3-SAT (alpha=4.26)
- Uniform Random 3-SAT (alpha=4.26, filtered to SAT instances)
"""
from __future__ import annotations

import json
import math
from pathlib import Path
import random
import statistics


def generate_planted_3sat(n: int, m: int, rng: random.Random) -> tuple[list[tuple[int, ...]], list[int]]:
    sol = [rng.choice([1, -1]) for _ in range(n)]
    clauses: list[tuple[int, ...]] = []
    while len(clauses) < m:
        vs = rng.sample(range(1, n + 1), 3)
        signs = [rng.choice([1, -1]) for _ in range(3)]
        clause = tuple(v * s for v, s in zip(vs, signs))
        # Ensure clause is satisfied by planted solution
        if any((lit > 0 and sol[abs(lit) - 1] == 1) or (lit < 0 and sol[abs(lit) - 1] == -1) for lit in clause):
            clauses.append(clause)
    return clauses, sol


def dpll(clauses: list[tuple[int, ...]], assignment: dict[int, int], n: int, bias: dict[int, int] | None = None) -> tuple[bool, int, dict[int, int] | None]:
    nodes = 1
    # Unit propagation & pure literal simplified loop
    assign = dict(assignment)
    changed = True
    while changed:
        changed = False
        for c in clauses:
            unassigned = []
            sat = False
            for lit in c:
                v = abs(lit)
                if v in assign:
                    if (lit > 0 and assign[v] == 1) or (lit < 0 and assign[v] == -1):
                        sat = True
                        break
                else:
                    unassigned.append(lit)
            if sat:
                continue
            if not unassigned:
                return False, nodes, None
            if len(unassigned) == 1:
                lit = unassigned[0]
                assign[abs(lit)] = 1 if lit > 0 else -1
                changed = True

    if len(assign) == n:
        # Verify all clauses
        for c in clauses:
            if not any((lit > 0 and assign[abs(lit)] == 1) or (lit < 0 and assign[abs(lit)] == -1) for lit in c):
                return False, nodes, None
        return True, nodes, assign

    # Choose first unassigned variable
    for v in range(1, n + 1):
        if v not in assign:
            first_val = bias[v] if (bias and v in bias) else 1
            for val in (first_val, -first_val):
                assign[v] = val
                ok, sub_nodes, sol = dpll(clauses, assign, n, bias)
                nodes += sub_nodes
                if ok:
                    return True, nodes, sol
                del assign[v]
            return False, nodes, None
    return False, nodes, None


def generate_random_sat_3sat(n: int, m: int, rng: random.Random) -> tuple[list[tuple[int, ...]], dict[int, int]]:
    while True:
        clauses = []
        for _ in range(m):
            vs = rng.sample(range(1, n + 1), 3)
            signs = [rng.choice([1, -1]) for _ in range(3)]
            clauses.append(tuple(v * s for v, s in zip(vs, signs)))
        ok, _, sol = dpll(clauses, {}, n)
        if ok and sol is not None:
            return clauses, sol


def structural_majority_bias(clauses: list[tuple[int, ...]], n: int, k: int) -> dict[int, int]:
    counts = {v: 0 for v in range(1, n + 1)}
    for c in clauses:
        for lit in c:
            counts[abs(lit)] += 1 if lit > 0 else -1
    # Pick top-k variables with strongest polarity bias
    ranked = sorted(range(1, n + 1), key=lambda v: abs(counts[v]), reverse=True)[:k]
    return {v: (1 if counts[v] >= 0 else -1) for v in ranked}


def run_benchmark(n: int, alpha: float, k: int, instances: int, seed: int) -> dict:
    rng = random.Random(seed)
    m = int(round(alpha * n))
    results: dict[str, dict[str, list[int]]] = {
        "planted": {"no_guide": [], "oracle_k": [], "structural_k": []},
        "random_sat": {"no_guide": [], "oracle_k": [], "structural_k": []},
    }

    for _ in range(instances):
        # 1. Planted
        p_clauses, p_sol = generate_planted_3sat(n, m, rng)
        _, n0, _ = dpll(p_clauses, {}, n)
        oracle_bias = {v: p_sol[v - 1] for v in range(1, k + 1)}
        _, n_ora, _ = dpll(p_clauses, {}, n, bias=oracle_bias)
        struct_bias = structural_majority_bias(p_clauses, n, k)
        _, n_str, _ = dpll(p_clauses, {}, n, bias=struct_bias)
        results["planted"]["no_guide"].append(n0)
        results["planted"]["oracle_k"].append(n_ora)
        results["planted"]["structural_k"].append(n_str)

        # 2. Uniform Random SAT
        r_clauses, r_sol = generate_random_sat_3sat(n, m, rng)
        _, rn0, _ = dpll(r_clauses, {}, n)
        r_oracle_bias = {v: r_sol[v] for v in range(1, k + 1)}
        _, rn_ora, _ = dpll(r_clauses, {}, n, bias=r_oracle_bias)
        r_struct_bias = structural_majority_bias(r_clauses, n, k)
        _, rn_str, _ = dpll(r_clauses, {}, n, bias=r_struct_bias)
        results["random_sat"]["no_guide"].append(rn0)
        results["random_sat"]["oracle_k"].append(rn_ora)
        results["random_sat"]["structural_k"].append(rn_str)

    summary: dict[str, object] = {"n": n, "m": m, "k_bits": k, "instances": instances}
    for dist in ("planted", "random_sat"):
        d_out = {}
        base = statistics.mean(results[dist]["no_guide"])
        for mode in ("no_guide", "oracle_k", "structural_k"):
            mean_val = statistics.mean(results[dist][mode])
            reduction_pct = (1.0 - mean_val / base) * 100.0 if base > 0 else 0.0
            gain_per_bit = (math.log2(base / mean_val) / k) if (mode != "no_guide" and mean_val > 0 and base > 0) else 0.0
            d_out[mode] = {
                "mean_nodes": round(mean_val, 3),
                "reduction_pct": round(reduction_pct, 2),
                "log2_gain_per_bit": round(gain_per_bit, 4),
            }
        summary[dist] = d_out
    return summary


def main() -> None:
    out_dir = Path("/Users/akasha/ai/science/experiments/pnp_advice_efficiency")
    out_dir.mkdir(parents=True, exist_ok=True)
    report = {
        "experiment": "advice_efficiency_and_resilience",
        "rounds": [
            run_benchmark(n=16, alpha=4.26, k=4, instances=40, seed=20261124),
            run_benchmark(n=20, alpha=4.26, k=4, instances=40, seed=20261125),
        ],
    }
    (out_dir / "results.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
