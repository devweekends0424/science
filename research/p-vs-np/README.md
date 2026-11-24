# SAT partition functions and algebraic complexity

**Status: research formula notebook, not a proof of P != NP or VP != VNP.**  
Published: 2026-11-24. AI-assisted compilation and auditing.

Main file: [formulas.tex](./formulas.tex) (standalone LaTeX).

## Scope and proof status

- **[D]** Definitions of SAT violation energy, symbolic clause variables, and information quantities.
- **[I]** Algebraic identities: partition polynomial, DFT inversion, quantum amplitude, exact moments, sample formulas, and a constructive VNP-membership argument.
- **[T]** Conditional cumulant bounds under a clause dependency graph; the hypotheses and local convergence region are explicit.
- **[C]** Small exact examples and counterexamples for complex-zero locations.
- **[O]** No superpolynomial lower bound for the symbolic SAT family, no hardness theorem, and no P vs NP resolution.

**Important:** For a fixed CNF, the *univariate* polynomial in z has an O(m)-gate arithmetic circuit if its coefficients are supplied as unrestricted field constants (Horner's rule). Symbolic families and uniform coefficient computation are different questions. Membership of the symbolic family in VNP does not imply VNP-hardness.

The formula with clause-variables X_C represents 3-CNF instances with **distinct clauses of width exactly three**, each clause using three distinct Boolean variables. Duplicate clauses require an occurrence-indexed variant.

## Prior work / provenance

The notebook reorganizes standard mathematical identities, existing published bounds, and counterexamples discussed in an AI-assisted research conversation. It is not a claim of original discovery or a universal proof.

- L. G. Valiant, *Completeness Classes in Algebra*, STOC 1979: https://doi.org/10.1145/800135.804419
- V. Féray, P.-L. Méliot, A. Nikeghbali, dependency-graph cumulant bound (Theorem 34 in the linked manuscript): https://www.imo.universite-paris-saclay.fr/~pierre-loic.meliot/works/speed.pdf
- A. Barvinok, *On the zeros of partition functions with multi-spin interactions*, 2026: https://doi.org/10.4171/AIHPD/228
- Anthropic, *VP ≠ VNP over every field*, research announcement and Lean formalization (2026-11-23; independent mathematical review must be assessed separately): https://github.com/anthropics/formal-math/tree/main/vp-vnp

No Lean or full LaTeX compilation is claimed for this repository at the time of publication.
