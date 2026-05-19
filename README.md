# OOLONG-Pairs — Lean Proofs

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20062396.svg)](https://doi.org/10.5281/zenodo.20062396)

Machine-checked Lean 4 proofs for:

**"From Recursive Scaffolding to Admissibility-First Construction: Mechanism, Stability, and Failure-Mode Decomposition on OOLONG-Pairs"**

Paper DOI (concept, always resolves to latest): [10.5281/zenodo.20277804](https://doi.org/10.5281/zenodo.20277804)

---

## Author

Shawn Kevin Jason — Independent Researcher, Las Vegas, NV
ORCID: [![ORCID iD](https://orcid.org/sites/default/files/images/orcid_16x16.png)](https://orcid.org/0009-0003-9208-1556) [0009-0003-9208-1556](https://orcid.org/0009-0003-9208-1556)

---

## What This Repository Contains

Seven standalone Lean 4 proof files covering the principal formal results of the paper. The proofs split into four groups: a **filter-mode structural** group establishing that filter operations cannot increase pair recall against any gold set and that filter-mode GAF therefore inherits its candidate set's recall ceiling (so when candidate generation under-generates, filter-mode collapses with it); a **construction-mode sufficiency** group establishing the GAF-O ceiling — that deterministic admissibility-first construction over an exactly identified admissible set yields perfect precision and recall; a **diagnostic ceiling** group establishing the Endpoint-Factorization Insufficiency Lemma — when the gold relation is a strict subset of the role product, endpoint-only construction necessarily over-emits and the precision ceiling is exactly the role-product density; and an **amplification analysis** group establishing the probabilistic factorization of joint pair-correctness probabilities under independent endpoint errors, in three cases (symmetric, role-split, and partially factorized).

Each file is independent and verifies against the current Mathlib release.

---

## Files

### Filter-Mode Structural

**`177_filter_recall_preservation.lean`** — Filter Recall Preservation (Monotonicity and Oracle Preservation)
Two structural facts about filter operations on candidate sets, in a single file. The monotonicity direction (`filter_recall_le`): for any candidate set `S`, filter `F ⊆ S`, and gold `G`, `pairRecall F G ≤ pairRecall S G`. Filter operations only delete from the candidate set, so they cannot increase recall against any gold set. The preservation direction (`oracle_filter_recall_eq`): the oracle filter `P ∩ G` — which keeps exactly those candidates that lie inside the gold — preserves recall exactly, so `pairRecall (P ∩ G) G = pairRecall P G`. Together these formalize §4.6's diagnostic that filter-mode GAF (Z2G-F oracle, Z2G-M model-based) removes false positives but cannot create missing pairs, and anchor §5.3's filter-vs-construction distinction. The maximum recall achievable by any filter on `P` is exactly `pairRecall P G` itself; filter-mode is recall-ceilinged at the candidate set's own recall.

**`188_filter_mode_collapse.lean`** — Filter-Mode Collapse Corollary
Immediate corollary of filter recall monotonicity: for any candidate set `S` with `pairRecall S G ≤ ε`, every filter `F ⊆ S` inherits the bound, so `pairRecall F G ≤ ε`. Anchors §5.6's seed-7702 cascade. When RLM under-generated q8 (producing only 378 predicted pairs against 97,461 gold pairs, F1 ≈ 0.0077), Z2G-M filter-mode GAF inherited the collapse because filtering cannot create missing pairs — the recall ceiling transfers from candidate set to filter deterministically. Construction-mode GAF (Z1G-S) avoids this dependency by not requiring a candidate set in the first place.

### Construction-Mode Sufficiency

**`178_oracle_construction_sufficiency.lean`** — Oracle Admissibility-First Construction Sufficiency (GAF-O Ceiling)
Two-layer proof of the construction-mode upper bound. The abstract content (`self_perfect_metrics`) is that any nonempty pair set evaluated against itself yields `pairPrecision = pairRecall = 1`; the construction specialization (`oracle_construction_sufficiency`) instantiates this for symmetric oracle construction `constructSym S := (S ×ˢ S).filter (·.1 < ·.2)` over a linearly-ordered admissible set `S`. The GAF-O ceiling formalized: when endpoint admissibility is identified exactly, deterministic symmetric construction emits exactly the gold pair set, saturating F1 to 1. All non-oracle construction variants (Z1G-S with GPT-5-mini classifier, Z1G-S-Big with GPT-5 classifier) are bounded above by this ceiling, with the gap quantified by classifier precision and recall on the endpoint predicate.

### Diagnostic Ceiling

**`195_endpoint_factorization_insufficiency.lean`** — Endpoint-Factorization Insufficiency Lemma
For finite sets `A : Finset α`, `B : Finset β`, and a strict nonempty subset `R ⊂ A ×ˢ B`: the prediction `C := A ×ˢ B` against gold `R` satisfies `(A ×ˢ B) \ R` nonempty, `pairRecall (A ×ˢ B) R = 1`, `pairPrecision (A ×ˢ B) R = |R| / |A ×ˢ B|`, and `pairPrecision (A ×ˢ B) R < 1`. Diagnostic content: endpoint summaries are sufficient only when the admissible relation factors through them. If the true predicate has the form `A(u) ∧ B(v) ∧ R(u,v)` with `R` strictly contained in `A ×ˢ B`, then endpoint-only construction necessarily over-emits at recall = 1, and the precision ceiling is exactly the role-product density `|R| / |A ×ˢ B|`. The formal companion to §5.7's q15 seed-7702 role-product diagnostic, where Big construction observed precision ≈ 585/1037 ≈ 0.564 against gold density ≈ 593/1043 ≈ 0.568 — empirical hit on the predicted ceiling within rounding.

### Amplification Analysis

**`191_pair_precision_symmetric.lean`** — Symmetric Pair Precision Amplification under Independence
For events `E_u`, `E_v` on a measure space with shared marginal probability `p` and joint independence (`μ(E_u ∩ E_v) = μ E_u · μ E_v`), the joint probability is `p²`. In the symmetric admissibility case `Pair(u,v) = A(u) ∧ A(v)`, where each endpoint shares the same per-endpoint correctness probability and endpoint outcomes are independent, the per-pair precision under independent endpoint errors is exactly `p²`. Independence is encoded as the explicit hypothesis `μ(E_u ∩ E_v) = μ E_u · μ E_v` (Strategy B formalization), matching the paper's "under approximate independence" framing as an assumption rather than a constructed property.

**`192_pair_precision_role_split.lean`** — Role-Split Pair Precision Amplification under Independence
Asymmetric generalization of 191 to `Pair(u,v) = A(u) ∧ B(v)` where the two endpoints occupy distinct admissibility roles with potentially different correctness probabilities `p_A` and `p_B`. Under joint independence and role-specific marginals, the joint probability factors as `p_A · p_B`. The pair-recall identity has the same structure with role-specific recalls `r_A · r_B` replacing the precisions.

**`193_pair_precision_partial_factorization.lean`** — Partially Factorized Pair Precision Amplification under Independence
Generalizes 192 to `Pair(u,v) = A(u) ∧ B(v) ∧ R(u,v)` where `R` is a residual pair-level relation with density `ρ = |R|/|A × B|`. Under three-way joint independence (`μ(E_A ∩ E_B ∩ E_R) = μ E_A · μ E_B · μ E_R`) and marginals `p_A`, `p_B`, `ρ`, the joint probability factors as `p_A · p_B · ρ`. Probabilistic shadow of 195's deterministic Endpoint-Factorization Insufficiency Lemma: even with perfect endpoint role recovery (`p_A = p_B = 1`), the pair-precision factor is bounded above by `ρ < 1` whenever `R` is a strict subset of `A × B`. The two lemmas (deterministic combinatorial 195 and probabilistic factorization 193) together capture the §5.7 ceiling diagnostic from both directions.

---

## Mapping to the Paper

| Paper Result | File | Lean Theorem |
|---|---|---|
| Filter Recall Monotonicity (§5.3 — filter-mode cannot create missing candidates) | `177_filter_recall_preservation.lean` | `filter_recall_le` |
| Oracle Filter Recall Preservation (§4.6 — Z2G-F removes false positives only) | `177_filter_recall_preservation.lean` | `oracle_filter_recall_eq` |
| Filter-Mode Collapse Corollary (§5.6 — seed-7702 q8 cascade) | `188_filter_mode_collapse.lean` | `filter_mode_collapse` |
| Oracle Construction Sufficiency / GAF-O Ceiling (§4.7) | `178_oracle_construction_sufficiency.lean` | `oracle_construction_sufficiency`, `self_perfect_metrics` |
| Endpoint-Factorization Insufficiency Lemma (§5.7 — q15 role-product diagnostic) | `195_endpoint_factorization_insufficiency.lean` | `endpoint_factorization_insufficiency` |
| Symmetric Pair Precision Amplification (§5.7 — `≈ p²`) | `191_pair_precision_symmetric.lean` | `pair_precision_symmetric` |
| Role-Split Pair Precision Amplification (§5.7 — `≈ p_A · p_B`) | `192_pair_precision_role_split.lean` | `pair_precision_role_split` |
| Partially Factorized Pair Precision Amplification (§5.7 — `≈ p_A · p_B · ρ`) | `193_pair_precision_partial_factorization.lean` | `pair_precision_partial_factorization` |

---

## How to Verify

1. Open [live.lean-lang.org](https://live.lean-lang.org)
2. Confirm the dropdown in the upper right is set to **Latest Mathlib**
3. Paste the contents of any `.lean` file into the editor
4. Wait for checking to complete — "No goals" on each theorem and no errors in the Problems pane confirms verification

Each file is independent; no cross-file imports are required.

---

## Scope

These proofs verify the formal logical structure of the principal results: the filter-mode structural facts (recall preservation and collapse), the construction-mode sufficiency ceiling, the deterministic endpoint-factorization insufficiency lemma, and the probabilistic amplification factorization in three pair-predicate cases (symmetric, role-split, partially factorized). They do not establish:

- The full empirical decomposition reported in the paper — the canonical 20-query seed-7700 run, the three-seed representative subset on q8/q9/q11/q15/q20, the per-query operating-point matrix, the q15 seed-7702 pair-set decomposition showing role-product mechanism convergence, and the cost/routing analyses
- The bottleneck taxonomy in §5.9 (endpoint-classifier noise, false-positive amplification, residual pair-level relation structure, verifier miscalibration, candidate-generation collapse, benchmark/seed validity, cost/routing) as predictive claims; the bottleneck framework is a diagnostic decomposition, not a theorem
- The conjectural predictions in §6 and §8 about non-factorizing predicates, learned feasibility classifiers, calibrated verifiers, and generalization beyond OOLONG-Pairs
- The 191/192/193 amplification claims in their full probabilistic-model construction; these files formalize the conditional factorization `μ(joint) = ∏ marginals` under independence as a hypothesis on the measure, leaving the construction of a specific Bernoulli endpoint-error model to the paper's informal framing

---

## Related Work

The foundational projection-theoretic result underlying the framework is developed in:

*Projection Insufficiency and Trajectory Realization: A Unified Constraint-Based Framework for Bounded Systems* — [DOI: 10.5281/zenodo.19633241](https://doi.org/10.5281/zenodo.19633241) (Lean proofs: [10.5281/zenodo.19687629](https://doi.org/10.5281/zenodo.19687629))

The forward-case impossibility result establishing the divergence kernel and arithmetic-witness machinery is developed in:

*The Non-Locality of Extendability: An Impossibility Theorem for Bounded Information Systems, with Applications to Generative Sequential Systems* — [DOI: 10.5281/zenodo.19688367](https://doi.org/10.5281/zenodo.19688367) (Lean proofs: [10.5281/zenodo.19687799](https://doi.org/10.5281/zenodo.19687799))

The stochastic extension establishing the admissibility-dynamics framework is developed in:

*Inconsistency Accumulation in Forward-Local Sequential Policies: A Lower Bound under Delayed Constraints* — [DOI: 10.5281/zenodo.19688628](https://doi.org/10.5281/zenodo.19688628) (Lean proofs: [10.5281/zenodo.19687094](https://doi.org/10.5281/zenodo.19687094))

The language-model specialization providing the structural-ceiling and certification-depth context for bounded-context generative systems is developed in:

*Language Model Hallucinations: An Impossibility Theorem and Its Architectural Consequences* — [DOI: 10.5281/zenodo.19715059](https://doi.org/10.5281/zenodo.19715059) (Lean proofs: [10.5281/zenodo.20059771](https://doi.org/10.5281/zenodo.20059771))

The theoretical predecessor analyzing Recursive Language Models through the admissibility-dynamics framework — for which the present paper is the empirical companion — is developed in:

*Recursive Language Models Through the Admissibility-Dynamics Framework: A Principled Theory of When Recursive Scaffolding Succeeds* — [DOI: 10.5281/zenodo.19753549](https://doi.org/10.5281/zenodo.19753549) (Lean proofs: [10.5281/zenodo.20060154](https://doi.org/10.5281/zenodo.20060154))

---

## License

MIT
