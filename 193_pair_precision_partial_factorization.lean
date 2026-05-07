/-
  193_pair_precision_partial_factorization.lean

  Catalog ID 193.  Paper 6 (OOLONG-Pairs), §5.7.

  Author : Shawn Kevin Jason
  Repo   : github.com/shawnjason/OOLONG-Pairs  (forthcoming)

  Partially Factorized Pair Precision Amplification under
  Independent Endpoint Errors and Residual Pair-Level Relation.

  In the partially factorized admissibility case
  Pair(u,v) = A(u) ∧ B(v) ∧ R(u,v), where the pair predicate
  decomposes into a role-A endpoint condition, a role-B endpoint
  condition, and a residual pair-level relation R ⊆ A × B with
  density ρ = |R| / |A × B|, under the joint-independence
  assumption that the role events and relation event factor as
  μ(E_A ∩ E_B ∩ E_R) = μ E_A · μ E_B · μ E_R, the joint
  probability of correct classification on all three components
  is the product of the per-component probabilities:

      P(A_correct ∧ B_correct ∧ R_holds) = p_A · p_B · ρ.

  Diagnostic content: this is the §5.7 result that endpoint-only
  classification cannot exceed the relation-density ceiling.
  Even with perfect endpoint roles (p_A = p_B = 1), the pair
  precision is bounded above by ρ < 1 whenever R is a strict
  subset of A × B.  This is the probabilistic shadow of catalog
  ID 195's deterministic Endpoint-Factorization Insufficiency
  lemma.

  Strategy B formalization: independence as a direct hypothesis
  on the measure (matching 191 and 192).  Generalizes the
  symmetric (191) and role-split (192) cases by introducing the
  third factor ρ for residual pair-level structure.

  Standalone (deliberately so for per-file verification on
  live.lean-lang.org).
-/

import Mathlib

namespace OOLONGPairs.AmplificationPartialFactorization

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Partially Factorized Pair Amplification under Independence**
    (Paper 6 §5.7).

    For role-A correctness, role-B correctness, and pair-relation
    events `E_A`, `E_B`, `E_R` on a probability space with measure
    `μ`, under joint independence
    (`μ(E_A ∩ E_B ∩ E_R) = μ E_A · μ E_B · μ E_R`) and marginal
    probabilities `p_A`, `p_B`, `ρ`:

        μ (E_A ∩ E_B ∩ E_R) = p_A · p_B · ρ.

    Diagnostic interpretation: pair-level precision under
    independent endpoint errors and residual relation structure
    factors as the product of per-component probabilities.  When
    the relation density ρ < 1, this strictly bounds pair
    precision below 1 even with perfect endpoint classification —
    the probabilistic counterpart to ID 195's deterministic
    insufficiency lemma. -/
theorem pair_precision_partial_factorization
    (μ : Measure Ω)
    {E_A E_B E_R : Set Ω}
    (h_indep : μ (E_A ∩ E_B ∩ E_R) = μ E_A * μ E_B * μ E_R)
    {p_A p_B ρ : ENNReal}
    (h_A : μ E_A = p_A)
    (h_B : μ E_B = p_B)
    (h_R : μ E_R = ρ) :
    μ (E_A ∩ E_B ∩ E_R) = p_A * p_B * ρ := by
  rw [h_indep, h_A, h_B, h_R]

end OOLONGPairs.AmplificationPartialFactorization