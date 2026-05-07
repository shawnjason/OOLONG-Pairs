/-
  192_pair_precision_role_split.lean

  Catalog ID 192.  Paper 6 (OOLONG-Pairs), §5.7.

  Author : Shawn Kevin Jason
  Repo   : github.com/shawnjason/OOLONG-Pairs  (forthcoming)

  Role-Split Pair Precision Amplification under Independent
  Endpoint Errors.

  In the role-split admissibility case Pair(u,v) = A(u) ∧ B(v),
  where the two endpoints occupy distinct admissibility roles
  (predicate A for the first endpoint, predicate B for the
  second), under the assumption that endpoint correctness events
  are independent, the joint probability of both endpoints being
  correctly classified equals the product of the per-role
  correctness probabilities:

      P(A_correct ∧ B_correct) = P(A_correct) · P(B_correct)
                               = p_A · p_B.

  This generalizes the symmetric case (191) to asymmetric pair
  predicates where the two roles can have different per-endpoint
  precisions.  The corresponding pair-recall identity has the
  same structure with r_A · r_B replacing p_A · p_B.

  Strategy B formalization: the independence assumption is encoded
  as the explicit hypothesis μ(E_A ∩ E_B) = μ(E_A) · μ(E_B) on the
  measure μ, matching 191's approach for consistency across the
  amplification trio (191, 192, 193).

  Standalone (deliberately so for per-file verification on
  live.lean-lang.org).
-/

import Mathlib

namespace OOLONGPairs.AmplificationRoleSplit

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Role-Split Pair Amplification under Independence** (Paper 6 §5.7).

    For role-A and role-B correctness events `E_A`, `E_B` on a
    probability space with measure `μ`, under independence
    (`μ(E_A ∩ E_B) = μ E_A · μ E_B`) and role-specific marginal
    probabilities `μ E_A = p_A`, `μ E_B = p_B`:

        μ (E_A ∩ E_B) = p_A · p_B.

    Diagnostic interpretation: in the role-split admissibility
    case where the two endpoints have potentially different
    correctness probabilities `p_A` and `p_B`, the per-pair
    precision under independent endpoint errors is the product
    `p_A · p_B`.  This is the asymmetric generalization of the
    symmetric `p²` amplification (191). -/
theorem pair_precision_role_split
    (μ : Measure Ω)
    {E_A E_B : Set Ω}
    (h_indep : μ (E_A ∩ E_B) = μ E_A * μ E_B)
    {p_A p_B : ENNReal}
    (h_A : μ E_A = p_A)
    (h_B : μ E_B = p_B) :
    μ (E_A ∩ E_B) = p_A * p_B := by
  rw [h_indep, h_A, h_B]

end OOLONGPairs.AmplificationRoleSplit