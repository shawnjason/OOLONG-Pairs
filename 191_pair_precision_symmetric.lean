/-
  191_pair_precision_symmetric.lean

  Catalog ID 191.  Paper 6 (OOLONG-Pairs), §5.7.

  Author : Shawn Kevin Jason
  Repo   : github.com/shawnjason/OOLONG-Pairs  (forthcoming)

  Symmetric Pair Precision Amplification under Independent
  Endpoint Errors.

  In the symmetric admissibility case Pair(u,v) = A(u) ∧ A(v),
  under the assumption that endpoint correctness events are
  independent, the joint probability that both endpoints of a
  pair are correctly classified equals the square of the
  per-endpoint correctness probability:

      P(correct_u ∧ correct_v) = P(correct_u) · P(correct_v)
                               = p · p = p².

  This is the probabilistic content of Paper 6 §5.7's
  amplification analysis for the symmetric case.

  Strategy B formalization: the independence assumption is encoded
  as the explicit hypothesis μ(E_u ∩ E_v) = μ(E_u) · μ(E_v) on the
  measure μ, rather than via Mathlib's ProbabilityTheory.IndepSet
  structure (Strategy A).  This conditional framing matches the
  paper's "under approximate independence" wording (an assumption
  on the model, not a constructed property) and decouples the
  proof from particular Mathlib probability-API choices.

  Standalone (deliberately so for per-file verification on
  live.lean-lang.org).
-/

import Mathlib

namespace OOLONGPairs.AmplificationSymmetric

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Symmetric Pair Amplification under Independence** (Paper 6 §5.7).

    For events `E_u`, `E_v` on a probability space with measure `μ`,
    under independence (`μ(E_u ∩ E_v) = μ E_u · μ E_v`) and equal
    marginal probability `μ E_u = μ E_v = p`, the joint probability
    is `p²`:

        μ (E_u ∩ E_v) = p · p.

    Diagnostic interpretation: in the symmetric admissibility case
    where each endpoint shares the same correctness probability `p`
    and endpoint outcomes are independent, the probability that
    both endpoints of a pair are correctly classified is exactly
    `p²`.  This is the per-pair precision amplification result. -/
theorem pair_precision_symmetric
    (μ : Measure Ω)
    {E_u E_v : Set Ω}
    (h_indep : μ (E_u ∩ E_v) = μ E_u * μ E_v)
    {p : ENNReal}
    (h_u : μ E_u = p)
    (h_v : μ E_v = p) :
    μ (E_u ∩ E_v) = p * p := by
  rw [h_indep, h_u, h_v]

end OOLONGPairs.AmplificationSymmetric