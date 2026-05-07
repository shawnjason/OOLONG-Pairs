/-
  195_endpoint_factorization_insufficiency.lean

  Catalog ID 195.  Paper 6 (OOLONG-Pairs), §5.7.

  Author : Shawn Kevin Jason
  Repo   : github.com/shawnjason/OOLONG-Pairs  (forthcoming)

  Endpoint-Factorization Insufficiency Lemma.

  When the predicted pair set is the full Cartesian role-product
  C := A ×ˢ B and the gold admissibility relation R is a strict,
  nonempty subset of C, then:

      (i)   C \ R   is nonempty,
      (ii)  recall    (C, R) = 1, and
      (iii) precision (C, R) = |R| / |C|  <  1.

  Diagnostic content: whenever the true admissible relation does
  not exhaust the endpoint product, endpoint-only construction
  over-emits, and the precision ceiling is exactly |R| / |A ×ˢ B|.

  This is the formal companion to Paper 6 §5.7's q15 role-product
  diagnostic, which observed precision ≈ 0.564 ≈ |gold|/|role-product|
  ≈ 0.568 — the empirical hit on the predicted ceiling.

  Pure finite combinatorics; Standalone (deliberately so for
  per-file verification on live.lean-lang.org).
-/

import Mathlib

namespace OOLONGPairs.EndpointFactorization

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Pair precision of predicted set `P` against gold set `G`:
    `|P ∩ G| / |P|`.  Returns 0 when `P = ∅`. -/
def pairPrecision (P G : Finset (α × β)) : ℚ :=
  ((P ∩ G).card : ℚ) / (P.card : ℚ)

/-- Pair recall of predicted set `P` against gold set `G`:
    `|P ∩ G| / |G|`.  Returns 0 when `G = ∅`.

    Note: We avoid the bare name `recall` because it is a
    reserved command keyword in Lean 4. -/
def pairRecall (P G : Finset (α × β)) : ℚ :=
  ((P ∩ G).card : ℚ) / (G.card : ℚ)

/-- **Endpoint-Factorization Insufficiency** (Paper 6 §5.7).

    For finite sets `A : Finset α`, `B : Finset β`, and a strict
    nonempty subset `R ⊂ A ×ˢ B`:

      • `(A ×ˢ B) \ R` is nonempty,
      • `pairRecall    (A ×ˢ B) R = 1`,
      • `pairPrecision (A ×ˢ B) R = |R| / |A ×ˢ B|`, and
      • `pairPrecision (A ×ˢ B) R < 1`.

    Equivalently: endpoint summaries are sufficient only when the
    admissible relation factors through them.  If the true predicate
    has the form `A(u) ∧ B(v) ∧ R(u,v)` with `R` strict in `A ×ˢ B`,
    then endpoint construction necessarily under-precises by exactly
    the role-product density. -/
theorem endpoint_factorization_insufficiency
    (A : Finset α) (B : Finset β) (R : Finset (α × β))
    (hR_strict   : R ⊂ A ×ˢ B)
    (hR_nonempty : R.Nonempty) :
    ((A ×ˢ B) \ R).Nonempty ∧
    pairRecall    (A ×ˢ B) R = 1 ∧
    pairPrecision (A ×ˢ B) R = (R.card : ℚ) / ((A ×ˢ B).card : ℚ) ∧
    pairPrecision (A ×ˢ B) R < 1 := by
  -- Project the components of `R ⊂ A ×ˢ B` without consuming it,
  -- so it remains available for `Finset.card_lt_card` below.
  have hRsub : R ⊆ A ×ˢ B := hR_strict.1
  have hRne  : ¬ (A ×ˢ B) ⊆ R := hR_strict.2
  -- (i) Strict subset ⇒ set difference is nonempty.
  have h_diff : ((A ×ˢ B) \ R).Nonempty := by
    rw [Finset.sdiff_nonempty]
    exact hRne
  -- R ⊆ A ×ˢ B  ⇒  (A ×ˢ B) ∩ R = R.
  have h_inter : (A ×ˢ B) ∩ R = R := Finset.inter_eq_right.mpr hRsub
  -- |R| > 0  (R is nonempty).
  have hRpos : 0 < R.card := Finset.card_pos.mpr hR_nonempty
  have hR_ne_q : (R.card : ℚ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp hRpos
  -- |R| < |A ×ˢ B|  (strict inclusion ⇒ strict cardinality).
  have hRlt : R.card < (A ×ˢ B).card := Finset.card_lt_card hR_strict
  -- |A ×ˢ B| > 0  in ℚ.
  have hCpos_q : (0 : ℚ) < ((A ×ˢ B).card : ℚ) := by
    exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) hRlt
  refine ⟨h_diff, ?_, ?_, ?_⟩
  · -- pairRecall (A ×ˢ B) R = 1
    unfold pairRecall
    rw [h_inter]
    exact div_self hR_ne_q
  · -- pairPrecision (A ×ˢ B) R = |R| / |A ×ˢ B|
    unfold pairPrecision
    rw [h_inter]
  · -- pairPrecision (A ×ˢ B) R < 1
    unfold pairPrecision
    rw [h_inter, div_lt_one hCpos_q]
    exact_mod_cast hRlt

end OOLONGPairs.EndpointFactorization