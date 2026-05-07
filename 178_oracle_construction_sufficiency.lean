/-
  178_oracle_construction_sufficiency.lean

  Catalog ID 178.  Paper 6 (OOLONG-Pairs), §4.7.

  Author : Shawn Kevin Jason
  Repo   : github.com/shawnjason/OOLONG-Pairs  (forthcoming)

  Oracle Admissibility-First Construction Sufficiency Lemma.

  When the exact admissible user set S is known, deterministic
  symmetric pair construction over S emits exactly the gold pair
  set, achieving:

      pairPrecision = pairRecall = 1   (and hence F1 = 1).

  This is the GAF-O ceiling: construction-mode GAF saturates F1
  to 1 whenever endpoint admissibility is identified exactly.
  All non-oracle construction variants are bounded above by this
  ceiling.

  The proof is structured in two layers:
    (i) `self_perfect_metrics` — the abstract content: any
         nonempty pair set evaluated against itself yields
         perfect precision and recall;
    (ii) `oracle_construction_sufficiency` — specialization to
         symmetric construction over an admissible set, which
         tautologically equals itself.

  Pure finite combinatorics; Standalone (deliberately so for
  per-file verification on live.lean-lang.org).
-/

import Mathlib

namespace OOLONGPairs.OracleConstruction

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Pair precision of predicted set `P` against gold set `G`:
    `|P ∩ G| / |P|`.  Returns 0 when `P = ∅`.

    Note: We use `pairPrecision`/`pairRecall` rather than the bare
    names `precision`/`recall` because `recall` is a reserved
    command keyword in Lean 4. -/
def pairPrecision (P G : Finset (α × β)) : ℚ :=
  ((P ∩ G).card : ℚ) / (P.card : ℚ)

/-- Pair recall of predicted set `P` against gold set `G`:
    `|P ∩ G| / |G|`.  Returns 0 when `G = ∅`. -/
def pairRecall (P G : Finset (α × β)) : ℚ :=
  ((P ∩ G).card : ℚ) / (G.card : ℚ)

/-- **Self-Equality gives Perfect Precision and Recall.**

    For any nonempty pair set `G`, evaluating it against itself
    yields perfect precision and perfect recall.  This is the
    abstract content underlying GAF-O's F1 = 1 ceiling: when the
    prediction is identical to the gold (which is what oracle
    construction guarantees), the metrics saturate. -/
theorem self_perfect_metrics
    (G : Finset (α × β))
    (hG_ne : G.Nonempty) :
    pairPrecision G G = 1 ∧ pairRecall G G = 1 := by
  have hG_pos : 0 < G.card := Finset.card_pos.mpr hG_ne
  have hG_ne_q : (G.card : ℚ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp hG_pos
  refine ⟨?_, ?_⟩
  · unfold pairPrecision
    rw [Finset.inter_self]
    exact div_self hG_ne_q
  · unfold pairRecall
    rw [Finset.inter_self]
    exact div_self hG_ne_q

/-- Symmetric pair construction over a finite set with linear order:
    all pairs `(u, v) ∈ S × S` with `u < v`.

    This is the deterministic GAF-O construction operation: given
    an admissible user set `S`, emit every ordered pair from `S`. -/
def constructSym {γ : Type*} [LinearOrder γ] [DecidableEq γ]
    (S : Finset γ) : Finset (γ × γ) :=
  (S ×ˢ S).filter (fun p => p.1 < p.2)

/-- **GAF-O Oracle Construction Sufficiency** (Paper 6 §4.7).

    For any finite admissible user set `S` with a linear order, if
    the gold pair set is `constructSym S` (the symmetric pairs over
    `S`), then deterministic symmetric construction emits exactly
    that gold set.  Therefore:

      pairPrecision (constructSym S) (constructSym S) = 1,
      pairRecall    (constructSym S) (constructSym S) = 1.

    Diagnostic content: this is the GAF-O ceiling — construction-
    mode GAF achieves F1 = 1 whenever endpoint admissibility is
    identified exactly.  All non-oracle construction variants
    (Z1G-S, Z1G-S-Big) are bounded above by this ceiling, with the
    gap quantified by classifier precision/recall on the endpoint
    predicate. -/
theorem oracle_construction_sufficiency
    {γ : Type*} [LinearOrder γ] [DecidableEq γ]
    (S : Finset γ)
    (hS : (constructSym S).Nonempty) :
    pairPrecision (constructSym S) (constructSym S) = 1 ∧
    pairRecall    (constructSym S) (constructSym S) = 1 :=
  self_perfect_metrics (constructSym S) hS

end OOLONGPairs.OracleConstruction