/-
  177_filter_recall_preservation.lean

  Catalog ID 177.  Paper 6 (OOLONG-Pairs), §4.6, §5.3.

  Author : Shawn Kevin Jason
  Repo   : github.com/shawnjason/OOLONG-Pairs  (forthcoming)

  Filter Recall Preservation Lemmas.

  Two structural facts about filter operations on candidate sets:

    (i)  Filter monotonicity: any filter `F ⊆ P` cannot increase
         pair recall against any gold set `G`,
            pairRecall F G ≤ pairRecall P G.
    (ii) Oracle filter preservation: the oracle filter
         `F* := P ∩ G` removes only items outside `G`, hence
         preserves recall exactly,
            pairRecall (P ∩ G) G = pairRecall P G.

  Together these formalize §4.6's diagnostic that Z2G-F removes
  all false positives over Z2 candidates but cannot add missing
  pairs (recall stays equal to candidate-set true-positive
  coverage).  This is the lemma that anchors §5.3's filter-vs-
  construction distinction: filter-mode GAF is recall-bounded by
  its candidate set, while construction-mode GAF is not.

  Pure finite combinatorics; Standalone (deliberately so for
  per-file verification on live.lean-lang.org).
-/

import Mathlib

namespace OOLONGPairs.FilterRecall

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Pair recall of predicted set `P` against gold set `G`:
    `|P ∩ G| / |G|`.  Returns 0 when `G = ∅`.

    Note: We use `pairRecall` rather than the bare name `recall`
    because `recall` is a reserved command keyword in Lean 4. -/
def pairRecall (P G : Finset (α × β)) : ℚ :=
  ((P ∩ G).card : ℚ) / (G.card : ℚ)

/-- **Filter Recall Monotonicity** (Paper 6 §5.3).

    For any predicted set `P`, filter `F ⊆ P`, and gold `G`,
    pair recall is monotone in the prediction:

      pairRecall F G ≤ pairRecall P G.

    Filter operations only delete from `P` (never add), so
    they cannot increase recall.  This is the structural content
    of "filter mode cannot create missing candidates." -/
theorem filter_recall_le
    (P F G : Finset (α × β))
    (h_filter : F ⊆ P) :
    pairRecall F G ≤ pairRecall P G := by
  unfold pairRecall
  -- F ⊆ P  ⇒  F ∩ G ⊆ P ∩ G  (proven inline via membership for
  -- robustness against `inter_subset_inter` API variation).
  have h_inter : F ∩ G ⊆ P ∩ G := by
    intro x hx
    rw [Finset.mem_inter] at hx ⊢
    exact ⟨h_filter hx.1, hx.2⟩
  -- Lift to ℚ and use division monotonicity.  `gcongr` decomposes
  -- the inequality, finds `h_inter` in scope, and closes all
  -- side goals (including the cardinality and cast steps) automatically.
  gcongr

/-- **Oracle Filter Recall Preservation** (Paper 6 §4.6).

    The oracle filter `P ∩ G` keeps exactly the items in `P` that
    lie inside the gold `G`, removing only false positives.
    Recall is preserved exactly:

      pairRecall (P ∩ G) G = pairRecall P G.

    Equivalent reading: any filter that removes only items outside
    the gold preserves recall.  Hence the maximum recall achievable
    by any filter on `P` equals the recall of `P` itself —
    filter-mode GAF is recall-ceilinged at the candidate set's
    own recall. -/
theorem oracle_filter_recall_eq
    (P G : Finset (α × β)) :
    pairRecall (P ∩ G) G = pairRecall P G := by
  unfold pairRecall
  -- (P ∩ G) ∩ G  =  P ∩ (G ∩ G)  =  P ∩ G.
  have h_inter : (P ∩ G) ∩ G = P ∩ G := by
    rw [Finset.inter_assoc, Finset.inter_self]
  rw [h_inter]

end OOLONGPairs.FilterRecall