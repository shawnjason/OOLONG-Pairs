/-
  188_filter_mode_collapse.lean

  Catalog ID 188.  Paper 6 (OOLONG-Pairs), §5.3, §5.6.

  Author : Shawn Kevin Jason
  Repo   : github.com/shawnjason/OOLONG-Pairs  (forthcoming)

  Filter-Mode Collapse Corollary.

  When the candidate set `S` has low pair recall against gold `G`,
  every filter `F ⊆ S` also has low pair recall.  Specifically,
  for any upper bound ε on `pairRecall S G`, the same bound
  applies to `pairRecall F G`:

        pairRecall S G ≤ ε   ⟹   pairRecall F G ≤ ε.

  Diagnostic content: this is the immediate corollary of filter
  recall monotonicity (catalog ID 177).  Filter operations only
  delete from the candidate set, so their recall is bounded above
  by the candidate set's own recall.  Hence when RLM under-
  generates (e.g., the seed-7702 q8 collapse: 378 predicted pairs
  against 97,461 gold pairs), Z2G-M filter-mode GAF inherits the
  collapse because filtering cannot create missing pairs.
  Construction-mode GAF, by contrast, does not depend on the
  candidate set and is not bounded by this corollary.

  Pure finite combinatorics; Standalone (deliberately so for
  per-file verification on live.lean-lang.org).  The auxiliary
  `filter_recall_le` lemma is reproduced here from 177 for self-
  contained verification.
-/

import Mathlib

namespace OOLONGPairs.FilterCollapse

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Pair recall of predicted set `P` against gold set `G`:
    `|P ∩ G| / |G|`.  Returns 0 when `G = ∅`.

    Note: We use `pairRecall` rather than the bare name `recall`
    because `recall` is a reserved command keyword in Lean 4. -/
def pairRecall (P G : Finset (α × β)) : ℚ :=
  ((P ∩ G).card : ℚ) / (G.card : ℚ)

/-- **Filter Recall Monotonicity** (catalog ID 177; reproduced).

    For any candidate set `S`, filter `F ⊆ S`, and gold `G`:

        pairRecall F G ≤ pairRecall S G.

    Filter operations cannot increase recall; this is the
    structural ceiling exploited by the collapse corollary. -/
theorem filter_recall_le
    (S F G : Finset (α × β))
    (h_filter : F ⊆ S) :
    pairRecall F G ≤ pairRecall S G := by
  unfold pairRecall
  have h_inter : F ∩ G ⊆ S ∩ G := by
    intro x hx
    rw [Finset.mem_inter] at hx ⊢
    exact ⟨h_filter hx.1, hx.2⟩
  gcongr

/-- **Filter-Mode Collapse Corollary** (Paper 6 §5.6).

    For any candidate set `S` with bounded recall against gold `G`,
    every filter `F ⊆ S` inherits that bound:

        pairRecall S G ≤ ε   ⟹   pairRecall F G ≤ ε.

    Anchors §5.6's seed-7702 cascade.  When the candidate set
    under-generates (low recall), filter-mode GAF cannot recover.
    The recall ceiling transfers from the candidate set to every
    filter on it, deterministically.  Construction-mode GAF
    avoids this dependency by not requiring a candidate set. -/
theorem filter_mode_collapse
    (S F G : Finset (α × β))
    (h_filter : F ⊆ S)
    (ε : ℚ)
    (h_bound : pairRecall S G ≤ ε) :
    pairRecall F G ≤ ε :=
  le_trans (filter_recall_le S F G h_filter) h_bound

end OOLONGPairs.FilterCollapse