import GreedyThreeSumfree.RBandPrefixExact

namespace GreedyThreeSumfree
namespace RBand

/-- Prefix-gap notation used by the regular `r`-band exact characterization. -/
abbrev FullPrefixGap (r h e t : Nat) : Prop :=
  PrefixGap r h e t

theorem full_prefix_gap_candidate_covered {r h e t : Nat}
    (hp : Params r h e) (ht : FullPrefixGap r h e t) :
    CandidateTripleSumFrom r h e t :=
  prefix_gap_candidate_covered (r := r) (h := h) (e := e) (t := t) hp ht

theorem full_prefix_window_classified {r h e t : Nat}
    (hp : Params r h e)
    (htD : D r h e < t)
    (ht : t <= finalPrefixGapHi r h e) :
    InU r h e t ∨ FullPrefixGap r h e t :=
  prefix_window_classified (r := r) (h := h) (e := e) (t := t) hp htD ht

theorem full_periodic_block_gt_finalPrefixGapHi {r h e q n : Nat}
    (hp : Params r h e) (hq : 1 <= q)
    (hn : InPeriodicBlock r h e q n) :
    finalPrefixGapHi r h e < n :=
  periodic_block_gt_finalPrefixGapHi
    (r := r) (h := h) (e := e) (q := q) (n := n) hp hq hn

theorem full_candidate_le_finalPrefixGapHi_prefix {r h e z : Nat}
    (hp : Params r h e)
    (hz : Candidate r h e z)
    (hzle : z <= finalPrefixGapHi r h e) :
    InPrefix r h e z :=
  candidate_le_finalPrefixGapHi_prefix
    (r := r) (h := h) (e := e) (z := z) hp hz hzle

theorem full_prefix_window_candidate_safe {r h e z : Nat}
    (hp : Params r h e)
    (hzD : D r h e < z)
    (hzle : z <= finalPrefixGapHi r h e)
    (hz : Candidate r h e z) :
    ¬ CandidateTripleSumFrom r h e z :=
  prefix_window_candidate_safe
    (r := r) (h := h) (e := e) (z := z) hp hzD hzle hz

theorem full_prefix_window_characterization {r h e z : Nat}
    (hp : Params r h e)
    (hzD : D r h e < z)
    (hzle : z <= finalPrefixGapHi r h e) :
    Candidate r h e z ↔ ¬ CandidateTripleSumFrom r h e z :=
  regular_rband_prefix_window_characterization
    (r := r) (h := h) (e := e) (z := z) hp hzD hzle

/--
Exact characterization above the finite prefix window, where the positive
periodic decomposition applies.
-/
theorem regular_rband_eventual_characterization_of_large {r h e z : Nat}
    (hp : Params r h e)
    (hzgt : finalPrefixGapHi r h e < z) :
    Candidate r h e z ↔ ¬ CandidateTripleSumFrom r h e z := by
  have hzD : D r h e < z := by
    have hDle : D r h e <= finalPrefixGapHi r h e := by
      have hDge := D_ge_three (r := r) (h := h) (e := e) hp
      unfold finalPrefixGapHi
      omega
    omega
  exact regular_rband_above_seed_characterization
    (r := r) (h := h) (e := e) (z := z) hp hzD

/--
Global regular `r`-band exact characterization above the seed threshold `D`.

The candidate set is exactly the set of integers not represented by a sum of
three distinct smaller candidate elements.
-/
theorem regular_rband_exact_characterization {r h e z : Nat}
    (hp : Params r h e)
    (hzD : D r h e < z) :
    Candidate r h e z ↔ ¬ CandidateTripleSumFrom r h e z :=
  regular_rband_above_seed_characterization
    (r := r) (h := h) (e := e) (z := z) hp hzD

end RBand
end GreedyThreeSumfree
