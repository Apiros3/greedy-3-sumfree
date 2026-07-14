import GreedyThreeSumfree.TransitionDenseCapCoveragePredicates

namespace GreedyThreeSumfree
namespace TransitionDenseCap

theorem coveredBySmallerCandidates_one_add_twoE_of_restrictedTwoQ0Sum
    {r h t n : Nat} (hp : Params r h t)
    (hn : RestrictedTwoQ0Sum r h t n) :
    CoveredBySmallerCandidates r h t (2 * D r h t + 1 + n) := by
  rcases hn with ⟨u, v, hu, hv, huv, hsum⟩
  refine
    ⟨1, D r h t + u, D r h t + v,
      one_candidate r h t,
      inE_candidate (D_add_inE_of_inQ hu),
      inE_candidate (D_add_inE_of_inQ hv),
      ?_, ?_, ?_, ?_⟩
  · have hD := D_ge_three hp
    omega
  · omega
  · have hD := D_ge_three hp
    omega
  · omega

theorem coveredBySmallerCandidates_hSubOne_add_twoE_of_restrictedTwoQ0Sum
    {r h t m : Nat} (hp : Params r h t)
    (hm : RestrictedTwoQ0Sum r h t m) :
    CoveredBySmallerCandidates r h t (2 * D r h t + (h - 1) + m) := by
  rcases hm with ⟨u, v, hu, hv, huv, hsum⟩
  refine
    ⟨h - 1, D r h t + u, D r h t + v,
      h_sub_one_candidate r h t,
      inE_candidate (D_add_inE_of_inQ hu),
      inE_candidate (D_add_inE_of_inQ hv),
      ?_, ?_, ?_, ?_⟩
  · unfold D
    have hr := hp.r_pos
    have hh := hp.h_ge_six
    have hcoef : 1 <= 2 * r := by omega
    have hmul : h <= 2 * r * h := by
      simpa [Nat.one_mul] using Nat.mul_le_mul_right h hcoef
    omega
  · omega
  · have hD := D_ge_three hp
    have hh := hp.h_ge_six
    omega
  · omega

theorem coveredBySmallerCandidates_pair_or_shift_of_restrictedTwoQ0SumOrShift
    {r h t n : Nat} (hp : Params r h t)
    (hn : RestrictedTwoQ0SumOrShift r h t n) :
    CoveredBySmallerCandidates r h t (2 * D r h t + 1 + n) := by
  rcases hn with hn | hn
  · exact
      coveredBySmallerCandidates_one_add_twoE_of_restrictedTwoQ0Sum
        (r := r) (h := h) (t := t) (n := n) hp hn
  · rcases hn with ⟨m, hm, hshift⟩
    have htarget :
        2 * D r h t + 1 + n = 2 * D r h t + (h - 1) + m := by
      rw [hshift]
      have hh := hp.h_ge_six
      omega
    rw [htarget]
    exact
      coveredBySmallerCandidates_hSubOne_add_twoE_of_restrictedTwoQ0Sum
        (r := r) (h := h) (t := t) (m := m) hp hm

theorem coveredBySmallerCandidates_threeE_of_restrictedThreeQ0Sum
    {r h t n : Nat} (hp : Params r h t)
    (hn : RestrictedThreeQ0Sum r h t n) :
    CoveredBySmallerCandidates r h t (3 * D r h t + n) := by
  rcases hn with ⟨u, v, w, hu, hv, hw, huv, hvw, hsum⟩
  refine
    ⟨D r h t + u, D r h t + v, D r h t + w,
      inE_candidate (D_add_inE_of_inQ hu),
      inE_candidate (D_add_inE_of_inQ hv),
      inE_candidate (D_add_inE_of_inQ hw),
      ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · have hD := D_ge_three hp
    omega
  · omega

/--
Pointwise candidate coverage from
`(1 + ^2E) ∪ ((h-1) + ^2E) = [2D+2, 4D+h]`.
-/
theorem coveredBySmallerCandidates_prefix_pair_interval {r h t target : Nat}
    (hp : Params r h t)
    (htarget : InInterval (2 * D r h t + 2) (4 * D r h t + h) target) :
    CoveredBySmallerCandidates r h t target := by
  let n := target - (2 * D r h t + 1)
  have hnInterval : InInterval 1 (2 * D r h t + h - 1) n := by
    unfold InInterval at *
    dsimp [n]
    constructor
    · omega
    · omega
  have hsum : target = 2 * D r h t + 1 + n := by
    dsimp [n]
    unfold InInterval at htarget
    omega
  rw [hsum]
  exact
    coveredBySmallerCandidates_pair_or_shift_of_restrictedTwoQ0SumOrShift
      (r := r) (h := h) (t := t) (n := n) hp
      (restrictedTwoQ0Sum_or_shift_dense_cap_coverage
        (r := r) (h := h) (t := t) (n := n) hp hnInterval)

/-- Pointwise candidate coverage from `^3E = [3D+3, 6D]`. -/
theorem coveredBySmallerCandidates_prefix_triple_interval {r h t target : Nat}
    (hp : Params r h t)
    (htarget : InInterval (3 * D r h t + 3) (6 * D r h t) target) :
    CoveredBySmallerCandidates r h t target := by
  let n := target - 3 * D r h t
  have hnInterval : InInterval 3 (3 * D r h t) n := by
    unfold InInterval at *
    dsimp [n]
    constructor
    · omega
    · omega
  have hsum : target = 3 * D r h t + n := by
    dsimp [n]
    unfold InInterval at htarget
    omega
  rw [hsum]
  exact
    coveredBySmallerCandidates_threeE_of_restrictedThreeQ0Sum
      (r := r) (h := h) (t := t) (n := n) hp
      (restrictedThreeQ0Sum_dense_cap_pointwise
        (r := r) (h := h) (t := t) (n := n) hp hnInterval)

/--
Dense-cap prefix gap coverage after `E`: every target in `[2D+2, 6D]` is a sum
of three distinct smaller candidates.
-/
theorem coveredBySmallerCandidates_dense_cap_prefix_gap {r h t target : Nat}
    (hp : Params r h t)
    (htarget : InInterval (2 * D r h t + 2) (6 * D r h t) target) :
    CoveredBySmallerCandidates r h t target := by
  by_cases hpair : target <= 4 * D r h t + h
  · exact
      coveredBySmallerCandidates_prefix_pair_interval
        (r := r) (h := h) (t := t) (target := target) hp
        ⟨htarget.1, hpair⟩
  · have htriple_lo : 3 * D r h t + 3 <= target := by
      have hD := D_ge_three hp
      have hh := hp.h_ge_six
      omega
    exact
      coveredBySmallerCandidates_prefix_triple_interval
        (r := r) (h := h) (t := t) (target := target) hp
        ⟨htriple_lo, htarget.2⟩

end TransitionDenseCap
end GreedyThreeSumfree
