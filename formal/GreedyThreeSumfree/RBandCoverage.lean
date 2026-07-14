import GreedyThreeSumfree.RBandIntervals

namespace GreedyThreeSumfree
namespace RBand

/--
Bounded index selection for shifted pair slices.

If `m` lies in the possible sum-index range `0..2r-2`, then it can be written
as `i+j` with both indices in the regular `r`-band range.
-/
theorem bounded_pair_indices {r m : Nat} (hr : 1 <= r) (hm : m <= 2 * r - 2) :
    ∃ i j : Nat, i < r ∧ j < r ∧ i + j = m := by
  by_cases hm_lt : m < r
  · exact ⟨0, m, by omega, hm_lt, by omega⟩
  · refine ⟨m - (r - 1), r - 1, ?_, ?_, ?_⟩ <;> omega

/--
Bounded shifted-adjacent two-sum witness for every target in a shifted pair
slice whose index lies in the possible regular `r`-band range.
-/
theorem shifted_adjacent_pair_sum_exists_bounded {r h e m t : Nat} (hp : Params r h e)
    (hm : m <= 2 * r - 2) (ht : InShiftedPairSlice r h e m t) :
    ∃ i j x y : Nat,
      i < r ∧
      j < r ∧
      i + j = m ∧
      InH r h e i x ∧
      InInterval (shiftedAdjacentLo r h e j) (shiftedAdjacentHi r h e j) y ∧
      x + y = t := by
  rcases bounded_pair_indices (r := r) (m := m) hp.r_pos hm with
    ⟨i, j, hi, hj, hij⟩
  rcases shifted_adjacent_pair_sum_of_sum
      (r := r) (h := h) (e := e) (i := i) (j := j) (m := m) hp hij ht with
    ⟨x, y, hx, hy, hsum⟩
  exact ⟨i, j, x, y, hi, hj, hij, hx, hy, hsum⟩

/--
Every point in the shifted-adjacent interval for `j` is a translate of a point
of `H_j` by one of the two prefix singleton residues `1` or `h-1`.
-/
theorem shiftedAdjacent_mem_prefix_translate {r h e j y : Nat} (hp : Params r h e)
    (hy : InInterval (shiftedAdjacentLo r h e j) (shiftedAdjacentHi r h e j) y) :
    ∃ eps v : Nat,
      (eps = 1 ∨ eps = h - 1) ∧
      InH r h e j v ∧
      eps + v = y := by
  by_cases hleft : y <= HLo r h e j + h
  · refine ⟨1, y - 1, Or.inl rfl, ?_, ?_⟩
    · unfold InH InInterval HHi
      unfold InInterval shiftedAdjacentLo shiftedAdjacentHi at hy
      constructor <;> omega
    · unfold InInterval shiftedAdjacentLo shiftedAdjacentHi at hy
      omega
  · refine ⟨h - 1, y - (h - 1), Or.inr rfl, ?_, ?_⟩
    · have hD := D_ge_h_add_one (r := r) (h := h) (e := e) hp
      have hL : h + 1 <= HLo r h e j := by
        unfold HLo
        omega
      have hh := hp.h_ge_six
      unfold InH InInterval HHi
      unfold InInterval shiftedAdjacentLo shiftedAdjacentHi at hy
      constructor
      · apply Nat.le_sub_of_add_le
        omega
      · rw [Nat.sub_le_iff_le_add]
        omega
    · have hD := D_ge_h_add_one (r := r) (h := h) (e := e) hp
      have hL : h + 1 <= HLo r h e j := by
        unfold HLo
        omega
      have hh := hp.h_ge_six
      unfold InInterval shiftedAdjacentLo shiftedAdjacentHi at hy
      have hy_ge_eps : h - 1 <= y := by omega
      exact Nat.add_sub_of_le hy_ge_eps

/--
Bounded shifted pair coverage in prefix-pair form: a target in a bounded shifted
slice is `eps + x + v`, where `eps` is one of the two prefix singleton residues
and `x,v` lie in bounded `H` intervals.
-/
theorem shifted_pair_slice_prefix_pair_witness {r h e m t : Nat} (hp : Params r h e)
    (hm : m <= 2 * r - 2) (ht : InShiftedPairSlice r h e m t) :
    ∃ eps i j x v : Nat,
      (eps = 1 ∨ eps = h - 1) ∧
      i < r ∧
      j < r ∧
      i + j = m ∧
      InH r h e i x ∧
      InH r h e j v ∧
      eps + x + v = t := by
  rcases shifted_adjacent_pair_sum_exists_bounded
      (r := r) (h := h) (e := e) (m := m) (t := t) hp hm ht with
    ⟨i, j, x, y, hi, hj, hij, hx, hy, hxy⟩
  rcases shiftedAdjacent_mem_prefix_translate
      (r := r) (h := h) (e := e) (j := j) (y := y) hp hy with
    ⟨eps, v, heps, hv, heq⟩
  refine ⟨eps, i, j, x, v, heps, hi, hj, hij, hx, hv, ?_⟩
  omega

/--
The previous witness split into the two concrete prefix alternatives.
-/
theorem shifted_pair_slice_prefix_pair_cases {r h e m t : Nat} (hp : Params r h e)
    (hm : m <= 2 * r - 2) (ht : InShiftedPairSlice r h e m t) :
    (∃ i j x v : Nat,
      i < r ∧
      j < r ∧
      i + j = m ∧
      InH r h e i x ∧
      InH r h e j v ∧
      1 + x + v = t) ∨
    (∃ i j x v : Nat,
      i < r ∧
      j < r ∧
      i + j = m ∧
      InH r h e i x ∧
      InH r h e j v ∧
      (h - 1) + x + v = t) := by
  rcases shifted_pair_slice_prefix_pair_witness
      (r := r) (h := h) (e := e) (m := m) (t := t) hp hm ht with
    ⟨eps, i, j, x, v, heps, hi, hj, hij, hx, hv, hsum⟩
  rcases heps with rfl | rfl
  · exact Or.inl ⟨i, j, x, v, hi, hj, hij, hx, hv, hsum⟩
  · exact Or.inr ⟨i, j, x, v, hi, hj, hij, hx, hv, hsum⟩

end RBand
end GreedyThreeSumfree
