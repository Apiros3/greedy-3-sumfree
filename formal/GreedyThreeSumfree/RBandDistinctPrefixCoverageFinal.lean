import GreedyThreeSumfree.RBandDistinctPrefixCoverage

namespace GreedyThreeSumfree
namespace RBand

theorem prefix_singletons_lt_H {r h e i x : Nat} (hp : Params r h e)
    (hx : InH r h e i x) :
    1 < x ∧ h - 1 < x := by
  have hD := D_ge_h_add_one (r := r) (h := h) (e := e) hp
  have hh := hp.h_ge_six
  unfold InH InInterval HLo at hx
  constructor <;> omega

/-- The first part of the final prefix gap has the ordered triple `1 < h-1 < x`. -/
theorem final_prefix_gap_first_distinct_prefix_covered {r h e t : Nat}
    (hp : Params r h e)
    (ht : InInterval (finalPrefixGapLo r h e) (finalPrefixGapFirstHi r h e) t) :
    DistinctPrefixTripleSum r h e t := by
  rcases final_prefix_gap_first_prefix_witness
      (r := r) (h := h) (e := e) (t := t) hp ht with
    ⟨x, hxH, h1, hh1, hx, hsum⟩
  have hh := hp.h_ge_six
  have hlt : h - 1 < x := (prefix_singletons_lt_H (r := r) (h := h) (e := e)
    (i := r - 1) (x := x) hp hxH).2
  exact ⟨1, h - 1, x, h1, hh1, hx, by omega, hlt, hsum⟩

/--
For a shifted-pair slice whose two `H` indices are strictly ordered, the prefix
singleton lies below both `H` witnesses and the interval gap gives the second
ordering relation.
-/
theorem shifted_pair_slice_distinct_prefix_of_lt_indices {r h e i j t : Nat}
    (hp : Params r h e) (hi : i < r) (hj : j < r) (hij : i < j)
    (ht : InShiftedPairSlice r h e (i + j) t) :
    DistinctPrefixTripleSum r h e t := by
  rcases shifted_adjacent_pair_sum_of_indices
      (r := r) (h := h) (e := e) (i := i) (j := j) (t := t) hp ht with
    ⟨x, y, hx, hy, hsum_xy⟩
  rcases shiftedAdjacent_mem_prefix_translate
      (r := r) (h := h) (e := e) (j := j) (y := y) hp hy with
    ⟨eps, v, heps, hv, heq⟩
  have hepsPrefix : InPrefix r h e eps := by
    rcases heps with rfl | rfl
    · exact prefix_one r h e
    · exact prefix_h_sub_one r h e
  have hxPrefix : InPrefix r h e x :=
    prefix_of_inH (r := r) (h := h) (e := e) (i := i) (x := x) hi hx
  have hvPrefix : InPrefix r h e v :=
    prefix_of_inH (r := r) (h := h) (e := e) (i := j) (x := v) hj hv
  have heps_lt_x : eps < x := by
    rcases heps with rfl | rfl
    · exact (prefix_singletons_lt_H (r := r) (h := h) (e := e)
        (i := i) (x := x) hp hx).1
    · exact (prefix_singletons_lt_H (r := r) (h := h) (e := e)
        (i := i) (x := x) hp hx).2
  have hx_lt_v : x < v := by
    have hgap := HHi_lt_HLo_of_lt (r := r) (h := h) (e := e) hp hij
    exact Nat.lt_of_le_of_lt hx.2 (Nat.lt_of_lt_of_le hgap hv.1)
  have hsum : eps + x + v = t := by
    omega
  exact ⟨eps, x, v, hepsPrefix, hxPrefix, hvPrefix, heps_lt_x, hx_lt_v, hsum⟩

/--
Same-index shifted-pair slices are still distinctly covered by switching
between the two prefix singletons and using the distinct two-sum interior of
`H_i`.
-/
theorem shifted_pair_slice_same_index_distinct_prefix {r h e i t : Nat}
    (hp : Params r h e) (hi : i < r)
    (ht : InShiftedPairSlice r h e (i + i) t) :
    DistinctPrefixTripleSum r h e t := by
  have hsliceLo :
      shiftedPairSliceLo r h e (i + i) = 2 * HLo r h e i + 2 := by
    unfold shiftedPairSliceLo HLo
    simp [Nat.left_distrib, Nat.right_distrib]
    omega
  have hsliceHi :
      shiftedPairSliceHi r h e (i + i) = 2 * HLo r h e i + 3 * h - 4 := by
    unfold shiftedPairSliceHi HLo
    simp [Nat.left_distrib, Nat.right_distrib]
    omega
  have hslice :
      InInterval (2 * HLo r h e i + 2) (2 * HLo r h e i + 3 * h - 4) t := by
    unfold InShiftedPairSlice at ht
    simpa [hsliceLo, hsliceHi] using ht
  have hHHi : HHi r h e i = HLo r h e i + h - 1 := rfl
  by_cases hlow : t <= 2 * HHi r h e i
  · have htPair :
        InInterval (2 * HLo r h e i + 1) (2 * HHi r h e i - 1) (t - 1) := by
      rw [hHHi] at hlow
      unfold InInterval
      rw [hHHi]
      have hslo := hslice.1
      constructor <;> omega
    rcases H_pair_sum_distinct_same_index
        (r := r) (h := h) (e := e) (i := i) (t := t - 1) hp htPair with
      ⟨x, y, hx, hy, hxy, hsum_xy⟩
    have hxPrefix : InPrefix r h e x :=
      prefix_of_inH (r := r) (h := h) (e := e) (i := i) (x := x) hi hx
    have hyPrefix : InPrefix r h e y :=
      prefix_of_inH (r := r) (h := h) (e := e) (i := i) (x := y) hi hy
    have h1x : 1 < x := (prefix_singletons_lt_H (r := r) (h := h) (e := e)
      (i := i) (x := x) hp hx).1
    have hsum : 1 + x + y = t := by
      have ht_pos : 1 <= t := by
        have hslo := hslice.1
        omega
      omega
    exact ⟨1, x, y, prefix_one r h e, hxPrefix, hyPrefix, h1x, hxy, hsum⟩
  · have htPair :
        InInterval (2 * HLo r h e i + 1) (2 * HHi r h e i - 1) (t - (h - 1)) := by
      have hgt : 2 * (HLo r h e i + h - 1) < t := by
        have hgt' : 2 * HHi r h e i < t := Nat.lt_of_not_ge hlow
        rwa [hHHi] at hgt'
      have hshi := hslice.2
      unfold InInterval
      rw [hHHi]
      constructor <;> omega
    rcases H_pair_sum_distinct_same_index
        (r := r) (h := h) (e := e) (i := i) (t := t - (h - 1)) hp htPair with
      ⟨x, y, hx, hy, hxy, hsum_xy⟩
    have hxPrefix : InPrefix r h e x :=
      prefix_of_inH (r := r) (h := h) (e := e) (i := i) (x := x) hi hx
    have hyPrefix : InPrefix r h e y :=
      prefix_of_inH (r := r) (h := h) (e := e) (i := i) (x := y) hi hy
    have hepsx : h - 1 < x := (prefix_singletons_lt_H (r := r) (h := h) (e := e)
      (i := i) (x := x) hp hx).2
    have hsum : (h - 1) + x + y = t := by
      have ht_ge : h - 1 <= t := by
        have hHLo : h + 1 <= HLo r h e i := by
          have hD := D_ge_h_add_one (r := r) (h := h) (e := e) hp
          unfold HLo
          omega
        have hslo := hslice.1
        have hD := D_ge_h_add_one (r := r) (h := h) (e := e) hp
        omega
      omega
    exact
      ⟨h - 1, x, y, prefix_h_sub_one r h e, hxPrefix, hyPrefix,
        hepsx, hxy, hsum⟩

/-- The whole shifted-pair chain has ordered distinct prefix witnesses. -/
theorem shiftedPairSlice_chain_distinct_prefix_covered {r h e t : Nat}
    (hp : Params r h e)
    (ht :
      InInterval (2 * D r h e + 2)
        (2 * D r h e + (4 * r - 1) * h - 4) t) :
    DistinctPrefixTripleSum r h e t := by
  rcases shiftedPairSlice_chain_cover_bounded
      (r := r) (h := h) (e := e) (t := t) hp ht with
    ⟨m, hm, hmem⟩
  by_cases hm0 : m = 0
  · have hslice : InShiftedPairSlice r h e (0 + 0) t := by
      simpa [hm0] using hmem
    exact shifted_pair_slice_same_index_distinct_prefix
      (r := r) (h := h) (e := e) (i := 0) (t := t) hp
      (by
        have hr := hp.r_pos
        omega)
      hslice
  · by_cases hmtop : m = 2 * r - 2
    · have hidx : (r - 1) + (r - 1) = 2 * r - 2 := by
        have hr := hp.r_pos
        omega
      have hslice : InShiftedPairSlice r h e ((r - 1) + (r - 1)) t := by
        simpa [hmtop, hidx] using hmem
      exact shifted_pair_slice_same_index_distinct_prefix
        (r := r) (h := h) (e := e) (i := r - 1) (t := t)
        hp
        (by
          have hr := hp.r_pos
          omega)
        hslice
    · have hm_lt_top : m < 2 * r - 2 := by
        omega
      by_cases hm_lt_r : m < r
      · have hm_pos : 0 < m := by
          omega
        have hslice : InShiftedPairSlice r h e (0 + m) t := by
          simpa using hmem
        exact shifted_pair_slice_distinct_prefix_of_lt_indices
          (r := r) (h := h) (e := e) (i := 0) (j := m) (t := t)
          hp (by omega) hm_lt_r hm_pos hslice
      · let i := m - (r - 1)
        have hidx : i + (r - 1) = m := by
          dsimp [i]
          omega
        have hi : i < r := by
          dsimp [i]
          omega
        have hij : i < r - 1 := by
          dsimp [i]
          omega
        have hlast : r - 1 < r := by
          omega
        have hslice : InShiftedPairSlice r h e (i + (r - 1)) t := by
          simpa [hidx] using hmem
        exact shifted_pair_slice_distinct_prefix_of_lt_indices
          (r := r) (h := h) (e := e) (i := i) (j := r - 1) (t := t)
          hp hi hlast hij hslice

/-- Full final-prefix-gap distinct ordered prefix coverage. -/
theorem final_prefix_gap_distinct_prefix_covered {r h e t : Nat}
    (hp : Params r h e)
    (ht : InInterval (finalPrefixGapLo r h e) (finalPrefixGapHi r h e) t) :
    DistinctPrefixTripleSum r h e t := by
  by_cases hfirst : t <= finalPrefixGapFirstHi r h e
  · exact final_prefix_gap_first_distinct_prefix_covered
      (r := r) (h := h) (e := e) (t := t) hp ⟨ht.1, hfirst⟩
  · by_cases hshift : t <= 2 * D r h e + (4 * r - 1) * h - 4
    · have hlo : 2 * D r h e + 2 <= t := by
        have hDnext := D_add_two_le_next_grid (r := r) (h := h) (e := e) hp
        unfold finalPrefixGapFirstHi at hfirst
        omega
      exact shiftedPairSlice_chain_distinct_prefix_covered
        (r := r) (h := h) (e := e) (t := t) hp ⟨hlo, hshift⟩
    · have hlo3 : 2 * D r h e + (4 * r - 1) * h - 3 <= t := by
        have hsucc :
            (2 * D r h e + (4 * r - 1) * h - 4) + 1 <= t :=
          Nat.succ_le_of_lt (Nat.lt_of_not_ge hshift)
        have hlarge : 4 <= 2 * D r h e + (4 * r - 1) * h := by
          have hD := D_ge_three (r := r) (h := h) (e := e) hp
          have hh := hp.h_ge_six
          have hr := hp.r_pos
          omega
        have hstep :
            (2 * D r h e + (4 * r - 1) * h - 4) + 1 =
              2 * D r h e + (4 * r - 1) * h - 3 := by
          omega
        simpa [hstep] using hsucc
      exact final_prefix_gap_third_range_distinct_prefix_covered
        (r := r) (h := h) (e := e) (t := t) hp ⟨hlo3, ht.2⟩

end RBand
end GreedyThreeSumfree
