import GreedyThreeSumfree.BoundaryRBandCoverage
import GreedyThreeSumfree.IntervalSumWitnesses

namespace GreedyThreeSumfree
namespace BoundaryRBand

/-- Ordered distinct triple sum from the boundary-band prefix. -/
def DistinctPrefixTripleSum (r h t : Nat) : Prop :=
  ∃ x y z : Nat,
    InPrefix r h x ∧
    InPrefix r h y ∧
    InPrefix r h z ∧
    x < y ∧
    y < z ∧
    x + y + z = t

theorem distinctPrefixTripleSum_of_distinct_inU {r h t : Nat}
    (ht :
      ∃ x y z : Nat,
        InU r h x ∧
        InU r h y ∧
        InU r h z ∧
        x < y ∧
        y < z ∧
        x + y + z = t) :
    DistinctPrefixTripleSum r h t := by
  rcases ht with ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩
  exact
    ⟨x, y, z, prefix_of_inU hx, prefix_of_inU hy, prefix_of_inU hz,
      hxy, hyz, hsum⟩

theorem HLo_lt_HHi {r h i : Nat} (hp : Params r h) :
    HLo r h i < HHi r h i := by
  have hh := hp.h_ge_six
  unfold HHi
  omega

theorem HHi_lt_HLo_of_lt {r h i j : Nat} (hp : Params r h) (hij : i < j) :
    HHi r h i < HLo r h j := by
  have hh := hp.h_ge_six
  have hij_le : i + 1 <= j := by omega
  have hcoef : 2 * (i + 1) <= 2 * j := Nat.mul_le_mul_left 2 hij_le
  have hprod : 2 * (i + 1) * h <= 2 * j * h :=
    Nat.mul_le_mul_right h hcoef
  have hprod_eq : 2 * (i + 1) * h = 2 * i * h + 2 * h := by
    simp [Nat.left_distrib, Nat.right_distrib]
  rw [hprod_eq] at hprod
  have hhi_bound : HHi r h i < D r h + 2 * i * h + 2 * h := by
    unfold HHi HLo
    omega
  have hlo_bound : D r h + 2 * i * h + 2 * h <= HLo r h j := by
    unfold HLo
    omega
  exact Nat.lt_of_lt_of_le hhi_bound hlo_bound

theorem prefix_singletons_lt_H {r h i x : Nat} (hp : Params r h)
    (hx : InH r h i x) :
    1 < x ∧ h - 1 < x := by
  have hD := D_ge_h_add_one (r := r) (h := h) hp
  have hh := hp.h_ge_six
  unfold InH InInterval HLo at hx
  constructor <;> omega

/--
Same-`H_i` two-sum coverage with ordered distinct witnesses.

The endpoint trim is the usual distinct-pair range
`[2 * HLo_i + 1, 2 * HHi_i - 1]`.
-/
theorem H_pair_sum_distinct_same_index {r h i t : Nat} (hp : Params r h)
    (ht : InInterval (2 * HLo r h i + 1) (2 * HHi r h i - 1) t) :
    ∃ x y : Nat,
      InH r h i x ∧
      InH r h i y ∧
      x < y ∧
      x + y = t := by
  have hLU : HLo r h i < HHi r h i := HLo_lt_HHi hp
  have htNat :
      NatInterval (2 * HLo r h i + 1) (2 * HHi r h i - 1) t := by
    simpa [NatInterval, InInterval] using ht
  rcases interval_pair_sum_distinct hLU htNat with
    ⟨x, y, hx, hy, hxy, hsum⟩
  refine ⟨x, y, ?_, ?_, hxy, hsum⟩
  · simpa [InH, NatInterval, InInterval] using hx
  · simpa [InH, NatInterval, InInterval] using hy

theorem H_pair_distinct_sum_interval_nonempty {r h i : Nat} (hp : Params r h) :
    2 * HLo r h i + 1 <= 2 * HHi r h i - 1 := by
  have hh := hp.h_ge_six
  unfold HHi
  omega

/--
For strictly increasing interval indices, the fixed-index three-`H` witness is
automatically ordered and therefore distinct.
-/
theorem H_triple_sum_distinct_of_strict_indices {r h i j k t : Nat}
    (hp : Params r h) (hij : i < j) (hjk : j < k)
    (ht : InTripleHSlice r h (i + j + k) t) :
    ∃ x y z : Nat,
      InH r h i x ∧
      InH r h j y ∧
      InH r h k z ∧
      x < y ∧
      y < z ∧
      x + y + z = t := by
  rcases H_triple_sum_of_indices
      (r := r) (h := h) (i := i) (j := j) (k := k) hp ht with
    ⟨x, y, z, hx, hy, hz, hsum⟩
  have hxy_gap := HHi_lt_HLo_of_lt (r := r) (h := h) hp hij
  have hyz_gap := HHi_lt_HLo_of_lt (r := r) (h := h) hp hjk
  have hxy : x < y := by
    exact Nat.lt_of_le_of_lt hx.2 (Nat.lt_of_lt_of_le hxy_gap hy.1)
  have hyz : y < z := by
    exact Nat.lt_of_le_of_lt hy.2 (Nat.lt_of_lt_of_le hyz_gap hz.1)
  exact ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩

/--
Same-interval distinct three-sum coverage for the interior of one `H_i`.
-/
theorem H_triple_sum_distinct_same_index {r h i t : Nat} (hp : Params r h)
    (ht : InInterval (3 * HLo r h i + 3) (3 * HHi r h i - 3) t) :
    ∃ x y z : Nat,
      InH r h i x ∧
      InH r h i y ∧
      InH r h i z ∧
      x < y ∧
      y < z ∧
      x + y + z = t := by
  have hh := hp.h_ge_six
  have hwidth : HLo r h i + 2 <= HHi r h i := by
    unfold HHi
    omega
  have htNat :
      NatInterval (3 * HLo r h i + 3) (3 * HHi r h i - 3) t := by
    simpa [NatInterval, InInterval] using ht
  rcases interval_triple_sum_distinct hwidth htNat with
    ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩
  refine ⟨x, y, z, ?_, ?_, ?_, hxy, hyz, hsum⟩
  · simpa [InH, NatInterval, InInterval] using hx
  · simpa [InH, NatInterval, InInterval] using hy
  · simpa [InH, NatInterval, InInterval] using hz

theorem H_triple_sum_distinct_two_left_indices {r h i j t : Nat}
    (hp : Params r h) (hij : i < j)
    (ht :
      InInterval (2 * HLo r h i + 1 + HLo r h j)
        (2 * HHi r h i - 1 + HHi r h j) t) :
    ∃ x y z : Nat,
      InH r h i x ∧
      InH r h i y ∧
      InH r h j z ∧
      x < y ∧
      y < z ∧
      x + y + z = t := by
  have hPair : 2 * HLo r h i + 1 <= 2 * HHi r h i - 1 :=
    H_pair_distinct_sum_interval_nonempty (r := r) (h := h) (i := i) hp
  have hJ : HLo r h j <= HHi r h j := HLo_le_HHi hp
  rcases interval_pair_sum hPair hJ ht with ⟨s, z, hs, hz, hsum_sz⟩
  rcases H_pair_sum_distinct_same_index
      (r := r) (h := h) (i := i) (t := s) hp hs with
    ⟨x, y, hx, hy, hxy, hsum_xy⟩
  have hgap := HHi_lt_HLo_of_lt (r := r) (h := h) hp hij
  have hyz : y < z := by
    exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hy.2 hgap) hz.1
  exact ⟨x, y, z, hx, hy, hz, hxy, hyz, by omega⟩

theorem H_triple_sum_distinct_two_right_indices {r h i j t : Nat}
    (hp : Params r h) (hij : i < j)
    (ht :
      InInterval (HLo r h i + (2 * HLo r h j + 1))
        (HHi r h i + (2 * HHi r h j - 1)) t) :
    ∃ x y z : Nat,
      InH r h i x ∧
      InH r h j y ∧
      InH r h j z ∧
      x < y ∧
      y < z ∧
      x + y + z = t := by
  have hI : HLo r h i <= HHi r h i := HLo_le_HHi hp
  have hPair : 2 * HLo r h j + 1 <= 2 * HHi r h j - 1 :=
    H_pair_distinct_sum_interval_nonempty (r := r) (h := h) (i := j) hp
  rcases interval_pair_sum hI hPair ht with ⟨x, s, hx, hs, hsum_xs⟩
  rcases H_pair_sum_distinct_same_index
      (r := r) (h := h) (i := j) (t := s) hp hs with
    ⟨y, z, hy, hz, hyz, hsum_yz⟩
  have hgap := HHi_lt_HLo_of_lt (r := r) (h := h) hp hij
  have hxy : x < y := by
    exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hx.2 hgap) hy.1
  exact ⟨x, y, z, hx, hy, hz, hxy, hyz, by omega⟩

theorem H_triple_sum_distinct_two_left_inU {r h i j t : Nat}
    (hp : Params r h) (hi : i < r) (hj : j < r) (hij : i < j)
    (ht :
      InInterval (2 * HLo r h i + 1 + HLo r h j)
        (2 * HHi r h i - 1 + HHi r h j) t) :
    ∃ x y z : Nat,
      InU r h x ∧
      InU r h y ∧
      InU r h z ∧
      x < y ∧
      y < z ∧
      x + y + z = t := by
  rcases H_triple_sum_distinct_two_left_indices
      (r := r) (h := h) (i := i) (j := j) (t := t) hp hij ht with
    ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩
  exact
    ⟨x, y, z, ⟨i, hi, hx⟩, ⟨i, hi, hy⟩, ⟨j, hj, hz⟩, hxy, hyz, hsum⟩

theorem H_triple_sum_distinct_two_right_inU {r h i j t : Nat}
    (hp : Params r h) (hi : i < r) (hj : j < r) (hij : i < j)
    (ht :
      InInterval (HLo r h i + (2 * HLo r h j + 1))
        (HHi r h i + (2 * HHi r h j - 1)) t) :
    ∃ x y z : Nat,
      InU r h x ∧
      InU r h y ∧
      InU r h z ∧
      x < y ∧
      y < z ∧
      x + y + z = t := by
  rcases H_triple_sum_distinct_two_right_indices
      (r := r) (h := h) (i := i) (j := j) (t := t) hp hij ht with
    ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩
  exact
    ⟨x, y, z, ⟨i, hi, hx⟩, ⟨j, hj, hy⟩, ⟨j, hj, hz⟩, hxy, hyz, hsum⟩

theorem tripleHSlice_distinct_same_inU {r h i t : Nat}
    (hp : Params r h) (hi : i < r)
    (ht :
      InInterval (tripleHSliceLo r h (i + i + i) + 3)
        (tripleHSliceHi r h (i + i + i) - 3) t) :
    ∃ x y z : Nat,
      InU r h x ∧
      InU r h y ∧
      InU r h z ∧
      x < y ∧
      y < z ∧
      x + y + z = t := by
  have hlo :
      3 * HLo r h i + 3 =
        tripleHSliceLo r h (i + i + i) + 3 := by
    unfold HLo tripleHSliceLo
    simp [Nat.left_distrib, Nat.right_distrib]
    omega
  have hhi :
      3 * HHi r h i - 3 =
        tripleHSliceHi r h (i + i + i) - 3 := by
    have hh := hp.h_ge_six
    unfold HHi HLo tripleHSliceHi
    simp [Nat.left_distrib, Nat.right_distrib]
    omega
  have htSame :
      InInterval (3 * HLo r h i + 3) (3 * HHi r h i - 3) t := by
    rw [hlo, hhi]
    exact ht
  rcases H_triple_sum_distinct_same_index
      (r := r) (h := h) (i := i) (t := t) hp htSame with
    ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩
  exact
    ⟨x, y, z, ⟨i, hi, hx⟩, ⟨i, hi, hy⟩, ⟨i, hi, hz⟩, hxy, hyz, hsum⟩

theorem tripleHSlice_distinct_strict_inU {r h i j k t : Nat}
    (hp : Params r h) (hi : i < r) (hj : j < r) (hk : k < r)
    (hij : i < j) (hjk : j < k)
    (ht : InTripleHSlice r h (i + j + k) t) :
    ∃ x y z : Nat,
      InU r h x ∧
      InU r h y ∧
      InU r h z ∧
      x < y ∧
      y < z ∧
      x + y + z = t := by
  rcases H_triple_sum_distinct_of_strict_indices
      (r := r) (h := h) (i := i) (j := j) (k := k) (t := t)
      hp hij hjk ht with
    ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩
  exact
    ⟨x, y, z, ⟨i, hi, hx⟩, ⟨j, hj, hy⟩, ⟨k, hk, hz⟩, hxy, hyz, hsum⟩

theorem tripleHSlice_distinct_two_left_inU {r h i j t : Nat}
    (hp : Params r h) (hi : i < r) (hj : j < r) (hij : i < j)
    (ht :
      InInterval (tripleHSliceLo r h (i + i + j) + 1)
        (tripleHSliceHi r h (i + i + j) - 1) t) :
    ∃ x y z : Nat,
      InU r h x ∧
      InU r h y ∧
      InU r h z ∧
      x < y ∧
      y < z ∧
      x + y + z = t := by
  have hlo :
      2 * HLo r h i + 1 + HLo r h j =
        tripleHSliceLo r h (i + i + j) + 1 := by
    unfold HLo tripleHSliceLo
    simp [Nat.left_distrib, Nat.right_distrib]
    omega
  have hhi :
      2 * HHi r h i - 1 + HHi r h j =
        tripleHSliceHi r h (i + i + j) - 1 := by
    have hh := hp.h_ge_six
    unfold HHi HLo tripleHSliceHi
    simp [Nat.left_distrib, Nat.right_distrib]
    omega
  have htMixed :
      InInterval (2 * HLo r h i + 1 + HLo r h j)
        (2 * HHi r h i - 1 + HHi r h j) t := by
    rw [hlo, hhi]
    exact ht
  exact H_triple_sum_distinct_two_left_inU
    (r := r) (h := h) (i := i) (j := j) (t := t) hp hi hj hij htMixed

theorem tripleHSlice_distinct_two_right_inU {r h i j t : Nat}
    (hp : Params r h) (hi : i < r) (hj : j < r) (hij : i < j)
    (ht :
      InInterval (tripleHSliceLo r h (i + j + j) + 1)
        (tripleHSliceHi r h (i + j + j) - 1) t) :
    ∃ x y z : Nat,
      InU r h x ∧
      InU r h y ∧
      InU r h z ∧
      x < y ∧
      y < z ∧
      x + y + z = t := by
  have hlo :
      HLo r h i + (2 * HLo r h j + 1) =
        tripleHSliceLo r h (i + j + j) + 1 := by
    unfold HLo tripleHSliceLo
    simp [Nat.left_distrib, Nat.right_distrib]
    omega
  have hhi :
      HHi r h i + (2 * HHi r h j - 1) =
        tripleHSliceHi r h (i + j + j) - 1 := by
    have hh := hp.h_ge_six
    unfold HHi HLo tripleHSliceHi
    simp [Nat.left_distrib, Nat.right_distrib]
    omega
  have htMixed :
      InInterval (HLo r h i + (2 * HLo r h j + 1))
        (HHi r h i + (2 * HHi r h j - 1)) t := by
    rw [hlo, hhi]
    exact ht
  exact H_triple_sum_distinct_two_right_inU
    (r := r) (h := h) (i := i) (j := j) (t := t) hp hi hj hij htMixed

theorem shifted_pair_slice_distinct_prefix_of_lt_indices {r h i j t : Nat}
    (hp : Params r h) (hi : i < r) (hj : j < r) (hij : i < j)
    (ht : InShiftedPairSlice r h (i + j) t) :
    DistinctPrefixTripleSum r h t := by
  rcases shifted_adjacent_pair_sum_of_indices
      (r := r) (h := h) (i := i) (j := j) (t := t) hp ht with
    ⟨x, y, hx, hy, hsum_xy⟩
  rcases shiftedAdjacent_mem_prefix_translate
      (r := r) (h := h) (j := j) (y := y) hp hy with
    ⟨eps, v, heps, hv, heq⟩
  have hepsPrefix : InPrefix r h eps := by
    rcases heps with rfl | rfl
    · exact prefix_one r h
    · exact prefix_h_sub_one r h
  have hxPrefix : InPrefix r h x :=
    prefix_of_inH (r := r) (h := h) (i := i) (x := x) hi hx
  have hvPrefix : InPrefix r h v :=
    prefix_of_inH (r := r) (h := h) (i := j) (x := v) hj hv
  have heps_lt_x : eps < x := by
    rcases heps with rfl | rfl
    · exact (prefix_singletons_lt_H (r := r) (h := h) (i := i) (x := x) hp hx).1
    · exact (prefix_singletons_lt_H (r := r) (h := h) (i := i) (x := x) hp hx).2
  have hx_lt_v : x < v := by
    have hgap := HHi_lt_HLo_of_lt (r := r) (h := h) hp hij
    exact Nat.lt_of_le_of_lt hx.2 (Nat.lt_of_lt_of_le hgap hv.1)
  have hsum : eps + x + v = t := by
    omega
  exact ⟨eps, x, v, hepsPrefix, hxPrefix, hvPrefix, heps_lt_x, hx_lt_v, hsum⟩

theorem shifted_pair_slice_same_index_distinct_prefix {r h i t : Nat}
    (hp : Params r h) (hi : i < r)
    (ht : InShiftedPairSlice r h (i + i) t) :
    DistinctPrefixTripleSum r h t := by
  have hsliceLo :
      shiftedPairSliceLo r h (i + i) = 2 * HLo r h i + 2 := by
    unfold shiftedPairSliceLo HLo
    simp [Nat.left_distrib, Nat.right_distrib]
    omega
  have hsliceHi :
      shiftedPairSliceHi r h (i + i) = 2 * HLo r h i + 3 * h - 4 := by
    unfold shiftedPairSliceHi HLo
    simp [Nat.left_distrib, Nat.right_distrib]
    omega
  have hslice :
      InInterval (2 * HLo r h i + 2) (2 * HLo r h i + 3 * h - 4) t := by
    unfold InShiftedPairSlice at ht
    simpa [hsliceLo, hsliceHi] using ht
  have hHHi : HHi r h i = HLo r h i + h - 1 := rfl
  by_cases hlow : t <= 2 * HHi r h i
  · have htPair :
        InInterval (2 * HLo r h i + 1) (2 * HHi r h i - 1) (t - 1) := by
      rw [hHHi] at hlow
      unfold InInterval
      rw [hHHi]
      have hslo := hslice.1
      constructor <;> omega
    rcases H_pair_sum_distinct_same_index
        (r := r) (h := h) (i := i) (t := t - 1) hp htPair with
      ⟨x, y, hx, hy, hxy, hsum_xy⟩
    have hxPrefix : InPrefix r h x :=
      prefix_of_inH (r := r) (h := h) (i := i) (x := x) hi hx
    have hyPrefix : InPrefix r h y :=
      prefix_of_inH (r := r) (h := h) (i := i) (x := y) hi hy
    have h1x : 1 < x := (prefix_singletons_lt_H (r := r) (h := h)
      (i := i) (x := x) hp hx).1
    have hsum : 1 + x + y = t := by
      have ht_pos : 1 <= t := by
        have hslo := hslice.1
        omega
      omega
    exact ⟨1, x, y, prefix_one r h, hxPrefix, hyPrefix, h1x, hxy, hsum⟩
  · have htPair :
        InInterval (2 * HLo r h i + 1) (2 * HHi r h i - 1) (t - (h - 1)) := by
      have hgt : 2 * (HLo r h i + h - 1) < t := by
        have hgt' : 2 * HHi r h i < t := Nat.lt_of_not_ge hlow
        rwa [hHHi] at hgt'
      have hshi := hslice.2
      unfold InInterval
      rw [hHHi]
      constructor <;> omega
    rcases H_pair_sum_distinct_same_index
        (r := r) (h := h) (i := i) (t := t - (h - 1)) hp htPair with
      ⟨x, y, hx, hy, hxy, hsum_xy⟩
    have hxPrefix : InPrefix r h x :=
      prefix_of_inH (r := r) (h := h) (i := i) (x := x) hi hx
    have hyPrefix : InPrefix r h y :=
      prefix_of_inH (r := r) (h := h) (i := i) (x := y) hi hy
    have hepsx : h - 1 < x := (prefix_singletons_lt_H (r := r) (h := h)
      (i := i) (x := x) hp hx).2
    have hsum : (h - 1) + x + y = t := by
      have ht_ge : h - 1 <= t := by
        have hD := D_ge_h_add_one (r := r) (h := h) hp
        have hslo := hslice.1
        unfold HLo at hslo
        omega
      omega
    exact
      ⟨h - 1, x, y, prefix_h_sub_one r h, hxPrefix, hyPrefix,
        hepsx, hxy, hsum⟩

theorem shiftedPairSlice_chain_distinct_prefix_covered {r h t : Nat}
    (hp : Params r h)
    (ht :
      InInterval (finalPrefixGapLo r h)
        (2 * D r h + (4 * r - 1) * h - 4) t) :
    DistinctPrefixTripleSum r h t := by
  rcases shiftedPairSlice_chain_cover_bounded
      (r := r) (h := h) (t := t) hp ht with
    ⟨m, hm, hmem⟩
  by_cases hm0 : m = 0
  · have hslice : InShiftedPairSlice r h (0 + 0) t := by
      simpa [hm0] using hmem
    exact shifted_pair_slice_same_index_distinct_prefix
      (r := r) (h := h) (i := 0) (t := t) hp (by
        have hr := hp.r_pos
        omega) hslice
  · by_cases hmtop : m = 2 * r - 2
    · have hidx : (r - 1) + (r - 1) = 2 * r - 2 := by
        have hr := hp.r_pos
        omega
      have hslice : InShiftedPairSlice r h ((r - 1) + (r - 1)) t := by
        simpa [hmtop, hidx] using hmem
      exact shifted_pair_slice_same_index_distinct_prefix
        (r := r) (h := h) (i := r - 1) (t := t) hp (by omega) hslice
    · have hm_lt_top : m < 2 * r - 2 := by
        omega
      by_cases hm_lt_r : m < r
      · have hm_pos : 0 < m := by
          omega
        have hslice : InShiftedPairSlice r h (0 + m) t := by
          simpa using hmem
        exact shifted_pair_slice_distinct_prefix_of_lt_indices
          (r := r) (h := h) (i := 0) (j := m) (t := t)
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
        have hslice : InShiftedPairSlice r h (i + (r - 1)) t := by
          simpa [hidx] using hmem
        exact shifted_pair_slice_distinct_prefix_of_lt_indices
          (r := r) (h := h) (i := i) (j := r - 1) (t := t)
          hp hi hlast hij hslice

theorem tripleHSlice_oneTrim_next_lo_le_hi_succ {r h m : Nat}
    (hp : Params r h) :
    tripleHSliceLo r h (m + 1) + 1 <=
      (tripleHSliceHi r h m - 1) + 1 := by
  have hh := hp.h_ge_six
  have hhi_pos : 1 <= tripleHSliceHi r h m := by
    unfold tripleHSliceHi
    omega
  have hstep : 2 * (m + 1) * h = 2 * m * h + 2 * h := by
    simp [Nat.left_distrib, Nat.right_distrib]
  rw [Nat.sub_add_cancel hhi_pos]
  unfold tripleHSliceLo tripleHSliceHi
  rw [hstep]
  omega

theorem tripleHSlice_oneTrim_chain_cover {r h a n t : Nat}
    (hp : Params r h)
    (ht :
      InInterval (tripleHSliceLo r h a + 1)
        (tripleHSliceHi r h (a + n) - 1) t) :
    ∃ m : Nat,
      a <= m ∧
      m <= a + n ∧
      InInterval (tripleHSliceLo r h m + 1)
        (tripleHSliceHi r h m - 1) t := by
  induction n with
  | zero =>
      exact ⟨a, by omega, by omega, by simpa using ht⟩
  | succ n ih =>
      by_cases htn : t <= tripleHSliceHi r h (a + n) - 1
      · rcases ih ⟨ht.1, htn⟩ with ⟨m, hma, hmhi, hmem⟩
        exact ⟨m, hma, by omega, hmem⟩
      · have hsucc :
            (tripleHSliceHi r h (a + n) - 1) + 1 <= t :=
          Nat.succ_le_of_lt (Nat.lt_of_not_ge htn)
        have hbridge :
            tripleHSliceLo r h ((a + n) + 1) + 1 <=
              (tripleHSliceHi r h (a + n) - 1) + 1 :=
          tripleHSlice_oneTrim_next_lo_le_hi_succ
            (r := r) (h := h) (m := a + n) hp
        have hlo : tripleHSliceLo r h ((a + n) + 1) + 1 <= t :=
          Nat.le_trans hbridge hsucc
        have hidx : (a + n) + 1 = a + (n + 1) := by omega
        have hhi : t <= tripleHSliceHi r h ((a + n) + 1) - 1 := by
          simpa [hidx] using ht.2
        exact ⟨(a + n) + 1, by omega, by omega, ⟨hlo, hhi⟩⟩

theorem tripleHSlice_final_same_distinct_inU {r h t : Nat}
    (hp : Params r h)
    (ht :
      InInterval (tripleHSliceLo r h (3 * r - 3) + 3)
        (tripleHSliceHi r h (3 * r - 3) - 3) t) :
    ∃ x y z : Nat,
      InU r h x ∧
      InU r h y ∧
      InU r h z ∧
      x < y ∧
      y < z ∧
      x + y + z = t := by
  have hr := hp.r_pos
  have hidx : (r - 1) + (r - 1) + (r - 1) = 3 * r - 3 := by
    omega
  exact tripleHSlice_distinct_same_inU
    (r := r) (h := h) (i := r - 1) (t := t) hp (by omega)
    (by simpa [hidx] using ht)

theorem final_prefix_gap_third_lo_ge_tripleHSlice_oneTrim_start {r h : Nat}
    (hp : Params r h) :
    tripleHSliceLo r h (r - 1) + 1 <=
      2 * D r h + (4 * r - 1) * h - 3 := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have hcoefA : 2 * r + 2 * (r - 1) = 4 * r - 2 := by
    omega
  have hprodA : 2 * r * h + 2 * (r - 1) * h = (4 * r - 2) * h := by
    rw [← Nat.add_mul, hcoefA]
  have hcoefB : 4 * r - 1 = (4 * r - 2) + 1 := by
    omega
  have hprodB : (4 * r - 1) * h = (4 * r - 2) * h + h := by
    rw [hcoefB, Nat.add_mul]
    omega
  have hmain : D r h + 2 * (r - 1) * h + 4 <= (4 * r - 1) * h := by
    unfold D
    rw [hprodB]
    omega
  unfold tripleHSliceLo
  omega

theorem tripleHSlice_high_oneTrim_distinct_inU {r h m t : Nat}
    (hp : Params r h) (hr2 : 2 <= r)
    (hmlo : r - 1 <= m) (hmhi : m <= 3 * r - 4)
    (ht :
      InInterval (tripleHSliceLo r h m + 1)
        (tripleHSliceHi r h m - 1) t) :
    ∃ x y z : Nat,
      InU r h x ∧
      InU r h y ∧
      InU r h z ∧
      x < y ∧
      y < z ∧
      x + y + z = t := by
  by_cases hm_low : m <= 2 * r - 2
  · let a := m - (r - 1)
    have ha_lt_r : a < r := by
      dsimp [a]
      omega
    have hlast_lt : r - 1 < r := by
      omega
    by_cases ha0 : a = 0
    · have hm_eq : m = r - 1 := by
        dsimp [a] at ha0
        omega
      have hslice :
          InInterval (tripleHSliceLo r h (0 + 0 + (r - 1)) + 1)
            (tripleHSliceHi r h (0 + 0 + (r - 1)) - 1) t := by
        simpa [hm_eq] using ht
      exact tripleHSlice_distinct_two_left_inU
        (r := r) (h := h) (i := 0) (j := r - 1) (t := t)
        hp (by omega) hlast_lt (by omega) hslice
    · by_cases halast : a = r - 1
      · have hm_eq : m = 2 * r - 2 := by
          dsimp [a] at halast
          omega
        have hslice :
            InInterval (tripleHSliceLo r h (0 + (r - 1) + (r - 1)) + 1)
              (tripleHSliceHi r h (0 + (r - 1) + (r - 1)) - 1) t := by
          have hidx' : (r - 1) + (r - 1) = m := by
            omega
          simpa [hidx'] using ht
        exact tripleHSlice_distinct_two_right_inU
          (r := r) (h := h) (i := 0) (j := r - 1) (t := t)
          hp (by omega) hlast_lt (by omega) hslice
      · have ha_pos : 0 < a := by
          omega
        have ha_lt_last : a < r - 1 := by
          omega
        have hm_eq : 0 + a + (r - 1) = m := by
          dsimp [a]
          omega
        have hsliceTrim :
            InInterval (tripleHSliceLo r h (0 + a + (r - 1)) + 1)
              (tripleHSliceHi r h (0 + a + (r - 1)) - 1) t := by
          have hidx : a + (r - 1) = m := by
            dsimp [a]
            omega
          simpa [hidx] using ht
        have hsliceFull : InTripleHSlice r h (0 + a + (r - 1)) t := by
          unfold InTripleHSlice InInterval at *
          constructor <;> omega
        exact tripleHSlice_distinct_strict_inU
          (r := r) (h := h) (i := 0) (j := a) (k := r - 1) (t := t)
          hp (by omega) ha_lt_r hlast_lt ha_pos ha_lt_last hsliceFull
  · let a := m - (2 * r - 2)
    have hm_gt : 2 * r - 2 < m := Nat.lt_of_not_ge hm_low
    have ha_pos : 0 < a := by
      dsimp [a]
      omega
    have ha_lt_last : a < r - 1 := by
      dsimp [a]
      omega
    have ha_lt_r : a < r := by
      omega
    have hlast_lt : r - 1 < r := by
      omega
    have hm_eq : a + (r - 1) + (r - 1) = m := by
      dsimp [a]
      omega
    have hslice :
        InInterval (tripleHSliceLo r h (a + (r - 1) + (r - 1)) + 1)
          (tripleHSliceHi r h (a + (r - 1) + (r - 1)) - 1) t := by
      simpa [hm_eq] using ht
    exact tripleHSlice_distinct_two_right_inU
      (r := r) (h := h) (i := a) (j := r - 1) (t := t)
      hp ha_lt_r hlast_lt ha_lt_last hslice

theorem final_prefix_gap_middle_range_distinct_inU {r h t : Nat}
    (hp : Params r h)
    (ht :
      InInterval (2 * D r h + (4 * r - 1) * h - 3)
        (tripleHSliceHi r h (3 * r - 3) - 3) t) :
    ∃ x y z : Nat,
      InU r h x ∧
      InU r h y ∧
      InU r h z ∧
      x < y ∧
      y < z ∧
      x + y + z = t := by
  by_cases hr1 : r = 1
  · subst r
    have htrim :
        InInterval (tripleHSliceLo 1 h (3 * 1 - 3) + 3)
          (tripleHSliceHi 1 h (3 * 1 - 3) - 3) t := by
      constructor
      · have hh := hp.h_ge_six
        have hlo :
            tripleHSliceLo 1 h (3 * 1 - 3) + 3 <=
              2 * D 1 h + (4 * 1 - 1) * h - 3 := by
          unfold tripleHSliceLo D
          omega
        exact Nat.le_trans hlo ht.1
      · exact ht.2
    exact tripleHSlice_final_same_distinct_inU
      (r := 1) (h := h) (t := t) hp htrim
  · have hr2 : 2 <= r := by
      have hr := hp.r_pos
      omega
    by_cases htop : t <= tripleHSliceHi r h (3 * r - 4) - 1
    · have hidx : (r - 1) + (2 * r - 3) = 3 * r - 4 := by
        omega
      have htchain :
          InInterval (tripleHSliceLo r h (r - 1) + 1)
            (tripleHSliceHi r h ((r - 1) + (2 * r - 3)) - 1) t := by
        constructor
        · exact Nat.le_trans
            (final_prefix_gap_third_lo_ge_tripleHSlice_oneTrim_start
              (r := r) (h := h) hp)
            ht.1
        · simpa [hidx] using htop
      rcases tripleHSlice_oneTrim_chain_cover
          (r := r) (h := h) (a := r - 1) (n := 2 * r - 3)
          (t := t) hp htchain with
        ⟨m, hmlo, hmhi, hmem⟩
      have hmhi' : m <= 3 * r - 4 := by
        omega
      exact tripleHSlice_high_oneTrim_distinct_inU
        (r := r) (h := h) (m := m) (t := t)
        hp hr2 hmlo hmhi' hmem
    · have hsucc :
          (tripleHSliceHi r h (3 * r - 4) - 1) + 1 <= t :=
        Nat.succ_le_of_lt (Nat.lt_of_not_ge htop)
      have hbridge :
          tripleHSliceLo r h (3 * r - 3) + 3 <=
            (tripleHSliceHi r h (3 * r - 4) - 1) + 1 := by
        have hh := hp.h_ge_six
        have hhi_pos : 1 <= tripleHSliceHi r h (3 * r - 4) := by
          unfold tripleHSliceHi
          omega
        have hcoef : 3 * r - 3 = (3 * r - 4) + 1 := by
          omega
        have hstep :
            2 * (3 * r - 3) * h =
              2 * (3 * r - 4) * h + 2 * h := by
          rw [hcoef]
          simp [Nat.left_distrib, Nat.right_distrib]
        rw [Nat.sub_add_cancel hhi_pos]
        unfold tripleHSliceLo tripleHSliceHi
        rw [hstep]
        omega
      have hlo : tripleHSliceLo r h (3 * r - 3) + 3 <= t :=
        Nat.le_trans hbridge hsucc
      have hhi : t <= tripleHSliceHi r h (3 * r - 3) - 3 := ht.2
      exact tripleHSlice_final_same_distinct_inU
        (r := r) (h := h) (t := t) hp ⟨hlo, hhi⟩

theorem final_prefix_gap_middle_range_distinct_prefix_covered {r h t : Nat}
    (hp : Params r h)
    (ht :
      InInterval (2 * D r h + (4 * r - 1) * h - 3)
        (tripleHSliceHi r h (3 * r - 3) - 3) t) :
    DistinctPrefixTripleSum r h t :=
  distinctPrefixTripleSum_of_distinct_inU
    (final_prefix_gap_middle_range_distinct_inU
      (r := r) (h := h) (t := t) hp ht)

private theorem HLo_last_eq_formula {r h : Nat} (hp : Params r h) :
    HLo r h (r - 1) = (4 * r - 2) * h - 1 := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have hcoef : 2 * r + 2 * (r - 1) = 4 * r - 2 := by
    omega
  have hprod : 2 * r * h + 2 * (r - 1) * h = (4 * r - 2) * h := by
    rw [← Nat.add_mul, hcoef]
  have hbase : 1 <= 2 * r * h := by
    have hcoef2 : 2 <= 2 * r := by omega
    have hprod2 : 2 * h <= 2 * r * h := Nat.mul_le_mul_right h hcoef2
    omega
  unfold HLo D
  rw [← hprod]
  symm
  exact Nat.sub_add_comm hbase

private theorem HHi_last_eq_formula {r h : Nat} (hp : Params r h) :
    HHi r h (r - 1) = (4 * r - 1) * h - 2 := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have hcoef : 4 * r - 1 = (4 * r - 2) + 1 := by
    omega
  have hprod : (4 * r - 1) * h = (4 * r - 2) * h + h := by
    rw [hcoef, Nat.add_mul]
    omega
  rw [HHi, HLo_last_eq_formula (r := r) (h := h) hp]
  rw [hprod]
  have hApos : 1 <= (4 * r - 2) * h := by
    have hcoef4 : 2 <= 4 * r - 2 := by omega
    have hprod4 : 2 * h <= (4 * r - 2) * h := Nat.mul_le_mul_right h hcoef4
    omega
  rw [← Nat.sub_add_comm (m := h) hApos]
  omega

private theorem tripleHSliceHi_last_eq_formula {r h : Nat} (hp : Params r h) :
    tripleHSliceHi r h (3 * r - 3) = (12 * r - 3) * h - 6 := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have hglob := tripleHSlice_global_hi_eq (r := r) (h := h) hp
  rw [hglob]
  have hcoef : 6 * r + (6 * r - 3) = 12 * r - 3 := by
    omega
  have hprod : (6 * r) * h + (6 * r - 3) * h = (12 * r - 3) * h := by
    rw [← Nat.add_mul, hcoef]
  have hmul : 3 * (2 * r * h) = (6 * r) * h := by
    rw [← Nat.mul_assoc]
    congr 1
    omega
  change 3 * (2 * r * h - 1) + (6 * r - 3) * h - 3 =
    (12 * r - 3) * h - 6
  rw [Nat.mul_sub_left_distrib]
  rw [hmul]
  rw [← hprod]
  let A := (6 * r) * h
  let B := (6 * r - 3) * h
  change (A - 3) + B - 3 = A + B - 6
  have hA3 : 3 <= A := by
    dsimp [A]
    have hcoef6 : 6 <= 6 * r := by omega
    have hprod6 : 6 * h <= (6 * r) * h := Nat.mul_le_mul_right h hcoef6
    omega
  calc
    (A - 3) + B - 3 = (A + B - 3) - 3 := by
      rw [← Nat.sub_add_comm (n := A) (m := B) (k := 3) hA3]
    _ = A + B - (3 + 3) := by rw [Nat.sub_sub]
    _ = A + B - 6 := by omega

theorem finalPrefixGapHi_eq_c_add_two_HHi_last_sub_one {r h : Nat}
    (hp : Params r h) :
    finalPrefixGapHi r h = c r h + 2 * HHi r h (r - 1) - 1 := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  rw [finalPrefixGapHi_eq_formula (r := r) (h := h) hp]
  rw [HHi_last_eq_formula (r := r) (h := h) hp]
  have hcoef : 4 * r + 2 * (4 * r - 1) = 12 * r - 2 := by
    omega
  have hprod : (4 * r) * h + (2 * (4 * r - 1)) * h = (12 * r - 2) * h := by
    rw [← Nat.add_mul, hcoef]
  have hmul : 2 * ((4 * r - 1) * h) = (2 * (4 * r - 1)) * h := by
    rw [← Nat.mul_assoc]
  unfold c
  rw [Nat.mul_sub_left_distrib]
  rw [hmul]
  rw [← hprod]
  let A := (4 * r) * h
  let B := (2 * (4 * r - 1)) * h
  change A + B - 6 = A - 1 + (B - 4) - 1
  have hA1 : 1 <= A := by
    dsimp [A]
    have hcoef4 : 4 <= 4 * r := by omega
    have hprod4 : 4 * h <= (4 * r) * h := Nat.mul_le_mul_right h hcoef4
    omega
  have hB4 : 4 <= B := by
    dsimp [B]
    have hcoefB : 4 <= 2 * (4 * r - 1) := by omega
    have hprodB : 4 * h <= (2 * (4 * r - 1)) * h :=
      Nat.mul_le_mul_right h hcoefB
    omega
  omega

theorem c_pair_last_lo_le_triple_top_succ {r h : Nat} (hp : Params r h) :
    c r h + (2 * HLo r h (r - 1) + 1) <=
      (tripleHSliceHi r h (3 * r - 3) - 3) + 1 := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  rw [HLo_last_eq_formula (r := r) (h := h) hp]
  rw [tripleHSliceHi_last_eq_formula (r := r) (h := h) hp]
  have hcoef : 4 * r + 2 * (4 * r - 2) = 12 * r - 4 := by
    omega
  have hprod : (4 * r) * h + (2 * (4 * r - 2)) * h = (12 * r - 4) * h := by
    rw [← Nat.add_mul, hcoef]
  have hmul : 2 * ((4 * r - 2) * h) = (2 * (4 * r - 2)) * h := by
    rw [← Nat.mul_assoc]
  have hcoefTop : 12 * r - 3 = (12 * r - 4) + 1 := by
    omega
  have hprodTop : (12 * r - 3) * h = (12 * r - 4) * h + h := by
    rw [hcoefTop, Nat.add_mul]
    omega
  unfold c
  rw [hprodTop]
  rw [Nat.mul_sub_left_distrib]
  rw [hmul]
  rw [← hprod]
  let A := (4 * r) * h
  let B := (2 * (4 * r - 2)) * h
  change A - 1 + (B - 2 + 1) <= (A + B + h - 6 - 3) + 1
  have hA1 : 1 <= A := by
    dsimp [A]
    have hcoef4 : 4 <= 4 * r := by omega
    have hprod4 : 4 * h <= (4 * r) * h := Nat.mul_le_mul_right h hcoef4
    omega
  have hB2 : 2 <= B := by
    dsimp [B]
    have hcoefB : 2 <= 2 * (4 * r - 2) := by omega
    have hprodB : 2 * h <= (2 * (4 * r - 2)) * h :=
      Nat.mul_le_mul_right h hcoefB
    omega
  omega

theorem final_prefix_gap_top_c_pair_distinct_prefix_covered {r h t : Nat}
    (hp : Params r h)
    (ht :
      InInterval ((tripleHSliceHi r h (3 * r - 3) - 3) + 1)
        (finalPrefixGapHi r h) t) :
    DistinctPrefixTripleSum r h t := by
  let s := t - c r h
  have hs_interval :
      InInterval (2 * HLo r h (r - 1) + 1)
        (2 * HHi r h (r - 1) - 1) s := by
    unfold s
    constructor
    · apply Nat.le_sub_of_add_le
      have hcomm :
          2 * HLo r h (r - 1) + 1 + c r h =
            c r h + (2 * HLo r h (r - 1) + 1) := by omega
      rw [hcomm]
      exact Nat.le_trans (c_pair_last_lo_le_triple_top_succ (r := r) (h := h) hp) ht.1
    · rw [Nat.sub_le_iff_le_add]
      rw [finalPrefixGapHi_eq_c_add_two_HHi_last_sub_one (r := r) (h := h) hp] at ht
      have hcomm :
          c r h + 2 * HHi r h (r - 1) - 1 =
            2 * HHi r h (r - 1) - 1 + c r h := by
        have hH := HLo_ge_three (r := r) (h := h) (i := r - 1) hp
        unfold HHi
        omega
      have ht2 := ht.2
      rwa [hcomm] at ht2
  rcases H_pair_sum_distinct_same_index
      (r := r) (h := h) (i := r - 1) (t := s) hp hs_interval with
    ⟨x, y, hx, hy, hxy, hsum_xy⟩
  have hlast : r - 1 < r := by
    have hr := hp.r_pos
    omega
  have hxPrefix : InPrefix r h x :=
    prefix_of_inH (r := r) (h := h) (i := r - 1) (x := x) hlast hx
  have hyPrefix : InPrefix r h y :=
    prefix_of_inH (r := r) (h := h) (i := r - 1) (x := y) hlast hy
  have hyc : y < c r h := by
    have hHc := HHi_last_lt_c (r := r) (h := h) hp
    exact Nat.lt_of_le_of_lt hy.2 hHc
  have hc_le_t : c r h <= t := by
    have hD := D_ge_three (r := r) (h := h) hp
    have hle := c_pair_last_lo_le_triple_top_succ (r := r) (h := h) hp
    omega
  have hsum : x + y + c r h = t := by
    unfold s at hsum_xy
    omega
  exact
    ⟨x, y, c r h, hxPrefix, hyPrefix, prefix_c r h, hxy, hyc, hsum⟩

/-- Full final-prefix-gap distinct ordered prefix coverage for the boundary family. -/
theorem final_prefix_gap_distinct_prefix_covered {r h t : Nat}
    (hp : Params r h)
    (ht : InInterval (finalPrefixGapLo r h) (finalPrefixGapHi r h) t) :
    DistinctPrefixTripleSum r h t := by
  by_cases hshift : t <= 2 * D r h + (4 * r - 1) * h - 4
  · exact shiftedPairSlice_chain_distinct_prefix_covered
      (r := r) (h := h) (t := t) hp ⟨ht.1, hshift⟩
  · by_cases hmid : t <= tripleHSliceHi r h (3 * r - 3) - 3
    · have hlo : 2 * D r h + (4 * r - 1) * h - 3 <= t := by
        have hsucc :
            (2 * D r h + (4 * r - 1) * h - 4) + 1 <= t :=
          Nat.succ_le_of_lt (Nat.lt_of_not_ge hshift)
        have hlarge : 4 <= 2 * D r h + (4 * r - 1) * h := by
          have hD := D_ge_three (r := r) (h := h) hp
          have hh := hp.h_ge_six
          have hr := hp.r_pos
          omega
        have hstep :
            (2 * D r h + (4 * r - 1) * h - 4) + 1 =
              2 * D r h + (4 * r - 1) * h - 3 := by
          omega
        simpa [hstep] using hsucc
      exact final_prefix_gap_middle_range_distinct_prefix_covered
        (r := r) (h := h) (t := t) hp ⟨hlo, hmid⟩
    · have hlo :
          (tripleHSliceHi r h (3 * r - 3) - 3) + 1 <= t :=
        Nat.succ_le_of_lt (Nat.lt_of_not_ge hmid)
      exact final_prefix_gap_top_c_pair_distinct_prefix_covered
        (r := r) (h := h) (t := t) hp ⟨hlo, ht.2⟩

end BoundaryRBand
end GreedyThreeSumfree
