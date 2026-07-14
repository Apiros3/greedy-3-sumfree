import GreedyThreeSumfree.BoundaryRBandIntervals

namespace GreedyThreeSumfree
namespace BoundaryRBand

/--
Non-distinct triple sum from the boundary-band prefix.

This intentionally does not encode ordering or distinctness.
-/
def NonDistinctPrefixTripleSum (r h t : Nat) : Prop :=
  ∃ x y z : Nat,
    InPrefix r h x ∧ InPrefix r h y ∧ InPrefix r h z ∧
      x + y + z = t

/--
Non-distinct triple sum from the boundary-band candidate set.

This intentionally does not encode ordering, distinctness, or the requirement
that the three summands are smaller than the target.
-/
def NonDistinctCandidateTripleSum (r h t : Nat) : Prop :=
  ∃ x y z : Nat,
    Candidate r h x ∧ Candidate r h y ∧ Candidate r h z ∧
      x + y + z = t

/-- The gap after the isolated boundary prefix point `c`, before periodicity starts. -/
def finalPrefixGapLo (r h : Nat) : Nat := c r h + 1

/-- The last point before the first positive periodic block. -/
def finalPrefixGapHi (r h : Nat) : Nat := M r h + VBot r h - 1

/-- The gap between the last `H` interval and the isolated boundary point `c`. -/
def preCGapLo (r h : Nat) : Nat := HLo r h (r - 1) + h

/-- The last point before the isolated boundary point `c`. -/
def preCGapHi (r h : Nat) : Nat := HHi r h (r - 1) + h

theorem prefix_one (r h : Nat) : InPrefix r h 1 := by
  exact Or.inl rfl

theorem prefix_h_sub_one (r h : Nat) : InPrefix r h (h - 1) := by
  exact Or.inr (Or.inl rfl)

theorem prefix_c (r h : Nat) : InPrefix r h (c r h) := by
  exact Or.inr (Or.inr (Or.inl rfl))

theorem prefix_of_inU {r h x : Nat} (hx : InU r h x) :
    InPrefix r h x := by
  exact Or.inr (Or.inr (Or.inr hx))

theorem prefix_of_inH {r h i x : Nat} (hi : i < r) (hx : InH r h i x) :
    InPrefix r h x := by
  exact prefix_of_inU (r := r) (h := h) ⟨i, hi, hx⟩

theorem candidate_of_prefix {r h x : Nat} (hx : InPrefix r h x) :
    Candidate r h x := by
  exact Or.inl hx

theorem candidate_one (r h : Nat) : Candidate r h 1 :=
  candidate_of_prefix (prefix_one r h)

theorem candidate_h_sub_one (r h : Nat) : Candidate r h (h - 1) :=
  candidate_of_prefix (prefix_h_sub_one r h)

theorem candidate_c (r h : Nat) : Candidate r h (c r h) :=
  candidate_of_prefix (prefix_c r h)

theorem candidate_of_inU {r h x : Nat} (hx : InU r h x) :
    Candidate r h x :=
  candidate_of_prefix (prefix_of_inU hx)

theorem candidate_of_inH {r h i x : Nat} (hi : i < r) (hx : InH r h i x) :
    Candidate r h x :=
  candidate_of_prefix (prefix_of_inH hi hx)

theorem nonDistinct_candidate_of_prefix {r h t : Nat}
    (ht : NonDistinctPrefixTripleSum r h t) :
    NonDistinctCandidateTripleSum r h t := by
  rcases ht with ⟨x, y, z, hx, hy, hz, hsum⟩
  exact ⟨x, y, z, candidate_of_prefix hx, candidate_of_prefix hy, candidate_of_prefix hz, hsum⟩

/--
Bounded index selection for shifted pair slices.

If `m` lies in the possible sum-index range `0..2r-2`, then it can be written
as `i+j` with both indices in the boundary `r`-band range.
-/
theorem bounded_pair_indices {r m : Nat} (hr : 1 <= r) (hm : m <= 2 * r - 2) :
    ∃ i j : Nat, i < r ∧ j < r ∧ i + j = m := by
  by_cases hm_lt : m < r
  · exact ⟨0, m, by omega, hm_lt, by omega⟩
  · refine ⟨m - (r - 1), r - 1, ?_, ?_, ?_⟩ <;> omega

/--
Bounded shifted-adjacent two-sum witness for every target in a shifted pair
slice whose index lies in the possible boundary `r`-band range.
-/
theorem shifted_adjacent_pair_sum_exists_bounded {r h m t : Nat} (hp : Params r h)
    (hm : m <= 2 * r - 2) (ht : InShiftedPairSlice r h m t) :
    ∃ i j x y : Nat,
      i < r ∧
      j < r ∧
      i + j = m ∧
      InH r h i x ∧
      InInterval (shiftedAdjacentLo r h j) (shiftedAdjacentHi r h j) y ∧
      x + y = t := by
  rcases bounded_pair_indices (r := r) (m := m) hp.r_pos hm with
    ⟨i, j, hi, hj, hij⟩
  rcases shifted_adjacent_pair_sum_of_sum
      (r := r) (h := h) (i := i) (j := j) (m := m) hp hij ht with
    ⟨x, y, hx, hy, hsum⟩
  exact ⟨i, j, x, y, hi, hj, hij, hx, hy, hsum⟩

/--
Every point in the shifted-adjacent interval for `j` is a translate of a point
of `H_j` by one of the two small prefix residues `1` or `h-1`.
-/
theorem shiftedAdjacent_mem_prefix_translate {r h j y : Nat} (hp : Params r h)
    (hy : InInterval (shiftedAdjacentLo r h j) (shiftedAdjacentHi r h j) y) :
    ∃ eps v : Nat,
      (eps = 1 ∨ eps = h - 1) ∧
      InH r h j v ∧
      eps + v = y := by
  by_cases hleft : y <= HLo r h j + h
  · refine ⟨1, y - 1, Or.inl rfl, ?_, ?_⟩
    · unfold InH InInterval HHi
      unfold InInterval shiftedAdjacentLo shiftedAdjacentHi at hy
      constructor <;> omega
    · unfold InInterval shiftedAdjacentLo shiftedAdjacentHi at hy
      omega
  · refine ⟨h - 1, y - (h - 1), Or.inr rfl, ?_, ?_⟩
    · have hD := D_ge_h_add_one (r := r) (h := h) hp
      have hL : h + 1 <= HLo r h j := by
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
    · have hD := D_ge_h_add_one (r := r) (h := h) hp
      have hL : h + 1 <= HLo r h j := by
        unfold HLo
        omega
      have hh := hp.h_ge_six
      unfold InInterval shiftedAdjacentLo shiftedAdjacentHi at hy
      have hy_ge_eps : h - 1 <= y := by omega
      exact Nat.add_sub_of_le hy_ge_eps

/--
Bounded shifted pair coverage in prefix-pair form: a target in a bounded
shifted slice is `eps + x + v`, where `eps` is one of the two small prefix
residues and `x,v` lie in bounded `H` intervals.
-/
theorem shifted_pair_slice_prefix_pair_witness {r h m t : Nat} (hp : Params r h)
    (hm : m <= 2 * r - 2) (ht : InShiftedPairSlice r h m t) :
    ∃ eps i j x v : Nat,
      (eps = 1 ∨ eps = h - 1) ∧
      i < r ∧
      j < r ∧
      i + j = m ∧
      InH r h i x ∧
      InH r h j v ∧
      eps + x + v = t := by
  rcases shifted_adjacent_pair_sum_exists_bounded
      (r := r) (h := h) (m := m) (t := t) hp hm ht with
    ⟨i, j, x, y, hi, hj, hij, hx, hy, hxy⟩
  rcases shiftedAdjacent_mem_prefix_translate
      (r := r) (h := h) (j := j) (y := y) hp hy with
    ⟨eps, v, heps, hv, heq⟩
  refine ⟨eps, i, j, x, v, heps, hi, hj, hij, hx, hv, ?_⟩
  omega

/--
The shifted-pair slice cases, repackaged with explicit prefix witnesses for
all three summands.
-/
theorem shifted_pair_slice_prefix_pair_inPrefix_witness {r h m t : Nat}
    (hp : Params r h) (hm : m <= 2 * r - 2) (ht : InShiftedPairSlice r h m t) :
    ∃ eps i j x v : Nat,
      (eps = 1 ∨ eps = h - 1) ∧
      i < r ∧
      j < r ∧
      i + j = m ∧
      InH r h i x ∧
      InH r h j v ∧
      InPrefix r h eps ∧
      InPrefix r h x ∧
      InPrefix r h v ∧
      eps + x + v = t := by
  rcases shifted_pair_slice_prefix_pair_witness
      (r := r) (h := h) (m := m) (t := t) hp hm ht with
    ⟨eps, i, j, x, v, heps, hi, hj, hij, hx, hv, hsum⟩
  rcases heps with rfl | rfl
  · exact
      ⟨1, i, j, x, v, Or.inl rfl, hi, hj, hij, hx, hv, prefix_one r h,
        prefix_of_inH hi hx, prefix_of_inH hj hv, hsum⟩
  · exact
      ⟨h - 1, i, j, x, v, Or.inr rfl, hi, hj, hij, hx, hv, prefix_h_sub_one r h,
        prefix_of_inH hi hx, prefix_of_inH hj hv, hsum⟩

theorem shifted_pair_slice_prefix_pair_candidate_witness {r h m t : Nat}
    (hp : Params r h) (hm : m <= 2 * r - 2) (ht : InShiftedPairSlice r h m t) :
    ∃ eps i j x v : Nat,
      (eps = 1 ∨ eps = h - 1) ∧
      i < r ∧
      j < r ∧
      i + j = m ∧
      InH r h i x ∧
      InH r h j v ∧
      Candidate r h eps ∧
      Candidate r h x ∧
      Candidate r h v ∧
      eps + x + v = t := by
  rcases shifted_pair_slice_prefix_pair_inPrefix_witness
      (r := r) (h := h) (m := m) (t := t) hp hm ht with
    ⟨eps, i, j, x, v, heps, hi, hj, hij, hx, hv, hpeps, hpx, hpv, hsum⟩
  exact
    ⟨eps, i, j, x, v, heps, hi, hj, hij, hx, hv,
      candidate_of_prefix hpeps, candidate_of_prefix hpx, candidate_of_prefix hpv, hsum⟩

theorem shifted_pair_slice_nonDistinct_prefix_triple {r h m t : Nat}
    (hp : Params r h) (hm : m <= 2 * r - 2) (ht : InShiftedPairSlice r h m t) :
    NonDistinctPrefixTripleSum r h t := by
  rcases shifted_pair_slice_prefix_pair_inPrefix_witness
      (r := r) (h := h) (m := m) (t := t) hp hm ht with
    ⟨eps, _i, _j, x, v, _heps, _hi, _hj, _hij, _hx, _hv, hpeps, hpx, hpv, hsum⟩
  exact ⟨eps, x, v, hpeps, hpx, hpv, hsum⟩

theorem shifted_pair_slice_nonDistinct_candidate_triple {r h m t : Nat}
    (hp : Params r h) (hm : m <= 2 * r - 2) (ht : InShiftedPairSlice r h m t) :
    NonDistinctCandidateTripleSum r h t :=
  nonDistinct_candidate_of_prefix
    (shifted_pair_slice_nonDistinct_prefix_triple
      (r := r) (h := h) (m := m) (t := t) hp hm ht)

/--
Bounded index selection for three boundary-band intervals.

If `m` lies in the possible sum-index range `0..3r-3`, then it can be
written as `i+j+k` with all three indices in the boundary `r`-band range.
-/
theorem bounded_triple_indices {r m : Nat} (hr : 1 <= r) (hm : m <= 3 * r - 3) :
    ∃ i j k : Nat, i < r ∧ j < r ∧ k < r ∧ i + j + k = m := by
  by_cases hm_pair : m <= 2 * r - 2
  · rcases bounded_pair_indices (r := r) (m := m) hr hm_pair with
      ⟨i, j, hi, hj, hij⟩
    exact ⟨i, j, 0, hi, hj, by omega, by omega⟩
  · have hm' : m - (r - 1) <= 2 * r - 2 := by omega
    rcases bounded_pair_indices (r := r) (m := m - (r - 1)) hr hm' with
      ⟨i, j, hi, hj, hij⟩
    exact ⟨i, j, r - 1, hi, hj, by omega, by omega⟩

/--
Bounded three-`H` coverage for one slice: every target in a feasible slice has
a witness from three bounded boundary-band intervals.
-/
theorem H_triple_sum_exists_bounded {r h m t : Nat} (hp : Params r h)
    (hm : m <= 3 * r - 3) (ht : InTripleHSlice r h m t) :
    ∃ i j k x y z : Nat,
      i < r ∧
      j < r ∧
      k < r ∧
      i + j + k = m ∧
      InH r h i x ∧
      InH r h j y ∧
      InH r h k z ∧
      x + y + z = t := by
  rcases bounded_triple_indices (r := r) (m := m) hp.r_pos hm with
    ⟨i, j, k, hi, hj, hk, hijk⟩
  rcases H_triple_sum_of_sum
      (r := r) (h := h) (i := i) (j := j) (k := k) (m := m) hp hijk ht with
    ⟨x, y, z, hx, hy, hz, hsum⟩
  exact ⟨i, j, k, x, y, z, hi, hj, hk, hijk, hx, hy, hz, hsum⟩

/-- The bounded slice witness repackaged as a witness from the union `U`. -/
theorem tripleHSlice_U_witness {r h m t : Nat} (hp : Params r h)
    (hm : m <= 3 * r - 3) (ht : InTripleHSlice r h m t) :
    ∃ x y z : Nat,
      InU r h x ∧ InU r h y ∧ InU r h z ∧ x + y + z = t := by
  rcases H_triple_sum_exists_bounded
      (r := r) (h := h) (m := m) (t := t) hp hm ht with
    ⟨i, j, k, x, y, z, hi, hj, hk, _hijk, hx, hy, hz, hsum⟩
  exact ⟨x, y, z, ⟨i, hi, hx⟩, ⟨j, hj, hy⟩, ⟨k, hk, hz⟩, hsum⟩

/--
The chain of all feasible three-`H` slices covers the full non-distinct
three-`U` sum range.
-/
theorem tripleHSlice_chain_cover_bounded {r h t : Nat} (hp : Params r h)
    (ht :
      InInterval (tripleHSliceLo r h 0)
        (tripleHSliceHi r h (3 * r - 3)) t) :
    ∃ m : Nat, m <= 3 * r - 3 ∧ InTripleHSlice r h m t := by
  have ht' :
      InInterval (tripleHSliceLo r h 0)
        (tripleHSliceHi r h (0 + (3 * r - 3))) t := by
    simpa using ht
  rcases tripleHSlice_chain_cover
      (r := r) (h := h) (a := 0) (n := 3 * r - 3) (t := t) hp ht' with
    ⟨m, _hmlo, hmhi, hmem⟩
  exact ⟨m, by omega, hmem⟩

theorem tripleHSlice_chain_U_witness {r h t : Nat} (hp : Params r h)
    (ht :
      InInterval (tripleHSliceLo r h 0)
        (tripleHSliceHi r h (3 * r - 3)) t) :
    ∃ x y z : Nat,
      InU r h x ∧ InU r h y ∧ InU r h z ∧ x + y + z = t := by
  rcases tripleHSlice_chain_cover_bounded
      (r := r) (h := h) (t := t) hp ht with
    ⟨m, hm, hmem⟩
  exact tripleHSlice_U_witness (r := r) (h := h) (m := m) hp hm hmem

theorem tripleHSlice_chain_nonDistinct_prefix_triple {r h t : Nat}
    (hp : Params r h)
    (ht :
      InInterval (tripleHSliceLo r h 0)
        (tripleHSliceHi r h (3 * r - 3)) t) :
    NonDistinctPrefixTripleSum r h t := by
  rcases tripleHSlice_chain_U_witness
      (r := r) (h := h) (t := t) hp ht with
    ⟨x, y, z, hx, hy, hz, hsum⟩
  exact ⟨x, y, z, prefix_of_inU hx, prefix_of_inU hy, prefix_of_inU hz, hsum⟩

theorem tripleHSlice_chain_nonDistinct_candidate_triple {r h t : Nat}
    (hp : Params r h)
    (ht :
      InInterval (tripleHSliceLo r h 0)
        (tripleHSliceHi r h (3 * r - 3)) t) :
    NonDistinctCandidateTripleSum r h t :=
  nonDistinct_candidate_of_prefix
    (tripleHSlice_chain_nonDistinct_prefix_triple
      (r := r) (h := h) (t := t) hp ht)

theorem preCGapLo_eq_HLo_last_add_h (r h : Nat) :
    preCGapLo r h = HLo r h (r - 1) + h := by
  rfl

theorem preCGapHi_eq_HHi_last_add_h (r h : Nat) :
    preCGapHi r h = HHi r h (r - 1) + h := by
  rfl

theorem preCGapHi_eq_c_sub_one {r h : Nat} (hp : Params r h) :
    preCGapHi r h = c r h - 1 := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have hcoef : 2 * (r - 1) + 2 = 2 * r := by omega
  have hprod : 2 * (r - 1) * h + 2 * h = 2 * r * h := by
    rw [← Nat.add_mul, hcoef]
  have hmul : 2 * (2 * r * h) = 4 * r * h := by
    rw [Nat.mul_assoc]
    rw [Nat.mul_assoc]
    omega
  have hbig : 2 <= 4 * r * h := by
    have hcoef4 : 4 <= 4 * r := by omega
    have hprod4 : 4 * h <= 4 * r * h := Nat.mul_le_mul_right h hcoef4
    omega
  unfold preCGapHi HHi HLo D c
  omega

theorem preCGapLo_le_preCGapHi {r h : Nat} (hp : Params r h) :
    preCGapLo r h <= preCGapHi r h := by
  have hH := HLo_le_HHi (r := r) (h := h) (i := r - 1) hp
  unfold preCGapLo preCGapHi
  omega

/-- Coverage of any internal prefix gap by `1 + (h-1) + H_i`. -/
theorem prefix_internal_gap_prefix_witness {r h i t : Nat}
    (hp : Params r h) (hi : i < r)
    (ht : InInterval (HLo r h i + h) (HHi r h i + h) t) :
    ∃ x : Nat,
      InH r h i x ∧
      InPrefix r h 1 ∧
      InPrefix r h (h - 1) ∧
      InPrefix r h x ∧
      1 + (h - 1) + x = t := by
  let x := t - h
  have hh := hp.h_ge_six
  have hxH : InH r h i x := by
    unfold x
    unfold InH InInterval
    constructor
    · apply Nat.le_sub_of_add_le
      exact ht.1
    · rw [Nat.sub_le_iff_le_add]
      exact ht.2
  have hxPrefix : InPrefix r h x :=
    prefix_of_inH (r := r) (h := h) (i := i) (x := x) hi hxH
  refine ⟨x, hxH, prefix_one r h, prefix_h_sub_one r h, hxPrefix, ?_⟩
  unfold x
  have hle : h <= t := by
    have hD := D_ge_h_add_one (r := r) (h := h) hp
    have htlo := ht.1
    unfold HLo at htlo
    omega
  have hprefix : 1 + (h - 1) = h := by omega
  rw [hprefix]
  exact Nat.add_sub_of_le hle

theorem prefix_internal_gap_candidate_witness {r h i t : Nat}
    (hp : Params r h) (hi : i < r)
    (ht : InInterval (HLo r h i + h) (HHi r h i + h) t) :
    ∃ x : Nat,
      InH r h i x ∧
      Candidate r h 1 ∧
      Candidate r h (h - 1) ∧
      Candidate r h x ∧
      1 + (h - 1) + x = t := by
  rcases prefix_internal_gap_prefix_witness
      (r := r) (h := h) (i := i) (t := t) hp hi ht with
    ⟨x, hx, h1, hh1, hpx, hsum⟩
  exact
    ⟨x, hx, candidate_of_prefix h1, candidate_of_prefix hh1,
      candidate_of_prefix hpx, hsum⟩

theorem preC_gap_prefix_witness {r h t : Nat} (hp : Params r h)
    (ht : InInterval (preCGapLo r h) (preCGapHi r h) t) :
    ∃ x : Nat,
      InH r h (r - 1) x ∧
      InPrefix r h 1 ∧
      InPrefix r h (h - 1) ∧
      InPrefix r h x ∧
      1 + (h - 1) + x = t := by
  have hlast : r - 1 < r := by
    have hr := hp.r_pos
    omega
  exact prefix_internal_gap_prefix_witness
    (r := r) (h := h) (i := r - 1) (t := t) hp hlast ht

theorem preC_gap_nonDistinct_prefix_triple {r h t : Nat} (hp : Params r h)
    (ht : InInterval (preCGapLo r h) (preCGapHi r h) t) :
    NonDistinctPrefixTripleSum r h t := by
  rcases preC_gap_prefix_witness
      (r := r) (h := h) (t := t) hp ht with
    ⟨x, _hx, h1, hh1, hpx, hsum⟩
  exact ⟨1, h - 1, x, h1, hh1, hpx, hsum⟩

theorem preC_gap_nonDistinct_candidate_triple {r h t : Nat} (hp : Params r h)
    (ht : InInterval (preCGapLo r h) (preCGapHi r h) t) :
    NonDistinctCandidateTripleSum r h t :=
  nonDistinct_candidate_of_prefix
    (preC_gap_nonDistinct_prefix_triple
      (r := r) (h := h) (t := t) hp ht)

theorem finalPrefixGapLo_eq_c_add_one (r h : Nat) :
    finalPrefixGapLo r h = c r h + 1 := by
  rfl

theorem finalPrefixGapHi_eq_M_add_VBot_sub_one (r h : Nat) :
    finalPrefixGapHi r h = M r h + VBot r h - 1 := by
  rfl

theorem finalPrefixGapHi_eq_formula {r h : Nat} (hp : Params r h) :
    finalPrefixGapHi r h = (12 * r - 2) * h - 6 := by
  have hsum : M r h + VBot r h = (12 * r - 2) * h - 5 := by
    have hr := hp.r_pos
    have hh := hp.h_ge_six
    have hcoef : (10 * r - 2) + 2 * r = 12 * r - 2 := by omega
    have hprod : (10 * r - 2) * h + 2 * r * h = (12 * r - 2) * h := by
      rw [← Nat.add_mul, hcoef]
    have hbigD : 2 <= 2 * r * h := by
      have hcoef2 : 2 <= 2 * r := by omega
      have hprod2 : 2 * h <= 2 * r * h := Nat.mul_le_mul_right h hcoef2
      omega
    have hbigM : 3 <= (10 * r - 2) * h := by
      have hcoef10 : 8 <= 10 * r - 2 := by omega
      have hprod10 : 8 * h <= (10 * r - 2) * h := Nat.mul_le_mul_right h hcoef10
      omega
    unfold M VBot D
    omega
  unfold finalPrefixGapHi
  rw [hsum]
  omega

theorem shiftedPairSlice_global_lo_eq_finalPrefixGapLo {r h : Nat} (hp : Params r h) :
    shiftedPairSliceLo r h 0 = finalPrefixGapLo r h := by
  have hmul : 2 * (2 * r * h) = 4 * r * h := by
    rw [Nat.mul_assoc]
    rw [Nat.mul_assoc]
    omega
  have hbig : 2 <= 4 * r * h := by
    have hr := hp.r_pos
    have hh := hp.h_ge_six
    have hcoef4 : 4 <= 4 * r := by omega
    have hprod4 : 4 * h <= 4 * r * h := Nat.mul_le_mul_right h hcoef4
    omega
  unfold shiftedPairSliceLo finalPrefixGapLo c D
  rw [Nat.mul_sub_left_distrib]
  rw [hmul]
  omega

theorem shiftedPairSlice_global_hi_eq {r h : Nat} (hp : Params r h) :
    shiftedPairSliceHi r h (2 * r - 2) =
      2 * D r h + (4 * r - 1) * h - 4 := by
  have hr := hp.r_pos
  have hcoef : 2 * (2 * r - 2) + 3 = 4 * r - 1 := by omega
  have hprod : 2 * (2 * r - 2) * h + 3 * h = (4 * r - 1) * h := by
    rw [← Nat.add_mul, hcoef]
  unfold shiftedPairSliceHi
  omega

theorem shiftedPairSlice_chain_cover_bounded {r h t : Nat} (hp : Params r h)
    (ht :
      InInterval (finalPrefixGapLo r h)
        (2 * D r h + (4 * r - 1) * h - 4) t) :
    ∃ m : Nat, m <= 2 * r - 2 ∧ InShiftedPairSlice r h m t := by
  have ht' :
      InInterval (shiftedPairSliceLo r h 0)
        (shiftedPairSliceHi r h (0 + (2 * r - 2))) t := by
    rw [shiftedPairSlice_global_lo_eq_finalPrefixGapLo hp]
    have hhi := shiftedPairSlice_global_hi_eq (r := r) (h := h) hp
    simpa [hhi]
  rcases shiftedPairSlice_chain_cover
      (r := r) (h := h) (a := 0) (n := 2 * r - 2) (t := t) hp ht' with
    ⟨m, _hmlo, hmhi, hmem⟩
  exact ⟨m, by omega, hmem⟩

theorem shiftedPairSlice_chain_prefix_pair_inPrefix_witness {r h t : Nat}
    (hp : Params r h)
    (ht :
      InInterval (finalPrefixGapLo r h)
        (2 * D r h + (4 * r - 1) * h - 4) t) :
    ∃ m eps i j x v : Nat,
      m <= 2 * r - 2 ∧
      (eps = 1 ∨ eps = h - 1) ∧
      i < r ∧
      j < r ∧
      i + j = m ∧
      InH r h i x ∧
      InH r h j v ∧
      InPrefix r h eps ∧
      InPrefix r h x ∧
      InPrefix r h v ∧
      eps + x + v = t := by
  rcases shiftedPairSlice_chain_cover_bounded
      (r := r) (h := h) (t := t) hp ht with
    ⟨m, hm, hmem⟩
  rcases shifted_pair_slice_prefix_pair_inPrefix_witness
      (r := r) (h := h) (m := m) (t := t) hp hm hmem with
    ⟨eps, i, j, x, v, heps, hi, hj, hij, hx, hv, hpeps, hpx, hpv, hsum⟩
  exact ⟨m, eps, i, j, x, v, hm, heps, hi, hj, hij, hx, hv, hpeps, hpx, hpv, hsum⟩

theorem shiftedPairSlice_chain_nonDistinct_prefix_triple {r h t : Nat}
    (hp : Params r h)
    (ht :
      InInterval (finalPrefixGapLo r h)
        (2 * D r h + (4 * r - 1) * h - 4) t) :
    NonDistinctPrefixTripleSum r h t := by
  rcases shiftedPairSlice_chain_prefix_pair_inPrefix_witness
      (r := r) (h := h) (t := t) hp ht with
    ⟨_m, eps, _i, _j, x, v, _hm, _heps, _hi, _hj, _hij, _hx, _hv,
      hpeps, hpx, hpv, hsum⟩
  exact ⟨eps, x, v, hpeps, hpx, hpv, hsum⟩

theorem shiftedPairSlice_chain_nonDistinct_candidate_triple {r h t : Nat}
    (hp : Params r h)
    (ht :
      InInterval (finalPrefixGapLo r h)
        (2 * D r h + (4 * r - 1) * h - 4) t) :
    NonDistinctCandidateTripleSum r h t :=
  nonDistinct_candidate_of_prefix
    (shiftedPairSlice_chain_nonDistinct_prefix_triple
      (r := r) (h := h) (t := t) hp ht)

theorem tripleHSlice_global_lo_eq (r h : Nat) :
    tripleHSliceLo r h 0 = 3 * D r h := by
  unfold tripleHSliceLo
  omega

theorem tripleHSlice_global_hi_eq {r h : Nat} (hp : Params r h) :
    tripleHSliceHi r h (3 * r - 3) =
      3 * D r h + (6 * r - 3) * h - 3 := by
  have hr := hp.r_pos
  have hcoef : 2 * (3 * r - 3) + 3 = 6 * r - 3 := by omega
  have hprod : 2 * (3 * r - 3) * h + 3 * h = (6 * r - 3) * h := by
    rw [← Nat.add_mul, hcoef]
  unfold tripleHSliceHi
  omega

theorem tripleHSlice_global_lo_le_shiftedPair_global_hi_succ {r h : Nat}
    (hp : Params r h) :
    tripleHSliceLo r h 0 <=
      (2 * D r h + (4 * r - 1) * h - 4) + 1 := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have hDle : D r h + 3 <= (4 * r - 1) * h := by
    have hcoef : 2 * r + 1 <= 4 * r - 1 := by omega
    have hprod : (2 * r + 1) * h <= (4 * r - 1) * h :=
      Nat.mul_le_mul_right h hcoef
    rw [Nat.add_mul] at hprod
    unfold D
    omega
  unfold tripleHSliceLo
  omega

end BoundaryRBand
end GreedyThreeSumfree
