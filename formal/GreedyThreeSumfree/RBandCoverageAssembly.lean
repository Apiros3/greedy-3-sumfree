import GreedyThreeSumfree.RBandTripleCoverage

namespace GreedyThreeSumfree
namespace RBand

/--
Non-distinct triple sum from the regular-band prefix.

This intentionally does not encode ordering or distinctness.
-/
def NonDistinctPrefixTripleSum (r h e t : Nat) : Prop :=
  ∃ x y z : Nat,
    InPrefix r h e x ∧ InPrefix r h e y ∧ InPrefix r h e z ∧
      x + y + z = t

/--
Non-distinct triple sum from the regular-band candidate set.

This intentionally does not encode ordering, distinctness, or the requirement
that the three summands are smaller than the target.
-/
def NonDistinctCandidateTripleSum (r h e t : Nat) : Prop :=
  ∃ x y z : Nat,
    Candidate r h e x ∧ Candidate r h e y ∧ Candidate r h e z ∧
      x + y + z = t

def finalPrefixGapLo (r h e : Nat) : Nat := D r h e + (2 * r - 1) * h

def finalPrefixGapFirstHi (r h e : Nat) : Nat := D r h e + 2 * r * h - 1

def finalPrefixGapHi (r h e : Nat) : Nat :=
  3 * D r h e + (6 * r - 3) * h - 6

theorem prefix_one (r h e : Nat) : InPrefix r h e 1 := by
  exact Or.inl rfl

theorem prefix_h_sub_one (r h e : Nat) : InPrefix r h e (h - 1) := by
  exact Or.inr (Or.inl rfl)

theorem prefix_of_inU {r h e x : Nat} (hx : InU r h e x) :
    InPrefix r h e x := by
  exact Or.inr (Or.inr hx)

theorem prefix_of_inH {r h e i x : Nat} (hi : i < r) (hx : InH r h e i x) :
    InPrefix r h e x := by
  exact prefix_of_inU (r := r) (h := h) (e := e) ⟨i, hi, hx⟩

theorem candidate_of_prefix {r h e x : Nat} (hx : InPrefix r h e x) :
    Candidate r h e x := by
  exact Or.inl hx

theorem candidate_one (r h e : Nat) : Candidate r h e 1 :=
  candidate_of_prefix (prefix_one r h e)

theorem candidate_h_sub_one (r h e : Nat) : Candidate r h e (h - 1) :=
  candidate_of_prefix (prefix_h_sub_one r h e)

theorem candidate_of_inU {r h e x : Nat} (hx : InU r h e x) :
    Candidate r h e x :=
  candidate_of_prefix (prefix_of_inU hx)

theorem candidate_of_inH {r h e i x : Nat} (hi : i < r) (hx : InH r h e i x) :
    Candidate r h e x :=
  candidate_of_prefix (prefix_of_inH hi hx)

theorem nonDistinct_candidate_of_prefix {r h e t : Nat}
    (ht : NonDistinctPrefixTripleSum r h e t) :
    NonDistinctCandidateTripleSum r h e t := by
  rcases ht with ⟨x, y, z, hx, hy, hz, hsum⟩
  exact ⟨x, y, z, candidate_of_prefix hx, candidate_of_prefix hy, candidate_of_prefix hz, hsum⟩

/--
The shifted-pair slice cases, repackaged with explicit prefix witnesses for
all three summands.
-/
theorem shifted_pair_slice_prefix_pair_inPrefix_cases {r h e m t : Nat}
    (hp : Params r h e) (hm : m <= 2 * r - 2) (ht : InShiftedPairSlice r h e m t) :
    (∃ i j x v : Nat,
      i < r ∧
      j < r ∧
      i + j = m ∧
      InH r h e i x ∧
      InH r h e j v ∧
      InPrefix r h e 1 ∧
      InPrefix r h e x ∧
      InPrefix r h e v ∧
      1 + x + v = t) ∨
    (∃ i j x v : Nat,
      i < r ∧
      j < r ∧
      i + j = m ∧
      InH r h e i x ∧
      InH r h e j v ∧
      InPrefix r h e (h - 1) ∧
      InPrefix r h e x ∧
      InPrefix r h e v ∧
      (h - 1) + x + v = t) := by
  rcases shifted_pair_slice_prefix_pair_cases
      (r := r) (h := h) (e := e) (m := m) (t := t) hp hm ht with hcase | hcase
  · rcases hcase with ⟨i, j, x, v, hi, hj, hij, hx, hv, hsum⟩
    exact Or.inl
      ⟨i, j, x, v, hi, hj, hij, hx, hv, prefix_one r h e,
        prefix_of_inH hi hx, prefix_of_inH hj hv, hsum⟩
  · rcases hcase with ⟨i, j, x, v, hi, hj, hij, hx, hv, hsum⟩
    exact Or.inr
      ⟨i, j, x, v, hi, hj, hij, hx, hv, prefix_h_sub_one r h e,
        prefix_of_inH hi hx, prefix_of_inH hj hv, hsum⟩

/--
The shifted-pair slice cases, repackaged with candidate witnesses for all
three summands.
-/
theorem shifted_pair_slice_prefix_pair_candidate_cases {r h e m t : Nat}
    (hp : Params r h e) (hm : m <= 2 * r - 2) (ht : InShiftedPairSlice r h e m t) :
    (∃ i j x v : Nat,
      i < r ∧
      j < r ∧
      i + j = m ∧
      InH r h e i x ∧
      InH r h e j v ∧
      Candidate r h e 1 ∧
      Candidate r h e x ∧
      Candidate r h e v ∧
      1 + x + v = t) ∨
    (∃ i j x v : Nat,
      i < r ∧
      j < r ∧
      i + j = m ∧
      InH r h e i x ∧
      InH r h e j v ∧
      Candidate r h e (h - 1) ∧
      Candidate r h e x ∧
      Candidate r h e v ∧
      (h - 1) + x + v = t) := by
  rcases shifted_pair_slice_prefix_pair_inPrefix_cases
      (r := r) (h := h) (e := e) (m := m) (t := t) hp hm ht with hcase | hcase
  · rcases hcase with ⟨i, j, x, v, hi, hj, hij, hx, hv, h1, hpx, hpv, hsum⟩
    exact Or.inl
      ⟨i, j, x, v, hi, hj, hij, hx, hv, candidate_of_prefix h1,
        candidate_of_prefix hpx, candidate_of_prefix hpv, hsum⟩
  · rcases hcase with ⟨i, j, x, v, hi, hj, hij, hx, hv, heps, hpx, hpv, hsum⟩
    exact Or.inr
      ⟨i, j, x, v, hi, hj, hij, hx, hv, candidate_of_prefix heps,
        candidate_of_prefix hpx, candidate_of_prefix hpv, hsum⟩

theorem shifted_pair_slice_prefix_pair_inPrefix_witness {r h e m t : Nat}
    (hp : Params r h e) (hm : m <= 2 * r - 2) (ht : InShiftedPairSlice r h e m t) :
    ∃ eps i j x v : Nat,
      (eps = 1 ∨ eps = h - 1) ∧
      i < r ∧
      j < r ∧
      i + j = m ∧
      InH r h e i x ∧
      InH r h e j v ∧
      InPrefix r h e eps ∧
      InPrefix r h e x ∧
      InPrefix r h e v ∧
      eps + x + v = t := by
  rcases shifted_pair_slice_prefix_pair_inPrefix_cases
      (r := r) (h := h) (e := e) (m := m) (t := t) hp hm ht with hcase | hcase
  · rcases hcase with ⟨i, j, x, v, hi, hj, hij, hx, hv, h1, hpx, hpv, hsum⟩
    exact ⟨1, i, j, x, v, Or.inl rfl, hi, hj, hij, hx, hv, h1, hpx, hpv, hsum⟩
  · rcases hcase with ⟨i, j, x, v, hi, hj, hij, hx, hv, heps, hpx, hpv, hsum⟩
    exact ⟨h - 1, i, j, x, v, Or.inr rfl, hi, hj, hij, hx, hv, heps, hpx, hpv, hsum⟩

theorem shifted_pair_slice_prefix_pair_candidate_witness {r h e m t : Nat}
    (hp : Params r h e) (hm : m <= 2 * r - 2) (ht : InShiftedPairSlice r h e m t) :
    ∃ eps i j x v : Nat,
      (eps = 1 ∨ eps = h - 1) ∧
      i < r ∧
      j < r ∧
      i + j = m ∧
      InH r h e i x ∧
      InH r h e j v ∧
      Candidate r h e eps ∧
      Candidate r h e x ∧
      Candidate r h e v ∧
      eps + x + v = t := by
  rcases shifted_pair_slice_prefix_pair_inPrefix_witness
      (r := r) (h := h) (e := e) (m := m) (t := t) hp hm ht with
    ⟨eps, i, j, x, v, heps, hi, hj, hij, hx, hv, hpeps, hpx, hpv, hsum⟩
  exact
    ⟨eps, i, j, x, v, heps, hi, hj, hij, hx, hv,
      candidate_of_prefix hpeps, candidate_of_prefix hpx, candidate_of_prefix hpv, hsum⟩

theorem shifted_pair_slice_nonDistinct_prefix_triple {r h e m t : Nat}
    (hp : Params r h e) (hm : m <= 2 * r - 2) (ht : InShiftedPairSlice r h e m t) :
    NonDistinctPrefixTripleSum r h e t := by
  rcases shifted_pair_slice_prefix_pair_inPrefix_witness
      (r := r) (h := h) (e := e) (m := m) (t := t) hp hm ht with
    ⟨eps, i, j, x, v, _heps, _hi, _hj, _hij, _hx, _hv, hpeps, hpx, hpv, hsum⟩
  exact ⟨eps, x, v, hpeps, hpx, hpv, hsum⟩

theorem shifted_pair_slice_nonDistinct_candidate_triple {r h e m t : Nat}
    (hp : Params r h e) (hm : m <= 2 * r - 2) (ht : InShiftedPairSlice r h e m t) :
    NonDistinctCandidateTripleSum r h e t :=
  nonDistinct_candidate_of_prefix
    (shifted_pair_slice_nonDistinct_prefix_triple
      (r := r) (h := h) (e := e) (m := m) (t := t) hp hm ht)

theorem shiftedPairSlice_global_lo_eq (r h e : Nat) :
    shiftedPairSliceLo r h e 0 = 2 * D r h e + 2 := by
  unfold shiftedPairSliceLo
  omega

theorem shiftedPairSlice_global_hi_eq {r h e : Nat} (hp : Params r h e) :
    shiftedPairSliceHi r h e (2 * r - 2) =
      2 * D r h e + (4 * r - 1) * h - 4 := by
  have hr := hp.r_pos
  have hcoef : 2 * (2 * r - 2) + 3 = 4 * r - 1 := by omega
  have hprod : 2 * (2 * r - 2) * h + 3 * h = (4 * r - 1) * h := by
    rw [← Nat.add_mul, hcoef]
  unfold shiftedPairSliceHi
  omega

theorem tripleHSlice_global_lo_le_shiftedPair_global_hi_succ {r h e : Nat}
    (hp : Params r h e) :
    tripleHSliceLo r h e 0 <=
      (2 * D r h e + (4 * r - 1) * h - 4) + 1 := by
  rw [tripleHSlice_global_lo_eq]
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have he := hp.e_le_h_sub_two
  have htwo_le : 2 <= 2 * r := by omega
  have h2h_le : 2 * h <= 2 * r * h :=
    Nat.mul_le_mul_right h htwo_le
  have he3_le_h1 : e + 3 <= h + 1 := by omega
  have h1_le_2h : h + 1 <= 2 * h := by omega
  have he3_le_2rh : e + 3 <= 2 * r * h :=
    Nat.le_trans (Nat.le_trans he3_le_h1 h1_le_2h) h2h_le
  have hcoef : (2 * r - 1) + 2 * r = 4 * r - 1 := by omega
  have hprod : (2 * r - 1) * h + 2 * r * h = (4 * r - 1) * h := by
    rw [← Nat.add_mul, hcoef]
  have hDadd : D r h e + 3 <= (4 * r - 1) * h := by
    unfold D
    rw [← hprod]
    omega
  have hraw :
      3 * D r h e + 3 <= 2 * D r h e + (4 * r - 1) * h := by
    omega
  have hle_sub :
      3 * D r h e <= 2 * D r h e + (4 * r - 1) * h - 3 :=
    Nat.le_sub_of_add_le hraw
  have hlarge : 4 <= 2 * D r h e + (4 * r - 1) * h := by
    have hD := D_ge_three (r := r) (h := h) (e := e) hp
    omega
  have hsub :
      2 * D r h e + (4 * r - 1) * h - 3 =
        (2 * D r h e + (4 * r - 1) * h - 4) + 1 := by
    omega
  simpa [hsub] using hle_sub

theorem finalPrefixGapHi_le_tripleHSlice_global_hi {r h e : Nat}
    (hp : Params r h e) :
    finalPrefixGapHi r h e <= tripleHSliceHi r h e (3 * r - 3) := by
  have hglob := tripleHSlice_global_hi_eq (r := r) (h := h) (e := e) hp
  rw [hglob]
  unfold finalPrefixGapHi
  exact Nat.sub_le_sub_left (by omega : 3 <= 6)
    (3 * D r h e + (6 * r - 3) * h)

theorem finalPrefixGapLo_eq_HLo_last_add_h {r h e : Nat} (hp : Params r h e) :
    finalPrefixGapLo r h e = HLo r h e (r - 1) + h := by
  have hr := hp.r_pos
  have hcoef : 2 * (r - 1) + 1 = 2 * r - 1 := by omega
  unfold finalPrefixGapLo HLo
  rw [← hcoef, Nat.add_mul, Nat.one_mul]
  omega

theorem finalPrefixGapFirstHi_eq_HHi_last_add_h {r h e : Nat}
    (hp : Params r h e) :
    finalPrefixGapFirstHi r h e = HHi r h e (r - 1) + h := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have hcoef : 2 * (r - 1) + 2 = 2 * r := by omega
  unfold finalPrefixGapFirstHi HHi HLo
  rw [← hcoef, Nat.add_mul]
  omega

/--
The chain of all shifted-pair slices `m=0..2r-2` covers the global shifted
pair interval.
-/
theorem shiftedPairSlice_chain_cover_bounded {r h e t : Nat} (hp : Params r h e)
    (ht :
      InInterval (2 * D r h e + 2)
        (2 * D r h e + (4 * r - 1) * h - 4) t) :
    ∃ m : Nat, m <= 2 * r - 2 ∧ InShiftedPairSlice r h e m t := by
  have ht' :
      InInterval (shiftedPairSliceLo r h e 0)
        (shiftedPairSliceHi r h e (0 + (2 * r - 2))) t := by
    rw [shiftedPairSlice_global_lo_eq]
    have hhi := shiftedPairSlice_global_hi_eq (r := r) (h := h) (e := e) hp
    simpa [hhi]
  rcases shiftedPairSlice_chain_cover
      (r := r) (h := h) (e := e) (a := 0) (n := 2 * r - 2) (t := t) hp ht' with
    ⟨m, _hmlo, hmhi, hmem⟩
  exact ⟨m, by omega, hmem⟩

theorem shiftedPairSlice_chain_prefix_pair_inPrefix_witness {r h e t : Nat}
    (hp : Params r h e)
    (ht :
      InInterval (2 * D r h e + 2)
        (2 * D r h e + (4 * r - 1) * h - 4) t) :
    ∃ m eps i j x v : Nat,
      m <= 2 * r - 2 ∧
      (eps = 1 ∨ eps = h - 1) ∧
      i < r ∧
      j < r ∧
      i + j = m ∧
      InH r h e i x ∧
      InH r h e j v ∧
      InPrefix r h e eps ∧
      InPrefix r h e x ∧
      InPrefix r h e v ∧
      eps + x + v = t := by
  rcases shiftedPairSlice_chain_cover_bounded
      (r := r) (h := h) (e := e) (t := t) hp ht with
    ⟨m, hm, hmem⟩
  rcases shifted_pair_slice_prefix_pair_inPrefix_witness
      (r := r) (h := h) (e := e) (m := m) (t := t) hp hm hmem with
    ⟨eps, i, j, x, v, heps, hi, hj, hij, hx, hv, hpeps, hpx, hpv, hsum⟩
  exact ⟨m, eps, i, j, x, v, hm, heps, hi, hj, hij, hx, hv, hpeps, hpx, hpv, hsum⟩

theorem shiftedPairSlice_chain_prefix_pair_candidate_witness {r h e t : Nat}
    (hp : Params r h e)
    (ht :
      InInterval (2 * D r h e + 2)
        (2 * D r h e + (4 * r - 1) * h - 4) t) :
    ∃ m eps i j x v : Nat,
      m <= 2 * r - 2 ∧
      (eps = 1 ∨ eps = h - 1) ∧
      i < r ∧
      j < r ∧
      i + j = m ∧
      InH r h e i x ∧
      InH r h e j v ∧
      Candidate r h e eps ∧
      Candidate r h e x ∧
      Candidate r h e v ∧
      eps + x + v = t := by
  rcases shiftedPairSlice_chain_prefix_pair_inPrefix_witness
      (r := r) (h := h) (e := e) (t := t) hp ht with
    ⟨m, eps, i, j, x, v, hm, heps, hi, hj, hij, hx, hv, hpeps, hpx, hpv, hsum⟩
  exact
    ⟨m, eps, i, j, x, v, hm, heps, hi, hj, hij, hx, hv,
      candidate_of_prefix hpeps, candidate_of_prefix hpx, candidate_of_prefix hpv, hsum⟩

theorem shiftedPairSlice_chain_nonDistinct_prefix_triple {r h e t : Nat}
    (hp : Params r h e)
    (ht :
      InInterval (2 * D r h e + 2)
        (2 * D r h e + (4 * r - 1) * h - 4) t) :
    NonDistinctPrefixTripleSum r h e t := by
  rcases shiftedPairSlice_chain_prefix_pair_inPrefix_witness
      (r := r) (h := h) (e := e) (t := t) hp ht with
    ⟨_m, eps, _i, _j, x, v, _hm, _heps, _hi, _hj, _hij, _hx, _hv,
      hpeps, hpx, hpv, hsum⟩
  exact ⟨eps, x, v, hpeps, hpx, hpv, hsum⟩

theorem shiftedPairSlice_chain_nonDistinct_candidate_triple {r h e t : Nat}
    (hp : Params r h e)
    (ht :
      InInterval (2 * D r h e + 2)
        (2 * D r h e + (4 * r - 1) * h - 4) t) :
    NonDistinctCandidateTripleSum r h e t :=
  nonDistinct_candidate_of_prefix
    (shiftedPairSlice_chain_nonDistinct_prefix_triple
      (r := r) (h := h) (e := e) (t := t) hp ht)

/-- Coverage of the first part of the final prefix gap by `1 + (h-1) + H_{r-1}`. -/
theorem final_prefix_gap_first_prefix_witness {r h e t : Nat} (hp : Params r h e)
    (ht : InInterval (finalPrefixGapLo r h e) (finalPrefixGapFirstHi r h e) t) :
    ∃ x : Nat,
      InH r h e (r - 1) x ∧
      InPrefix r h e 1 ∧
      InPrefix r h e (h - 1) ∧
      InPrefix r h e x ∧
      1 + (h - 1) + x = t := by
  let x := t - h
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have hxH : InH r h e (r - 1) x := by
    constructor
    · unfold x
      apply Nat.le_sub_of_add_le
      rw [← finalPrefixGapLo_eq_HLo_last_add_h
        (r := r) (h := h) (e := e) hp]
      exact ht.1
    · unfold x
      rw [Nat.sub_le_iff_le_add]
      rw [← finalPrefixGapFirstHi_eq_HHi_last_add_h
        (r := r) (h := h) (e := e) hp]
      exact ht.2
  have hxPrefix : InPrefix r h e x :=
    prefix_of_inH (r := r) (h := h) (e := e) (i := r - 1) (x := x) (by omega) hxH
  refine ⟨x, hxH, prefix_one r h e, prefix_h_sub_one r h e, hxPrefix, ?_⟩
  unfold x
  have hle : h <= t := by
    have hD := D_ge_h_add_one (r := r) (h := h) (e := e) hp
    have hD_le_lo : D r h e <= finalPrefixGapLo r h e := by
      unfold finalPrefixGapLo
      omega
    exact Nat.le_trans (by omega : h <= D r h e) (Nat.le_trans hD_le_lo ht.1)
  have hprefix : 1 + (h - 1) = h := by omega
  rw [hprefix]
  exact Nat.add_sub_of_le hle

theorem final_prefix_gap_first_nonDistinct_prefix_triple {r h e t : Nat}
    (hp : Params r h e)
    (ht : InInterval (finalPrefixGapLo r h e) (finalPrefixGapFirstHi r h e) t) :
    NonDistinctPrefixTripleSum r h e t := by
  rcases final_prefix_gap_first_prefix_witness
      (r := r) (h := h) (e := e) (t := t) hp ht with
    ⟨x, _hxH, h1, hh1, hx, hsum⟩
  exact ⟨1, h - 1, x, h1, hh1, hx, hsum⟩

theorem final_prefix_gap_first_nonDistinct_candidate_triple {r h e t : Nat}
    (hp : Params r h e)
    (ht : InInterval (finalPrefixGapLo r h e) (finalPrefixGapFirstHi r h e) t) :
    NonDistinctCandidateTripleSum r h e t :=
  nonDistinct_candidate_of_prefix
    (final_prefix_gap_first_nonDistinct_prefix_triple
      (r := r) (h := h) (e := e) (t := t) hp ht)

/--
The three-`U` chain witness, made explicit as non-distinct prefix coverage.
Mixed-index distinctness is deliberately not claimed here.
-/
theorem tripleHSlice_chain_nonDistinct_prefix_triple {r h e t : Nat}
    (hp : Params r h e)
    (ht :
      InInterval (tripleHSliceLo r h e 0)
        (tripleHSliceHi r h e (3 * r - 3)) t) :
    NonDistinctPrefixTripleSum r h e t := by
  rcases tripleHSlice_chain_U_witness
      (r := r) (h := h) (e := e) (t := t) hp ht with
    ⟨x, y, z, hx, hy, hz, hsum⟩
  exact
    ⟨x, y, z, prefix_of_inU hx, prefix_of_inU hy, prefix_of_inU hz, hsum⟩

theorem tripleHSlice_chain_nonDistinct_candidate_triple {r h e t : Nat}
    (hp : Params r h e)
    (ht :
      InInterval (tripleHSliceLo r h e 0)
        (tripleHSliceHi r h e (3 * r - 3)) t) :
    NonDistinctCandidateTripleSum r h e t :=
  nonDistinct_candidate_of_prefix
    (tripleHSlice_chain_nonDistinct_prefix_triple
      (r := r) (h := h) (e := e) (t := t) hp ht)

/--
Final prefix gap coverage assembled from:
* `1 + (h-1) + H_{r-1}`;
* the shifted pair-slice chain in prefix-pair form;
* the non-distinct three-`U` chain.

The resulting triple is a non-distinct prefix triple; no mixed-index
three-`U` distinctness is claimed.
-/
theorem final_prefix_gap_nonDistinct_prefix_covered {r h e t : Nat}
    (hp : Params r h e)
    (ht : InInterval (finalPrefixGapLo r h e) (finalPrefixGapHi r h e) t) :
    NonDistinctPrefixTripleSum r h e t := by
  by_cases hfirst : t <= finalPrefixGapFirstHi r h e
  · exact final_prefix_gap_first_nonDistinct_prefix_triple
      (r := r) (h := h) (e := e) (t := t) hp ⟨ht.1, hfirst⟩
  · by_cases hshift : t <= 2 * D r h e + (4 * r - 1) * h - 4
    · have hlo : 2 * D r h e + 2 <= t := by
        have hDnext := D_add_two_le_next_grid (r := r) (h := h) (e := e) hp
        unfold finalPrefixGapFirstHi at hfirst
        omega
      exact shiftedPairSlice_chain_nonDistinct_prefix_triple
        (r := r) (h := h) (e := e) (t := t) hp ⟨hlo, hshift⟩
    · have hlo3 : 3 * D r h e <= t := by
        have hsucc :
            (2 * D r h e + (4 * r - 1) * h - 4) + 1 <= t :=
          Nat.succ_le_of_lt (Nat.lt_of_not_ge hshift)
        have hlo_overlap :=
          tripleHSlice_global_lo_le_shiftedPair_global_hi_succ
            (r := r) (h := h) (e := e) hp
        rw [tripleHSlice_global_lo_eq] at hlo_overlap
        exact Nat.le_trans hlo_overlap hsucc
      have hhi3 : t <= tripleHSliceHi r h e (3 * r - 3) := by
        exact Nat.le_trans ht.2
          (finalPrefixGapHi_le_tripleHSlice_global_hi
            (r := r) (h := h) (e := e) hp)
      have ht3 :
          InInterval (tripleHSliceLo r h e 0)
            (tripleHSliceHi r h e (3 * r - 3)) t := by
        constructor
        · rw [tripleHSlice_global_lo_eq]
          exact hlo3
        · exact hhi3
      exact tripleHSlice_chain_nonDistinct_prefix_triple
        (r := r) (h := h) (e := e) (t := t) hp ht3

theorem final_prefix_gap_nonDistinct_candidate_covered {r h e t : Nat}
    (hp : Params r h e)
    (ht : InInterval (finalPrefixGapLo r h e) (finalPrefixGapHi r h e) t) :
    NonDistinctCandidateTripleSum r h e t :=
  nonDistinct_candidate_of_prefix
    (final_prefix_gap_nonDistinct_prefix_covered
      (r := r) (h := h) (e := e) (t := t) hp ht)

end RBand
end GreedyThreeSumfree
