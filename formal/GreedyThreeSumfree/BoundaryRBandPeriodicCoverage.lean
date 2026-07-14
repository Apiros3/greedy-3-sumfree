import GreedyThreeSumfree.BoundaryRBandDistinctCoverage
import GreedyThreeSumfree.BoundaryRBandPeriodicSafetyFinal

namespace GreedyThreeSumfree
namespace BoundaryRBand

/--
Membership in the translate `K_i + h`, recorded with the original `K_i`
witness. This is the offset form of an internal periodic gap.
-/
def InKAddH (r h i t : Nat) : Prop :=
  ∃ v : Nat, InK r h i v ∧ v + h = t

/-- Interval membership in `K_i+h` gives the corresponding translated witness. -/
theorem inKAddH_of_interval {r h i t : Nat}
    (ht : InInterval (KLo r h i + h) (KHi r h i + h) t) :
    InKAddH r h i t := by
  let v := t - h
  have hh_le_t : h <= t := by
    exact Nat.le_trans (Nat.le_add_left h (KLo r h i)) ht.1
  have hvlo : KLo r h i <= v := by
    dsimp [v]
    exact Nat.le_sub_of_add_le ht.1
  have hvhi : v <= KHi r h i := by
    dsimp [v]
    rw [Nat.sub_le_iff_le_add]
    exact ht.2
  have hsum : v + h = t := by
    dsimp [v]
    exact Nat.sub_add_cancel hh_le_t
  exact ⟨v, ⟨hvlo, hvhi⟩, hsum⟩

/-- A positive periodic translate of a residue in `V` is a candidate. -/
theorem candidate_of_periodic_residue {r h q rho : Nat}
    (hq : 1 <= q) (hrho : InV r h rho) :
    Candidate r h (q * M r h + rho) := by
  exact Or.inr ⟨q, hq, ⟨rho, hrho, rfl⟩⟩

/-- Prefix candidates are below every positive periodic translate. -/
theorem prefix_lt_positive_periodic_residue {r h q p rho : Nat}
    (hp : Params r h) (hq : 1 <= q)
    (hpfx : InPrefix r h p) (_hrho : InV r h rho) :
    p < q * M r h + rho := by
  have hp_lt_M : p < M r h := prefix_lt_M hp hpfx
  have hM_le_qM : M r h <= q * M r h := by
    have hmul : 1 * M r h <= q * M r h :=
      Nat.mul_le_mul_right (M r h) hq
    simpa using hmul
  omega

/--
Explicit internal periodic-gap witness.

For `t = v+h` with `v in K_i`, the target `qM+t` is represented as
`1 + (h-1) + (qM+v)`.
-/
theorem periodic_internal_gap_candidate_triple_witness {r h q i t : Nat}
    (hp : Params r h) (hq : 1 <= q) (hi : i < r)
    (ht : InKAddH r h i t) :
    ∃ v : Nat,
      InK r h i v ∧
      v + h = t ∧
      Candidate r h 1 ∧
      Candidate r h (h - 1) ∧
      Candidate r h (q * M r h + v) ∧
      1 < h - 1 ∧
      h - 1 < q * M r h + v ∧
      q * M r h + v < q * M r h + t ∧
      1 + (h - 1) + (q * M r h + v) = q * M r h + t := by
  rcases ht with ⟨v, hvK, hvt⟩
  have hvV : InV r h v := ⟨i, hi, hvK⟩
  have hper : Candidate r h (q * M r h + v) :=
    candidate_of_periodic_residue (r := r) (h := h) (q := q) hq hvV
  have hlt_one_h : 1 < h - 1 := by
    have hh := hp.h_ge_six
    omega
  have hlt_h_per : h - 1 < q * M r h + v :=
    prefix_lt_positive_periodic_residue
      (r := r) (h := h) (q := q) (p := h - 1) (rho := v)
      hp hq (prefix_h_sub_one r h) hvV
  have hv_lt_t : v < t := by
    have hh := hp.h_ge_six
    omega
  have hper_lt_target : q * M r h + v < q * M r h + t := by
    exact Nat.add_lt_add_left hv_lt_t (q * M r h)
  have hsum : 1 + (h - 1) + (q * M r h + v) = q * M r h + t := by
    have hh := hp.h_ge_six
    omega
  exact
    ⟨v, hvK, hvt, candidate_one r h, candidate_h_sub_one r h, hper,
      hlt_one_h, hlt_h_per, hper_lt_target, hsum⟩

/--
Internal periodic-gap coverage for one boundary `r`-band slice.
-/
theorem periodic_internal_gap_candidate_triple {r h q i t : Nat}
    (hp : Params r h) (hq : 1 <= q) (hi : i < r)
    (ht : InInterval (KLo r h i + h) (KHi r h i + h) t) :
    CandidateTripleSumFrom r h (q * M r h + t) := by
  rcases periodic_internal_gap_candidate_triple_witness
      (r := r) (h := h) (q := q) (i := i) (t := t)
      hp hq hi (inKAddH_of_interval (r := r) (h := h) (i := i) ht) with
    ⟨v, _hvK, _hvt, h1, hh1, hper, hlt_one_h, hlt_h_per, hper_lt_target, hsum⟩
  exact ⟨1, h - 1, q * M r h + v, h1, hh1, hper,
    hlt_one_h, hlt_h_per, hper_lt_target, hsum⟩

/-- The shifted `K + {1,h-1} + H` slice. -/
def shiftedVUSliceLo (r h m : Nat) : Nat :=
  shiftedPairSliceLo r h m - 1

/-- The shifted `K + {1,h-1} + H` slice. -/
def shiftedVUSliceHi (r h m : Nat) : Nat :=
  shiftedPairSliceHi r h m - 1

def InShiftedVUSlice (r h m t : Nat) : Prop :=
  InInterval (shiftedVUSliceLo r h m) (shiftedVUSliceHi r h m) t

theorem shiftedPairSlice_of_shiftedVUSlice_add_one {r h m t : Nat}
    (hp : Params r h) (ht : InShiftedVUSlice r h m t) :
    InShiftedPairSlice r h m (t + 1) := by
  have hlo1 : 1 <= shiftedPairSliceLo r h m := by
    unfold shiftedPairSliceLo
    omega
  have hhi1 : 1 <= shiftedPairSliceHi r h m := by
    have hD := D_ge_three (r := r) (h := h) hp
    unfold shiftedPairSliceHi
    omega
  unfold InShiftedVUSlice InShiftedPairSlice InInterval at *
  unfold shiftedVUSliceLo shiftedVUSliceHi at ht
  constructor <;> omega

theorem shiftedVUSlice_of_shiftedPairSlice_add_one {r h m t : Nat}
    (hp : Params r h) (ht : InShiftedPairSlice r h m (t + 1)) :
    InShiftedVUSlice r h m t := by
  have hlo1 : 1 <= shiftedPairSliceLo r h m := by
    unfold shiftedPairSliceLo
    omega
  have hhi1 : 1 <= shiftedPairSliceHi r h m := by
    have hD := D_ge_three (r := r) (h := h) hp
    unfold shiftedPairSliceHi
    omega
  unfold InShiftedVUSlice InShiftedPairSlice InInterval at *
  unfold shiftedVUSliceLo shiftedVUSliceHi
  constructor <;> omega

/--
Slice-level shifted `K + {1,h-1} + H` coverage.
-/
theorem shifted_VU_slice_candidate_triple {r h q m t : Nat}
    (hp : Params r h) (hq : 1 <= q) (hm : m <= 2 * r - 2)
    (ht : InShiftedVUSlice r h m t) :
    CandidateTripleSumFrom r h (q * M r h + t) := by
  have htPair : InShiftedPairSlice r h m (t + 1) :=
    shiftedPairSlice_of_shiftedVUSlice_add_one
      (r := r) (h := h) (m := m) (t := t) hp ht
  rcases shifted_pair_slice_prefix_pair_inPrefix_witness
      (r := r) (h := h) (m := m) (t := t + 1) hp hm htPair with
    ⟨eps, i, j, x, u, heps, hi, hj, _hij, hxH, huH, hepsP, _hxP, huP, hsumPair⟩
  let v := x - 1
  have hvK : InK r h i v := by
    dsimp [v]
    exact sub_one_mem_K_of_mem_H (r := r) (h := h) (i := i) (x := x) hp hxH
  have hvV : InV r h v := ⟨i, hi, hvK⟩
  have hper : Candidate r h (q * M r h + v) :=
    candidate_of_periodic_residue (r := r) (h := h) (q := q) hq hvV
  have huCand : Candidate r h u := candidate_of_prefix huP
  have hepsCand : Candidate r h eps := candidate_of_prefix hepsP
  have hx_ge_one : 1 <= x := by
    have hHlo := HLo_ge_three (r := r) (h := h) (i := i) hp
    exact Nat.le_trans (by omega : 1 <= HLo r h i) hxH.1
  have hx_sub : v + 1 = x := by
    dsimp [v]
    exact Nat.sub_add_cancel hx_ge_one
  have hsumPair' : eps + (v + 1) + u = t + 1 := by
    simpa [hx_sub] using hsumPair
  have hsumOffset : eps + v + u = t := by
    omega
  have hu_ge_h_add_one : h + 1 <= u := by
    have hD := D_ge_h_add_one (r := r) (h := h) hp
    unfold InH InInterval HLo at huH
    omega
  have heps_lt_u : eps < u := by
    rcases heps with rfl | rfl
    · have hh := hp.h_ge_six
      omega
    · have hh := hp.h_ge_six
      omega
  have hu_lt_per : u < q * M r h + v :=
    prefix_lt_positive_periodic_residue
      (r := r) (h := h) (q := q) (p := u) (rho := v)
      hp hq huP hvV
  have hv_lt_t : v < t := by
    have heps_pos : 1 <= eps := by
      rcases heps with rfl | rfl
      · omega
      · have hh := hp.h_ge_six
        omega
    have hu_pos : 1 <= u := by omega
    omega
  have hper_lt_target : q * M r h + v < q * M r h + t := by
    exact Nat.add_lt_add_left hv_lt_t (q * M r h)
  have hsumTarget : eps + u + (q * M r h + v) = q * M r h + t := by
    omega
  exact
    ⟨eps, u, q * M r h + v, hepsCand, huCand, hper,
      heps_lt_u, hu_lt_per, hper_lt_target, hsumTarget⟩

theorem shiftedVUSlice_chain_cover_bounded {r h t : Nat}
    (hp : Params r h)
    (ht :
      InInterval (shiftedVUSliceLo r h 0)
        (shiftedVUSliceHi r h (2 * r - 2)) t) :
    ∃ m : Nat, m <= 2 * r - 2 ∧ InShiftedVUSlice r h m t := by
  have htPairRaw :
      InInterval (shiftedPairSliceLo r h 0)
        (shiftedPairSliceHi r h (2 * r - 2)) (t + 1) := by
    have hlo1 : 1 <= shiftedPairSliceLo r h 0 := by
      unfold shiftedPairSliceLo
      omega
    have hhi1 : 1 <= shiftedPairSliceHi r h (2 * r - 2) := by
      have hD := D_ge_three (r := r) (h := h) hp
      unfold shiftedPairSliceHi
      omega
    unfold InInterval at *
    unfold shiftedVUSliceLo shiftedVUSliceHi at ht
    constructor <;> omega
  have htPair :
      InInterval (finalPrefixGapLo r h)
        (2 * D r h + (4 * r - 1) * h - 4) (t + 1) := by
    have hlo := shiftedPairSlice_global_lo_eq_finalPrefixGapLo (r := r) (h := h) hp
    have hhi := shiftedPairSlice_global_hi_eq (r := r) (h := h) hp
    rw [← hlo, ← hhi]
    exact htPairRaw
  rcases shiftedPairSlice_chain_cover_bounded
      (r := r) (h := h) (t := t + 1) hp htPair with
    ⟨m, hm, hmPair⟩
  exact ⟨m, hm,
    shiftedVUSlice_of_shiftedPairSlice_add_one
      (r := r) (h := h) (m := m) (t := t) hp hmPair⟩

theorem shifted_VU_chain_candidate_triple {r h q t : Nat}
    (hp : Params r h) (hq : 1 <= q)
    (ht :
      InInterval (shiftedVUSliceLo r h 0)
        (shiftedVUSliceHi r h (2 * r - 2)) t) :
    CandidateTripleSumFrom r h (q * M r h + t) := by
  rcases shiftedVUSlice_chain_cover_bounded
      (r := r) (h := h) (t := t) hp ht with
    ⟨m, hm, hmem⟩
  exact shifted_VU_slice_candidate_triple
    (r := r) (h := h) (q := q) (m := m) (t := t) hp hq hm hmem

/-- Left endpoint for the shifted `K + Sigma_2^*(H)` slice. -/
def shiftedVUUSliceLo (r h m : Nat) : Nat :=
  tripleHSliceLo r h m - 1

/-- Right endpoint for the shifted `K + Sigma_2^*(H)` slice. -/
def shiftedVUUSliceHi (r h m : Nat) : Nat :=
  tripleHSliceHi r h m - 1

def InShiftedVUUSlice (r h m t : Nat) : Prop :=
  InInterval (shiftedVUUSliceLo r h m) (shiftedVUUSliceHi r h m) t

theorem H_pair_sum_distinct_of_strict_indices {r h j k t : Nat}
    (hp : Params r h) (hjk : j < k)
    (ht :
      InInterval (HLo r h j + HLo r h k)
        (HHi r h j + HHi r h k) t) :
    ∃ y z : Nat,
      InH r h j y ∧
      InH r h k z ∧
      y < z ∧
      y + z = t := by
  have hJ : HLo r h j <= HHi r h j := HLo_le_HHi hp
  have hK : HLo r h k <= HHi r h k := HLo_le_HHi hp
  rcases interval_pair_sum hJ hK ht with ⟨y, z, hy, hz, hsum⟩
  have hgap := HHi_lt_HLo_of_lt (r := r) (h := h) hp hjk
  have hyz : y < z :=
    Nat.lt_of_le_of_lt hy.2 (Nat.lt_of_lt_of_le hgap hz.1)
  exact ⟨y, z, hy, hz, hyz, hsum⟩

private theorem candidate_triple_of_periodic_v_and_prefix_pair {r h q v y z t : Nat}
    (hp : Params r h) (hq : 1 <= q)
    (hvV : InV r h v)
    (hyP : InPrefix r h y) (hzP : InPrefix r h z)
    (hyz : y < z) (hv_lt_t : v < t) (hsum : v + y + z = t) :
    CandidateTripleSumFrom r h (q * M r h + t) := by
  have hyCand : Candidate r h y := candidate_of_prefix hyP
  have hzCand : Candidate r h z := candidate_of_prefix hzP
  have hper : Candidate r h (q * M r h + v) :=
    candidate_of_periodic_residue (r := r) (h := h) (q := q) hq hvV
  have hz_lt_per : z < q * M r h + v :=
    prefix_lt_positive_periodic_residue
      (r := r) (h := h) (q := q) (p := z) (rho := v)
      hp hq hzP hvV
  have hper_lt_target : q * M r h + v < q * M r h + t :=
    Nat.add_lt_add_left hv_lt_t (q * M r h)
  have hsumTarget : y + z + (q * M r h + v) = q * M r h + t := by
    omega
  exact
    ⟨y, z, q * M r h + v, hyCand, hzCand, hper,
      hyz, hz_lt_per, hper_lt_target, hsumTarget⟩

theorem shifted_VUU_slice_candidate_triple_of_strict_pair {r h q i j k t : Nat}
    (hp : Params r h) (hq : 1 <= q)
    (hi : i < r) (hj : j < r) (hk : k < r) (hjk : j < k)
    (ht : InShiftedVUUSlice r h (i + j + k) t) :
    CandidateTripleSumFrom r h (q * M r h + t) := by
  have hK : KLo r h i <= KHi r h i := KLo_le_KHi hp
  have hPair :
      HLo r h j + HLo r h k <= HHi r h j + HHi r h k := by
    have hJ : HLo r h j <= HHi r h j := HLo_le_HHi hp
    have hK' : HLo r h k <= HHi r h k := HLo_le_HHi hp
    omega
  have htSum :
      InInterval (KLo r h i + (HLo r h j + HLo r h k))
        (KHi r h i + (HHi r h j + HHi r h k)) t := by
    have hD := D_ge_three (r := r) (h := h) hp
    have hh := hp.h_ge_six
    unfold InShiftedVUUSlice InInterval shiftedVUUSliceLo shiftedVUUSliceHi at ht
    unfold InInterval
    unfold tripleHSliceLo tripleHSliceHi KLo KHi HHi HLo at *
    simp [Nat.left_distrib, Nat.right_distrib] at *
    constructor <;> omega
  rcases interval_pair_sum hK hPair htSum with ⟨v, s, hvK, hsPair, hsum_vs⟩
  rcases H_pair_sum_distinct_of_strict_indices
      (r := r) (h := h) (j := j) (k := k) (t := s)
      hp hjk hsPair with
    ⟨y, z, hyH, hzH, hyz, hsum_yz⟩
  have hvK' : InK r h i v := by
    simpa [InK] using hvK
  have hvV : InV r h v := ⟨i, hi, hvK'⟩
  have hyP : InPrefix r h y := prefix_of_inH (r := r) (h := h) hj hyH
  have hzP : InPrefix r h z := prefix_of_inH (r := r) (h := h) hk hzH
  have hv_lt_t : v < t := by
    have hHlo := HLo_ge_three (r := r) (h := h) (i := j) hp
    omega
  have hsum : v + y + z = t := by
    omega
  exact candidate_triple_of_periodic_v_and_prefix_pair
    (r := r) (h := h) (q := q) (v := v) (y := y) (z := z) (t := t)
    hp hq hvV hyP hzP hyz hv_lt_t hsum

theorem shifted_VUU_slice_candidate_triple_of_same_pair {r h q i j t : Nat}
    (hp : Params r h) (hq : 1 <= q) (hi : i < r) (hj : j < r)
    (ht :
      InInterval (shiftedVUUSliceLo r h (i + j + j) + 1)
        (shiftedVUUSliceHi r h (i + j + j) - 1) t) :
    CandidateTripleSumFrom r h (q * M r h + t) := by
  have hK : KLo r h i <= KHi r h i := KLo_le_KHi hp
  have hPair :
      2 * HLo r h j + 1 <= 2 * HHi r h j - 1 :=
    H_pair_distinct_sum_interval_nonempty (r := r) (h := h) (i := j) hp
  have htSum :
      InInterval (KLo r h i + (2 * HLo r h j + 1))
        (KHi r h i + (2 * HHi r h j - 1)) t := by
    have hD := D_ge_three (r := r) (h := h) hp
    have hh := hp.h_ge_six
    unfold InInterval shiftedVUUSliceLo shiftedVUUSliceHi at ht
    unfold InInterval
    unfold tripleHSliceLo tripleHSliceHi KLo KHi HHi HLo at *
    simp [Nat.left_distrib, Nat.right_distrib] at *
    constructor <;> omega
  rcases interval_pair_sum hK hPair htSum with ⟨v, s, hvK, hsPair, hsum_vs⟩
  rcases H_pair_sum_distinct_same_index
      (r := r) (h := h) (i := j) (t := s) hp hsPair with
    ⟨y, z, hyH, hzH, hyz, hsum_yz⟩
  have hvK' : InK r h i v := by
    simpa [InK] using hvK
  have hvV : InV r h v := ⟨i, hi, hvK'⟩
  have hyP : InPrefix r h y := prefix_of_inH (r := r) (h := h) hj hyH
  have hzP : InPrefix r h z := prefix_of_inH (r := r) (h := h) hj hzH
  have hv_lt_t : v < t := by
    have hHlo := HLo_ge_three (r := r) (h := h) (i := j) hp
    omega
  have hsum : v + y + z = t := by
    omega
  exact candidate_triple_of_periodic_v_and_prefix_pair
    (r := r) (h := h) (q := q) (v := v) (y := y) (z := z) (t := t)
    hp hq hvV hyP hzP hyz hv_lt_t hsum

theorem shifted_VUU_slice_candidate_triple {r h q i j k t : Nat}
    (hp : Params r h) (hq : 1 <= q)
    (hi : i < r) (hj : j < r) (hk : k < r) (hjk : j <= k)
    (ht :
      InInterval (shiftedVUUSliceLo r h (i + j + k) + 1)
        (shiftedVUUSliceHi r h (i + j + k) - 1) t) :
    CandidateTripleSumFrom r h (q * M r h + t) := by
  by_cases hlt : j < k
  · have htRaw : InShiftedVUUSlice r h (i + j + k) t := by
      unfold InShiftedVUUSlice InInterval at *
      constructor <;> omega
    exact shifted_VUU_slice_candidate_triple_of_strict_pair
      (r := r) (h := h) (q := q) (i := i) (j := j) (k := k) (t := t)
      hp hq hi hj hk hlt htRaw
  · have hEq : j = k := by omega
    subst k
    exact shifted_VUU_slice_candidate_triple_of_same_pair
      (r := r) (h := h) (q := q) (i := i) (j := j) (t := t)
      hp hq hi hj (by simpa using ht)

theorem bounded_ordered_pair_indices {r m : Nat} (hr : 1 <= r) (hm : m <= 2 * r - 2) :
    ∃ j k : Nat, j < r ∧ k < r ∧ j <= k ∧ j + k = m := by
  rcases bounded_pair_indices (r := r) (m := m) hr hm with
    ⟨j, k, hj, hk, hsum⟩
  by_cases hjk : j <= k
  · exact ⟨j, k, hj, hk, hjk, hsum⟩
  · exact ⟨k, j, hk, hj, by omega, by omega⟩

theorem bounded_VUU_indices {r m : Nat} (hr : 1 <= r) (hm : m <= 3 * r - 3) :
    ∃ i j k : Nat, i < r ∧ j < r ∧ k < r ∧ j <= k ∧ i + j + k = m := by
  by_cases hm_pair : m <= 2 * r - 2
  · rcases bounded_ordered_pair_indices (r := r) (m := m) hr hm_pair with
      ⟨j, k, hj, hk, hjk, hsum⟩
    exact ⟨0, j, k, by omega, hj, hk, hjk, by omega⟩
  · let i := m - (2 * r - 2)
    refine ⟨i, r - 1, r - 1, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp [i]
      omega
    · omega
    · omega
    · omega
    · dsimp [i]
      omega

theorem shiftedVUUSlice_oneTrim_next_lo_le_hi_succ {r h m : Nat}
    (hp : Params r h) :
    shiftedVUUSliceLo r h (m + 1) + 1 <=
      (shiftedVUUSliceHi r h m - 1) + 1 := by
  have hh := hp.h_ge_six
  have hD := D_ge_three (r := r) (h := h) hp
  unfold shiftedVUUSliceLo shiftedVUUSliceHi tripleHSliceLo tripleHSliceHi
  simp [Nat.left_distrib, Nat.right_distrib]
  omega

theorem shiftedVUUSlice_oneTrim_chain_cover {r h a n t : Nat}
    (hp : Params r h)
    (ht :
      InInterval (shiftedVUUSliceLo r h a + 1)
        (shiftedVUUSliceHi r h (a + n) - 1) t) :
    ∃ m : Nat,
      a <= m ∧
      m <= a + n ∧
      InInterval (shiftedVUUSliceLo r h m + 1)
        (shiftedVUUSliceHi r h m - 1) t := by
  induction n with
  | zero =>
      exact ⟨a, by omega, by omega, by simpa using ht⟩
  | succ n ih =>
      by_cases htn : t <= shiftedVUUSliceHi r h (a + n) - 1
      · rcases ih ⟨ht.1, htn⟩ with ⟨m, hma, hmhi, hmem⟩
        exact ⟨m, hma, by omega, hmem⟩
      · have hsucc :
            (shiftedVUUSliceHi r h (a + n) - 1) + 1 <= t :=
          Nat.succ_le_of_lt (Nat.lt_of_not_ge htn)
        have hbridge :
            shiftedVUUSliceLo r h ((a + n) + 1) + 1 <=
              (shiftedVUUSliceHi r h (a + n) - 1) + 1 :=
          shiftedVUUSlice_oneTrim_next_lo_le_hi_succ
            (r := r) (h := h) (m := a + n) hp
        have hlo : shiftedVUUSliceLo r h ((a + n) + 1) + 1 <= t :=
          Nat.le_trans hbridge hsucc
        have hidx : (a + n) + 1 = a + (n + 1) := by omega
        have hhi : t <= shiftedVUUSliceHi r h ((a + n) + 1) - 1 := by
          simpa [hidx] using ht.2
        exact ⟨(a + n) + 1, by omega, by omega, ⟨hlo, hhi⟩⟩

theorem shifted_VUU_chain_candidate_triple {r h q t : Nat}
    (hp : Params r h) (hq : 1 <= q)
    (ht :
      InInterval (shiftedVUUSliceLo r h 0 + 1)
        (shiftedVUUSliceHi r h (3 * r - 3) - 1) t) :
    CandidateTripleSumFrom r h (q * M r h + t) := by
  rcases shiftedVUUSlice_oneTrim_chain_cover
      (r := r) (h := h) (a := 0) (n := 3 * r - 3) (t := t)
      hp (by simpa using ht) with
    ⟨m, _hmlo, hmhi, hmem⟩
  have hm : m <= 3 * r - 3 := by
    omega
  rcases bounded_VUU_indices (r := r) (m := m) hp.r_pos hm with
    ⟨i, j, k, hi, hj, hk, hjk, hsum⟩
  have hmem' :
      InInterval (shiftedVUUSliceLo r h (i + j + k) + 1)
        (shiftedVUUSliceHi r h (i + j + k) - 1) t := by
    simpa [hsum] using hmem
  exact shifted_VUU_slice_candidate_triple
    (r := r) (h := h) (q := q) (i := i) (j := j) (k := k) (t := t)
    hp hq hi hj hk hjk hmem'

/-- First offset after the last periodic `K` interval. -/
def postLastPeriodicGapLo (r h : Nat) : Nat :=
  VTop r h + 1

/-- Last post-periodic-gap offset before the next block. -/
def postLastPeriodicGapHi (r h : Nat) : Nat :=
  M r h + VBot r h - 1

theorem postLastPeriodicGapLo_eq_last_internal_lo {r h : Nat}
    (hp : Params r h) :
    postLastPeriodicGapLo r h = KLo r h (r - 1) + h := by
  have hh := hp.h_ge_six
  have hH := HLo_ge_three (r := r) (h := h) (i := r - 1) hp
  unfold postLastPeriodicGapLo
  rw [VTop_eq_KHi_last (r := r) (h := h) hp]
  unfold KHi KLo HHi
  omega

theorem last_internal_hi_eq_c_sub_two {r h : Nat}
    (hp : Params r h) :
    KHi r h (r - 1) + h = c r h - 2 := by
  have hK : KHi r h (r - 1) + 1 = HHi r h (r - 1) :=
    KHi_add_one_eq_HHi (r := r) (h := h) (i := r - 1) hp
  have hpre := preCGapHi_eq_c_sub_one (r := r) (h := h) hp
  unfold preCGapHi at hpre
  have hcpos : 2 <= c r h := by
    have hD := D_lt_c (r := r) (h := h) hp
    have hDpos := D_ge_three (r := r) (h := h) hp
    omega
  omega

theorem postLastPeriodicGapHi_eq_finalPrefixGapHi {r h : Nat}
    (_hp : Params r h) :
    postLastPeriodicGapHi r h = finalPrefixGapHi r h := by
  unfold postLastPeriodicGapHi finalPrefixGapHi
  rfl

theorem shiftedVUSlice_global_lo_eq_c {r h : Nat}
    (hp : Params r h) :
    shiftedVUSliceLo r h 0 = c r h := by
  have hlo := shiftedPairSlice_global_lo_eq_finalPrefixGapLo (r := r) (h := h) hp
  unfold shiftedVUSliceLo finalPrefixGapLo at *
  have hcpos : 1 <= c r h := by
    have hD := D_lt_c (r := r) (h := h) hp
    have hDpos := D_pos (r := r) (h := h) hp
    omega
  omega

theorem shiftedVUSlice_global_hi_eq {r h : Nat}
    (hp : Params r h) :
    shiftedVUSliceHi r h (2 * r - 2) =
      2 * D r h + (4 * r - 1) * h - 5 := by
  have hhi := shiftedPairSlice_global_hi_eq (r := r) (h := h) hp
  unfold shiftedVUSliceHi
  rw [hhi]
  have hlarge : 1 <= 2 * D r h + (4 * r - 1) * h - 4 := by
    have hD := D_ge_three (r := r) (h := h) hp
    omega
  omega

theorem shiftedVUUSlice_global_trim_lo_eq {r h : Nat}
    (hp : Params r h) :
    shiftedVUUSliceLo r h 0 + 1 = 3 * D r h := by
  have hD := D_ge_three (r := r) (h := h) hp
  unfold shiftedVUUSliceLo tripleHSliceLo
  omega

theorem shiftedVUUSlice_global_trim_hi_eq {r h : Nat}
    (hp : Params r h) :
    shiftedVUUSliceHi r h (3 * r - 3) - 1 =
      tripleHSliceHi r h (3 * r - 3) - 2 := by
  have hhi : 1 <= tripleHSliceHi r h (3 * r - 3) := by
    have hD := D_ge_three (r := r) (h := h) hp
    unfold tripleHSliceHi
    omega
  unfold shiftedVUUSliceHi
  omega

theorem shiftedVUU_global_lo_le_shiftedVU_global_hi_succ {r h : Nat}
    (hp : Params r h) :
    shiftedVUUSliceLo r h 0 + 1 <=
      shiftedVUSliceHi r h (2 * r - 2) + 1 := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  rw [shiftedVUUSlice_global_trim_lo_eq (r := r) (h := h) hp]
  rw [shiftedVUSlice_global_hi_eq (r := r) (h := h) hp]
  have hD_bound : D r h + 4 <= (4 * r - 1) * h := by
    have hcoef : 2 * r + 1 <= 4 * r - 1 := by
      omega
    have hprod : (2 * r + 1) * h <= (4 * r - 1) * h :=
      Nat.mul_le_mul_right h hcoef
    rw [Nat.add_mul] at hprod
    unfold D
    omega
  omega

theorem top_c_KH_lo_le_shiftedVUU_hi_succ {r h : Nat}
    (hp : Params r h) :
    c r h + (KLo r h (r - 1) + HLo r h (r - 1)) <=
      (shiftedVUUSliceHi r h (3 * r - 3) - 1) + 1 := by
  have hbridge := c_pair_last_lo_le_triple_top_succ (r := r) (h := h) hp
  have hK : KLo r h (r - 1) + 1 = HLo r h (r - 1) :=
    KLo_add_one_eq_HLo (r := r) (h := h) (i := r - 1) hp
  have hhi := shiftedVUUSlice_global_trim_hi_eq (r := r) (h := h) hp
  rw [hhi]
  have hHlo_pos : 1 <= HLo r h (r - 1) := by
    have hH := HLo_ge_three (r := r) (h := h) (i := r - 1) hp
    omega
  omega

theorem top_c_KH_hi_eq_finalPrefixGapHi {r h : Nat}
    (hp : Params r h) :
    c r h + (KHi r h (r - 1) + HHi r h (r - 1)) =
      finalPrefixGapHi r h := by
  rw [finalPrefixGapHi_eq_c_add_two_HHi_last_sub_one (r := r) (h := h) hp]
  have hK : KHi r h (r - 1) + 1 = HHi r h (r - 1) :=
    KHi_add_one_eq_HHi (r := r) (h := h) (i := r - 1) hp
  have hHpos : 1 <= HHi r h (r - 1) := by
    have hH := HLo_ge_three (r := r) (h := h) (i := r - 1) hp
    have hle := HLo_le_HHi (r := r) (h := h) (i := r - 1) hp
    omega
  omega

theorem c_sub_one_eq_two_D {r h : Nat} (hp : Params r h) :
    c r h - 1 = 2 * D r h := by
  have hbase : 1 <= 2 * r * h := by
    have hcoef : 2 <= 2 * r := by
      have hr := hp.r_pos
      omega
    have hprod : 2 * h <= 2 * r * h := Nat.mul_le_mul_right h hcoef
    have hh := hp.h_ge_six
    omega
  have hmul : 2 * (2 * r * h) = 4 * r * h := by
    rw [← Nat.mul_assoc]
    congr 1
    omega
  unfold c D
  rw [Nat.mul_sub_left_distrib]
  rw [hmul]
  omega

theorem c_sub_one_periodic_candidate_triple {r h q t : Nat}
    (hp : Params r h) (hq : 1 <= q) (ht : t = c r h - 1) :
    CandidateTripleSumFrom r h (q * M r h + t) := by
  have h0 : 0 < r := by
    have hr := hp.r_pos
    omega
  have hH0 : InH r h 0 (HLo r h 0) := by
    exact ⟨Nat.le_refl _, HLo_le_HHi (r := r) (h := h) (i := 0) hp⟩
  have hH0P : InPrefix r h (HLo r h 0) :=
    prefix_of_inH (r := r) (h := h) (i := 0) (x := HLo r h 0) (by omega) hH0
  have hvV : InV r h (VBot r h) := VBot_inV (r := r) (h := h) hp
  have hper : Candidate r h (q * M r h + VBot r h) :=
    candidate_of_periodic_residue (r := r) (h := h) (q := q) hq hvV
  have hH0Cand : Candidate r h (HLo r h 0) := candidate_of_prefix hH0P
  have h1H : 1 < HLo r h 0 := by
    have hH := HLo_ge_three (r := r) (h := h) (i := 0) hp
    omega
  have hHper : HLo r h 0 < q * M r h + VBot r h :=
    prefix_lt_positive_periodic_residue
      (r := r) (h := h) (q := q) (p := HLo r h 0) (rho := VBot r h)
      hp hq hH0P hvV
  have hv_lt_t : VBot r h < t := by
    have hD := D_ge_three (r := r) (h := h) hp
    rw [ht, c_sub_one_eq_two_D (r := r) (h := h) hp]
    unfold VBot
    omega
  have hper_lt_target :
      q * M r h + VBot r h < q * M r h + t :=
    Nat.add_lt_add_left hv_lt_t (q * M r h)
  have hsum : 1 + HLo r h 0 + (q * M r h + VBot r h) = q * M r h + t := by
    rw [ht, c_sub_one_eq_two_D (r := r) (h := h) hp]
    rw [HLo_zero_eq_D]
    unfold VBot
    have hD := D_ge_three (r := r) (h := h) hp
    omega
  exact
    ⟨1, HLo r h 0, q * M r h + VBot r h,
      candidate_one r h, hH0Cand, hper, h1H, hHper, hper_lt_target, hsum⟩

theorem top_c_KH_candidate_triple {r h q t : Nat}
    (hp : Params r h) (hq : 1 <= q)
    (ht :
      InInterval (c r h + (KLo r h (r - 1) + HLo r h (r - 1)))
        (finalPrefixGapHi r h) t) :
    CandidateTripleSumFrom r h (q * M r h + t) := by
  let s := t - c r h
  have hs_interval :
      InInterval (KLo r h (r - 1) + HLo r h (r - 1))
        (KHi r h (r - 1) + HHi r h (r - 1)) s := by
    unfold s
    constructor
    · apply Nat.le_sub_of_add_le
      have hcomm :
          KLo r h (r - 1) + HLo r h (r - 1) + c r h =
            c r h + (KLo r h (r - 1) + HLo r h (r - 1)) := by omega
      rw [hcomm]
      exact ht.1
    · rw [Nat.sub_le_iff_le_add]
      have ht2 := ht.2
      rw [← top_c_KH_hi_eq_finalPrefixGapHi (r := r) (h := h) hp] at ht2
      have hcomm :
          c r h + (KHi r h (r - 1) + HHi r h (r - 1)) =
            KHi r h (r - 1) + HHi r h (r - 1) + c r h := by omega
      rwa [hcomm] at ht2
  have hK : KLo r h (r - 1) <= KHi r h (r - 1) := KLo_le_KHi hp
  have hH : HLo r h (r - 1) <= HHi r h (r - 1) := HLo_le_HHi hp
  rcases interval_pair_sum hK hH hs_interval with ⟨v, x, hvK, hxH, hsum_vx⟩
  have hc_le_t : c r h <= t := by
    exact Nat.le_trans (Nat.le_add_right (c r h) (KLo r h (r - 1) + HLo r h (r - 1))) ht.1
  have hs_add : s + c r h = t := by
    dsimp [s]
    exact Nat.sub_add_cancel hc_le_t
  have hlast : r - 1 < r := by
    have hr := hp.r_pos
    omega
  have hvV : InV r h v := ⟨r - 1, hlast, hvK⟩
  have hxP : InPrefix r h x := prefix_of_inH (r := r) (h := h) hlast hxH
  have hper : Candidate r h (q * M r h + v) :=
    candidate_of_periodic_residue (r := r) (h := h) (q := q) hq hvV
  have hxCand : Candidate r h x := candidate_of_prefix hxP
  have hcCand : Candidate r h (c r h) := candidate_c r h
  have hxc : x < c r h := by
    have hHc := HHi_last_lt_c (r := r) (h := h) hp
    exact Nat.lt_of_le_of_lt hxH.2 hHc
  have hcper : c r h < q * M r h + v :=
    prefix_lt_positive_periodic_residue
      (r := r) (h := h) (q := q) (p := c r h) (rho := v)
      hp hq (prefix_c r h) hvV
  have hv_lt_t : v < t := by
    have hcpos : 1 <= c r h := by
      have hD := D_lt_c (r := r) (h := h) hp
      have hDpos := D_pos (r := r) (h := h) hp
      omega
    have hxpos : 1 <= x := by
      have hHlo := HLo_ge_three (r := r) (h := h) (i := r - 1) hp
      exact Nat.le_trans (by omega : 1 <= HLo r h (r - 1)) hxH.1
    omega
  have hper_lt_target :
      q * M r h + v < q * M r h + t :=
    Nat.add_lt_add_left hv_lt_t (q * M r h)
  have hsum : x + c r h + (q * M r h + v) = q * M r h + t := by
    omega
  exact
    ⟨x, c r h, q * M r h + v, hxCand, hcCand, hper,
      hxc, hcper, hper_lt_target, hsum⟩

/--
Post-last periodic gap coverage for boundary `r`-bands.

The cases are the last internal translate, the singleton `c-1`, the shifted
`K+{1,h-1}+H` chain, the shifted `K+H+H` chain, and the final
`c+K_{r-1}+H_{r-1}` range.
-/
theorem post_last_periodic_gap_candidate_covered {r h q t : Nat}
    (hp : Params r h) (hq : 1 <= q)
    (ht : InInterval (postLastPeriodicGapLo r h) (postLastPeriodicGapHi r h) t) :
    CandidateTripleSumFrom r h (q * M r h + t) := by
  by_cases hinternal : t <= KHi r h (r - 1) + h
  · have hi_last : r - 1 < r := by
      have hr := hp.r_pos
      omega
    have htInternal :
        InInterval (KLo r h (r - 1) + h) (KHi r h (r - 1) + h) t := by
      constructor
      · rw [← postLastPeriodicGapLo_eq_last_internal_lo
          (r := r) (h := h) hp]
        exact ht.1
      · exact hinternal
    exact periodic_internal_gap_candidate_triple
      (r := r) (h := h) (q := q) (i := r - 1) (t := t)
      hp hq hi_last htInternal
  · have h_after_internal :
        (KHi r h (r - 1) + h) + 1 <= t :=
      Nat.succ_le_of_lt (Nat.lt_of_not_ge hinternal)
    by_cases hsingle : t = c r h - 1
    · exact c_sub_one_periodic_candidate_triple
        (r := r) (h := h) (q := q) (t := t) hp hq hsingle
    · by_cases hVU : t <= shiftedVUSliceHi r h (2 * r - 2)
      · have hloVU : shiftedVUSliceLo r h 0 <= t := by
          rw [shiftedVUSlice_global_lo_eq_c (r := r) (h := h) hp]
          have hlast_internal := last_internal_hi_eq_c_sub_two (r := r) (h := h) hp
          omega
        exact shifted_VU_chain_candidate_triple
          (r := r) (h := h) (q := q) (t := t)
          hp hq ⟨hloVU, hVU⟩
      · have hsuccVU :
            shiftedVUSliceHi r h (2 * r - 2) + 1 <= t :=
          Nat.succ_le_of_lt (Nat.lt_of_not_ge hVU)
        by_cases hVUU : t <= shiftedVUUSliceHi r h (3 * r - 3) - 1
        · have hloVUU : shiftedVUUSliceLo r h 0 + 1 <= t :=
            Nat.le_trans
              (shiftedVUU_global_lo_le_shiftedVU_global_hi_succ
                (r := r) (h := h) hp)
              hsuccVU
          exact shifted_VUU_chain_candidate_triple
            (r := r) (h := h) (q := q) (t := t)
            hp hq ⟨hloVUU, hVUU⟩
        · have hsuccVUU :
              (shiftedVUUSliceHi r h (3 * r - 3) - 1) + 1 <= t :=
            Nat.succ_le_of_lt (Nat.lt_of_not_ge hVUU)
          have hloTop :
              c r h + (KLo r h (r - 1) + HLo r h (r - 1)) <= t :=
            Nat.le_trans
              (top_c_KH_lo_le_shiftedVUU_hi_succ (r := r) (h := h) hp)
              hsuccVUU
          have hhiTop : t <= finalPrefixGapHi r h := by
            rw [← postLastPeriodicGapHi_eq_finalPrefixGapHi
              (r := r) (h := h) hp]
            exact ht.2
          exact top_c_KH_candidate_triple
            (r := r) (h := h) (q := q) (t := t)
            hp hq ⟨hloTop, hhiTop⟩

/-- Offsets omitted from the positive periodic residue blocks. -/
def PeriodicGapOffset (r h t : Nat) : Prop :=
  (∃ i : Nat, i < r - 1 ∧
    InInterval (KLo r h i + h) (KHi r h i + h) t) ∨
  InInterval (postLastPeriodicGapLo r h) (postLastPeriodicGapHi r h) t

/-- Candidate-triple coverage for all positive periodic gap offsets. -/
theorem periodic_gap_offset_candidate_covered {r h q t : Nat}
    (hp : Params r h) (hq : 1 <= q)
    (ht : PeriodicGapOffset r h t) :
    CandidateTripleSumFrom r h (q * M r h + t) := by
  rcases ht with hInternal | hPost
  · rcases hInternal with ⟨i, hi, htI⟩
    have hir : i < r := by
      omega
    exact periodic_internal_gap_candidate_triple
      (r := r) (h := h) (q := q) (i := i) (t := t) hp hq hir htI
  · exact post_last_periodic_gap_candidate_covered
      (r := r) (h := h) (q := q) (t := t) hp hq hPost

end BoundaryRBand
end GreedyThreeSumfree
