import GreedyThreeSumfree.RBandPeriodicCoverage
import GreedyThreeSumfree.RBandMixedDistinctCoverage

namespace GreedyThreeSumfree
namespace RBand

/-- Left endpoint for the shifted `V + Sigma_2^*(U)` slice. -/
def shiftedVUUSliceLo (r h e m : Nat) : Nat :=
  tripleHSliceLo r h e m - 2

/-- Right endpoint for the shifted `V + Sigma_2^*(U)` slice. -/
def shiftedVUUSliceHi (r h e m : Nat) : Nat :=
  tripleHSliceHi r h e m - 2

/-- Membership in one raw shifted `V + U + U` slice. -/
def InShiftedVUUSlice (r h e m t : Nat) : Prop :=
  InInterval (shiftedVUUSliceLo r h e m) (shiftedVUUSliceHi r h e m) t

/--
For strictly increasing `H` indices, a two-`H` sum has an ordered distinct
witness.  Distinctness comes from interval separation.
-/
theorem H_pair_sum_distinct_of_strict_indices {r h e j k t : Nat}
    (hp : Params r h e) (hjk : j < k)
    (ht :
      InInterval (HLo r h e j + HLo r h e k)
        (HHi r h e j + HHi r h e k) t) :
    ∃ y z : Nat,
      InH r h e j y ∧
      InH r h e k z ∧
      y < z ∧
      y + z = t := by
  have hJ : HLo r h e j <= HHi r h e j := HLo_le_HHi hp
  have hK : HLo r h e k <= HHi r h e k := HLo_le_HHi hp
  rcases interval_pair_sum hJ hK ht with ⟨y, z, hy, hz, hsum⟩
  have hgap := HHi_lt_HLo_of_lt (r := r) (h := h) (e := e) hp hjk
  have hyz : y < z :=
    Nat.lt_of_le_of_lt hy.2 (Nat.lt_of_lt_of_le hgap hz.1)
  exact ⟨y, z, hy, hz, hyz, hsum⟩

/-- Package one periodic `V` residue and an ordered distinct prefix pair. -/
private theorem candidate_triple_of_periodic_v_and_prefix_pair {r h e q v y z t : Nat}
    (hp : Params r h e) (hq : 1 <= q)
    (hvV : InV r h e v)
    (hyP : InPrefix r h e y) (hzP : InPrefix r h e z)
    (hyz : y < z) (hv_lt_t : v < t) (hsum : v + y + z = t) :
    CandidateTripleSumFrom r h e (q * M r h e + t) := by
  have hyCand : Candidate r h e y := candidate_of_prefix hyP
  have hzCand : Candidate r h e z := candidate_of_prefix hzP
  have hper : Candidate r h e (q * M r h e + v) :=
    candidate_of_periodic_residue (r := r) (h := h) (e := e) (q := q) hq hvV
  have hz_lt_per : z < q * M r h e + v :=
    prefix_lt_positive_periodic_residue
      (r := r) (h := h) (e := e) (q := q) (p := z) (rho := v)
      hp hq hzP hvV
  have hper_lt_target : q * M r h e + v < q * M r h e + t :=
    Nat.add_lt_add_left hv_lt_t (q * M r h e)
  have hsumTarget : y + z + (q * M r h e + v) = q * M r h e + t := by
    omega
  exact
    ⟨y, z, q * M r h e + v, hyCand, hzCand, hper,
      hyz, hz_lt_per, hper_lt_target, hsumTarget⟩

theorem shifted_VUU_slice_candidate_triple_of_strict_pair {r h e q i j k t : Nat}
    (hp : Params r h e) (hq : 1 <= q)
    (hi : i < r) (hj : j < r) (hk : k < r) (hjk : j < k)
    (ht : InShiftedVUUSlice r h e (i + j + k) t) :
    CandidateTripleSumFrom r h e (q * M r h e + t) := by
  have hI : ILo r h e i <= IHi r h e i := ILo_le_IHi hp
  have hPair :
      HLo r h e j + HLo r h e k <= HHi r h e j + HHi r h e k := by
    have hJ : HLo r h e j <= HHi r h e j := HLo_le_HHi hp
    have hK : HLo r h e k <= HHi r h e k := HLo_le_HHi hp
    omega
  have htSum :
      InInterval (ILo r h e i + (HLo r h e j + HLo r h e k))
        (IHi r h e i + (HHi r h e j + HHi r h e k)) t := by
    have hD := D_ge_three (r := r) (h := h) (e := e) hp
    have hh := hp.h_ge_six
    unfold InShiftedVUUSlice InInterval shiftedVUUSliceLo shiftedVUUSliceHi at ht
    unfold InInterval
    unfold tripleHSliceLo tripleHSliceHi ILo IHi HHi HLo at *
    simp [Nat.left_distrib, Nat.right_distrib] at *
    constructor <;> omega
  rcases interval_pair_sum hI hPair htSum with ⟨v, s, hvI, hsPair, hsum_vs⟩
  rcases H_pair_sum_distinct_of_strict_indices
      (r := r) (h := h) (e := e) (j := j) (k := k) (t := s)
      hp hjk hsPair with
    ⟨y, z, hyH, hzH, hyz, hsum_yz⟩
  have hvI' : InI r h e i v := by
    simpa [InI] using hvI
  have hvV : InV r h e v := ⟨i, hi, hvI'⟩
  have hyP : InPrefix r h e y := prefix_of_inH (r := r) (h := h) (e := e) hj hyH
  have hzP : InPrefix r h e z := prefix_of_inH (r := r) (h := h) (e := e) hk hzH
  have hv_lt_t : v < t := by
    have hHlo := HLo_ge_three (r := r) (h := h) (e := e) (i := j) hp
    omega
  have hsum : v + y + z = t := by
    omega
  exact candidate_triple_of_periodic_v_and_prefix_pair
    (r := r) (h := h) (e := e) (q := q) (v := v) (y := y) (z := z) (t := t)
    hp hq hvV hyP hzP hyz hv_lt_t hsum

theorem shifted_VUU_slice_candidate_triple_of_same_pair {r h e q i j t : Nat}
    (hp : Params r h e) (hq : 1 <= q) (hi : i < r) (hj : j < r)
    (ht :
      InInterval (shiftedVUUSliceLo r h e (i + j + j) + 1)
        (shiftedVUUSliceHi r h e (i + j + j) - 1) t) :
    CandidateTripleSumFrom r h e (q * M r h e + t) := by
  have hI : ILo r h e i <= IHi r h e i := ILo_le_IHi hp
  have hPair :
      2 * HLo r h e j + 1 <= 2 * HHi r h e j - 1 :=
    H_pair_distinct_sum_interval_nonempty (r := r) (h := h) (e := e) (i := j) hp
  have htSum :
      InInterval (ILo r h e i + (2 * HLo r h e j + 1))
        (IHi r h e i + (2 * HHi r h e j - 1)) t := by
    have hD := D_ge_three (r := r) (h := h) (e := e) hp
    have hh := hp.h_ge_six
    unfold InInterval shiftedVUUSliceLo shiftedVUUSliceHi at ht
    unfold InInterval
    unfold tripleHSliceLo tripleHSliceHi ILo IHi HHi HLo at *
    simp [Nat.left_distrib, Nat.right_distrib] at *
    constructor <;> omega
  rcases interval_pair_sum hI hPair htSum with ⟨v, s, hvI, hsPair, hsum_vs⟩
  rcases H_pair_sum_distinct_same_index
      (r := r) (h := h) (e := e) (i := j) (t := s) hp hsPair with
    ⟨y, z, hyH, hzH, hyz, hsum_yz⟩
  have hvI' : InI r h e i v := by
    simpa [InI] using hvI
  have hvV : InV r h e v := ⟨i, hi, hvI'⟩
  have hyP : InPrefix r h e y := prefix_of_inH (r := r) (h := h) (e := e) hj hyH
  have hzP : InPrefix r h e z := prefix_of_inH (r := r) (h := h) (e := e) hj hzH
  have hv_lt_t : v < t := by
    have hHlo := HLo_ge_three (r := r) (h := h) (e := e) (i := j) hp
    omega
  have hsum : v + y + z = t := by
    omega
  exact candidate_triple_of_periodic_v_and_prefix_pair
    (r := r) (h := h) (e := e) (q := q) (v := v) (y := y) (z := z) (t := t)
    hp hq hvV hyP hzP hyz hv_lt_t hsum

/--
Slice-level shifted `V + Sigma_2^*(U)` coverage for explicit indices.

The slice is one-trimmed.  That trim is necessary for the `j = k` diagonal,
where the two prefix `H_j` witnesses must be distinct.
-/
theorem shifted_VUU_slice_candidate_triple {r h e q i j k t : Nat}
    (hp : Params r h e) (hq : 1 <= q)
    (hi : i < r) (hj : j < r) (hk : k < r) (hjk : j <= k)
    (ht :
      InInterval (shiftedVUUSliceLo r h e (i + j + k) + 1)
        (shiftedVUUSliceHi r h e (i + j + k) - 1) t) :
    CandidateTripleSumFrom r h e (q * M r h e + t) := by
  by_cases hlt : j < k
  · have htRaw : InShiftedVUUSlice r h e (i + j + k) t := by
      unfold InShiftedVUUSlice InInterval at *
      constructor <;> omega
    exact shifted_VUU_slice_candidate_triple_of_strict_pair
      (r := r) (h := h) (e := e) (q := q) (i := i) (j := j) (k := k) (t := t)
      hp hq hi hj hk hlt htRaw
  · have hEq : j = k := by omega
    subst k
    exact shifted_VUU_slice_candidate_triple_of_same_pair
      (r := r) (h := h) (e := e) (q := q) (i := i) (j := j) (t := t)
      hp hq hi hj (by simpa using ht)

theorem bounded_ordered_pair_indices {r m : Nat} (hr : 1 <= r) (hm : m <= 2 * r - 2) :
    ∃ j k : Nat, j < r ∧ k < r ∧ j <= k ∧ j + k = m := by
  rcases bounded_pair_indices (r := r) (m := m) hr hm with
    ⟨j, k, hj, hk, hsum⟩
  by_cases hjk : j <= k
  · exact ⟨j, k, hj, hk, hjk, hsum⟩
  · exact ⟨k, j, hk, hj, by omega, by omega⟩

/--
Bounded index selection for one periodic `V` index and an ordered pair of `U`
indices.
-/
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

theorem shiftedVUUSlice_oneTrim_next_lo_le_hi_succ {r h e m : Nat}
    (hp : Params r h e) :
    shiftedVUUSliceLo r h e (m + 1) + 1 <=
      (shiftedVUUSliceHi r h e m - 1) + 1 := by
  have hh := hp.h_ge_six
  have hD := D_ge_three (r := r) (h := h) (e := e) hp
  unfold shiftedVUUSliceLo shiftedVUUSliceHi tripleHSliceLo tripleHSliceHi
  simp [Nat.left_distrib, Nat.right_distrib]
  omega

/--
The one-trimmed shifted `VUU` slices form an overlapping chain.
-/
theorem shiftedVUUSlice_oneTrim_chain_cover {r h e a n t : Nat}
    (hp : Params r h e)
    (ht :
      InInterval (shiftedVUUSliceLo r h e a + 1)
        (shiftedVUUSliceHi r h e (a + n) - 1) t) :
    ∃ m : Nat,
      a <= m ∧
      m <= a + n ∧
      InInterval (shiftedVUUSliceLo r h e m + 1)
        (shiftedVUUSliceHi r h e m - 1) t := by
  induction n with
  | zero =>
      exact ⟨a, by omega, by omega, by simpa using ht⟩
  | succ n ih =>
      by_cases htn : t <= shiftedVUUSliceHi r h e (a + n) - 1
      · rcases ih ⟨ht.1, htn⟩ with ⟨m, hma, hmhi, hmem⟩
        exact ⟨m, hma, by omega, hmem⟩
      · have hsucc :
            (shiftedVUUSliceHi r h e (a + n) - 1) + 1 <= t :=
          Nat.succ_le_of_lt (Nat.lt_of_not_ge htn)
        have hbridge :
            shiftedVUUSliceLo r h e ((a + n) + 1) + 1 <=
              (shiftedVUUSliceHi r h e (a + n) - 1) + 1 :=
          shiftedVUUSlice_oneTrim_next_lo_le_hi_succ
            (r := r) (h := h) (e := e) (m := a + n) hp
        have hlo : shiftedVUUSliceLo r h e ((a + n) + 1) + 1 <= t :=
          Nat.le_trans hbridge hsucc
        have hidx : (a + n) + 1 = a + (n + 1) := by omega
        have hhi : t <= shiftedVUUSliceHi r h e ((a + n) + 1) - 1 := by
          simpa [hidx] using ht.2
        exact ⟨(a + n) + 1, by omega, by omega, ⟨hlo, hhi⟩⟩

/--
The chained one-trimmed `V + Sigma_2^*(U)` range is covered by ordered
candidate triples.
-/
theorem shifted_VUU_chain_candidate_triple {r h e q t : Nat}
    (hp : Params r h e) (hq : 1 <= q)
    (ht :
      InInterval (shiftedVUUSliceLo r h e 0 + 1)
        (shiftedVUUSliceHi r h e (3 * r - 3) - 1) t) :
    CandidateTripleSumFrom r h e (q * M r h e + t) := by
  rcases shiftedVUUSlice_oneTrim_chain_cover
      (r := r) (h := h) (e := e) (a := 0) (n := 3 * r - 3) (t := t)
      hp (by simpa using ht) with
    ⟨m, _hmlo, hmhi, hmem⟩
  have hm : m <= 3 * r - 3 := by
    omega
  rcases bounded_VUU_indices (r := r) (m := m) hp.r_pos hm with
    ⟨i, j, k, hi, hj, hk, hjk, hsum⟩
  have hmem' :
      InInterval (shiftedVUUSliceLo r h e (i + j + k) + 1)
        (shiftedVUUSliceHi r h e (i + j + k) - 1) t := by
    simpa [hsum] using hmem
  exact shifted_VUU_slice_candidate_triple
    (r := r) (h := h) (e := e) (q := q) (i := i) (j := j) (k := k) (t := t)
    hp hq hi hj hk hjk hmem'

end RBand
end GreedyThreeSumfree
