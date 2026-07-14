import GreedyThreeSumfree.RBandPeriodicCoverageFinal

namespace GreedyThreeSumfree
namespace RBand

/-- First offset after the last periodic `I` interval. -/
def postLastPeriodicGapLo (r h e : Nat) : Nat :=
  VTop r h e + 1

/-- Last post-periodic-gap offset before the next block. -/
def postLastPeriodicGapHi (r h e : Nat) : Nat :=
  M r h e + D r h e - 3

/-- The post-last offset starts at the last internal translate `I_{r-1}+h`. -/
theorem postLastPeriodicGapLo_eq_last_internal_lo {r h e : Nat}
    (hp : Params r h e) :
    postLastPeriodicGapLo r h e = ILo r h e (r - 1) + h := by
  have hh := hp.h_ge_six
  have hH := HLo_ge_three (r := r) (h := h) (e := e) (i := r - 1) hp
  unfold postLastPeriodicGapLo
  rw [VTop_eq_IHi_last (r := r) (h := h) (e := e) hp]
  unfold IHi ILo
  omega

/-- The last internal translate ends at `VTop+h`. -/
theorem last_internal_hi_eq_VTop_add_h {r h e : Nat}
    (hp : Params r h e) :
    IHi r h e (r - 1) + h = VTop r h e + h := by
  rw [← VTop_eq_IHi_last (r := r) (h := h) (e := e) hp]

/-- Paper endpoint `M+D-3` is the previously formalized final prefix-gap top. -/
theorem postLastPeriodicGapHi_eq_finalPrefixGapHi {r h e : Nat}
    (_hp : Params r h e) :
    postLastPeriodicGapHi r h e = finalPrefixGapHi r h e := by
  unfold postLastPeriodicGapHi finalPrefixGapHi M
  omega

/-- Global left endpoint of the shifted `V + {1,h-1} + U` chain. -/
theorem shiftedVUSlice_global_lo_eq (r h e : Nat) :
    shiftedVUSliceLo r h e 0 = 2 * D r h e := by
  unfold shiftedVUSliceLo shiftedPairSliceLo
  omega

/-- Global right endpoint of the shifted `V + {1,h-1} + U` chain. -/
theorem shiftedVUSlice_global_hi_eq {r h e : Nat}
    (hp : Params r h e) :
    shiftedVUSliceHi r h e (2 * r - 2) =
      2 * D r h e + (4 * r - 1) * h - 6 := by
  have hr := hp.r_pos
  have hcoef : 2 * (2 * r - 2) + 3 = 4 * r - 1 := by
    omega
  have hprod : 2 * (2 * r - 2) * h + 3 * h = (4 * r - 1) * h := by
    rw [← Nat.add_mul, hcoef]
  unfold shiftedVUSliceHi shiftedPairSliceHi
  omega

/-- The shifted-`VU` chain begins before the last internal translate finishes. -/
theorem shiftedVU_global_lo_le_last_internal_hi_succ {r h e : Nat}
    (hp : Params r h e) :
    shiftedVUSliceLo r h e 0 <= IHi r h e (r - 1) + h + 1 := by
  have hh := hp.h_ge_six
  have he := hp.e_le_h_sub_two
  rw [shiftedVUSlice_global_lo_eq]
  rw [← VTop_eq_IHi_last (r := r) (h := h) (e := e) hp]
  unfold VTop D
  omega

/-- Trimmed global left endpoint of the shifted `V + Sigma_2^*(U)` chain. -/
theorem shiftedVUUSlice_global_trim_lo_eq {r h e : Nat}
    (hp : Params r h e) :
    shiftedVUUSliceLo r h e 0 + 1 = 3 * D r h e - 1 := by
  have hD := D_ge_three (r := r) (h := h) (e := e) hp
  unfold shiftedVUUSliceLo tripleHSliceLo
  omega

/-- Trimmed global right endpoint of the shifted `V + Sigma_2^*(U)` chain. -/
theorem shiftedVUUSlice_global_trim_hi_eq_finalPrefixGapHi {r h e : Nat}
    (hp : Params r h e) :
    shiftedVUUSliceHi r h e (3 * r - 3) - 1 =
      finalPrefixGapHi r h e := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have hD := D_ge_three (r := r) (h := h) (e := e) hp
  have hcoef : 2 * (3 * r - 3) + 3 = 6 * r - 3 := by
    omega
  have hprod : 2 * (3 * r - 3) * h + 3 * h = (6 * r - 3) * h := by
    rw [← Nat.add_mul, hcoef]
  unfold shiftedVUUSliceHi tripleHSliceHi finalPrefixGapHi
  omega

/-- The shifted-`VUU` chain begins before the shifted-`VU` chain finishes. -/
theorem shiftedVUU_global_lo_le_shiftedVU_global_hi_succ {r h e : Nat}
    (hp : Params r h e) :
    shiftedVUUSliceLo r h e 0 + 1 <=
      shiftedVUSliceHi r h e (2 * r - 2) + 1 := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have he := hp.e_le_h_sub_two
  have hD := D_ge_three (r := r) (h := h) (e := e) hp
  have hD_bound : D r h e + 4 <= (4 * r - 1) * h := by
    have hcoef_two : 2 <= 2 * r := by
      omega
    have htwice_le : 2 * h <= 2 * r * h := by
      exact Nat.mul_le_mul_right h hcoef_two
    have h_add_two_le : h + 2 <= 2 * r * h := by
      omega
    have hcoef : (2 * r - 1) + 2 * r = 4 * r - 1 := by
      omega
    have hprod :
        (2 * r - 1) * h + 2 * r * h = (4 * r - 1) * h := by
      rw [← Nat.add_mul, hcoef]
    unfold D
    rw [← hprod]
    omega
  rw [shiftedVUUSlice_global_trim_lo_eq (r := r) (h := h) (e := e) hp]
  rw [shiftedVUSlice_global_hi_eq (r := r) (h := h) (e := e) hp]
  omega

/--
Post-last periodic gap coverage for regular `r`-bands.

The three cases are the last internal translate, the shifted `VU` chain, and
the high shifted `VUU` chain.
-/
theorem post_last_periodic_gap_candidate_covered {r h e q t : Nat}
    (hp : Params r h e) (hq : 1 <= q)
    (ht : InInterval (postLastPeriodicGapLo r h e) (postLastPeriodicGapHi r h e) t) :
    CandidateTripleSumFrom r h e (q * M r h e + t) := by
  by_cases hinternal : t <= IHi r h e (r - 1) + h
  · have hi_last : r - 1 < r := by
      have hr := hp.r_pos
      omega
    have htInternal :
        InInterval (ILo r h e (r - 1) + h) (IHi r h e (r - 1) + h) t := by
      constructor
      · rw [← postLastPeriodicGapLo_eq_last_internal_lo
          (r := r) (h := h) (e := e) hp]
        exact ht.1
      · exact hinternal
    exact periodic_internal_gap_candidate_triple
      (r := r) (h := h) (e := e) (q := q) (i := r - 1) (t := t)
      hp hq hi_last htInternal
  · by_cases hVU : t <= shiftedVUSliceHi r h e (2 * r - 2)
    · have hsucc :
          IHi r h e (r - 1) + h + 1 <= t :=
        Nat.succ_le_of_lt (Nat.lt_of_not_ge hinternal)
      have hloVU : shiftedVUSliceLo r h e 0 <= t :=
        Nat.le_trans
          (shiftedVU_global_lo_le_last_internal_hi_succ
            (r := r) (h := h) (e := e) hp)
          hsucc
      exact shifted_VU_chain_candidate_triple
        (r := r) (h := h) (e := e) (q := q) (t := t)
        hp hq ⟨hloVU, hVU⟩
    · have hsucc :
          shiftedVUSliceHi r h e (2 * r - 2) + 1 <= t :=
        Nat.succ_le_of_lt (Nat.lt_of_not_ge hVU)
      have hloVUU : shiftedVUUSliceLo r h e 0 + 1 <= t :=
        Nat.le_trans
          (shiftedVUU_global_lo_le_shiftedVU_global_hi_succ
            (r := r) (h := h) (e := e) hp)
          hsucc
      have hhiVUU : t <= shiftedVUUSliceHi r h e (3 * r - 3) - 1 := by
        rw [shiftedVUUSlice_global_trim_hi_eq_finalPrefixGapHi
          (r := r) (h := h) (e := e) hp]
        rw [← postLastPeriodicGapHi_eq_finalPrefixGapHi
          (r := r) (h := h) (e := e) hp]
        exact ht.2
      exact shifted_VUU_chain_candidate_triple
        (r := r) (h := h) (e := e) (q := q) (t := t)
        hp hq ⟨hloVUU, hhiVUU⟩

end RBand
end GreedyThreeSumfree
