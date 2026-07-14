import GreedyThreeSumfree.BoundaryRBandPrefixCoverage
import GreedyThreeSumfree.BoundaryRBandPrefixSafety
import GreedyThreeSumfree.BoundaryRBandPeriodicCoverage
import GreedyThreeSumfree.BoundaryRBandPeriodicSafetyFinal

namespace GreedyThreeSumfree
namespace BoundaryRBand

theorem boundary_rband_prefix_window_characterization {r h z : Nat}
    (hp : Params r h)
    (hzD : D r h < z)
    (hzle : z <= finalPrefixGapHi r h) :
    Candidate r h z ↔ ¬ CandidateTripleSumFrom r h z := by
  constructor
  · intro hz
    exact prefix_window_candidate_safe
      (r := r) (h := h) (z := z) hp hzD hzle hz
  · intro hsafe
    rcases prefix_window_classified
        (r := r) (h := h) (t := z) hp hzD hzle with hPrefix | hGap
    · exact candidate_of_prefix hPrefix
    · exact False.elim
        (hsafe (prefix_gap_candidate_covered
          (r := r) (h := h) (t := z) hp hGap))

theorem finalPrefixGapHi_add_one_eq_M_add_VBot {r h : Nat}
    (hp : Params r h) :
    finalPrefixGapHi r h + 1 = M r h + VBot r h := by
  have hD := D_ge_three (r := r) (h := h) hp
  unfold finalPrefixGapHi VBot
  omega

theorem finalPrefixGapHi_ge_M {r h : Nat} (hp : Params r h) :
    M r h <= finalPrefixGapHi r h := by
  have hD := D_ge_three (r := r) (h := h) hp
  unfold finalPrefixGapHi VBot
  omega

theorem postLastPeriodicGapHi_eq_M_add_VBot_sub_one {r h : Nat}
    (_hp : Params r h) :
    postLastPeriodicGapHi r h = M r h + VBot r h - 1 := by
  rfl

/--
Every integer above the finite prefix window is a positive period translate of
an offset in the eventual boundary window.
-/
theorem above_finalPrefixGapHi_periodic_decomposition {r h z : Nat}
    (hp : Params r h) (hz : finalPrefixGapHi r h < z) :
    ∃ q t : Nat,
      1 <= q ∧
      InInterval (VBot r h) (postLastPeriodicGapHi r h) t ∧
      z = q * M r h + t := by
  let base := M r h + VBot r h
  let a := z - base
  let q := a / M r h + 1
  let t := a % M r h + VBot r h
  have hbase_eq : base = finalPrefixGapHi r h + 1 := by
    dsimp [base]
    rw [finalPrefixGapHi_add_one_eq_M_add_VBot
      (r := r) (h := h) hp]
  have hbase_le : base <= z := by
    rw [hbase_eq]
    exact Nat.succ_le_of_lt hz
  have hMpos : 0 < M r h := M_pos hp
  have hmodlt : a % M r h < M r h := Nat.mod_lt a hMpos
  have hdiv : (a / M r h) * M r h + a % M r h = a := by
    have h := Nat.div_add_mod a (M r h)
    rw [Nat.mul_comm] at h
    exact h
  have hsub : a + base = z := by
    dsimp [a]
    exact Nat.sub_add_cancel hbase_le
  have hsum : q * M r h + t = z := by
    dsimp [q, t]
    have hcalc :
        (a / M r h + 1) * M r h +
            (a % M r h + VBot r h) =
          a + (M r h + VBot r h) := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    rw [hcalc]
    dsimp [base] at hsub
    exact hsub
  refine ⟨q, t, ?_, ?_, hsum.symm⟩
  · change 1 <= a / M r h + 1
    exact Nat.succ_le_succ (Nat.zero_le (a / M r h))
  · constructor
    · dsimp [t]
      omega
    · dsimp [t]
      rw [postLastPeriodicGapHi_eq_M_add_VBot_sub_one
        (r := r) (h := h) hp]
      omega

private theorem KHi_add_one_eq_gap_lo {r h i : Nat} (hp : Params r h) :
    KHi r h i + 1 = KLo r h i + h := by
  have hh := hp.h_ge_six
  have hH := HLo_ge_three (r := r) (h := h) (i := i) hp
  unfold KHi KLo HHi
  omega

private theorem next_KLo_eq_gap_hi_succ {r h i : Nat} (hp : Params r h) :
    KLo r h (i + 1) = KHi r h i + h + 1 := by
  have hh := hp.h_ge_six
  have hH := HLo_ge_three (r := r) (h := h) (i := i) hp
  unfold KLo KHi HHi HLo
  simp [Nat.left_distrib, Nat.right_distrib]
  omega

private theorem periodic_offset_classified_to_index {r h i t : Nat}
    (hp : Params r h) (hi : i < r)
    (ht : InInterval (KLo r h 0) (KHi r h i) t) :
    InV r h t ∨
      ∃ j : Nat,
        j < i ∧ InInterval (KLo r h j + h) (KHi r h j + h) t := by
  induction i with
  | zero =>
      left
      refine ⟨0, hi, ?_⟩
      exact ht
  | succ i ih =>
      by_cases htprev : t <= KHi r h i
      · have hi_prev : i < r := by
          omega
        have ht_prev : InInterval (KLo r h 0) (KHi r h i) t :=
          ⟨ht.1, htprev⟩
        rcases ih hi_prev ht_prev with hV | hGap
        · exact Or.inl hV
        · rcases hGap with ⟨j, hji, hmem⟩
          exact Or.inr ⟨j, by omega, hmem⟩
      · have hgt : KHi r h i < t := Nat.lt_of_not_ge htprev
        by_cases htNext : KLo r h (i + 1) <= t
        · left
          exact ⟨i + 1, hi, ⟨htNext, ht.2⟩⟩
        · right
          refine ⟨i, by omega, ?_⟩
          have hltNext : t < KLo r h (i + 1) := Nat.lt_of_not_ge htNext
          constructor
          · rw [← KHi_add_one_eq_gap_lo (r := r) (h := h) (i := i) hp]
            exact Nat.succ_le_of_lt hgt
          · have hnext := next_KLo_eq_gap_hi_succ
              (r := r) (h := h) (i := i) hp
            rw [hnext] at hltNext
            omega

/--
Offsets in the boundary eventual window are either periodic residues or one of
the gap offsets already covered by the periodic coverage module.
-/
theorem periodic_offset_classified {r h t : Nat}
    (hp : Params r h)
    (ht : InInterval (VBot r h) (postLastPeriodicGapHi r h) t) :
    InV r h t ∨ PeriodicGapOffset r h t := by
  by_cases hbeforeLast : t <= VTop r h
  · have hlast : r - 1 < r := by
      have hr := hp.r_pos
      omega
    have htPeriodic : InInterval (KLo r h 0) (KHi r h (r - 1)) t := by
      constructor
      · rw [← VBot_eq_K_zero r h]
        exact ht.1
      · rw [← VTop_eq_KHi_last (r := r) (h := h) hp]
        exact hbeforeLast
    rcases periodic_offset_classified_to_index
        (r := r) (h := h) (i := r - 1) (t := t)
        hp hlast htPeriodic with hV | hGap
    · exact Or.inl hV
    · rcases hGap with ⟨j, hj, hmem⟩
      exact Or.inr (Or.inl ⟨j, hj, hmem⟩)
  · right
    right
    constructor
    · unfold postLastPeriodicGapLo
      exact Nat.succ_le_of_lt (Nat.lt_of_not_ge hbeforeLast)
    · exact ht.2

theorem boundary_rband_candidate_above_finalPrefixGapHi_periodic_block
    {r h z : Nat}
    (hp : Params r h) (hzgt : finalPrefixGapHi r h < z)
    (hz : Candidate r h z) :
    ∃ q rho : Nat, 1 <= q ∧ InV r h rho ∧ z = q * M r h + rho := by
  rcases hz with hzPrefix | hzBlock
  · have hzltM := prefix_lt_M (r := r) (h := h) hp hzPrefix
    have hMle := finalPrefixGapHi_ge_M (r := r) (h := h) hp
    omega
  · rcases hzBlock with ⟨q, hq, hzBlock⟩
    rcases hzBlock with ⟨rho, hrho, hz_eq⟩
    exact ⟨q, rho, hq, hrho, hz_eq⟩

theorem boundary_rband_not_candidate_above_finalPrefixGapHi_periodic_gap_offset
    {r h z : Nat}
    (hp : Params r h) (hzgt : finalPrefixGapHi r h < z)
    (hz : ¬ Candidate r h z) :
    ∃ q t : Nat, 1 <= q ∧ PeriodicGapOffset r h t ∧
      z = q * M r h + t := by
  rcases above_finalPrefixGapHi_periodic_decomposition
      (r := r) (h := h) (z := z) hp hzgt with
    ⟨q, t, hq, ht, hz_eq⟩
  rcases periodic_offset_classified (r := r) (h := h) (t := t) hp ht with
    hV | hGap
  · have hzCandidate : Candidate r h z := by
      rw [hz_eq]
      exact candidate_of_periodic_residue (r := r) (h := h) (q := q) hq hV
    exact False.elim (hz hzCandidate)
  · exact ⟨q, t, hq, hGap, hz_eq⟩

theorem boundary_rband_above_finalPrefixGapHi_decomposition {r h z : Nat}
    (hp : Params r h) (hzgt : finalPrefixGapHi r h < z) :
    (Candidate r h z →
      ∃ q rho : Nat, 1 <= q ∧ InV r h rho ∧ z = q * M r h + rho) ∧
    (¬ Candidate r h z →
      ∃ q t : Nat, 1 <= q ∧ PeriodicGapOffset r h t ∧
        z = q * M r h + t) :=
  ⟨boundary_rband_candidate_above_finalPrefixGapHi_periodic_block
      (r := r) (h := h) (z := z) hp hzgt,
    boundary_rband_not_candidate_above_finalPrefixGapHi_periodic_gap_offset
      (r := r) (h := h) (z := z) hp hzgt⟩

theorem boundary_rband_above_finalPrefixGapHi_candidate_or_gap {r h z : Nat}
    (hp : Params r h) (hzgt : finalPrefixGapHi r h < z) :
    (Candidate r h z ∧
      ∃ q rho : Nat, 1 <= q ∧ InV r h rho ∧
        z = q * M r h + rho) ∨
    (¬ Candidate r h z ∧
      ∃ q t : Nat, 1 <= q ∧ PeriodicGapOffset r h t ∧
        z = q * M r h + t) := by
  by_cases hzCandidate : Candidate r h z
  · exact Or.inl
      ⟨hzCandidate,
        boundary_rband_candidate_above_finalPrefixGapHi_periodic_block
          (r := r) (h := h) (z := z) hp hzgt hzCandidate⟩
  · exact Or.inr
      ⟨hzCandidate,
        boundary_rband_not_candidate_above_finalPrefixGapHi_periodic_gap_offset
          (r := r) (h := h) (z := z) hp hzgt hzCandidate⟩

theorem boundary_rband_above_seed_characterization {r h z : Nat}
    (hp : Params r h) (hzD : D r h < z) :
    Candidate r h z ↔ ¬ CandidateTripleSumFrom r h z := by
  by_cases hzPrefix : z <= finalPrefixGapHi r h
  · exact boundary_rband_prefix_window_characterization
      (r := r) (h := h) (z := z) hp hzD hzPrefix
  · have hzAfter : finalPrefixGapHi r h < z := Nat.lt_of_not_ge hzPrefix
    constructor
    · intro hzCandidate
      rcases boundary_rband_candidate_above_finalPrefixGapHi_periodic_block
          (r := r) (h := h) (z := z) hp hzAfter hzCandidate with
        ⟨q, rho, hq, hrho, hz_eq⟩
      exact periodic_block_safe
        (r := r) (h := h) (q := q) (rho := rho) (target := z)
        hp hq hrho hz_eq
    · intro hsafe
      rcases above_finalPrefixGapHi_periodic_decomposition
          (r := r) (h := h) (z := z) hp hzAfter with
        ⟨q, t, hq, ht, hz_eq⟩
      rcases periodic_offset_classified
          (r := r) (h := h) (t := t) hp ht with hV | hGap
      · rw [hz_eq]
        exact candidate_of_periodic_residue (r := r) (h := h) (q := q) hq hV
      · exact False.elim
          (hsafe (by
            rw [hz_eq]
            exact periodic_gap_offset_candidate_covered
              (r := r) (h := h) (q := q) (t := t) hp hq hGap))

end BoundaryRBand
end GreedyThreeSumfree
