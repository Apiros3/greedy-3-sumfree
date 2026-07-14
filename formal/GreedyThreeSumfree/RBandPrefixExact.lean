import GreedyThreeSumfree.RBandPrefixSafety
import GreedyThreeSumfree.RBandExact

namespace GreedyThreeSumfree
namespace RBand

/--
Finite prefix gaps before the first periodic block.

The first alternative is one of the internal gaps after `H_i`; the second is
the long final gap from just after `H_{r-1}` through the point before the first
periodic block.
-/
def PrefixGap (r h e t : Nat) : Prop :=
  (∃ i : Nat,
    i < r - 1 ∧
      InInterval (HLo r h e i + h) (HHi r h e i + h) t) ∨
    InInterval (finalPrefixGapLo r h e) (finalPrefixGapHi r h e) t

theorem prefix_internal_gap_candidate_covered {r h e i t : Nat}
    (hp : Params r h e) (hi : i < r)
    (ht : InInterval (HLo r h e i + h) (HHi r h e i + h) t) :
    CandidateTripleSumFrom r h e t := by
  let x := t - h
  have hh := hp.h_ge_six
  have hxH : InH r h e i x := by
    unfold x
    unfold InH InInterval
    constructor
    · apply Nat.le_sub_of_add_le
      exact ht.1
    · rw [Nat.sub_le_iff_le_add]
      exact ht.2
  have hxP : InPrefix r h e x :=
    prefix_of_inH (r := r) (h := h) (e := e) (i := i) (x := x) hi hxH
  have hlt1x : 1 < h - 1 := by omega
  have hlt2x : h - 1 < x := by
    have hD := D_ge_h_add_one (r := r) (h := h) (e := e) hp
    unfold x
    unfold InH InInterval HLo at hxH
    omega
  have hxlt : x < t := by
    unfold x
    have hle : h <= t := by
      have hD := D_ge_h_add_one (r := r) (h := h) (e := e) hp
      have htlo := ht.1
      unfold HLo at htlo
      omega
    omega
  have hsum : 1 + (h - 1) + x = t := by
    unfold x
    have hle : h <= t := by
      have hD := D_ge_h_add_one (r := r) (h := h) (e := e) hp
      have htlo := ht.1
      unfold HLo at htlo
      omega
    omega
  exact
    ⟨1, h - 1, x,
      candidate_one r h e,
      candidate_h_sub_one r h e,
      candidate_of_prefix hxP,
      hlt1x, hlt2x, hxlt, hsum⟩

theorem prefix_gap_candidate_covered {r h e t : Nat}
    (hp : Params r h e) (ht : PrefixGap r h e t) :
    CandidateTripleSumFrom r h e t := by
  rcases ht with hInternal | hFinal
  · rcases hInternal with ⟨i, hi, ht⟩
    have hir : i < r := by
      have hr := hp.r_pos
      omega
    exact prefix_internal_gap_candidate_covered
      (r := r) (h := h) (e := e) (i := i) (t := t) hp hir ht
  · exact final_prefix_gap_candidate_covered
      (r := r) (h := h) (e := e) (t := t) hp hFinal

private theorem HHi_add_one_eq_gap_lo {r h e i : Nat} (hp : Params r h e) :
    HHi r h e i + 1 = HLo r h e i + h := by
  have hh := hp.h_ge_six
  unfold HHi
  omega

private theorem next_HLo_eq_gap_hi_succ {r h e i : Nat} (hp : Params r h e) :
    HLo r h e (i + 1) = HHi r h e i + h + 1 := by
  have hh := hp.h_ge_six
  have hstep : HLo r h e (i + 1) = HLo r h e i + 2 * h := by
    unfold HLo
    simp [Nat.left_distrib, Nat.right_distrib]
    omega
  rw [hstep]
  unfold HHi
  omega

/--
Every point from `D` through `H_i` is either in a prefix interval or in one of
the internal prefix gaps before `H_i`.
-/
private theorem prefix_window_classified_to_index {r h e i t : Nat}
    (hp : Params r h e) (hi : i < r)
    (ht : InInterval (D r h e) (HHi r h e i) t) :
    InU r h e t ∨
      ∃ j : Nat,
        j < i ∧ InInterval (HLo r h e j + h) (HHi r h e j + h) t := by
  induction i with
  | zero =>
      left
      refine ⟨0, hi, ?_⟩
      constructor
      · simpa [HLo] using ht.1
      · exact ht.2
  | succ i ih =>
      by_cases htprev : t <= HHi r h e i
      · have hi_prev : i < r := by
          omega
        have ht_prev : InInterval (D r h e) (HHi r h e i) t := ⟨ht.1, htprev⟩
        rcases ih hi_prev ht_prev with hU | hGap
        · exact Or.inl hU
        · rcases hGap with ⟨j, hji, hmem⟩
          exact Or.inr ⟨j, by omega, hmem⟩
      · have hgt : HHi r h e i < t := Nat.lt_of_not_ge htprev
        by_cases htNext : HLo r h e (i + 1) <= t
        · left
          exact ⟨i + 1, hi, ⟨htNext, ht.2⟩⟩
        · right
          refine ⟨i, by omega, ?_⟩
          have hltNext : t < HLo r h e (i + 1) := Nat.lt_of_not_ge htNext
          constructor
          · rw [← HHi_add_one_eq_gap_lo (r := r) (h := h) (e := e) (i := i) hp]
            exact Nat.succ_le_of_lt hgt
          · have hnext := next_HLo_eq_gap_hi_succ
              (r := r) (h := h) (e := e) (i := i) hp
            rw [hnext] at hltNext
            omega

theorem prefix_window_classified {r h e t : Nat}
    (hp : Params r h e)
    (htD : D r h e < t)
    (ht : t <= finalPrefixGapHi r h e) :
    InU r h e t ∨ PrefixGap r h e t := by
  by_cases hbeforeFinal : t <= HHi r h e (r - 1)
  · have hlast : r - 1 < r := by
      have hr := hp.r_pos
      omega
    have htPrefix : InInterval (D r h e) (HHi r h e (r - 1)) t := by
      constructor <;> omega
    rcases prefix_window_classified_to_index
        (r := r) (h := h) (e := e) (i := r - 1) (t := t)
        hp hlast htPrefix with hU | hGap
    · exact Or.inl hU
    · rcases hGap with ⟨j, hj, hmem⟩
      exact Or.inr (Or.inl ⟨j, hj, hmem⟩)
  · right
    right
    constructor
    · have hgt : HHi r h e (r - 1) < t := Nat.lt_of_not_ge hbeforeFinal
      have hgapLo :
          finalPrefixGapLo r h e = HHi r h e (r - 1) + 1 := by
        have hh := hp.h_ge_six
        rw [finalPrefixGapLo_eq_HLo_last_add_h
          (r := r) (h := h) (e := e) hp]
        unfold HHi
        omega
      rw [hgapLo]
      exact Nat.succ_le_of_lt hgt
    · exact ht

theorem periodic_block_gt_finalPrefixGapHi {r h e q n : Nat}
    (hp : Params r h e) (hq : 1 <= q)
    (hn : InPeriodicBlock r h e q n) :
    finalPrefixGapHi r h e < n := by
  rcases hn with ⟨rho, hrho, rfl⟩
  have hMle : M r h e <= q * M r h e := by
    have hmul : 1 * M r h e <= q * M r h e :=
      Nat.mul_le_mul_right (M r h e) hq
    simpa using hmul
  have hrho_lo := inV_lower (r := r) (h := h) (e := e) hp hrho
  have hD := D_ge_three (r := r) (h := h) (e := e) hp
  unfold finalPrefixGapHi M VBot at *
  omega

theorem candidate_le_finalPrefixGapHi_prefix {r h e z : Nat}
    (hp : Params r h e)
    (hz : Candidate r h e z)
    (hzle : z <= finalPrefixGapHi r h e) :
    InPrefix r h e z := by
  rcases hz with hpfx | hblock
  · exact hpfx
  · rcases hblock with ⟨q, hq, hzblock⟩
    have hgt := periodic_block_gt_finalPrefixGapHi
      (r := r) (h := h) (e := e) (q := q) (n := z) hp hq hzblock
    omega

theorem prefix_window_candidate_safe {r h e z : Nat}
    (hp : Params r h e)
    (hzD : D r h e < z)
    (hzle : z <= finalPrefixGapHi r h e)
    (hz : Candidate r h e z) :
    ¬ CandidateTripleSumFrom r h e z := by
  have hzPrefix := candidate_le_finalPrefixGapHi_prefix
    (r := r) (h := h) (e := e) (z := z) hp hz hzle
  unfold InPrefix at hzPrefix
  rcases hzPrefix with h1 | hh1 | hU
  · rw [h1] at hzD
    have hD := D_ge_three (r := r) (h := h) (e := e) hp
    omega
  · rw [hh1] at hzD
    have hD := D_ge_h_add_one (r := r) (h := h) (e := e) hp
    omega
  · exact prefix_candidate_safe
      (r := r) (h := h) (e := e) (target := z) hp hU

theorem regular_rband_prefix_window_characterization {r h e z : Nat}
    (hp : Params r h e)
    (hzD : D r h e < z)
    (hzle : z <= finalPrefixGapHi r h e) :
    Candidate r h e z ↔ ¬ CandidateTripleSumFrom r h e z := by
  constructor
  · intro hz
    exact prefix_window_candidate_safe
      (r := r) (h := h) (e := e) (z := z) hp hzD hzle hz
  · intro hsafe
    rcases prefix_window_classified
        (r := r) (h := h) (e := e) (t := z) hp hzD hzle with hU | hGap
    · exact candidate_of_inU (r := r) (h := h) (e := e) hU
    · exact False.elim
        (hsafe (prefix_gap_candidate_covered
          (r := r) (h := h) (e := e) (t := z) hp hGap))

theorem finalPrefixGapHi_add_one_eq_M_add_VBot {r h e : Nat}
    (hp : Params r h e) :
    finalPrefixGapHi r h e + 1 = M r h e + VBot r h e := by
  have hD := D_ge_three (r := r) (h := h) (e := e) hp
  unfold finalPrefixGapHi M VBot
  omega

theorem postLastPeriodicGapHi_eq_M_add_VBot_sub_one {r h e : Nat}
    (hp : Params r h e) :
    postLastPeriodicGapHi r h e = M r h e + VBot r h e - 1 := by
  have hD := D_ge_three (r := r) (h := h) (e := e) hp
  unfold postLastPeriodicGapHi VBot
  omega

/--
Every integer above the finite prefix window is a positive period translate of
an offset in the formalized eventual window.
-/
theorem above_finalPrefixGapHi_periodic_decomposition {r h e z : Nat}
    (hp : Params r h e) (hz : finalPrefixGapHi r h e < z) :
    ∃ q t : Nat,
      1 <= q ∧
      InInterval (VBot r h e) (postLastPeriodicGapHi r h e) t ∧
      z = q * M r h e + t := by
  let base := M r h e + VBot r h e
  let a := z - base
  let q := a / M r h e + 1
  let t := a % M r h e + VBot r h e
  have hbase_eq : base = finalPrefixGapHi r h e + 1 := by
    dsimp [base]
    rw [finalPrefixGapHi_add_one_eq_M_add_VBot
      (r := r) (h := h) (e := e) hp]
  have hbase_le : base <= z := by
    rw [hbase_eq]
    exact Nat.succ_le_of_lt hz
  have hMpos : 0 < M r h e := M_pos hp
  have hmodlt : a % M r h e < M r h e := Nat.mod_lt a hMpos
  have hdiv : (a / M r h e) * M r h e + a % M r h e = a := by
    have h := Nat.div_add_mod a (M r h e)
    rw [Nat.mul_comm] at h
    exact h
  have hsub : a + base = z := by
    dsimp [a]
    exact Nat.sub_add_cancel hbase_le
  have hsum : q * M r h e + t = z := by
    dsimp [q, t]
    have hcalc :
        (a / M r h e + 1) * M r h e +
            (a % M r h e + VBot r h e) =
          a + (M r h e + VBot r h e) := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    rw [hcalc]
    dsimp [base] at hsub
    exact hsub
  refine ⟨q, t, ?_, ?_, hsum.symm⟩
  · change 1 <= a / M r h e + 1
    exact Nat.succ_le_succ (Nat.zero_le (a / M r h e))
  · constructor
    · dsimp [t]
      omega
    · dsimp [t]
      rw [postLastPeriodicGapHi_eq_M_add_VBot_sub_one
        (r := r) (h := h) (e := e) hp]
      omega

/--
Regular `r`-band exact characterization for every target strictly above the
third seed `D`.

The finite prefix window is handled by `regular_rband_prefix_window_characterization`;
all larger targets are reduced to the eventual periodic window.
-/
theorem regular_rband_above_seed_characterization {r h e z : Nat}
    (hp : Params r h e) (hzD : D r h e < z) :
    Candidate r h e z ↔ ¬ CandidateTripleSumFrom r h e z := by
  by_cases hzPrefix : z <= finalPrefixGapHi r h e
  · exact regular_rband_prefix_window_characterization
      (r := r) (h := h) (e := e) (z := z) hp hzD hzPrefix
  · have hzAfter : finalPrefixGapHi r h e < z := Nat.lt_of_not_ge hzPrefix
    rcases above_finalPrefixGapHi_periodic_decomposition
        (r := r) (h := h) (e := e) (z := z) hp hzAfter with
      ⟨q, t, hq, ht, hz_eq⟩
    rw [hz_eq]
    exact regular_rband_eventual_characterization
      (r := r) (h := h) (e := e) (q := q) (t := t) hp hq ht

end RBand
end GreedyThreeSumfree
