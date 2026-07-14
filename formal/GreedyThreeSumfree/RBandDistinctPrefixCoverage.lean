import GreedyThreeSumfree.RBandDistinctCoverageAssembly

namespace GreedyThreeSumfree
namespace RBand

/-- Ordered distinct triple sum from the regular-band prefix. -/
def DistinctPrefixTripleSum (r h e t : Nat) : Prop :=
  ∃ x y z : Nat,
    InPrefix r h e x ∧
    InPrefix r h e y ∧
    InPrefix r h e z ∧
    x < y ∧
    y < z ∧
    x + y + z = t

theorem distinctPrefixTripleSum_of_distinct_inU {r h e t : Nat}
    (ht :
      ∃ x y z : Nat,
        InU r h e x ∧
        InU r h e y ∧
        InU r h e z ∧
        x < y ∧
        y < z ∧
        x + y + z = t) :
    DistinctPrefixTripleSum r h e t := by
  rcases ht with ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩
  exact
    ⟨x, y, z, prefix_of_inU hx, prefix_of_inU hy, prefix_of_inU hz,
      hxy, hyz, hsum⟩

theorem finalPrefixGapHi_eq_tripleHSlice_final_hi_sub_three {r h e : Nat}
    (hp : Params r h e) :
    finalPrefixGapHi r h e = tripleHSliceHi r h e (3 * r - 3) - 3 := by
  have hglob := tripleHSlice_global_hi_eq (r := r) (h := h) (e := e) hp
  rw [hglob]
  unfold finalPrefixGapHi
  omega

theorem final_prefix_gap_third_lo_ge_tripleHSlice_oneTrim_start {r h e : Nat}
    (hp : Params r h e) :
    tripleHSliceLo r h e (r - 1) + 1 <=
      2 * D r h e + (4 * r - 1) * h - 3 := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have he := hp.e_le_h_sub_two
  have he4 : e + 4 <= 2 * h := by
    omega
  have hcoef : (2 * r - 1) + 2 * (r - 1) = 4 * r - 3 := by
    omega
  have hprod : (2 * r - 1) * h + 2 * (r - 1) * h = (4 * r - 3) * h := by
    rw [← Nat.add_mul, hcoef]
  have hcoef' : (4 * r - 3) + 2 = 4 * r - 1 := by
    omega
  have hprod' : (4 * r - 3) * h + 2 * h = (4 * r - 1) * h := by
    rw [← Nat.add_mul, hcoef']
  apply Nat.le_sub_of_add_le
  unfold tripleHSliceLo D
  omega

theorem tripleHSlice_oneTrim_next_lo_le_hi_succ {r h e m : Nat}
    (hp : Params r h e) :
    tripleHSliceLo r h e (m + 1) + 1 <=
      (tripleHSliceHi r h e m - 1) + 1 := by
  have hh := hp.h_ge_six
  have hD := D_ge_three (r := r) (h := h) (e := e) hp
  have hhi_pos : 1 <= tripleHSliceHi r h e m := by
    unfold tripleHSliceHi
    omega
  have hstep : 2 * (m + 1) * h = 2 * m * h + 2 * h := by
    simp [Nat.left_distrib, Nat.right_distrib]
  rw [Nat.sub_add_cancel hhi_pos]
  unfold tripleHSliceLo tripleHSliceHi
  rw [hstep]
  omega

/--
The one-trimmed three-`H` slices still form an overlapping chain for `h >= 6`.
This is the chain used before the final all-equal top slice, where only
two-equal or strict index patterns are selected.
-/
theorem tripleHSlice_oneTrim_chain_cover {r h e a n t : Nat}
    (hp : Params r h e)
    (ht :
      InInterval (tripleHSliceLo r h e a + 1)
        (tripleHSliceHi r h e (a + n) - 1) t) :
    ∃ m : Nat,
      a <= m ∧
      m <= a + n ∧
      InInterval (tripleHSliceLo r h e m + 1)
        (tripleHSliceHi r h e m - 1) t := by
  induction n with
  | zero =>
      exact ⟨a, by omega, by omega, by simpa using ht⟩
  | succ n ih =>
      by_cases htn : t <= tripleHSliceHi r h e (a + n) - 1
      · rcases ih ⟨ht.1, htn⟩ with ⟨m, hma, hmhi, hmem⟩
        exact ⟨m, hma, by omega, hmem⟩
      · have hsucc :
            (tripleHSliceHi r h e (a + n) - 1) + 1 <= t :=
          Nat.succ_le_of_lt (Nat.lt_of_not_ge htn)
        have hbridge :
            tripleHSliceLo r h e ((a + n) + 1) + 1 <=
              (tripleHSliceHi r h e (a + n) - 1) + 1 :=
          tripleHSlice_oneTrim_next_lo_le_hi_succ
            (r := r) (h := h) (e := e) (m := a + n) hp
        have hlo : tripleHSliceLo r h e ((a + n) + 1) + 1 <= t :=
          Nat.le_trans hbridge hsucc
        have hidx : (a + n) + 1 = a + (n + 1) := by omega
        have hhi : t <= tripleHSliceHi r h e ((a + n) + 1) - 1 := by
          simpa [hidx] using ht.2
        exact ⟨(a + n) + 1, by omega, by omega, ⟨hlo, hhi⟩⟩

theorem tripleHSlice_final_same_distinct_inU {r h e t : Nat}
    (hp : Params r h e)
    (ht :
      InInterval (tripleHSliceLo r h e (3 * r - 3) + 3)
        (tripleHSliceHi r h e (3 * r - 3) - 3) t) :
    ∃ x y z : Nat,
      InU r h e x ∧
      InU r h e y ∧
      InU r h e z ∧
      x < y ∧
      y < z ∧
      x + y + z = t := by
  have hr := hp.r_pos
  have hidx : (r - 1) + (r - 1) + (r - 1) = 3 * r - 3 := by
    omega
  exact tripleHSlice_distinct_same_inU
    (r := r) (h := h) (e := e) (i := r - 1) (t := t) hp (by omega)
    (by simpa [hidx] using ht)

/--
Concrete one-trimmed high-slice selection.

For `m` from `r-1` through `3r-4`, the selected index triples are never
all equal when `r >= 2`: below `2r-2` use `(0, m-(r-1), r-1)`, and above it
use `(m-(2r-2), r-1, r-1)`.
-/
theorem tripleHSlice_high_oneTrim_distinct_inU {r h e m t : Nat}
    (hp : Params r h e) (hr2 : 2 <= r)
    (hmlo : r - 1 <= m) (hmhi : m <= 3 * r - 4)
    (ht :
      InInterval (tripleHSliceLo r h e m + 1)
        (tripleHSliceHi r h e m - 1) t) :
    ∃ x y z : Nat,
      InU r h e x ∧
      InU r h e y ∧
      InU r h e z ∧
      x < y ∧
      y < z ∧
      x + y + z = t := by
  by_cases hm_low : m <= 2 * r - 2
  · let a := m - (r - 1)
    have ha_le : a <= r - 1 := by
      dsimp [a]
      omega
    have ha_lt_r : a < r := by
      omega
    have hlast_lt : r - 1 < r := by
      omega
    by_cases ha0 : a = 0
    · have hm_eq : m = r - 1 := by
        dsimp [a] at ha0
        omega
      have hslice :
          InInterval (tripleHSliceLo r h e (0 + 0 + (r - 1)) + 1)
            (tripleHSliceHi r h e (0 + 0 + (r - 1)) - 1) t := by
        simpa [hm_eq] using ht
      exact tripleHSlice_distinct_two_left_inU
        (r := r) (h := h) (e := e) (i := 0) (j := r - 1) (t := t)
        hp (by omega) hlast_lt (by omega) hslice
    · by_cases halast : a = r - 1
      · have hm_eq : m = 2 * r - 2 := by
          dsimp [a] at halast
          omega
        have hslice :
            InInterval (tripleHSliceLo r h e (0 + (r - 1) + (r - 1)) + 1)
              (tripleHSliceHi r h e (0 + (r - 1) + (r - 1)) - 1) t := by
          have hidx : 0 + (r - 1) + (r - 1) = m := by
            omega
          have hidx' : (r - 1) + (r - 1) = m := by
            omega
          simpa [hidx'] using ht
        exact tripleHSlice_distinct_two_right_inU
          (r := r) (h := h) (e := e) (i := 0) (j := r - 1) (t := t)
          hp (by omega) hlast_lt (by omega) hslice
      · have ha_pos : 0 < a := by
          omega
        have ha_lt_last : a < r - 1 := by
          omega
        have hm_eq : 0 + a + (r - 1) = m := by
          dsimp [a]
          omega
        have hsliceTrim :
            InInterval (tripleHSliceLo r h e (0 + a + (r - 1)) + 1)
              (tripleHSliceHi r h e (0 + a + (r - 1)) - 1) t := by
          have hidx : a + (r - 1) = m := by
            omega
          simpa [hidx] using ht
        have hsliceFull : InTripleHSlice r h e (0 + a + (r - 1)) t := by
          unfold InTripleHSlice InInterval at *
          constructor <;> omega
        exact tripleHSlice_distinct_strict_inU
          (r := r) (h := h) (e := e) (i := 0) (j := a) (k := r - 1) (t := t)
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
        InInterval (tripleHSliceLo r h e (a + (r - 1) + (r - 1)) + 1)
          (tripleHSliceHi r h e (a + (r - 1) + (r - 1)) - 1) t := by
      simpa [hm_eq] using ht
    exact tripleHSlice_distinct_two_right_inU
      (r := r) (h := h) (e := e) (i := a) (j := r - 1) (t := t)
      hp ha_lt_r hlast_lt ha_lt_last hslice

/--
Distinct three-`U` coverage for the third, high part of the final prefix gap,
namely the part beginning immediately after the shifted-pair chain endpoint.

This deliberately does not claim coverage of the earlier final-prefix-gap
subintervals.
-/
theorem final_prefix_gap_third_range_distinct_inU {r h e t : Nat}
    (hp : Params r h e)
    (ht :
      InInterval (2 * D r h e + (4 * r - 1) * h - 3)
        (finalPrefixGapHi r h e) t) :
    ∃ x y z : Nat,
      InU r h e x ∧
      InU r h e y ∧
      InU r h e z ∧
      x < y ∧
      y < z ∧
      x + y + z = t := by
  by_cases hr1 : r = 1
  · subst r
    have htrim :
        InInterval (tripleHSliceLo 1 h e (3 * 1 - 3) + 3)
          (tripleHSliceHi 1 h e (3 * 1 - 3) - 3) t := by
      constructor
      · have hh := hp.h_ge_six
        have he := hp.e_le_h_sub_two
        have hlo :
            tripleHSliceLo 1 h e (3 * 1 - 3) + 3 <=
              2 * D 1 h e + (4 * 1 - 1) * h - 3 := by
          apply Nat.le_sub_of_add_le
          unfold tripleHSliceLo D
          omega
        exact Nat.le_trans hlo ht.1
      · rw [finalPrefixGapHi_eq_tripleHSlice_final_hi_sub_three
          (r := 1) (h := h) (e := e) hp] at ht
        exact ht.2
    exact tripleHSlice_final_same_distinct_inU
      (r := 1) (h := h) (e := e) (t := t) hp htrim
  · have hr2 : 2 <= r := by
      have hr := hp.r_pos
      omega
    by_cases htop : t <= tripleHSliceHi r h e (3 * r - 4) - 1
    · have hidx : (r - 1) + (2 * r - 3) = 3 * r - 4 := by
        omega
      have htchain :
          InInterval (tripleHSliceLo r h e (r - 1) + 1)
            (tripleHSliceHi r h e ((r - 1) + (2 * r - 3)) - 1) t := by
        constructor
        · exact Nat.le_trans
            (final_prefix_gap_third_lo_ge_tripleHSlice_oneTrim_start
              (r := r) (h := h) (e := e) hp)
            ht.1
        · simpa [hidx] using htop
      rcases tripleHSlice_oneTrim_chain_cover
          (r := r) (h := h) (e := e) (a := r - 1) (n := 2 * r - 3)
          (t := t) hp htchain with
        ⟨m, hmlo, hmhi, hmem⟩
      have hmhi' : m <= 3 * r - 4 := by
        omega
      exact tripleHSlice_high_oneTrim_distinct_inU
        (r := r) (h := h) (e := e) (m := m) (t := t)
        hp hr2 hmlo hmhi' hmem
    · have hsucc :
          (tripleHSliceHi r h e (3 * r - 4) - 1) + 1 <= t :=
        Nat.succ_le_of_lt (Nat.lt_of_not_ge htop)
      have hbridge :
          tripleHSliceLo r h e (3 * r - 3) + 3 <=
            (tripleHSliceHi r h e (3 * r - 4) - 1) + 1 := by
        have hh := hp.h_ge_six
        have hD := D_ge_three (r := r) (h := h) (e := e) hp
        have hhi_pos : 1 <= tripleHSliceHi r h e (3 * r - 4) := by
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
      have hlo : tripleHSliceLo r h e (3 * r - 3) + 3 <= t :=
        Nat.le_trans hbridge hsucc
      have hhi : t <= tripleHSliceHi r h e (3 * r - 3) - 3 := by
        rw [finalPrefixGapHi_eq_tripleHSlice_final_hi_sub_three
          (r := r) (h := h) (e := e) hp] at ht
        exact ht.2
      exact tripleHSlice_final_same_distinct_inU
        (r := r) (h := h) (e := e) (t := t) hp ⟨hlo, hhi⟩

/--
Prefix-level form of `final_prefix_gap_third_range_distinct_inU`.

This is the concrete distinct final-prefix-gap coverage now proved: it covers
only the third range
`[2D + (4r - 1)h - 3, finalPrefixGapHi]`.
-/
theorem final_prefix_gap_third_range_distinct_prefix_covered {r h e t : Nat}
    (hp : Params r h e)
    (ht :
      InInterval (2 * D r h e + (4 * r - 1) * h - 3)
        (finalPrefixGapHi r h e) t) :
    DistinctPrefixTripleSum r h e t :=
  distinctPrefixTripleSum_of_distinct_inU
    (final_prefix_gap_third_range_distinct_inU
      (r := r) (h := h) (e := e) (t := t) hp ht)

end RBand
end GreedyThreeSumfree
