import GreedyThreeSumfree.BoundaryRBandDistinctCoverage
import GreedyThreeSumfree.BoundaryRBandSafety

namespace GreedyThreeSumfree
namespace BoundaryRBand

/--
Finite prefix gaps above `D` before the first periodic block.

The alternatives are: internal gaps after an `H_i`, the gap between the last
`H` interval and the isolated point `c`, and the gap after `c`.
-/
def PrefixGap (r h t : Nat) : Prop :=
  (∃ i : Nat,
    i < r - 1 ∧
      InInterval (HLo r h i + h) (HHi r h i + h) t) ∨
    InInterval (preCGapLo r h) (preCGapHi r h) t ∨
      InInterval (finalPrefixGapLo r h) (finalPrefixGapHi r h) t

/-- Prefix distinct coverage is already an ordered candidate triple from `t`. -/
theorem distinctPrefixTripleSum_candidateTripleSumFrom {r h t : Nat}
    (hp : Params r h) (ht : DistinctPrefixTripleSum r h t) :
    CandidateTripleSumFrom r h t := by
  rcases ht with ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩
  have hxpos : 1 <= x := residue_ge_one hp (Or.inl hx)
  have hypos : 1 <= y := residue_ge_one hp (Or.inl hy)
  have hzlt : z < t := by
    omega
  exact
    ⟨x, y, z, candidate_of_prefix hx, candidate_of_prefix hy,
      candidate_of_prefix hz, hxy, hyz, hzlt, hsum⟩

theorem prefix_internal_gap_distinct_prefix_covered {r h i t : Nat}
    (hp : Params r h) (hi : i < r)
    (ht : InInterval (HLo r h i + h) (HHi r h i + h) t) :
    DistinctPrefixTripleSum r h t := by
  rcases prefix_internal_gap_prefix_witness
      (r := r) (h := h) (i := i) (t := t) hp hi ht with
    ⟨x, hxH, h1, hh1, hx, hsum⟩
  have hh := hp.h_ge_six
  have hlt1 : 1 < h - 1 := by omega
  have hlt2 : h - 1 < x :=
    (prefix_singletons_lt_H (r := r) (h := h) (i := i) (x := x) hp hxH).2
  exact ⟨1, h - 1, x, h1, hh1, hx, hlt1, hlt2, hsum⟩

theorem prefix_internal_gap_candidate_covered {r h i t : Nat}
    (hp : Params r h) (hi : i < r)
    (ht : InInterval (HLo r h i + h) (HHi r h i + h) t) :
    CandidateTripleSumFrom r h t :=
  distinctPrefixTripleSum_candidateTripleSumFrom
    (r := r) (h := h) (t := t) hp
    (prefix_internal_gap_distinct_prefix_covered
      (r := r) (h := h) (i := i) (t := t) hp hi ht)

theorem preC_gap_distinct_prefix_covered {r h t : Nat}
    (hp : Params r h)
    (ht : InInterval (preCGapLo r h) (preCGapHi r h) t) :
    DistinctPrefixTripleSum r h t := by
  have hlast : r - 1 < r := by
    have hr := hp.r_pos
    omega
  exact prefix_internal_gap_distinct_prefix_covered
    (r := r) (h := h) (i := r - 1) (t := t) hp hlast ht

theorem preC_gap_candidate_covered {r h t : Nat}
    (hp : Params r h)
    (ht : InInterval (preCGapLo r h) (preCGapHi r h) t) :
    CandidateTripleSumFrom r h t :=
  distinctPrefixTripleSum_candidateTripleSumFrom
    (r := r) (h := h) (t := t) hp
    (preC_gap_distinct_prefix_covered (r := r) (h := h) (t := t) hp ht)

theorem final_prefix_gap_candidate_covered {r h t : Nat}
    (hp : Params r h)
    (ht : InInterval (finalPrefixGapLo r h) (finalPrefixGapHi r h) t) :
    CandidateTripleSumFrom r h t :=
  distinctPrefixTripleSum_candidateTripleSumFrom
    (r := r) (h := h) (t := t) hp
    (final_prefix_gap_distinct_prefix_covered
      (r := r) (h := h) (t := t) hp ht)

theorem prefix_gap_candidate_covered {r h t : Nat}
    (hp : Params r h) (ht : PrefixGap r h t) :
    CandidateTripleSumFrom r h t := by
  rcases ht with hInternal | hRest
  · rcases hInternal with ⟨i, hi, ht⟩
    have hir : i < r := by
      have hr := hp.r_pos
      omega
    exact prefix_internal_gap_candidate_covered
      (r := r) (h := h) (i := i) (t := t) hp hir ht
  · rcases hRest with hPreC | hFinal
    · exact preC_gap_candidate_covered
        (r := r) (h := h) (t := t) hp hPreC
    · exact final_prefix_gap_candidate_covered
        (r := r) (h := h) (t := t) hp hFinal

private theorem HHi_add_one_eq_gap_lo {r h i : Nat} (hp : Params r h) :
    HHi r h i + 1 = HLo r h i + h := by
  have hh := hp.h_ge_six
  unfold HHi
  omega

private theorem next_HLo_eq_gap_hi_succ {r h i : Nat} (hp : Params r h) :
    HLo r h (i + 1) = HHi r h i + h + 1 := by
  have hh := hp.h_ge_six
  have hstep : HLo r h (i + 1) = HLo r h i + 2 * h := by
    unfold HLo
    simp [Nat.left_distrib, Nat.right_distrib]
    omega
  rw [hstep]
  unfold HHi
  omega

private theorem prefix_window_classified_to_index {r h i t : Nat}
    (hp : Params r h) (hi : i < r)
    (ht : InInterval (D r h) (HHi r h i) t) :
    InU r h t ∨
      ∃ j : Nat,
        j < i ∧ InInterval (HLo r h j + h) (HHi r h j + h) t := by
  induction i with
  | zero =>
      left
      refine ⟨0, hi, ?_⟩
      constructor
      · simpa [HLo] using ht.1
      · exact ht.2
  | succ i ih =>
      by_cases htprev : t <= HHi r h i
      · have hi_prev : i < r := by
          omega
        have ht_prev : InInterval (D r h) (HHi r h i) t := ⟨ht.1, htprev⟩
        rcases ih hi_prev ht_prev with hU | hGap
        · exact Or.inl hU
        · rcases hGap with ⟨j, hji, hmem⟩
          exact Or.inr ⟨j, by omega, hmem⟩
      · have hgt : HHi r h i < t := Nat.lt_of_not_ge htprev
        by_cases htNext : HLo r h (i + 1) <= t
        · left
          exact ⟨i + 1, hi, ⟨htNext, ht.2⟩⟩
        · right
          refine ⟨i, by omega, ?_⟩
          have hltNext : t < HLo r h (i + 1) := Nat.lt_of_not_ge htNext
          constructor
          · rw [← HHi_add_one_eq_gap_lo (r := r) (h := h) (i := i) hp]
            exact Nat.succ_le_of_lt hgt
          · have hnext := next_HLo_eq_gap_hi_succ
              (r := r) (h := h) (i := i) hp
            rw [hnext] at hltNext
            omega

theorem prefix_window_classified {r h t : Nat}
    (hp : Params r h)
    (htD : D r h < t)
    (ht : t <= finalPrefixGapHi r h) :
    InPrefix r h t ∨ PrefixGap r h t := by
  by_cases hbeforeLast : t <= HHi r h (r - 1)
  · have hlast : r - 1 < r := by
      have hr := hp.r_pos
      omega
    have htPrefix : InInterval (D r h) (HHi r h (r - 1)) t := by
      constructor <;> omega
    rcases prefix_window_classified_to_index
        (r := r) (h := h) (i := r - 1) (t := t)
        hp hlast htPrefix with hU | hGap
    · exact Or.inl (prefix_of_inU hU)
    · rcases hGap with ⟨j, hj, hmem⟩
      exact Or.inr (Or.inl ⟨j, hj, hmem⟩)
  · have hgtLast : HHi r h (r - 1) < t := Nat.lt_of_not_ge hbeforeLast
    by_cases htc : t = c r h
    · exact Or.inl (by
        unfold InPrefix
        exact Or.inr (Or.inr (Or.inl htc)))
    · right
      by_cases hbeforeC : t < c r h
      · right
        left
        have hlo : preCGapLo r h <= t := by
          rw [preCGapLo_eq_HLo_last_add_h]
          have hh := hp.h_ge_six
          unfold HHi at hgtLast
          omega
        have hhi : t <= preCGapHi r h := by
          rw [preCGapHi_eq_c_sub_one (r := r) (h := h) hp]
          omega
        exact ⟨hlo, hhi⟩
      · right
        right
        have hc_lt_t : c r h < t := by omega
        constructor
        · rw [finalPrefixGapLo_eq_c_add_one]
          exact Nat.succ_le_of_lt hc_lt_t
        · exact ht

end BoundaryRBand
end GreedyThreeSumfree
