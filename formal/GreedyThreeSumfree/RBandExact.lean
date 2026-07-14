import GreedyThreeSumfree.RBandPeriodicCoverageAssembly
import GreedyThreeSumfree.RBandDistinctPrefixCoverageFinal
import GreedyThreeSumfree.RBandPeriodicSafetyFinal

namespace GreedyThreeSumfree
namespace RBand

/--
Offsets in a positive periodic block that are covered gaps rather than
periodic residues.

The first alternative covers the internal gaps between consecutive `I_i`
residue intervals.  The second alternative is the post-last gap through the
formalized endpoint `M + D - 3`.
-/
def PeriodicGapOffset (r h e t : Nat) : Prop :=
  (∃ i : Nat,
    i < r - 1 ∧
      InInterval (ILo r h e i + h) (IHi r h e i + h) t) ∨
    InInterval (postLastPeriodicGapLo r h e) (postLastPeriodicGapHi r h e) t

/-- Prefix distinct coverage is already an ordered candidate triple from `t`. -/
theorem distinctPrefixTripleSum_candidateTripleSumFrom {r h e t : Nat}
    (hp : Params r h e) (ht : DistinctPrefixTripleSum r h e t) :
    CandidateTripleSumFrom r h e t := by
  rcases ht with ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩
  have hxpos : 1 <= x := residue_ge_one hp (Or.inl hx)
  have hypos : 1 <= y := residue_ge_one hp (Or.inl hy)
  have hzlt : z < t := by
    omega
  exact
    ⟨x, y, z, candidate_of_prefix hx, candidate_of_prefix hy,
      candidate_of_prefix hz, hxy, hyz, hzlt, hsum⟩

/-- Candidate-triple coverage for the final prefix gap. -/
theorem final_prefix_gap_candidate_covered {r h e t : Nat}
    (hp : Params r h e)
    (ht : InInterval (finalPrefixGapLo r h e) (finalPrefixGapHi r h e) t) :
    CandidateTripleSumFrom r h e t :=
  distinctPrefixTripleSum_candidateTripleSumFrom
    (r := r) (h := h) (e := e) (t := t) hp
    (final_prefix_gap_distinct_prefix_covered
      (r := r) (h := h) (e := e) (t := t) hp ht)

/-- Omitted-value form of final-prefix-gap coverage. -/
theorem final_prefix_gap_omitted_covered {r h e t : Nat}
    (hp : Params r h e)
    (ht : InInterval (finalPrefixGapLo r h e) (finalPrefixGapHi r h e) t)
    (_homitted : ¬ Candidate r h e t) :
    CandidateTripleSumFrom r h e t :=
  final_prefix_gap_candidate_covered (r := r) (h := h) (e := e) (t := t) hp ht

/-- Candidate-triple coverage for every packaged positive periodic gap offset. -/
theorem periodic_gap_offset_candidate_covered {r h e q t : Nat}
    (hp : Params r h e) (hq : 1 <= q)
    (ht : PeriodicGapOffset r h e t) :
    CandidateTripleSumFrom r h e (q * M r h e + t) := by
  rcases ht with hInternal | hPost
  · rcases hInternal with ⟨i, hi, ht⟩
    have hir : i < r := by
      omega
    exact periodic_internal_gap_candidate_triple
      (r := r) (h := h) (e := e) (q := q) (i := i) (t := t)
      hp hq hir ht
  · exact post_last_periodic_gap_candidate_covered
      (r := r) (h := h) (e := e) (q := q) (t := t) hp hq hPost

/-- Omitted-value form of packaged periodic-gap coverage. -/
theorem periodic_gap_offset_omitted_covered {r h e q t : Nat}
    (hp : Params r h e) (hq : 1 <= q)
    (ht : PeriodicGapOffset r h e t)
    (_homitted : ¬ Candidate r h e (q * M r h e + t)) :
    CandidateTripleSumFrom r h e (q * M r h e + t) :=
  periodic_gap_offset_candidate_covered
    (r := r) (h := h) (e := e) (q := q) (t := t) hp hq ht

/--
Every offset from `VBot` through `I_i` is either in a periodic residue interval
or in one of the internal gaps before `I_i`.
-/
private theorem periodic_prefix_window_classified_to_index {r h e i t : Nat}
    (hp : Params r h e) (hi : i < r)
    (ht : InInterval (VBot r h e) (IHi r h e i) t) :
    InV r h e t ∨
      ∃ j : Nat,
        j < i ∧ InInterval (ILo r h e j + h) (IHi r h e j + h) t := by
  induction i with
  | zero =>
      left
      refine ⟨0, hi, ?_⟩
      constructor
      · rw [← VBot_eq_I_zero r h e]
        exact ht.1
      · exact ht.2
  | succ i ih =>
      by_cases htprev : t <= IHi r h e i
      · have hi_prev : i < r := by
          omega
        have ht_prev : InInterval (VBot r h e) (IHi r h e i) t := ⟨ht.1, htprev⟩
        rcases ih hi_prev ht_prev with hV | hGap
        · exact Or.inl hV
        · rcases hGap with ⟨j, hji, hmem⟩
          exact Or.inr ⟨j, by omega, hmem⟩
      · have hgt : IHi r h e i < t := Nat.lt_of_not_ge htprev
        by_cases htNext : ILo r h e (i + 1) <= t
        · left
          exact ⟨i + 1, hi, ⟨htNext, ht.2⟩⟩
        · right
          refine ⟨i, by omega, ?_⟩
          have hltNext : t < ILo r h e (i + 1) := Nat.lt_of_not_ge htNext
          constructor
          · have hgapLo : IHi r h e i + 1 = ILo r h e i + h := by
              have hh := hp.h_ge_six
              have hH := HLo_ge_three (r := r) (h := h) (e := e) (i := i) hp
              unfold ILo IHi
              omega
            rw [← hgapLo]
            exact Nat.succ_le_of_lt hgt
          · have hgapHi : ILo r h e (i + 1) = IHi r h e i + h + 1 := by
              have hh := hp.h_ge_six
              have hH := HLo_ge_three (r := r) (h := h) (e := e) (i := i) hp
              unfold ILo IHi HLo
              simp [Nat.left_distrib, Nat.right_distrib]
              omega
            rw [hgapHi] at hltNext
            omega

/--
The formalized eventual offset window is exactly the union of periodic residues
and packaged periodic gaps.
-/
theorem periodic_offset_window_classified {r h e t : Nat}
    (hp : Params r h e)
    (ht : InInterval (VBot r h e) (postLastPeriodicGapHi r h e) t) :
    InV r h e t ∨ PeriodicGapOffset r h e t := by
  by_cases hpost : VTop r h e < t
  · right
    right
    constructor
    · unfold postLastPeriodicGapLo
      omega
    · exact ht.2
  · have htTop : t <= VTop r h e := by
      omega
    have hlast : r - 1 < r := by
      have hr := hp.r_pos
      omega
    have htPrefix : InInterval (VBot r h e) (IHi r h e (r - 1)) t := by
      constructor
      · exact ht.1
      · rw [← VTop_eq_IHi_last (r := r) (h := h) (e := e) hp]
        exact htTop
    rcases periodic_prefix_window_classified_to_index
        (r := r) (h := h) (e := e) (i := r - 1) (t := t)
        hp hlast htPrefix with hV | hGap
    · exact Or.inl hV
    · rcases hGap with ⟨j, hj, hmem⟩
      exact Or.inr (Or.inl ⟨j, hj, hmem⟩)

/-- Included periodic residues are candidates and are safe. -/
theorem periodic_residue_candidate_safe {r h e q rho : Nat}
    (hp : Params r h e) (hq : 1 <= q) (hrho : InV r h e rho) :
    Candidate r h e (q * M r h e + rho) ∧
      ¬ CandidateTripleSumFrom r h e (q * M r h e + rho) := by
  exact
    ⟨candidate_of_periodic_residue
        (r := r) (h := h) (e := e) (q := q) hq hrho,
      periodic_block_safe
        (r := r) (h := h) (e := e) (q := q) (rho := rho)
        (target := q * M r h e + rho) hp hq hrho rfl⟩

/--
Any candidate at or beyond the first period is safe.  Prefix candidates are
below `M`; positive periodic candidates are handled by `periodic_block_safe`.
-/
theorem candidate_at_or_above_M_safe {r h e z : Nat}
    (hp : Params r h e) (hzM : M r h e <= z)
    (hz : Candidate r h e z) :
    ¬ CandidateTripleSumFrom r h e z := by
  rcases hz with hzPrefix | hzBlock
  · have hzlt := prefix_lt_M hp hzPrefix
    omega
  · rcases hzBlock with ⟨q, hq, hblock⟩
    rcases hblock with ⟨rho, hrho, hzeq⟩
    exact periodic_block_safe
      (r := r) (h := h) (e := e) (q := q) (rho := rho)
      (target := z) hp hq hrho hzeq

/--
Regular `r`-band exact characterization on the packaged eventual periodic
window.

This theorem is intentionally stated over offsets already classified as either
periodic residues `V` or one of the formalized periodic gaps.  The remaining
all-prefix safety and any wrapper proving that every earlier prefix-band
omission falls into such a case are outside this module.
-/
theorem regular_rband_eventual_characterization_of_classified_offset {r h e q t : Nat}
    (hp : Params r h e) (hq : 1 <= q)
    (ht : InV r h e t ∨ PeriodicGapOffset r h e t) :
    Candidate r h e (q * M r h e + t) ↔
      ¬ CandidateTripleSumFrom r h e (q * M r h e + t) := by
  constructor
  · intro hcandidate
    have hMle : M r h e <= q * M r h e + t := by
      have hmul : 1 * M r h e <= q * M r h e :=
        Nat.mul_le_mul_right (M r h e) hq
      omega
    exact candidate_at_or_above_M_safe
      (r := r) (h := h) (e := e) (z := q * M r h e + t)
      hp hMle hcandidate
  · intro hsafe
    rcases ht with htV | htGap
    · exact candidate_of_periodic_residue
        (r := r) (h := h) (e := e) (q := q) hq htV
    · exact False.elim
        (hsafe
          (periodic_gap_offset_candidate_covered
            (r := r) (h := h) (e := e) (q := q) (t := t) hp hq htGap))

/--
Regular `r`-band exact characterization for every offset in the eventual
periodic window `[VBot, M + D - 3]`.

This is the current exact wrapper above the last prefix band.  The prefix-band
safety/internal prefix-gap wrapper needed for a single all-`z` theorem remains
separate.
-/
theorem regular_rband_eventual_characterization {r h e q t : Nat}
    (hp : Params r h e) (hq : 1 <= q)
    (ht : InInterval (VBot r h e) (postLastPeriodicGapHi r h e) t) :
    Candidate r h e (q * M r h e + t) ↔
      ¬ CandidateTripleSumFrom r h e (q * M r h e + t) :=
  regular_rband_eventual_characterization_of_classified_offset
    (r := r) (h := h) (e := e) (q := q) (t := t)
    hp hq (periodic_offset_window_classified
      (r := r) (h := h) (e := e) (t := t) hp ht)

end RBand
end GreedyThreeSumfree
