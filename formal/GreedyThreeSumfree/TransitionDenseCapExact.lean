import GreedyThreeSumfree.TransitionDenseCapGapClassifier
import GreedyThreeSumfree.TransitionDenseCapPrefixCoverage
import GreedyThreeSumfree.TransitionDenseCapTailSafety

namespace GreedyThreeSumfree
namespace TransitionDenseCap

/-- Regions where the production coverage lemmas give a smaller triple. -/
def ProductionCoveredGap (r h t z : Nat) : Prop :=
  InInterval (2 * D r h t + 2) (6 * D r h t) z ∨
    InInterval (7 * D r h t + 2) (11 * D r h t + 2) z ∨
      (∃ q o : Nat,
        1 <= q ∧
          InInterval (2 * D r h t + 1) (6 * D r h t + 1) o ∧
            z = q * M r h t + o) ∨
        (∃ q o : Nat,
          1 <= q ∧
            InInterval (7 * D r h t + 2) (11 * D r h t + 2) o ∧
              z = q * M r h t + o)

/--
Residual obstruction after all production coverage/classification modules:
an omitted safe target above `D` outside the broad production-covered gaps.
-/
def DenseCapProductionObstruction (r h t z : Nat) : Prop :=
  D r h t < z ∧
    ¬ Candidate r h t z ∧
      ¬ CandidateTripleSumFrom r h t z ∧ ¬ ProductionCoveredGap r h t z

theorem dense_cap_candidate_gt_D_safe {r h t z : Nat}
    (hp : Params r h t) (hzgt : D r h t < z)
    (hz : Candidate r h t z) :
    ¬ CandidateTripleSumFrom r h t z := by
  unfold Candidate at hz
  rcases hz with hsmallOne | hsmallH | hE | hF | hperiodic
  · subst z
    have hD := D_ge_three (r := r) (h := h) (t := t) hp
    omega
  · subst z
    have hlt := h_sub_one_lt_D (r := r) (h := h) (t := t) hp
    omega
  · exact inE_candidateTripleSumFrom_false
      (r := r) (h := h) (t := t) (target := z) hp hE
  · exact inF_candidateTripleSumFrom_false
      (r := r) (h := h) (t := t) (target := z) hp hF
  · rcases hperiodic with ⟨q, hq, hzblock⟩
    unfold InPeriodicBlock Shift at hzblock
    rcases hzblock with ⟨rho, hrhoTail, hzEq⟩
    rw [hzEq]
    have hrho : OccupiedTailResidue r h t rho := by
      simpa [OccupiedTailResidue, InTailResidue] using hrhoTail
    exact periodic_tail_candidate_safe
      (r := r) (h := h) (t := t) (q := q) (rho := rho) hp hq hrho

theorem dense_cap_prefix_gap_candidateTripleSumFrom {r h t z : Nat}
    (hp : Params r h t)
    (hz : InInterval (2 * D r h t + 2) (6 * D r h t) z) :
    CandidateTripleSumFrom r h t z := by
  simpa [candidateTripleSumFrom_iff_coveredBySmallerCandidates] using
    coveredBySmallerCandidates_dense_cap_prefix_gap
      (r := r) (h := h) (t := t) (target := z) hp hz

theorem dense_cap_F_to_first_low_gap_candidateTripleSumFrom {r h t z : Nat}
    (hp : Params r h t)
    (hz : InInterval (7 * D r h t + 2) (11 * D r h t + 2) z) :
    CandidateTripleSumFrom r h t z := by
  simpa [candidateTripleSumFrom_iff_coveredBySmallerCandidates] using
    coveredBySmallerCandidates_dense_cap_F_to_first_low_gap
      (r := r) (h := h) (t := t) (target := z) hp hz

theorem dense_cap_periodic_low_to_high_gap_candidateTripleSumFrom
    {r h t q o : Nat} (hp : Params r h t) (hq : 1 <= q)
    (ho : InInterval (2 * D r h t + 1) (6 * D r h t + 1) o) :
    CandidateTripleSumFrom r h t (q * M r h t + o) := by
  simpa [candidateTripleSumFrom_iff_coveredBySmallerCandidates] using
    coveredBySmallerCandidates_dense_cap_periodic_low_to_high_gap
      (r := r) (h := h) (t := t) (q := q) (o := o) hp hq ho

theorem dense_cap_periodic_high_to_next_low_gap_candidateTripleSumFrom
    {r h t q o : Nat} (hp : Params r h t) (hq : 1 <= q)
    (ho : InInterval (7 * D r h t + 2) (11 * D r h t + 2) o) :
    CandidateTripleSumFrom r h t (q * M r h t + o) := by
  simpa [candidateTripleSumFrom_iff_coveredBySmallerCandidates] using
    coveredBySmallerCandidates_dense_cap_periodic_high_to_next_low_gap
      (r := r) (h := h) (t := t) (q := q) (o := o) hp hq ho

theorem productionCoveredGap_candidateTripleSumFrom {r h t z : Nat}
    (hp : Params r h t) (hz : ProductionCoveredGap r h t z) :
    CandidateTripleSumFrom r h t z := by
  rcases hz with hzPrefix | hzF | hzLow | hzHigh
  · exact dense_cap_prefix_gap_candidateTripleSumFrom
      (r := r) (h := h) (t := t) (z := z) hp hzPrefix
  · exact dense_cap_F_to_first_low_gap_candidateTripleSumFrom
      (r := r) (h := h) (t := t) (z := z) hp hzF
  · rcases hzLow with ⟨q, o, hq, ho, hzEq⟩
    rw [hzEq]
    exact dense_cap_periodic_low_to_high_gap_candidateTripleSumFrom
      (r := r) (h := h) (t := t) (q := q) (o := o) hp hq ho
  · rcases hzHigh with ⟨q, o, hq, ho, hzEq⟩
    rw [hzEq]
    exact dense_cap_periodic_high_to_next_low_gap_candidateTripleSumFrom
      (r := r) (h := h) (t := t) (q := q) (o := o) hp hq ho

theorem dense_cap_safe_omitted_is_production_obstruction {r h t z : Nat}
    (hp : Params r h t) (hzgt : D r h t < z)
    (hsafe : ¬ CandidateTripleSumFrom r h t z)
    (hzOmitted : ¬ Candidate r h t z) :
    DenseCapProductionObstruction r h t z := by
  refine ⟨hzgt, hzOmitted, hsafe, ?_⟩
  intro hcovered
  exact hsafe
    (productionCoveredGap_candidateTripleSumFrom
      (r := r) (h := h) (t := t) (z := z) hp hcovered)

theorem candidateTripleSumFrom_E_internal_gap_of_InEInternalGap
    {r h t i z : Nat} (hp : Params r h t) (hi : i < r)
    (hz : InEInternalGap r h t i z) :
    CandidateTripleSumFrom r h t z := by
  let u := z - D r h t
  have hu :
      InInterval (2 * i * h + h) (2 * i * h + 2 * h - 1) u := by
    unfold InEInternalGap InInterval at hz
    dsimp [u]
    constructor <;> omega
  have hzEq : z = D r h t + u := by
    unfold InEInternalGap InInterval at hz
    dsimp [u]
    omega
  rw [hzEq]
  exact candidateTripleSumFrom_E_internal_gap
    (r := r) (h := h) (t := t) (i := i) (u := u) hp hi hu

theorem candidateTripleSumFrom_F_internal_gap_of_InFInternalGap
    {r h t i z : Nat} (hp : Params r h t) (hi : i < r)
    (hz : InFInternalGap r h t i z) :
    CandidateTripleSumFrom r h t z := by
  let u := z - (6 * D r h t + 1)
  have hu :
      InInterval (2 * i * h + h) (2 * i * h + 2 * h - 1) u := by
    unfold InFInternalGap InInterval at hz
    dsimp [u]
    constructor <;> omega
  have hzEq : z = 6 * D r h t + 1 + u := by
    unfold InFInternalGap InInterval at hz
    dsimp [u]
    omega
  rw [hzEq]
  exact candidateTripleSumFrom_F_internal_gap
    (r := r) (h := h) (t := t) (i := i) (u := u) hp hi hu

theorem candidateTripleSumFrom_periodic_low_internal_gap_offset
    {r h t q i o : Nat} (hp : Params r h t) (hq : 1 <= q) (hi : i < r)
    (ho : InXInternalGapOffset r h t i o) :
    CandidateTripleSumFrom r h t (q * M r h t + o) := by
  let n := o - D r h t
  have hn :
      InInterval (2 * i * h + h) (2 * i * h + 2 * h - 1) n := by
    unfold InXInternalGapOffset InInterval at ho
    dsimp [n]
    constructor <;> omega
  have hoEq : o = D r h t + n := by
    unfold InXInternalGapOffset InInterval at ho
    dsimp [n]
    omega
  rw [hoEq]
  exact
    (candidateTripleSumFrom_iff_coveredBySmallerCandidates
      (r := r) (h := h) (t := t)
      (target := q * M r h t + (D r h t + n))).2
      (coveredBySmallerCandidates_periodic_low_internal_full_run_gap
        (r := r) (h := h) (t := t) (q := q) (i := i) (n := n)
        hp hq hi hn)

theorem candidateTripleSumFrom_periodic_high_internal_gap_offset
    {r h t q i o : Nat} (hp : Params r h t) (hq : 1 <= q) (hi : i < r)
    (ho : InYInternalGapOffset r h t i o) :
    CandidateTripleSumFrom r h t (q * M r h t + o) := by
  let n := o - (6 * D r h t + 2)
  have hn :
      InInterval (2 * i * h + h) (2 * i * h + 2 * h - 1) n := by
    unfold InYInternalGapOffset InInterval at ho
    dsimp [n]
    constructor <;> omega
  have hoEq : o = 6 * D r h t + 2 + n := by
    unfold InYInternalGapOffset InInterval at ho
    dsimp [n]
    omega
  rw [hoEq]
  exact
    (candidateTripleSumFrom_iff_coveredBySmallerCandidates
      (r := r) (h := h) (t := t)
      (target := q * M r h t + (6 * D r h t + 2 + n))).2
      (coveredBySmallerCandidates_periodic_high_internal_full_run_gap
        (r := r) (h := h) (t := t) (q := q) (i := i) (n := n)
        hp hq hi hn)

theorem dense_cap_above_first_tail_periodic_decomposition {r h t z : Nat}
    (_hp : Params r h t) (hz : 11 * D r h t + 2 < z) :
    ∃ q o : Nat,
      1 <= q ∧
        InInterval (D r h t) (11 * D r h t + 2) o ∧
          z = q * M r h t + o := by
  let base := M r h t + D r h t
  let a := z - base
  let q := a / M r h t + 1
  let o := a % M r h t + D r h t
  have hbase_eq : base = 11 * D r h t + 3 := by
    dsimp [base]
    unfold M
    omega
  have hbase_le : base <= z := by
    rw [hbase_eq]
    omega
  have hMpos : 0 < M r h t := M_pos
  have hmodlt : a % M r h t < M r h t := Nat.mod_lt a hMpos
  have hsub : a + base = z := by
    dsimp [a]
    exact Nat.sub_add_cancel hbase_le
  have hsum : q * M r h t + o = z := by
    dsimp [q, o]
    have hcalc :
        (a / M r h t + 1) * M r h t +
            (a % M r h t + D r h t) =
          a + (M r h t + D r h t) := by
      have hdiv : (a / M r h t) * M r h t + a % M r h t = a := by
        have h := Nat.div_add_mod a (M r h t)
        rw [Nat.mul_comm] at h
        exact h
      rw [Nat.add_mul, Nat.one_mul]
      omega
    rw [hcalc]
    dsimp [base] at hsub
    exact hsub
  refine ⟨q, o, ?_, ?_, hsum.symm⟩
  · dsimp [q]
    change 1 <= a / M r h t + 1
    exact Nat.succ_le_succ (Nat.zero_le (a / M r h t))
  · constructor
    · dsimp [o]
      omega
    · dsimp [o]
      have hmodle : a % M r h t <= 10 * D r h t + 2 := by
        unfold M at hmodlt ⊢
        omega
      omega

theorem no_DenseCapProductionObstruction {r h t z : Nat}
    (hp : Params r h t) :
    ¬ DenseCapProductionObstruction r h t z := by
  intro hobs
  rcases hobs with ⟨hzgt, hzOmitted, hsafe, hnotCovered⟩
  by_cases hzEhi : z <= 2 * D r h t + 1
  · have hzHull : InEHull r h t z := by
      unfold InEHull InInterval
      exact ⟨Nat.le_of_lt hzgt, hzEhi⟩
    rcases E_hull_not_candidate_internal_gap
        (r := r) (h := h) (t := t) (n := z) hp hzHull hzOmitted with
      ⟨i, hi, hgap⟩
    exact hsafe
      (candidateTripleSumFrom_E_internal_gap_of_InEInternalGap
        (r := r) (h := h) (t := t) (i := i) (z := z) hp hi hgap)
  · have hzAfterE : 2 * D r h t + 1 < z := Nat.lt_of_not_ge hzEhi
    by_cases hzPrefixGap : z <= 6 * D r h t
    · exact hnotCovered
        (Or.inl ⟨by omega, hzPrefixGap⟩)
    · have hzAfterPrefixGap : 6 * D r h t < z :=
        Nat.lt_of_not_ge hzPrefixGap
      by_cases hzFhi : z <= 7 * D r h t + 1
      · have hzHull : InFHull r h t z := by
          unfold InFHull InInterval
          constructor <;> omega
        rcases F_hull_not_candidate_internal_gap
            (r := r) (h := h) (t := t) (n := z) hp hzHull hzOmitted with
          ⟨i, hi, hgap⟩
        exact hsafe
          (candidateTripleSumFrom_F_internal_gap_of_InFInternalGap
            (r := r) (h := h) (t := t) (i := i) (z := z) hp hi hgap)
      · have hzAfterF : 7 * D r h t + 1 < z := Nat.lt_of_not_ge hzFhi
        by_cases hzFirstGap : z <= 11 * D r h t + 2
        · exact hnotCovered
            (Or.inr (Or.inl ⟨by omega, hzFirstGap⟩))
        · have hzAfterFirstGap : 11 * D r h t + 2 < z :=
            Nat.lt_of_not_ge hzFirstGap
          rcases dense_cap_above_first_tail_periodic_decomposition
              (r := r) (h := h) (t := t) (z := z) hp hzAfterFirstGap with
            ⟨q, o, hq, hoI, hzEq⟩
          have hnotTail : ¬ InTailResidue r h t o := by
            intro htail
            exact hzOmitted (by
              rw [hzEq]
              exact candidate_of_periodic_inTailResidue
                (r := r) (h := h) (t := t) (q := q) (u := o) hq htail)
          by_cases hoLow : o <= 2 * D r h t
          · have hoXHull : InXHullOffset r h t o := by
              unfold InXHullOffset InInterval
              exact ⟨hoI.1, hoLow⟩
            rcases X_hull_offset_not_tailResidue_internal_gap
                (r := r) (h := h) (t := t) (o := o) hp hoXHull hnotTail with
              ⟨i, hi, hgap⟩
            exact hsafe (by
              rw [hzEq]
              exact candidateTripleSumFrom_periodic_low_internal_gap_offset
                (r := r) (h := h) (t := t) (q := q) (i := i) (o := o)
                hp hq hi hgap)
          · have hoAfterLow : 2 * D r h t < o := Nat.lt_of_not_ge hoLow
            by_cases hoLowGap : o <= 6 * D r h t + 1
            · exact hnotCovered
                (Or.inr (Or.inr (Or.inl
                  ⟨q, o, hq, ⟨by omega, hoLowGap⟩, hzEq⟩)))
            · have hoAfterLowGap : 6 * D r h t + 1 < o :=
                Nat.lt_of_not_ge hoLowGap
              by_cases hoHigh : o <= 7 * D r h t + 1
              · have hoYHull : InYHullOffset r h t o := by
                  unfold InYHullOffset InInterval
                  constructor <;> omega
                rcases Y_hull_offset_not_tailResidue_internal_gap
                    (r := r) (h := h) (t := t) (o := o) hp hoYHull hnotTail with
                  ⟨i, hi, hgap⟩
                exact hsafe (by
                  rw [hzEq]
                  exact candidateTripleSumFrom_periodic_high_internal_gap_offset
                    (r := r) (h := h) (t := t) (q := q) (i := i) (o := o)
                    hp hq hi hgap)
              · have hoAfterHigh : 7 * D r h t + 1 < o :=
                  Nat.lt_of_not_ge hoHigh
                exact hnotCovered
                  (Or.inr (Or.inr (Or.inr
                    ⟨q, o, hq, ⟨by omega, hoI.2⟩, hzEq⟩)))

theorem dense_cap_exact_characterization {r h t z : Nat}
    (hp : Params r h t) (hzgt : D r h t < z) :
    Candidate r h t z ↔ ¬ CandidateTripleSumFrom r h t z := by
  constructor
  · intro hz
    exact dense_cap_candidate_gt_D_safe
      (r := r) (h := h) (t := t) (z := z) hp hzgt hz
  · intro hsafe
    by_cases hzCandidate : Candidate r h t z
    · exact hzCandidate
    · exact False.elim
        ((no_DenseCapProductionObstruction
            (r := r) (h := h) (t := t) (z := z) hp)
          (dense_cap_safe_omitted_is_production_obstruction
            (r := r) (h := h) (t := t) (z := z) hp
            hzgt hsafe hzCandidate))

end TransitionDenseCap
end GreedyThreeSumfree
