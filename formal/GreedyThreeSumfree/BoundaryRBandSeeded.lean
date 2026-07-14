import GreedyThreeSumfree.SeededGreedy
import GreedyThreeSumfree.BoundaryRBandExact

namespace GreedyThreeSumfree
namespace BoundaryRBand

/-- Initial seed for the boundary `r`-band theorem before recursion starts. -/
def BoundaryRBandSeed (r h z : Nat) : Prop :=
  z = 1 ∨ z = h - 1 ∨ z = D r h

theorem D_lt_M {r h : Nat} (hp : Params r h) :
    D r h < M r h := by
  have hDc := D_lt_c (r := r) (h := h) hp
  have hcM := c_lt_M (r := r) (h := h) hp
  omega

theorem D_inH_zero {r h : Nat} (hp : Params r h) :
    InH r h 0 (D r h) := by
  have hh := hp.h_ge_six
  unfold InH InInterval HHi HLo
  omega

theorem D_inU {r h : Nat} (hp : Params r h) :
    InU r h (D r h) := by
  refine ⟨0, ?_, D_inH_zero (r := r) (h := h) hp⟩
  have hr := hp.r_pos
  omega

theorem candidate_D {r h : Nat} (hp : Params r h) :
    Candidate r h (D r h) :=
  candidate_of_inU (r := r) (h := h)
    (D_inU (r := r) (h := h) hp)

/-- The explicit boundary candidate has exactly the three seed values through `D`. -/
theorem boundary_rband_candidate_seed_prefix {r h z : Nat}
    (hp : Params r h) (hzle : z <= D r h) :
    Candidate r h z ↔ BoundaryRBandSeed r h z := by
  constructor
  · intro hz
    rcases hz with hzPrefix | hzBlock
    · unfold InPrefix at hzPrefix
      rcases hzPrefix with h1 | hh1 | hc | hU
      · exact Or.inl h1
      · exact Or.inr (Or.inl hh1)
      · have hDc := D_lt_c (r := r) (h := h) hp
        exact False.elim (by omega)
      · have hDle := inU_lower (r := r) (h := h) (n := z) hp hU
        exact Or.inr (Or.inr (by omega))
    · rcases hzBlock with ⟨q, hq, hblock⟩
      have hMle := periodic_block_ge_M (r := r) (h := h)
        (q := q) (n := z) hq hblock
      have hDltM := D_lt_M (r := r) (h := h) hp
      exact False.elim (by omega)
  · intro hs
    unfold BoundaryRBandSeed at hs
    rcases hs with h1 | hh1 | hD
    · rw [h1]
      exact candidate_one r h
    · rw [hh1]
      exact candidate_h_sub_one r h
    · rw [hD]
      exact candidate_D (r := r) (h := h) hp

/--
The generic three-sum obstruction specializes to the boundary `r`-band
candidate set.
-/
theorem tripleSumFrom_candidate_iff_candidateTripleSumFrom {r h z : Nat} :
    TripleSumFrom (Candidate r h) z ↔ CandidateTripleSumFrom r h z := by
  constructor
  · intro htriple
    rcases htriple with ⟨x, y, w, hx, hy, hw, hxy, hyw, hwz, hsum⟩
    exact ⟨x, y, w, hx, hy, hw, hxy, hyw, hwz, hsum⟩
  · intro htriple
    rcases htriple with ⟨x, y, w, hx, hy, hw, hxy, hyw, hwz, hsum⟩
    exact ⟨x, y, w, hx, hy, hw, hxy, hyw, hwz, hsum⟩

/-- Boundary `r`-band exact characterization stated with the generic obstruction. -/
theorem boundary_rband_exact_characterization_tripleSumFrom {r h z : Nat}
    (hp : Params r h) (hzD : D r h < z) :
    Candidate r h z ↔ ¬ TripleSumFrom (Candidate r h) z := by
  rw [tripleSumFrom_candidate_iff_candidateTripleSumFrom]
  exact boundary_rband_above_seed_characterization
    (r := r) (h := h) (z := z) hp hzD

/-- The boundary `r`-band exact characterization is the recursive greedy step. -/
theorem boundary_rband_candidate_recursive_step {r h z : Nat}
    (hp : Params r h) (hzD : D r h < z) :
    RecursiveGreedyStep (Candidate r h) z := by
  unfold RecursiveGreedyStep GreedyAdmissible
  exact boundary_rband_exact_characterization_tripleSumFrom
    (r := r) (h := h) (z := z) hp hzD

/-- The boundary `r`-band candidate satisfies the seeded recursive greedy rule. -/
theorem boundary_rband_candidate_seededGreedySet {r h : Nat}
    (hp : Params r h) :
    SeededGreedySet (BoundaryRBandSeed r h) (Candidate r h) (D r h) := by
  constructor
  · intro z hzle
    exact boundary_rband_candidate_seed_prefix
      (r := r) (h := h) (z := z) hp hzle
  · intro z hzgt
    exact boundary_rband_candidate_recursive_step
      (r := r) (h := h) (z := z) hp hzgt

/--
Any set with the same seed through `D` and the same recursive admissibility
rule is extensionally equal to the explicit boundary `r`-band candidate.
-/
theorem boundary_rband_seededGreedySet_eq_candidate {r h : Nat}
    (hp : Params r h) {G : Nat → Prop}
    (hG : SeededGreedySet (BoundaryRBandSeed r h) G (D r h)) :
    ∀ z, G z ↔ Candidate r h z := by
  intro z
  exact seededGreedySet_ext hG
    (boundary_rband_candidate_seededGreedySet
      (r := r) (h := h) hp) z

end BoundaryRBand
end GreedyThreeSumfree
