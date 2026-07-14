import GreedyThreeSumfree.SeededGreedy
import GreedyThreeSumfree.RBandFull

namespace GreedyThreeSumfree
namespace RBand

/-- Initial seed for the regular `r`-band theorem before recursion starts. -/
def RBandSeed (r h e z : Nat) : Prop :=
  z = 1 ∨ z = h - 1 ∨ z = D r h e

theorem D_lt_M {r h e : Nat} (hp : Params r h e) :
    D r h e < M r h e := by
  have hD := D_ge_h_add_one (r := r) (h := h) (e := e) hp
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  unfold M
  omega

theorem D_inH_zero {r h e : Nat} (hp : Params r h e) :
    InH r h e 0 (D r h e) := by
  have hh := hp.h_ge_six
  unfold InH InInterval HHi HLo
  omega

theorem D_inU {r h e : Nat} (hp : Params r h e) :
    InU r h e (D r h e) := by
  refine ⟨0, ?_, D_inH_zero (r := r) (h := h) (e := e) hp⟩
  have hr := hp.r_pos
  omega

theorem candidate_D {r h e : Nat} (hp : Params r h e) :
    Candidate r h e (D r h e) :=
  candidate_of_inU (r := r) (h := h) (e := e)
    (D_inU (r := r) (h := h) (e := e) hp)

/-- The explicit candidate has exactly the three seed values through `D`. -/
theorem regular_rband_candidate_seed_prefix {r h e z : Nat}
    (hp : Params r h e) (hzle : z <= D r h e) :
    Candidate r h e z ↔ RBandSeed r h e z := by
  constructor
  · intro hz
    rcases hz with hzPrefix | hzBlock
    · unfold InPrefix at hzPrefix
      rcases hzPrefix with h1 | hh1 | hU
      · exact Or.inl h1
      · exact Or.inr (Or.inl hh1)
      · have hDle := inU_lower (r := r) (h := h) (e := e) (n := z) hp hU
        exact Or.inr (Or.inr (by omega))
    · rcases hzBlock with ⟨q, hq, hblock⟩
      have hMle := periodic_block_ge_M (r := r) (h := h) (e := e)
        (q := q) (n := z) hq hblock
      have hDltM := D_lt_M (r := r) (h := h) (e := e) hp
      exact False.elim (by omega)
  · intro hs
    unfold RBandSeed at hs
    rcases hs with h1 | hh1 | hD
    · rw [h1]
      exact candidate_one r h e
    · rw [hh1]
      exact candidate_h_sub_one r h e
    · rw [hD]
      exact candidate_D (r := r) (h := h) (e := e) hp

/--
The generic three-sum obstruction specializes to the regular `r`-band
candidate set.
-/
theorem tripleSumFrom_candidate_iff_candidateTripleSumFrom {r h e z : Nat} :
    TripleSumFrom (Candidate r h e) z ↔ CandidateTripleSumFrom r h e z := by
  constructor
  · intro htriple
    rcases htriple with ⟨x, y, w, hx, hy, hw, hxy, hyw, hwz, hsum⟩
    exact ⟨x, y, w, hx, hy, hw, hxy, hyw, hwz, hsum⟩
  · intro htriple
    rcases htriple with ⟨x, y, w, hx, hy, hw, hxy, hyw, hwz, hsum⟩
    exact ⟨x, y, w, hx, hy, hw, hxy, hyw, hwz, hsum⟩

/-- Regular `r`-band exact characterization stated with the generic obstruction. -/
theorem regular_rband_exact_characterization_tripleSumFrom {r h e z : Nat}
    (hp : Params r h e) (hzD : D r h e < z) :
    Candidate r h e z ↔ ¬ TripleSumFrom (Candidate r h e) z := by
  rw [tripleSumFrom_candidate_iff_candidateTripleSumFrom]
  exact regular_rband_exact_characterization
    (r := r) (h := h) (e := e) (z := z) hp hzD

/-- The regular `r`-band exact characterization is the recursive greedy step. -/
theorem regular_rband_candidate_recursive_step {r h e z : Nat}
    (hp : Params r h e) (hzD : D r h e < z) :
    RecursiveGreedyStep (Candidate r h e) z := by
  unfold RecursiveGreedyStep GreedyAdmissible
  exact regular_rband_exact_characterization_tripleSumFrom
    (r := r) (h := h) (e := e) (z := z) hp hzD

/-- The regular `r`-band candidate satisfies the seeded recursive greedy rule. -/
theorem regular_rband_candidate_seededGreedySet {r h e : Nat}
    (hp : Params r h e) :
    SeededGreedySet (RBandSeed r h e) (Candidate r h e) (D r h e) := by
  constructor
  · intro z hzle
    exact regular_rband_candidate_seed_prefix
      (r := r) (h := h) (e := e) (z := z) hp hzle
  · intro z hzgt
    exact regular_rband_candidate_recursive_step
      (r := r) (h := h) (e := e) (z := z) hp hzgt

/--
Any set with the same seed through `D` and the same recursive admissibility
rule is extensionally equal to the explicit regular `r`-band candidate.
-/
theorem regular_rband_seededGreedySet_eq_candidate {r h e : Nat}
    (hp : Params r h e) {G : Nat → Prop}
    (hG : SeededGreedySet (RBandSeed r h e) G (D r h e)) :
    ∀ z, G z ↔ Candidate r h e z := by
  intro z
  exact seededGreedySet_ext hG
    (regular_rband_candidate_seededGreedySet
      (r := r) (h := h) (e := e) hp) z

end RBand
end GreedyThreeSumfree
