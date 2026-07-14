import GreedyThreeSumfree.SeededGreedy
import GreedyThreeSumfree.TheoremB

namespace GreedyThreeSumfree
namespace NextDiagonal

/-- Initial seed for Theorem B before recursion starts. -/
def TheoremBSeed (g z : Nat) : Prop :=
  z = 1 ∨ z = g ∨ z = 2 * g + 1

theorem seed_inH {g : Nat} (_h : Params g) : InH g (2 * g + 1) := by
  unfold InH InInterval
  constructor <;> omega

theorem candidate_seed_value {g : Nat} (h : Params g) :
    Candidate g (2 * g + 1) :=
  candidate_of_H (seed_inH (g := g) h)

/-- The explicit Theorem B candidate has exactly the three seed values through `2g+1`. -/
theorem theoremB_candidate_seed_prefix {g z : Nat}
    (h : Params g) (hzle : z <= 2 * g + 1) :
    Candidate g z ↔ TheoremBSeed g z := by
  constructor
  · intro hz
    unfold Candidate at hz
    rcases hz with hp | hb
    · unfold InPrefix at hp
      rcases hp with h1 | hg | hc | hzH
      · exact Or.inl h1
      · exact Or.inr (Or.inl hg)
      · have hg5 := h.five_le_g
        exact False.elim (by
          rw [hc] at hzle
          unfold c at hzle
          omega)
      · unfold InH InInterval at hzH
        exact Or.inr (Or.inr (by omega))
    · rcases hb with ⟨q, hq, hzblock⟩
      have hMz : M g <= z := positive_block_ge_M hq hzblock
      have hseed_lt_M : 2 * g + 1 < M g := by
        unfold M
        omega
      exact False.elim (by omega)
  · intro hs
    unfold TheoremBSeed at hs
    rcases hs with h1 | hg | hseed
    · rw [h1]
      exact candidate_one g
    · rw [hg]
      exact candidate_g g
    · rw [hseed]
      exact candidate_seed_value h

/-- Theorem B's exact characterization is the recursive greedy step after the seed. -/
theorem theoremB_candidate_recursive_step {g z : Nat}
    (h : Params g) (hzgt : 2 * g + 1 < z) :
    RecursiveGreedyStep (Candidate g) z := by
  unfold RecursiveGreedyStep GreedyAdmissible
  exact exact_characterization h hzgt

/-- The candidate set satisfies the seeded recursive greedy criterion for Theorem B. -/
theorem theoremB_candidate_seededGreedySet {g : Nat} (h : Params g) :
    SeededGreedySet (TheoremBSeed g) (Candidate g) (2 * g + 1) := by
  constructor
  · intro z hzle
    exact theoremB_candidate_seed_prefix h hzle
  · intro z hzgt
    exact theoremB_candidate_recursive_step h hzgt

/--
Consequently, any set satisfying the same Theorem B seed and recursive greedy
criterion is extensionally equal to the explicit candidate set.
-/
theorem theoremB_seededGreedySet_eq_candidate {g : Nat} (h : Params g)
    {G : Nat → Prop}
    (hG : SeededGreedySet (TheoremBSeed g) G (2 * g + 1)) :
    ∀ z, G z ↔ Candidate g z := by
  intro z
  exact seededGreedySet_ext hG (theoremB_candidate_seededGreedySet h) z

end NextDiagonal
end GreedyThreeSumfree
