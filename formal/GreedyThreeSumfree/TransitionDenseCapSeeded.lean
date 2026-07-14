import GreedyThreeSumfree.SeededGreedy
import GreedyThreeSumfree.TransitionDenseCapExact

namespace GreedyThreeSumfree
namespace TransitionDenseCap

/-- The dense-cap candidate has exactly the three seed values through `D`. -/
theorem dense_cap_candidate_seed_prefix {r h t z : Nat}
    (hp : Params r h t) (hzle : z <= D r h t) :
    Candidate r h t z ↔ DenseCapSeed r h t z := by
  constructor
  · intro hz
    unfold Candidate at hz
    rcases hz with h1 | hh1 | hE | hF | hper
    · exact Or.inl h1
    · exact Or.inr (Or.inl hh1)
    · have hDle := inE_lower (r := r) (h := h) (t := t) hp hE
      exact Or.inr (Or.inr (by omega))
    · have hFlo := inF_lower (r := r) (h := h) (t := t) hp hF
      have hD := D_ge_three (r := r) (h := h) (t := t) hp
      exact False.elim (by omega)
    · rcases hper with ⟨q, hq, hblock⟩
      have hMle := periodic_block_ge_M (r := r) (h := h) (t := t)
        (q := q) (n := z) hq hblock
      have hDltM := D_lt_M (r := r) (h := h) (t := t)
      exact False.elim (by omega)
  · intro hs
    exact seed_subset_candidate (r := r) (h := h) (t := t) hp hs

/--
The generic three-sum obstruction specializes to the dense-cap candidate set.
-/
theorem tripleSumFrom_candidate_iff_candidateTripleSumFrom {r h t z : Nat} :
    TripleSumFrom (Candidate r h t) z ↔ CandidateTripleSumFrom r h t z := by
  constructor
  · intro htriple
    rcases htriple with ⟨x, y, w, hx, hy, hw, hxy, hyw, hwz, hsum⟩
    exact ⟨x, y, w, hx, hy, hw, hxy, hyw, hwz, hsum⟩
  · intro htriple
    rcases htriple with ⟨x, y, w, hx, hy, hw, hxy, hyw, hwz, hsum⟩
    exact ⟨x, y, w, hx, hy, hw, hxy, hyw, hwz, hsum⟩

/-- Dense-cap exact characterization stated with the generic obstruction. -/
theorem dense_cap_exact_characterization_tripleSumFrom {r h t z : Nat}
    (hp : Params r h t) (hzD : D r h t < z) :
    Candidate r h t z ↔ ¬ TripleSumFrom (Candidate r h t) z := by
  rw [tripleSumFrom_candidate_iff_candidateTripleSumFrom]
  exact dense_cap_exact_characterization
    (r := r) (h := h) (t := t) (z := z) hp hzD

/-- The dense-cap exact characterization is the recursive greedy step. -/
theorem dense_cap_candidate_recursive_step {r h t z : Nat}
    (hp : Params r h t) (hzD : D r h t < z) :
    RecursiveGreedyStep (Candidate r h t) z := by
  unfold RecursiveGreedyStep GreedyAdmissible
  exact dense_cap_exact_characterization_tripleSumFrom
    (r := r) (h := h) (t := t) (z := z) hp hzD

/-- The dense-cap candidate satisfies the seeded recursive greedy rule. -/
theorem dense_cap_candidate_seededGreedySet {r h t : Nat}
    (hp : Params r h t) :
    SeededGreedySet (DenseCapSeed r h t) (Candidate r h t) (D r h t) := by
  constructor
  · intro z hzle
    exact dense_cap_candidate_seed_prefix
      (r := r) (h := h) (t := t) (z := z) hp hzle
  · intro z hzgt
    exact dense_cap_candidate_recursive_step
      (r := r) (h := h) (t := t) (z := z) hp hzgt

/--
Any set with the same dense-cap seed through `D` and the same recursive
admissibility rule is extensionally equal to the explicit candidate set.
-/
theorem dense_cap_seededGreedySet_eq_candidate {r h t : Nat}
    (hp : Params r h t) {G : Nat → Prop}
    (hG : SeededGreedySet (DenseCapSeed r h t) G (D r h t)) :
    ∀ z, G z ↔ Candidate r h t z := by
  intro z
  exact seededGreedySet_ext hG
    (dense_cap_candidate_seededGreedySet
      (r := r) (h := h) (t := t) hp) z

/-- Function extensional form of `dense_cap_seededGreedySet_eq_candidate`. -/
theorem dense_cap_seededGreedySet_funext_eq_candidate {r h t : Nat}
    (hp : Params r h t) {G : Nat → Prop}
    (hG : SeededGreedySet (DenseCapSeed r h t) G (D r h t)) :
    G = Candidate r h t := by
  funext z
  exact propext
    (dense_cap_seededGreedySet_eq_candidate
      (r := r) (h := h) (t := t) hp hG z)

end TransitionDenseCap
end GreedyThreeSumfree
