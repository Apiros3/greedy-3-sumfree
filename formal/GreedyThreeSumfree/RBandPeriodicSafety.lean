import GreedyThreeSumfree.RBandResidueClassification

namespace GreedyThreeSumfree
namespace RBand

/--
An ordered triple of distinct earlier candidates summing to `target`.

This is the regular `r`-band analogue of the project-level `TripleSumFrom`
predicate, specialized to the R-band candidate set.
-/
def CandidateTripleSumFrom (r h e target : Nat) : Prop :=
  ∃ x y z : Nat,
    Candidate r h e x ∧ Candidate r h e y ∧ Candidate r h e z ∧
      x < y ∧ y < z ∧ z < target ∧ x + y + z = target

theorem add_three_mod (x y z m : Nat) :
    (x + y + z) % m = (x % m + y % m + z % m) % m := by
  simp [Nat.add_mod]

theorem triple_sum_mod {x y z target m : Nat} (hsum : x + y + z = target) :
    (x % m + y % m + z % m) % m = target % m := by
  rw [← hsum]
  symm
  exact add_three_mod x y z m

theorem prefix_mod_eq {r h e n : Nat} (hp : Params r h e)
    (hn : InPrefix r h e n) :
    n % M r h e = n :=
  Nat.mod_eq_of_lt (prefix_lt_M hp hn)

theorem periodic_block_mod_eq {r h e q rho n : Nat} (hp : Params r h e)
    (hrho : InV r h e rho) (hn : n = q * M r h e + rho) :
    n % M r h e = rho := by
  rw [hn]
  rw [Nat.mul_comm q (M r h e)]
  rw [Nat.mul_add_mod_self_left]
  exact Nat.mod_eq_of_lt (inV_lt_M hp hrho)

theorem in_periodic_block_mod_eq {r h e q n : Nat} (hp : Params r h e)
    (hn : InPeriodicBlock r h e q n) :
    ∃ rho : Nat, InV r h e rho ∧ n % M r h e = rho := by
  rcases hn with ⟨rho, hrho, hn_eq⟩
  exact ⟨rho, hrho, periodic_block_mod_eq hp hrho hn_eq⟩

/-- Every R-band candidate has a residue modulo `M` lying in `P union V`. -/
theorem candidate_mod_in_residue {r h e n : Nat} (hp : Params r h e)
    (hn : Candidate r h e n) :
    InResidue r h e (n % M r h e) := by
  rcases hn with hpfx | hblock
  · rw [prefix_mod_eq hp hpfx]
    exact Or.inl hpfx
  · rcases hblock with ⟨q, _hq, hnblock⟩
    rcases in_periodic_block_mod_eq (r := r) (h := h) (e := e) (q := q) hp hnblock with
      ⟨rho, hrho, hmod⟩
    rw [hmod]
    exact Or.inr hrho

/--
If the candidate residues are already strictly ordered, their residue sum is an
ordered residue triple sum.
-/
theorem candidate_ordered_residue_triple_sum {r h e x y z : Nat}
    (hp : Params r h e)
    (hx : Candidate r h e x) (hy : Candidate r h e y) (hz : Candidate r h e z)
    (hxy : x % M r h e < y % M r h e)
    (hyz : y % M r h e < z % M r h e) :
    OrderedResidueTripleSum r h e
      (x % M r h e + y % M r h e + z % M r h e) := by
  refine ⟨x % M r h e, y % M r h e, z % M r h e, ?_, ?_, ?_, hxy, hyz, rfl⟩
  · exact candidate_mod_in_residue hp hx
  · exact candidate_mod_in_residue hp hy
  · exact candidate_mod_in_residue hp hz

/--
The lower side of the residue squeeze: a residue sum cannot be strictly below
its congruent target residue.
-/
theorem residue_mod_contradiction_below {r h e rho S : Nat}
    (hmod : S % M r h e = rho) (hS_lt_rho : S < rho) :
    False := by
  have hle : rho <= S := by
    have hmod_le := Nat.mod_le S (M r h e)
    simpa [hmod] using hmod_le
  omega

/--
For an ordered residue triple, congruence to a target residue in `V` forces
literal equality of the residue sum.
-/
theorem ordered_residue_mod_eq_forces_eq {r h e rho S : Nat}
    (hp : Params r h e) (hrho : InV r h e rho)
    (hS : OrderedResidueTripleSum r h e S)
    (hmod : S % M r h e = rho) :
    S = rho := by
  by_cases hEq : S = rho
  · exact hEq
  · by_cases hrho_lt_S : rho < S
    · have hlo := ordered_residue_sum_lower hp hS
      have hhi := ordered_residue_sum_upper hp hS
      exact False.elim
        (residue_mod_contradiction hp hrho hlo hhi hmod hrho_lt_S)
    · have hS_lt_rho : S < rho := by omega
      exact False.elim (residue_mod_contradiction_below hmod hS_lt_rho)

/--
Witness-level form of `ordered_residue_mod_eq_forces_eq`, ready for applying
the exact-residue classification.
-/
theorem ordered_residue_witness_mod_eq_forces_eq {r h e rho x y z S : Nat}
    (hp : Params r h e) (hrho : InV r h e rho)
    (hx : InResidue r h e x) (hy : InResidue r h e y)
    (hz : InResidue r h e z) (hxy : x < y) (hyz : y < z)
    (hsum : x + y + z = S) (hmod : S % M r h e = rho) :
    x + y + z = rho := by
  have hS : OrderedResidueTripleSum r h e S :=
    ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩
  have hSeq := ordered_residue_mod_eq_forces_eq hp hrho hS hmod
  omega

/--
An ordered residue witness congruent to a target residue in `V` is classified
as the forced exact triple `(1, h-1, rho-h)`.
-/
theorem ordered_residue_witness_mod_eq_classification
    {r h e rho x y z S : Nat} (hp : Params r h e)
    (hrho : InV r h e rho)
    (hx : InResidue r h e x) (hy : InResidue r h e y)
    (hz : InResidue r h e z) (hxy : x < y) (hyz : y < z)
    (hsum : x + y + z = S) (hmod : S % M r h e = rho) :
    x = 1 ∧ y = h - 1 ∧ z = rho - h := by
  have hsum_rho := ordered_residue_witness_mod_eq_forces_eq
    (r := r) (h := h) (e := e) (rho := rho) (x := x) (y := y) (z := z) (S := S)
    hp hrho hx hy hz hxy hyz hsum hmod
  exact ordered_sum_eq_rho_classification
    (r := r) (h := h) (e := e) (rho := rho) (x := x) (y := y) (z := z)
    hp hx hy hz hxy hyz hsum_rho hrho

theorem ordered_residue_witness_mod_eq_inI_zero_impossible
    {r h e rho x y z S : Nat} (hp : Params r h e)
    (hx : InResidue r h e x) (hy : InResidue r h e y)
    (hz : InResidue r h e z) (hxy : x < y) (hyz : y < z)
    (hsum : x + y + z = S) (hmod : S % M r h e = rho)
    (hrhoI : InI r h e 0 rho) :
    False := by
  have hi : 0 < r := by
    have hr := hp.r_pos
    omega
  have hrho : InV r h e rho := ⟨0, hi, hrhoI⟩
  have hsum_rho := ordered_residue_witness_mod_eq_forces_eq
    (r := r) (h := h) (e := e) (rho := rho) (x := x) (y := y) (z := z) (S := S)
    hp hrho hx hy hz hxy hyz hsum hmod
  exact ordered_sum_eq_rho_inI_zero_impossible
    (r := r) (h := h) (e := e) (rho := rho) (x := x) (y := y) (z := z)
    hp hx hy hz hxy hyz hsum_rho hrhoI

theorem ordered_residue_witness_mod_eq_inI_last_prefix
    {r h e i rho x y z S : Nat} (hp : Params r h e)
    (hi_pos : 1 <= i) (hi : i < r)
    (hx : InResidue r h e x) (hy : InResidue r h e y)
    (hz : InResidue r h e z) (hxy : x < y) (hyz : y < z)
    (hsum : x + y + z = S) (hmod : S % M r h e = rho)
    (hrhoI : InI r h e i rho) :
    InPrefix r h e z := by
  have hrho : InV r h e rho := ⟨i, hi, hrhoI⟩
  have hsum_rho := ordered_residue_witness_mod_eq_forces_eq
    (r := r) (h := h) (e := e) (rho := rho) (x := x) (y := y) (z := z) (S := S)
    hp hrho hx hy hz hxy hyz hsum hmod
  exact ordered_sum_eq_rho_inI_last_prefix
    (r := r) (h := h) (e := e) (i := i) (rho := rho) (x := x) (y := y) (z := z)
    hp hi_pos hi hx hy hz hxy hyz hsum_rho hrhoI

theorem periodic_target_mod_eq {r h e q rho target : Nat}
    (hp : Params r h e) (hrho : InV r h e rho)
    (htarget : target = q * M r h e + rho) :
    target % M r h e = rho :=
  periodic_block_mod_eq hp hrho htarget

/--
Conditional periodic-target residue classification for actual candidate
triples.  The remaining unformalized bridge is to remove the explicit residue
ordering hypotheses from an arbitrary `CandidateTripleSumFrom`.
-/
theorem candidate_triple_ordered_residue_classification
    {r h e q rho target x y z : Nat} (hp : Params r h e)
    (hrho : InV r h e rho) (htarget : target = q * M r h e + rho)
    (hx : Candidate r h e x) (hy : Candidate r h e y) (hz : Candidate r h e z)
    (hxy_res : x % M r h e < y % M r h e)
    (hyz_res : y % M r h e < z % M r h e)
    (hsum : x + y + z = target) :
    x % M r h e = 1 ∧ y % M r h e = h - 1 ∧ z % M r h e = rho - h := by
  let S := x % M r h e + y % M r h e + z % M r h e
  have hmod_target : target % M r h e = rho :=
    periodic_target_mod_eq (r := r) (h := h) (e := e) (q := q)
      (rho := rho) (target := target) hp hrho htarget
  have hmod : S % M r h e = rho := by
    dsimp [S]
    rw [triple_sum_mod hsum, hmod_target]
  exact ordered_residue_witness_mod_eq_classification
    (r := r) (h := h) (e := e) (rho := rho)
    (x := x % M r h e) (y := y % M r h e) (z := z % M r h e) (S := S)
    hp hrho
    (candidate_mod_in_residue hp hx)
    (candidate_mod_in_residue hp hy)
    (candidate_mod_in_residue hp hz)
    hxy_res hyz_res rfl hmod

end RBand
end GreedyThreeSumfree
