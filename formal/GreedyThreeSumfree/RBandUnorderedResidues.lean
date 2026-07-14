import GreedyThreeSumfree.RBandPeriodicSafety

namespace GreedyThreeSumfree
namespace RBand

/--
No two entries of a three-term list are equal to the distinguished value `v`.
This is deliberately weaker than pairwise distinct residues: periodic candidate
triples may repeat large residues in different quotient blocks.
-/
def NoDuplicateValue3 (x y z v : Nat) : Prop :=
  (x = v → y ≠ v) ∧ (x = v → z ≠ v) ∧ (y = v → z ≠ v)

/--
The unordered residue feasibility needed by the exact-residue classification:
the three entries are available residues, and the two prefix singleton residues
`1` and `h-1` do not occur twice.
-/
def FeasibleUnorderedResidueTriple (r h e x y z : Nat) : Prop :=
  InResidue r h e x ∧ InResidue r h e y ∧ InResidue r h e z ∧
    NoDuplicateValue3 x y z 1 ∧ NoDuplicateValue3 x y z (h - 1)

/-- Symmetric statement of the forced unordered residue pattern. -/
def UnorderedResidueClassification (h rho x y z : Nat) : Prop :=
  (x = rho - h ∧ y = 1 ∧ z = h - 1) ∨
  (x = rho - h ∧ y = h - 1 ∧ z = 1) ∨
  (y = rho - h ∧ x = 1 ∧ z = h - 1) ∨
  (y = rho - h ∧ x = h - 1 ∧ z = 1) ∨
  (z = rho - h ∧ x = 1 ∧ y = h - 1) ∨
  (z = rho - h ∧ x = h - 1 ∧ y = 1)

theorem residue_lt_VBot_eq_one_or_h_sub_one {r h e x : Nat}
    (hp : Params r h e) (hx : InResidue r h e x)
    (hxlt : x < VBot r h e) :
    x = 1 ∨ x = h - 1 := by
  rcases hx with hxP | hxV
  · unfold InPrefix at hxP
    rcases hxP with rfl | rfl | hxU
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rcases hxU with ⟨i, _hi, hxH⟩
      have hD := D_ge_three hp
      unfold InH InInterval HLo at hxH
      unfold VBot at hxlt
      omega
  · have hxlo := inV_lower hp hxV
    omega

/-- A candidate with residue below `VBot` must come from the prefix. -/
theorem candidate_mod_lt_VBot_prefix {r h e n : Nat}
    (hp : Params r h e) (hn : Candidate r h e n)
    (hnlt : n % M r h e < VBot r h e) :
    InPrefix r h e n := by
  rcases hn with hnP | hnBlock
  · exact hnP
  · rcases hnBlock with ⟨q, _hq, hnq⟩
    rcases in_periodic_block_mod_eq (r := r) (h := h) (e := e) (q := q) hp hnq with
      ⟨rho, hrho, hnmod⟩
    have hrlo := inV_lower hp hrho
    rw [hnmod] at hnlt
    omega

theorem candidate_mod_lt_VBot_eq_one_or_h_sub_one {r h e n : Nat}
    (hp : Params r h e) (hn : Candidate r h e n)
    (hnlt : n % M r h e < VBot r h e) :
    n % M r h e = 1 ∨ n % M r h e = h - 1 := by
  exact residue_lt_VBot_eq_one_or_h_sub_one hp
    (candidate_mod_in_residue hp hn) hnlt

theorem candidate_mod_eq_one {r h e n : Nat}
    (hp : Params r h e) (hn : Candidate r h e n)
    (hnmod : n % M r h e = 1) :
    n = 1 := by
  have hnlt : n % M r h e < VBot r h e := by
    have hD := D_ge_h_add_one hp
    have hh := hp.h_ge_six
    rw [hnmod]
    unfold VBot
    omega
  have hnP := candidate_mod_lt_VBot_prefix hp hn hnlt
  have hprefix_mod := prefix_mod_eq hp hnP
  omega

theorem candidate_mod_eq_h_sub_one_of_lt_VBot {r h e n : Nat}
    (hp : Params r h e) (hn : Candidate r h e n)
    (hnlt : n % M r h e < VBot r h e)
    (hnmod : n % M r h e = h - 1) :
    n = h - 1 := by
  have hnP := candidate_mod_lt_VBot_prefix hp hn hnlt
  have hprefix_mod := prefix_mod_eq hp hnP
  omega

theorem residue_le_h_sub_one_eq_one_or_h_sub_one {r h e x : Nat}
    (hp : Params r h e) (hx : InResidue r h e x)
    (hxle : x <= h - 1) :
    x = 1 ∨ x = h - 1 := by
  by_cases hxone : x = 1
  · exact Or.inl hxone
  · have hxge := residue_ne_one_ge_h_sub_one hp hx hxone
    exact Or.inr (by omega)

private theorem two_large_residue_sum_exceeds_VTop
    {r h e x y z : Nat} (hp : Params r h e)
    (hx : InResidue r h e x) (hy : InResidue r h e y)
    (hz : InResidue r h e z)
    (hxgt : h - 1 < x) (hygt : h - 1 < y) :
    VTop r h e < x + y + z := by
  have hxlarge := residue_gt_h_sub_one_ge_VBot hp hx hxgt
  have hylarge := residue_gt_h_sub_one_ge_VBot hp hy hygt
  have hzlo := residue_ge_one hp hz
  have htoo := two_large_residues_exceed_VTop hp hxlarge hylarge
  omega

private theorem not_all_three_small_of_no_duplicates
    {h x y z : Nat}
    (hnd1 : NoDuplicateValue3 x y z 1)
    (hndh : NoDuplicateValue3 x y z (h - 1))
    (hxsmall : x = 1 ∨ x = h - 1)
    (hysmall : y = 1 ∨ y = h - 1)
    (hzsmall : z = 1 ∨ z = h - 1) :
    False := by
  rcases hxsmall with rfl | rfl
  · rcases hysmall with hy | hy
    · exact hnd1.1 rfl hy
    · rcases hzsmall with hz | hz
      · exact hnd1.2.1 rfl hz
      · exact hndh.2.2 hy hz
  · rcases hysmall with hy | hy
    · rcases hzsmall with hz | hz
      · exact hnd1.2.2 hy hz
      · exact hndh.2.1 rfl hz
    · exact hndh.1 rfl hy

private theorem VTop_lt_two_h_sub_one_add_one_of_not_low
    {r h e : Nat} (hp : Params r h e)
    (hnot : ¬ h - 1 < VBot r h e) :
    VTop r h e < (h - 1) + (h - 1) + 1 := by
  have hbot_le : VBot r h e <= h - 1 := by omega
  have hDhi := D_ge_h_add_one hp
  have hDlo : D r h e <= h + 1 := by
    have hD3 := D_ge_three hp
    unfold VBot at hbot_le
    omega
  have hDeq : D r h e = h + 1 := by omega
  have hprod_le : (2 * r - 1) * h <= h := by
    have he := hp.e_pos
    unfold D at hDeq
    omega
  unfold VTop
  omega

/--
Exact unordered residue classification.  No residue ordering is assumed; the
only distinctness information needed is that the two prefix singletons do not
occur twice.
-/
theorem unordered_exact_residue_classification
    {r h e rho x y z : Nat} (hp : Params r h e)
    (hxyz : FeasibleUnorderedResidueTriple r h e x y z)
    (hsum : x + y + z = rho) (hrho : InV r h e rho) :
    UnorderedResidueClassification h rho x y z := by
  rcases hxyz with ⟨hx, hy, hz, hnd1, hndh⟩
  have hrho_hi := inV_upper hp hrho
  by_cases hxlarge : h - 1 < x
  · have hyle : y <= h - 1 := by
      by_cases hyle : y <= h - 1
      · exact hyle
      have hylarge : h - 1 < y := by omega
      have htoo := two_large_residue_sum_exceeds_VTop hp hx hy hz hxlarge hylarge
      omega
    have hzle : z <= h - 1 := by
      by_cases hzle : z <= h - 1
      · exact hzle
      have hzlarge : h - 1 < z := by omega
      have htoo := two_large_residue_sum_exceeds_VTop
        (r := r) (h := h) (e := e) (x := x) (y := z) (z := y)
        hp hx hz hy hxlarge hzlarge
      omega
    rcases residue_le_h_sub_one_eq_one_or_h_sub_one hp hy hyle with hyone | hyh
    · rcases residue_le_h_sub_one_eq_one_or_h_sub_one hp hz hzle with hzone | hzh
      · exact False.elim (hnd1.2.2 hyone hzone)
      · left
        constructor
        · omega
        · exact ⟨hyone, hzh⟩
    · rcases residue_le_h_sub_one_eq_one_or_h_sub_one hp hz hzle with hzone | hzh
      · right
        left
        constructor
        · omega
        · exact ⟨hyh, hzone⟩
      · exact False.elim (hndh.2.2 hyh hzh)
  · have hxle : x <= h - 1 := by omega
    by_cases hylarge : h - 1 < y
    · have hzle : z <= h - 1 := by
        by_cases hzle : z <= h - 1
        · exact hzle
        have hzlarge : h - 1 < z := by omega
        have htoo := two_large_residue_sum_exceeds_VTop hp hy hz hx hylarge hzlarge
        omega
      rcases residue_le_h_sub_one_eq_one_or_h_sub_one hp hx hxle with hxone | hxh
      · rcases residue_le_h_sub_one_eq_one_or_h_sub_one hp hz hzle with hzone | hzh
        · exact False.elim (hnd1.2.1 hxone hzone)
        · right
          right
          left
          constructor
          · omega
          · exact ⟨hxone, hzh⟩
      · rcases residue_le_h_sub_one_eq_one_or_h_sub_one hp hz hzle with hzone | hzh
        · right
          right
          right
          left
          constructor
          · omega
          · exact ⟨hxh, hzone⟩
        · exact False.elim (hndh.2.1 hxh hzh)
    · have hyle : y <= h - 1 := by omega
      by_cases hzlarge : h - 1 < z
      · rcases residue_le_h_sub_one_eq_one_or_h_sub_one hp hx hxle with hxone | hxh
        · rcases residue_le_h_sub_one_eq_one_or_h_sub_one hp hy hyle with hyone | hyh
          · exact False.elim (hnd1.1 hxone hyone)
          · right
            right
            right
            right
            left
            constructor
            · omega
            · exact ⟨hxone, hyh⟩
        · rcases residue_le_h_sub_one_eq_one_or_h_sub_one hp hy hyle with hyone | hyh
          · right
            right
            right
            right
            right
            constructor
            · omega
            · exact ⟨hxh, hyone⟩
          · exact False.elim (hndh.1 hxh hyh)
      · have hzle : z <= h - 1 := by omega
        have hxsmall := residue_le_h_sub_one_eq_one_or_h_sub_one hp hx hxle
        have hysmall := residue_le_h_sub_one_eq_one_or_h_sub_one hp hy hyle
        have hzsmall := residue_le_h_sub_one_eq_one_or_h_sub_one hp hz hzle
        exact False.elim
          (not_all_three_small_of_no_duplicates hnd1 hndh hxsmall hysmall hzsmall)

theorem candidate_residue_noDuplicate_one {r h e x y z : Nat}
    (hp : Params r h e)
    (hx : Candidate r h e x) (hy : Candidate r h e y)
    (hz : Candidate r h e z) (hxy : x < y) (hyz : y < z) :
    NoDuplicateValue3 (x % M r h e) (y % M r h e) (z % M r h e) 1 := by
  constructor
  · intro hxone hyone
    have hxeq := candidate_mod_eq_one hp hx hxone
    have hyeq := candidate_mod_eq_one hp hy hyone
    omega
  · constructor
    · intro hxone hzone
      have hxeq := candidate_mod_eq_one hp hx hxone
      have hzeq := candidate_mod_eq_one hp hz hzone
      omega
    · intro hyone hzone
      have hyeq := candidate_mod_eq_one hp hy hyone
      have hzeq := candidate_mod_eq_one hp hz hzone
      omega

private theorem candidate_residue_h_sub_one_pair_impossible_of_exact_sum
    {r h e rho u v w : Nat} (hp : Params r h e) (hrho : InV r h e rho)
    (hu : Candidate r h e u) (hv : Candidate r h e v)
    (hw : Candidate r h e w) (huv : u < v)
    (hsum : u % M r h e + v % M r h e + w % M r h e = rho)
    (humod : u % M r h e = h - 1)
    (hvmod : v % M r h e = h - 1) :
    False := by
  by_cases hlow : h - 1 < VBot r h e
  · have hult : u % M r h e < VBot r h e := by
      rw [humod]
      exact hlow
    have hvlt : v % M r h e < VBot r h e := by
      rw [hvmod]
      exact hlow
    have hueq := candidate_mod_eq_h_sub_one_of_lt_VBot hp hu hult humod
    have hveq := candidate_mod_eq_h_sub_one_of_lt_VBot hp hv hvlt hvmod
    omega
  · have hwlo := residue_ge_one hp (candidate_mod_in_residue hp hw)
    have hrho_hi := inV_upper hp hrho
    have htop_lt := VTop_lt_two_h_sub_one_add_one_of_not_low hp hlow
    omega

theorem candidate_residue_noDuplicate_h_sub_one_of_exact_sum
    {r h e rho x y z : Nat} (hp : Params r h e) (hrho : InV r h e rho)
    (hx : Candidate r h e x) (hy : Candidate r h e y)
    (hz : Candidate r h e z) (hxy : x < y) (hyz : y < z)
    (hsum : x % M r h e + y % M r h e + z % M r h e = rho) :
    NoDuplicateValue3
      (x % M r h e) (y % M r h e) (z % M r h e) (h - 1) := by
  constructor
  · intro hxmod hymod
    exact candidate_residue_h_sub_one_pair_impossible_of_exact_sum
      (r := r) (h := h) (e := e) (rho := rho)
      (u := x) (v := y) (w := z) hp hrho hx hy hz hxy hsum hxmod hymod
  · constructor
    · intro hxmod hzmod
      have hxz : x < z := by omega
      have hsum' : x % M r h e + z % M r h e + y % M r h e = rho := by omega
      exact candidate_residue_h_sub_one_pair_impossible_of_exact_sum
        (r := r) (h := h) (e := e) (rho := rho)
        (u := x) (v := z) (w := y) hp hrho hx hz hy hxz hsum' hxmod hzmod
    · intro hymod hzmod
      have hsum' : y % M r h e + z % M r h e + x % M r h e = rho := by omega
      exact candidate_residue_h_sub_one_pair_impossible_of_exact_sum
        (r := r) (h := h) (e := e) (rho := rho)
        (u := y) (v := z) (w := x) hp hrho hy hz hx hyz hsum' hymod hzmod

theorem candidate_residues_feasible_of_exact_sum
    {r h e rho x y z : Nat} (hp : Params r h e) (hrho : InV r h e rho)
    (hx : Candidate r h e x) (hy : Candidate r h e y)
    (hz : Candidate r h e z) (hxy : x < y) (hyz : y < z)
    (hsum : x % M r h e + y % M r h e + z % M r h e = rho) :
    FeasibleUnorderedResidueTriple r h e
      (x % M r h e) (y % M r h e) (z % M r h e) := by
  exact ⟨candidate_mod_in_residue hp hx,
    candidate_mod_in_residue hp hy,
    candidate_mod_in_residue hp hz,
    candidate_residue_noDuplicate_one hp hx hy hz hxy hyz,
    candidate_residue_noDuplicate_h_sub_one_of_exact_sum
      hp hrho hx hy hz hxy hyz hsum⟩

theorem candidate_triple_residue_sum_mod_eq
    {r h e q rho target x y z : Nat} (hp : Params r h e)
    (hrho : InV r h e rho) (htarget : target = q * M r h e + rho)
    (hsum : x + y + z = target) :
    (x % M r h e + y % M r h e + z % M r h e) % M r h e = rho := by
  have hmod_target : target % M r h e = rho :=
    periodic_target_mod_eq (r := r) (h := h) (e := e) (q := q)
      (rho := rho) (target := target) hp hrho htarget
  rw [triple_sum_mod hsum, hmod_target]

/--
Candidate-level unordered classification once the residue sum has been reduced
from modulo equality to exact equality.  This is the bridge that removes the
explicit `x % M < y % M < z % M` residue-order hypothesis from the ordered
periodic-safety classification.
-/
theorem candidate_triple_exact_residue_unordered_classification
    {r h e q rho target x y z : Nat} (hp : Params r h e)
    (hrho : InV r h e rho) (_htarget : target = q * M r h e + rho)
    (hx : Candidate r h e x) (hy : Candidate r h e y) (hz : Candidate r h e z)
    (hxy : x < y) (hyz : y < z) (_hzlt : z < target)
    (_hsum : x + y + z = target)
    (hres_sum : x % M r h e + y % M r h e + z % M r h e = rho) :
    UnorderedResidueClassification h rho
      (x % M r h e) (y % M r h e) (z % M r h e) := by
  have hfeasible := candidate_residues_feasible_of_exact_sum
    (r := r) (h := h) (e := e) (rho := rho) (x := x) (y := y) (z := z)
    hp hrho hx hy hz hxy hyz hres_sum
  exact unordered_exact_residue_classification
    (r := r) (h := h) (e := e) (rho := rho)
    (x := x % M r h e) (y := y % M r h e) (z := z % M r h e)
    hp hfeasible hres_sum hrho

/--
Existential bridge from an arbitrary ordered candidate triple to unordered
residue data.  The first conclusion is the automatic modulo reduction; the
second records the classification available after the remaining exact-residue
step `S = rho`.
-/
theorem candidateTripleSumFrom_unordered_residue_bridge
    {r h e q rho target : Nat} (hp : Params r h e)
    (hrho : InV r h e rho) (htarget : target = q * M r h e + rho)
    (htriple : CandidateTripleSumFrom r h e target) :
    ∃ x y z : Nat,
      Candidate r h e x ∧ Candidate r h e y ∧ Candidate r h e z ∧
        x < y ∧ y < z ∧ z < target ∧ x + y + z = target ∧
        (x % M r h e + y % M r h e + z % M r h e) % M r h e = rho ∧
        (x % M r h e + y % M r h e + z % M r h e = rho →
          UnorderedResidueClassification h rho
            (x % M r h e) (y % M r h e) (z % M r h e)) := by
  rcases htriple with ⟨x, y, z, hx, hy, hz, hxy, hyz, hzlt, hsum⟩
  refine ⟨x, y, z, hx, hy, hz, hxy, hyz, hzlt, hsum, ?_, ?_⟩
  · exact candidate_triple_residue_sum_mod_eq
      (r := r) (h := h) (e := e) (q := q) (rho := rho)
      (target := target) (x := x) (y := y) (z := z)
      hp hrho htarget hsum
  · intro hres_sum
    exact candidate_triple_exact_residue_unordered_classification
      (r := r) (h := h) (e := e) (q := q) (rho := rho)
      (target := target) (x := x) (y := y) (z := z)
      hp hrho htarget hx hy hz hxy hyz hzlt hsum hres_sum

end RBand
end GreedyThreeSumfree
