import GreedyThreeSumfree.BoundaryRBandResidueClassification

namespace GreedyThreeSumfree
namespace BoundaryRBand

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
def FeasibleUnorderedResidueTriple (r h x y z : Nat) : Prop :=
  InResidue r h x ∧ InResidue r h y ∧ InResidue r h z ∧
    NoDuplicateValue3 x y z 1 ∧ NoDuplicateValue3 x y z (h - 1)

/-- Symmetric statement of the forced unordered residue pattern. -/
def UnorderedResidueClassification (h rho x y z : Nat) : Prop :=
  (x = rho - h ∧ y = 1 ∧ z = h - 1) ∨
  (x = rho - h ∧ y = h - 1 ∧ z = 1) ∨
  (y = rho - h ∧ x = 1 ∧ z = h - 1) ∨
  (y = rho - h ∧ x = h - 1 ∧ z = 1) ∨
  (z = rho - h ∧ x = 1 ∧ y = h - 1) ∨
  (z = rho - h ∧ x = h - 1 ∧ y = 1)

theorem h_sub_one_lt_VBot {r h : Nat} (hp : Params r h) :
    h - 1 < VBot r h := by
  have hD := D_ge_h_add_one hp
  have hone : 1 <= h := by
    have hh := hp.h_ge_six
    omega
  have hltD : h < D r h := Nat.lt_of_succ_le (by
    simpa [Nat.succ_eq_add_one] using hD)
  unfold VBot
  exact Nat.sub_lt_sub_right hone hltD

theorem residue_lt_VBot_eq_one_or_h_sub_one {r h x : Nat}
    (hp : Params r h) (hx : InResidue r h x)
    (hxlt : x < VBot r h) :
    x = 1 ∨ x = h - 1 := by
  rcases hx with hxP | hxV
  · unfold InPrefix at hxP
    rcases hxP with rfl | rfl | rfl | hxU
    · exact Or.inl rfl
    · exact Or.inr rfl
    · have hDc := D_lt_c hp
      unfold VBot at hxlt
      omega
    · rcases hxU with ⟨i, _hi, hxH⟩
      unfold InH InInterval HLo at hxH
      unfold VBot at hxlt
      omega
  · have hxlo := inV_lower hp hxV
    omega

/-- A candidate with residue below `VBot` must come from the prefix. -/
theorem candidate_mod_lt_VBot_prefix {r h n : Nat}
    (hp : Params r h) (hn : Candidate r h n)
    (hnlt : n % M r h < VBot r h) :
    InPrefix r h n := by
  rcases hn with hnP | hnBlock
  · exact hnP
  · rcases hnBlock with ⟨q, _hq, hnq⟩
    rcases in_periodic_block_mod_eq (r := r) (h := h) (q := q) hp hnq with
      ⟨rho, hrho, hnmod⟩
    have hrlo := inV_lower hp hrho
    rw [hnmod] at hnlt
    omega

theorem candidate_mod_lt_VBot_eq_one_or_h_sub_one {r h n : Nat}
    (hp : Params r h) (hn : Candidate r h n)
    (hnlt : n % M r h < VBot r h) :
    n % M r h = 1 ∨ n % M r h = h - 1 := by
  exact residue_lt_VBot_eq_one_or_h_sub_one hp
    (candidate_mod_in_residue hp hn) hnlt

theorem candidate_mod_eq_one {r h n : Nat}
    (hp : Params r h) (hn : Candidate r h n)
    (hnmod : n % M r h = 1) :
    n = 1 := by
  have hnlt : n % M r h < VBot r h := by
    have hD := D_ge_three hp
    rw [hnmod]
    unfold VBot
    omega
  have hnP := candidate_mod_lt_VBot_prefix hp hn hnlt
  have hprefix_mod := prefix_mod_eq hp hnP
  omega

theorem candidate_mod_eq_h_sub_one {r h n : Nat}
    (hp : Params r h) (hn : Candidate r h n)
    (hnmod : n % M r h = h - 1) :
    n = h - 1 := by
  have hnlt : n % M r h < VBot r h := by
    rw [hnmod]
    exact h_sub_one_lt_VBot hp
  have hnP := candidate_mod_lt_VBot_prefix hp hn hnlt
  have hprefix_mod := prefix_mod_eq hp hnP
  omega

theorem residue_le_h_sub_one_eq_one_or_h_sub_one {r h x : Nat}
    (hp : Params r h) (hx : InResidue r h x)
    (hxle : x <= h - 1) :
    x = 1 ∨ x = h - 1 := by
  by_cases hxone : x = 1
  · exact Or.inl hxone
  · have hxge := residue_ne_one_ge_h_sub_one hp hx hxone
    exact Or.inr (by omega)

private theorem two_large_residue_sum_exceeds_VTop
    {r h x y z : Nat} (hp : Params r h)
    (hx : InResidue r h x) (hy : InResidue r h y)
    (hz : InResidue r h z)
    (hxgt : h - 1 < x) (hygt : h - 1 < y) :
    VTop r h < x + y + z := by
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

/--
Exact unordered residue classification. No residue ordering is assumed; the
only distinctness information needed is that the two prefix singletons do not
occur twice.
-/
theorem unordered_exact_residue_classification
    {r h rho x y z : Nat} (hp : Params r h)
    (hxyz : FeasibleUnorderedResidueTriple r h x y z)
    (hsum : x + y + z = rho) (hrho : InV r h rho) :
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
        (r := r) (h := h) (x := x) (y := z) (z := y)
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

theorem rho_sub_h_inK_zero_lt_VBot {r h rho : Nat} (hp : Params r h)
    (hrhoK : InK r h 0 rho) :
    rho - h < VBot r h := by
  have hD := D_ge_three hp
  have hh := hp.h_ge_six
  unfold InK InInterval KLo KHi HHi HLo at hrhoK
  unfold VBot
  omega

theorem unordered_classification_inK_zero_impossible
    {r h rho x y z : Nat} (hp : Params r h)
    (hxyz : FeasibleUnorderedResidueTriple r h x y z)
    (hclass : UnorderedResidueClassification h rho x y z)
    (hrhoK : InK r h 0 rho) :
    False := by
  rcases hxyz with ⟨hx, hy, hz, hnd1, hndh⟩
  have hlow := rho_sub_h_inK_zero_lt_VBot hp hrhoK
  rcases hclass with hxyz | hxyz | hxyz | hxyz | hxyz | hxyz
  · rcases hxyz with ⟨hxrho, hyone, hzh⟩
    have hxlt : x < VBot r h := by omega
    rcases residue_lt_VBot_eq_one_or_h_sub_one hp hx hxlt with hxone | hxh
    · exact hnd1.1 hxone hyone
    · exact hndh.2.1 hxh hzh
  · rcases hxyz with ⟨hxrho, hyh, hzone⟩
    have hxlt : x < VBot r h := by omega
    rcases residue_lt_VBot_eq_one_or_h_sub_one hp hx hxlt with hxone | hxh
    · exact hnd1.2.1 hxone hzone
    · exact hndh.1 hxh hyh
  · rcases hxyz with ⟨hyrho, hxone, hzh⟩
    have hylt : y < VBot r h := by omega
    rcases residue_lt_VBot_eq_one_or_h_sub_one hp hy hylt with hyone | hyh
    · exact hnd1.1 hxone hyone
    · exact hndh.2.2 hyh hzh
  · rcases hxyz with ⟨hyrho, hxh, hzone⟩
    have hylt : y < VBot r h := by omega
    rcases residue_lt_VBot_eq_one_or_h_sub_one hp hy hylt with hyone | hyh
    · exact hnd1.2.2 hyone hzone
    · exact hndh.1 hxh hyh
  · rcases hxyz with ⟨hzrho, hxone, hyh⟩
    have hzlt : z < VBot r h := by omega
    rcases residue_lt_VBot_eq_one_or_h_sub_one hp hz hzlt with hzone | hzh
    · exact hnd1.2.1 hxone hzone
    · exact hndh.2.2 hyh hzh
  · rcases hxyz with ⟨hzrho, hxh, hyone⟩
    have hzlt : z < VBot r h := by omega
    rcases residue_lt_VBot_eq_one_or_h_sub_one hp hz hzlt with hzone | hzh
    · exact hnd1.2.2 hyone hzone
    · exact hndh.2.1 hxh hzh

theorem unordered_exact_residue_inK_zero_impossible
    {r h rho x y z : Nat} (hp : Params r h)
    (hxyz : FeasibleUnorderedResidueTriple r h x y z)
    (hsum : x + y + z = rho) (hrhoK : InK r h 0 rho) :
    False := by
  have hi : 0 < r := by
    have hr := hp.r_pos
    omega
  have hrho : InV r h rho := ⟨0, hi, hrhoK⟩
  have hclass := unordered_exact_residue_classification
    (r := r) (h := h) (rho := rho) (x := x) (y := y) (z := z)
    hp hxyz hsum hrho
  exact unordered_classification_inK_zero_impossible
    (r := r) (h := h) (rho := rho) (x := x) (y := y) (z := z)
    hp hxyz hclass hrhoK

theorem residue_eq_rho_sub_h_inK_prev_HHi
    {r h i rho x : Nat} (hp : Params r h) (hi_pos : 1 <= i)
    (hi : i < r) (hx : InResidue r h x)
    (hxrho : x = rho - h) (hrhoK : InK r h i rho) :
    x = HHi r h (i - 1) := by
  have hbounds : HLo r h i - h - 1 <= x ∧ x <= HLo r h i - 2 := by
    have hH := HLo_ge_three (r := r) (h := h) (i := i) hp
    have hh := hp.h_ge_six
    unfold InK InInterval KLo KHi HHi at hrhoK
    rw [hxrho]
    omega
  have hupper := residue_below_next_K_gap_le_prev_HHi
    (r := r) (h := h) (i := i) hp hi_pos hi hx hbounds.2
  have hprev := HHi_prev_eq_HLo_sub_h_sub_one
    (r := r) (h := h) (i := i) hp hi_pos
  omega

theorem residue_eq_rho_sub_h_inK_prefix
    {r h i rho x : Nat} (hp : Params r h) (hi_pos : 1 <= i)
    (hi : i < r) (hx : InResidue r h x)
    (hxrho : x = rho - h) (hrhoK : InK r h i rho) :
    InPrefix r h x := by
  have hxeq := residue_eq_rho_sub_h_inK_prev_HHi
    (r := r) (h := h) (i := i) (rho := rho) (x := x)
    hp hi_pos hi hx hxrho hrhoK
  subst x
  right
  right
  right
  refine ⟨i - 1, ?_, ?_⟩
  · omega
  · rw [hxeq]
    exact ⟨HLo_le_HHi hp, Nat.le_refl _⟩

theorem unordered_classification_inK_last_prefix
    {r h i rho x y z : Nat} (hp : Params r h) (hi_pos : 1 <= i)
    (hi : i < r) (hx : InResidue r h x) (hy : InResidue r h y)
    (hz : InResidue r h z)
    (hclass : UnorderedResidueClassification h rho x y z)
    (hrhoK : InK r h i rho) :
    (x = rho - h ∧ InPrefix r h x) ∨
      (y = rho - h ∧ InPrefix r h y) ∨
      (z = rho - h ∧ InPrefix r h z) := by
  rcases hclass with hxyz | hxyz | hxyz | hxyz | hxyz | hxyz
  · rcases hxyz with ⟨hxrho, _hyone, _hzh⟩
    left
    exact ⟨hxrho,
      residue_eq_rho_sub_h_inK_prefix hp hi_pos hi hx hxrho hrhoK⟩
  · rcases hxyz with ⟨hxrho, _hyh, _hzone⟩
    left
    exact ⟨hxrho,
      residue_eq_rho_sub_h_inK_prefix hp hi_pos hi hx hxrho hrhoK⟩
  · rcases hxyz with ⟨hyrho, _hxone, _hzh⟩
    right
    left
    exact ⟨hyrho,
      residue_eq_rho_sub_h_inK_prefix hp hi_pos hi hy hyrho hrhoK⟩
  · rcases hxyz with ⟨hyrho, _hxh, _hzone⟩
    right
    left
    exact ⟨hyrho,
      residue_eq_rho_sub_h_inK_prefix hp hi_pos hi hy hyrho hrhoK⟩
  · rcases hxyz with ⟨hzrho, _hxone, _hyh⟩
    right
    right
    exact ⟨hzrho,
      residue_eq_rho_sub_h_inK_prefix hp hi_pos hi hz hzrho hrhoK⟩
  · rcases hxyz with ⟨hzrho, _hxh, _hyone⟩
    right
    right
    exact ⟨hzrho,
      residue_eq_rho_sub_h_inK_prefix hp hi_pos hi hz hzrho hrhoK⟩

theorem unordered_exact_residue_inK_last_prefix
    {r h i rho x y z : Nat} (hp : Params r h) (hi_pos : 1 <= i)
    (hi : i < r) (hxyz : FeasibleUnorderedResidueTriple r h x y z)
    (hsum : x + y + z = rho) (hrhoK : InK r h i rho) :
    (x = rho - h ∧ InPrefix r h x) ∨
      (y = rho - h ∧ InPrefix r h y) ∨
      (z = rho - h ∧ InPrefix r h z) := by
  have hrho : InV r h rho := ⟨i, hi, hrhoK⟩
  have hclass := unordered_exact_residue_classification
    (r := r) (h := h) (rho := rho) (x := x) (y := y) (z := z)
    hp hxyz hsum hrho
  exact unordered_classification_inK_last_prefix
    (r := r) (h := h) (i := i) (rho := rho) (x := x) (y := y) (z := z)
    hp hi_pos hi hxyz.1 hxyz.2.1 hxyz.2.2.1 hclass hrhoK

theorem candidate_residue_noDuplicate_one {r h x y z : Nat}
    (hp : Params r h)
    (hx : Candidate r h x) (hy : Candidate r h y)
    (hz : Candidate r h z) (hxy : x < y) (hyz : y < z) :
    NoDuplicateValue3 (x % M r h) (y % M r h) (z % M r h) 1 := by
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

theorem candidate_residue_noDuplicate_h_sub_one {r h x y z : Nat}
    (hp : Params r h)
    (hx : Candidate r h x) (hy : Candidate r h y)
    (hz : Candidate r h z) (hxy : x < y) (hyz : y < z) :
    NoDuplicateValue3
      (x % M r h) (y % M r h) (z % M r h) (h - 1) := by
  constructor
  · intro hxmod hymod
    have hxeq := candidate_mod_eq_h_sub_one hp hx hxmod
    have hyeq := candidate_mod_eq_h_sub_one hp hy hymod
    omega
  · constructor
    · intro hxmod hzmod
      have hxeq := candidate_mod_eq_h_sub_one hp hx hxmod
      have hzeq := candidate_mod_eq_h_sub_one hp hz hzmod
      omega
    · intro hymod hzmod
      have hyeq := candidate_mod_eq_h_sub_one hp hy hymod
      have hzeq := candidate_mod_eq_h_sub_one hp hz hzmod
      omega

theorem candidate_residues_feasible_of_exact_sum
    {r h rho x y z : Nat} (hp : Params r h) (_hrho : InV r h rho)
    (hx : Candidate r h x) (hy : Candidate r h y)
    (hz : Candidate r h z) (hxy : x < y) (hyz : y < z)
    (_hsum : x % M r h + y % M r h + z % M r h = rho) :
    FeasibleUnorderedResidueTriple r h
      (x % M r h) (y % M r h) (z % M r h) := by
  exact ⟨candidate_mod_in_residue hp hx,
    candidate_mod_in_residue hp hy,
    candidate_mod_in_residue hp hz,
    candidate_residue_noDuplicate_one hp hx hy hz hxy hyz,
    candidate_residue_noDuplicate_h_sub_one hp hx hy hz hxy hyz⟩

theorem periodic_target_mod_eq {r h q rho target : Nat}
    (hp : Params r h) (hrho : InV r h rho)
    (htarget : target = q * M r h + rho) :
    target % M r h = rho :=
  periodic_block_mod_eq hp hrho htarget

theorem candidate_triple_residue_sum_mod_eq
    {r h q rho target x y z : Nat} (hp : Params r h)
    (hrho : InV r h rho) (htarget : target = q * M r h + rho)
    (hsum : x + y + z = target) :
    (x % M r h + y % M r h + z % M r h) % M r h = rho := by
  have hmod_target : target % M r h = rho :=
    periodic_target_mod_eq (r := r) (h := h) (q := q)
      (rho := rho) (target := target) hp hrho htarget
  rw [triple_sum_mod hsum, hmod_target]

/--
Candidate-level unordered classification once the residue sum has been reduced
from modulo equality to exact equality. This bridge removes any residue-order
hypothesis from the ordered boundary classification.
-/
theorem candidate_triple_exact_residue_unordered_classification
    {r h q rho target x y z : Nat} (hp : Params r h)
    (hrho : InV r h rho) (_htarget : target = q * M r h + rho)
    (hx : Candidate r h x) (hy : Candidate r h y) (hz : Candidate r h z)
    (hxy : x < y) (hyz : y < z) (_hzlt : z < target)
    (_hsum : x + y + z = target)
    (hres_sum : x % M r h + y % M r h + z % M r h = rho) :
    UnorderedResidueClassification h rho
      (x % M r h) (y % M r h) (z % M r h) := by
  have hfeasible := candidate_residues_feasible_of_exact_sum
    (r := r) (h := h) (rho := rho) (x := x) (y := y) (z := z)
    hp hrho hx hy hz hxy hyz hres_sum
  exact unordered_exact_residue_classification
    (r := r) (h := h) (rho := rho)
    (x := x % M r h) (y := y % M r h) (z := z % M r h)
    hp hfeasible hres_sum hrho

/--
Existential bridge from an arbitrary ordered candidate triple to unordered
residue data. The first conclusion is automatic modulo reduction; the second
records the classification available after the remaining exact-residue step
`S = rho`.
-/
theorem candidateTripleSumFrom_unordered_residue_bridge
    {r h q rho target : Nat} (hp : Params r h)
    (hrho : InV r h rho) (htarget : target = q * M r h + rho)
    (htriple : CandidateTripleSumFrom r h target) :
    ∃ x y z : Nat,
      Candidate r h x ∧ Candidate r h y ∧ Candidate r h z ∧
        x < y ∧ y < z ∧ z < target ∧ x + y + z = target ∧
        (x % M r h + y % M r h + z % M r h) % M r h = rho ∧
        (x % M r h + y % M r h + z % M r h = rho →
          UnorderedResidueClassification h rho
            (x % M r h) (y % M r h) (z % M r h)) := by
  rcases htriple with ⟨x, y, z, hx, hy, hz, hxy, hyz, hzlt, hsum⟩
  refine ⟨x, y, z, hx, hy, hz, hxy, hyz, hzlt, hsum, ?_, ?_⟩
  · exact candidate_triple_residue_sum_mod_eq
      (r := r) (h := h) (q := q) (rho := rho)
      (target := target) (x := x) (y := y) (z := z)
      hp hrho htarget hsum
  · intro hres_sum
    exact candidate_triple_exact_residue_unordered_classification
      (r := r) (h := h) (q := q) (rho := rho)
      (target := target) (x := x) (y := y) (z := z)
      hp hrho htarget hx hy hz hxy hyz hzlt hsum hres_sum

end BoundaryRBand
end GreedyThreeSumfree
