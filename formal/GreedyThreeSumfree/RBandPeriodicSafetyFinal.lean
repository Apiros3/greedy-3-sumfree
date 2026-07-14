import GreedyThreeSumfree.RBandUnorderedResidues

namespace GreedyThreeSumfree
namespace RBand

private theorem two_residue_sum_ge_h_of_not_both_one
    {r h e y z : Nat} (hp : Params r h e)
    (hy : InResidue r h e y) (hz : InResidue r h e z)
    (hnot : y = 1 → z ≠ 1) :
    h <= y + z := by
  by_cases hyone : y = 1
  · have hzne : z ≠ 1 := hnot hyone
    have hzlo := residue_ne_one_ge_h_sub_one hp hz hzne
    omega
  · have hylo := residue_ne_one_ge_h_sub_one hp hy hyone
    have hzlo := residue_ge_one hp hz
    omega

private theorem three_residue_sum_ge_two_h_sub_one_of_noDuplicate_one
    {r h e x y z : Nat} (hp : Params r h e)
    (hx : InResidue r h e x) (hy : InResidue r h e y)
    (hz : InResidue r h e z)
    (hnd1 : NoDuplicateValue3 x y z 1) :
    2 * h - 1 <= x + y + z := by
  by_cases hxone : x = 1
  · have hyne : y ≠ 1 := hnd1.1 hxone
    have hzne : z ≠ 1 := hnd1.2.1 hxone
    have hylo := residue_ne_one_ge_h_sub_one hp hy hyne
    have hzlo := residue_ne_one_ge_h_sub_one hp hz hzne
    omega
  · have hxlo := residue_ne_one_ge_h_sub_one hp hx hxone
    by_cases hyone : y = 1
    · have hzne : z ≠ 1 := hnd1.2.2 hyone
      have hzlo := residue_ne_one_ge_h_sub_one hp hz hzne
      omega
    · have hylo := residue_ne_one_ge_h_sub_one hp hy hyone
      have hzlo := residue_ge_one hp hz
      omega

theorem candidate_residue_noDuplicate_h_sub_one_of_lt_VBot
    {r h e x y z : Nat} (hp : Params r h e)
    (hlow : h - 1 < VBot r h e)
    (hx : Candidate r h e x) (hy : Candidate r h e y)
    (hz : Candidate r h e z) (hxy : x < y) (hyz : y < z) :
    NoDuplicateValue3
      (x % M r h e) (y % M r h e) (z % M r h e) (h - 1) := by
  constructor
  · intro hxmod hymod
    have hxlt : x % M r h e < VBot r h e := by
      rw [hxmod]
      exact hlow
    have hylt : y % M r h e < VBot r h e := by
      rw [hymod]
      exact hlow
    have hxeq := candidate_mod_eq_h_sub_one_of_lt_VBot hp hx hxlt hxmod
    have hyeq := candidate_mod_eq_h_sub_one_of_lt_VBot hp hy hylt hymod
    omega
  · constructor
    · intro hxmod hzmod
      have hxlt : x % M r h e < VBot r h e := by
        rw [hxmod]
        exact hlow
      have hzlt : z % M r h e < VBot r h e := by
        rw [hzmod]
        exact hlow
      have hxeq := candidate_mod_eq_h_sub_one_of_lt_VBot hp hx hxlt hxmod
      have hzeq := candidate_mod_eq_h_sub_one_of_lt_VBot hp hz hzlt hzmod
      omega
    · intro hymod hzmod
      have hylt : y % M r h e < VBot r h e := by
        rw [hymod]
        exact hlow
      have hzlt : z % M r h e < VBot r h e := by
        rw [hzmod]
        exact hlow
      have hyeq := candidate_mod_eq_h_sub_one_of_lt_VBot hp hy hylt hymod
      have hzeq := candidate_mod_eq_h_sub_one_of_lt_VBot hp hz hzlt hzmod
      omega

private theorem one_residue_ge_VBot_of_low_duplicates_forbidden
    {r h e x y z : Nat} (hp : Params r h e)
    (hx : InResidue r h e x) (hy : InResidue r h e y)
    (hz : InResidue r h e z)
    (hnd1 : NoDuplicateValue3 x y z 1)
    (hndh : NoDuplicateValue3 x y z (h - 1)) :
    VBot r h e <= x ∨ VBot r h e <= y ∨ VBot r h e <= z := by
  by_cases hxlarge : VBot r h e <= x
  · exact Or.inl hxlarge
  by_cases hylarge : VBot r h e <= y
  · exact Or.inr (Or.inl hylarge)
  by_cases hzlarge : VBot r h e <= z
  · exact Or.inr (Or.inr hzlarge)
  have hxlt : x < VBot r h e := by omega
  have hylt : y < VBot r h e := by omega
  have hzlt : z < VBot r h e := by omega
  have hxsmall := residue_lt_VBot_eq_one_or_h_sub_one hp hx hxlt
  have hysmall := residue_lt_VBot_eq_one_or_h_sub_one hp hy hylt
  have hzsmall := residue_lt_VBot_eq_one_or_h_sub_one hp hz hzlt
  rcases hxsmall with hxone | hxh
  · rcases hysmall with hyone | hyh
    · exact False.elim (hnd1.1 hxone hyone)
    · rcases hzsmall with hzone | hzh
      · exact False.elim (hnd1.2.1 hxone hzone)
      · exact False.elim (hndh.2.2 hyh hzh)
  · rcases hysmall with hyone | hyh
    · rcases hzsmall with hzone | hzh
      · exact False.elim (hnd1.2.2 hyone hzone)
      · exact False.elim (hndh.2.1 hxh hzh)
    · exact False.elim (hndh.1 hxh hyh)

theorem candidate_residue_sum_lower
    {r h e x y z : Nat} (hp : Params r h e)
    (hx : Candidate r h e x) (hy : Candidate r h e y)
    (hz : Candidate r h e z) (hxy : x < y) (hyz : y < z) :
    D r h e + h - 2 <=
      x % M r h e + y % M r h e + z % M r h e := by
  let rx := x % M r h e
  let ry := y % M r h e
  let rz := z % M r h e
  have hrx : InResidue r h e rx := candidate_mod_in_residue hp hx
  have hry : InResidue r h e ry := candidate_mod_in_residue hp hy
  have hrz : InResidue r h e rz := candidate_mod_in_residue hp hz
  have hnd1 : NoDuplicateValue3 rx ry rz 1 :=
    candidate_residue_noDuplicate_one hp hx hy hz hxy hyz
  by_cases hlow : h - 1 < VBot r h e
  · have hndh : NoDuplicateValue3 rx ry rz (h - 1) :=
      candidate_residue_noDuplicate_h_sub_one_of_lt_VBot
        (r := r) (h := h) (e := e) (x := x) (y := y) (z := z)
        hp hlow hx hy hz hxy hyz
    have hlarge := one_residue_ge_VBot_of_low_duplicates_forbidden
      (r := r) (h := h) (e := e) (x := rx) (y := ry) (z := rz)
      hp hrx hry hrz hnd1 hndh
    rcases hlarge with hxlarge | hylarge | hzlarge
    · have hyzlo := two_residue_sum_ge_h_of_not_both_one hp hry hrz hnd1.2.2
      unfold rx ry rz VBot at *
      omega
    · have hxzlo := two_residue_sum_ge_h_of_not_both_one hp hrx hrz hnd1.2.1
      unfold rx ry rz VBot at *
      omega
    · have hxylo := two_residue_sum_ge_h_of_not_both_one hp hrx hry hnd1.1
      unfold rx ry rz VBot at *
      omega
  · have hbase := three_residue_sum_ge_two_h_sub_one_of_noDuplicate_one
      (r := r) (h := h) (e := e) (x := rx) (y := ry) (z := rz)
      hp hrx hry hrz hnd1
    have hbot_le : VBot r h e <= h - 1 := by omega
    unfold rx ry rz VBot at *
    omega

private theorem candidate_mod_gt_VTop_eq
    {r h e n v : Nat} (hp : Params r h e)
    (hn : Candidate r h e n) (hmod : n % M r h e = v)
    (hvgt : VTop r h e < v) :
    n = v := by
  rcases hn with hnP | hnBlock
  · have hprefix_mod := prefix_mod_eq hp hnP
    omega
  · rcases hnBlock with ⟨q, _hq, hnq⟩
    rcases in_periodic_block_mod_eq
        (r := r) (h := h) (e := e) (q := q) hp hnq with
      ⟨rho, hrho, hnmod⟩
    have hrho_hi := inV_upper hp hrho
    omega

theorem candidate_residue_noDuplicate_of_gt_VTop
    {r h e x y z v : Nat} (hp : Params r h e)
    (hvgt : VTop r h e < v)
    (hx : Candidate r h e x) (hy : Candidate r h e y)
    (hz : Candidate r h e z) (hxy : x < y) (hyz : y < z) :
    NoDuplicateValue3
      (x % M r h e) (y % M r h e) (z % M r h e) v := by
  constructor
  · intro hxmod hymod
    have hxeq := candidate_mod_gt_VTop_eq hp hx hxmod hvgt
    have hyeq := candidate_mod_gt_VTop_eq hp hy hymod hvgt
    omega
  · constructor
    · intro hxmod hzmod
      have hxeq := candidate_mod_gt_VTop_eq hp hx hxmod hvgt
      have hzeq := candidate_mod_gt_VTop_eq hp hz hzmod hvgt
      omega
    · intro hymod hzmod
      have hyeq := candidate_mod_gt_VTop_eq hp hy hymod hvgt
      have hzeq := candidate_mod_gt_VTop_eq hp hz hzmod hvgt
      omega

private theorem sum_le_three_add_three_of_le_add_two_noDuplicate_top
    {T x y z : Nat}
    (hxle : x <= T + 2) (hyle : y <= T + 2) (hzle : z <= T + 2)
    (hnd1 : NoDuplicateValue3 x y z (T + 1))
    (hnd2 : NoDuplicateValue3 x y z (T + 2)) :
    x + y + z <= 3 * T + 3 := by
  have hxcase : x <= T ∨ x = T + 1 ∨ x = T + 2 := by omega
  have hycase : y <= T ∨ y = T + 1 ∨ y = T + 2 := by omega
  have hzcase : z <= T ∨ z = T + 1 ∨ z = T + 2 := by omega
  rcases hxcase with hxT | hxT1 | hxT2
  · rcases hycase with hyT | hyT1 | hyT2
    · rcases hzcase with hzT | hzT1 | hzT2 <;> omega
    · rcases hzcase with hzT | hzT1 | hzT2
      · omega
      · exact False.elim (hnd1.2.2 hyT1 hzT1)
      · omega
    · rcases hzcase with hzT | hzT1 | hzT2
      · omega
      · omega
      · exact False.elim (hnd2.2.2 hyT2 hzT2)
  · rcases hycase with hyT | hyT1 | hyT2
    · rcases hzcase with hzT | hzT1 | hzT2
      · omega
      · exact False.elim (hnd1.2.1 hxT1 hzT1)
      · omega
    · exact False.elim (hnd1.1 hxT1 hyT1)
    · rcases hzcase with hzT | hzT1 | hzT2
      · omega
      · exact False.elim (hnd1.2.1 hxT1 hzT1)
      · exact False.elim (hnd2.2.2 hyT2 hzT2)
  · rcases hycase with hyT | hyT1 | hyT2
    · rcases hzcase with hzT | hzT1 | hzT2
      · omega
      · omega
      · exact False.elim (hnd2.2.1 hxT2 hzT2)
    · rcases hzcase with hzT | hzT1 | hzT2
      · omega
      · exact False.elim (hnd1.2.2 hyT1 hzT1)
      · exact False.elim (hnd2.2.1 hxT2 hzT2)
    · exact False.elim (hnd2.1 hxT2 hyT2)

private theorem three_VTop_add_three_eq_sum_upper_final {r h e : Nat}
    (hp : Params r h e) :
    3 * VTop r h e + 3 = 3 * D r h e + (6 * r - 3) * h - 6 := by
  have hr := hp.r_pos
  have hD := D_ge_three hp
  have hcoef : 3 * (2 * r - 1) = 6 * r - 3 := by omega
  have hprod : 3 * ((2 * r - 1) * h) = (6 * r - 3) * h := by
    rw [← Nat.mul_assoc, hcoef]
  unfold VTop
  omega

theorem candidate_residue_sum_upper
    {r h e x y z : Nat} (hp : Params r h e)
    (hx : Candidate r h e x) (hy : Candidate r h e y)
    (hz : Candidate r h e z) (hxy : x < y) (hyz : y < z) :
    x % M r h e + y % M r h e + z % M r h e <=
      3 * D r h e + (6 * r - 3) * h - 6 := by
  let rx := x % M r h e
  let ry := y % M r h e
  let rz := z % M r h e
  have hrx : InResidue r h e rx := candidate_mod_in_residue hp hx
  have hry : InResidue r h e ry := candidate_mod_in_residue hp hy
  have hrz : InResidue r h e rz := candidate_mod_in_residue hp hz
  have hxle : rx <= VTop r h e + 2 := residue_le_VTop_add_two hp hrx
  have hyle : ry <= VTop r h e + 2 := residue_le_VTop_add_two hp hry
  have hzle : rz <= VTop r h e + 2 := residue_le_VTop_add_two hp hrz
  have hnd_top1 : NoDuplicateValue3 rx ry rz (VTop r h e + 1) :=
    candidate_residue_noDuplicate_of_gt_VTop
      (r := r) (h := h) (e := e) (x := x) (y := y) (z := z)
      hp (by omega) hx hy hz hxy hyz
  have hnd_top2 : NoDuplicateValue3 rx ry rz (VTop r h e + 2) :=
    candidate_residue_noDuplicate_of_gt_VTop
      (r := r) (h := h) (e := e) (x := x) (y := y) (z := z)
      hp (by omega) hx hy hz hxy hyz
  have hsum_le : rx + ry + rz <= 3 * VTop r h e + 3 :=
    sum_le_three_add_three_of_le_add_two_noDuplicate_top
      hxle hyle hzle hnd_top1 hnd_top2
  rw [three_VTop_add_three_eq_sum_upper_final hp] at hsum_le
  exact hsum_le

theorem candidate_residue_mod_eq_forces_eq
    {r h e rho x y z : Nat} (hp : Params r h e)
    (hrho : InV r h e rho)
    (hx : Candidate r h e x) (hy : Candidate r h e y)
    (hz : Candidate r h e z) (hxy : x < y) (hyz : y < z)
    (hmod :
      (x % M r h e + y % M r h e + z % M r h e) % M r h e = rho) :
    x % M r h e + y % M r h e + z % M r h e = rho := by
  let S := x % M r h e + y % M r h e + z % M r h e
  by_cases hEq : S = rho
  · exact hEq
  · by_cases hrho_lt_S : rho < S
    · have hlo : D r h e + h - 2 <= S := by
        dsimp [S]
        exact candidate_residue_sum_lower hp hx hy hz hxy hyz
      have hhi : S <= 3 * D r h e + (6 * r - 3) * h - 6 := by
        dsimp [S]
        exact candidate_residue_sum_upper hp hx hy hz hxy hyz
      exact False.elim
        (residue_mod_contradiction hp hrho hlo hhi hmod hrho_lt_S)
    · have hS_lt_rho : S < rho := by omega
      exact False.elim (residue_mod_contradiction_below hmod hS_lt_rho)

theorem candidateTripleSumFrom_residue_sum_eq
    {r h e q rho target : Nat} (hp : Params r h e)
    (hrho : InV r h e rho) (htarget : target = q * M r h e + rho)
    (htriple : CandidateTripleSumFrom r h e target) :
    ∃ x y z : Nat,
      Candidate r h e x ∧ Candidate r h e y ∧ Candidate r h e z ∧
        x < y ∧ y < z ∧ z < target ∧ x + y + z = target ∧
        x % M r h e + y % M r h e + z % M r h e = rho ∧
        UnorderedResidueClassification h rho
          (x % M r h e) (y % M r h e) (z % M r h e) := by
  rcases candidateTripleSumFrom_unordered_residue_bridge
      (r := r) (h := h) (e := e) (q := q) (rho := rho)
      (target := target) hp hrho htarget htriple with
    ⟨x, y, z, hx, hy, hz, hxy, hyz, hzlt, hsum, hmod, hclass_of_eq⟩
  have hres_sum := candidate_residue_mod_eq_forces_eq
    (r := r) (h := h) (e := e) (rho := rho) (x := x) (y := y) (z := z)
    hp hrho hx hy hz hxy hyz hmod
  exact ⟨x, y, z, hx, hy, hz, hxy, hyz, hzlt, hsum, hres_sum,
    hclass_of_eq hres_sum⟩

theorem unordered_classification_inI_zero_impossible
    {r h e rho x y z : Nat} (hp : Params r h e)
    (hfeasible : FeasibleUnorderedResidueTriple r h e x y z)
    (hclass : UnorderedResidueClassification h rho x y z)
    (hrhoI : InI r h e 0 rho) :
    False := by
  rcases hfeasible with ⟨hx, hy, hz, hnd1, hndh⟩
  have hrho_sub_lt : rho - h < VBot r h e := by
    have hD := D_ge_three hp
    unfold InI InInterval ILo IHi HLo at hrhoI
    unfold VBot
    omega
  rcases hclass with hxyz | hxyz | hxyz | hxyz | hxyz | hxyz
  · rcases hxyz with ⟨hxrho, hyone, hzh⟩
    have hxsmall := residue_lt_VBot_eq_one_or_h_sub_one hp hx (by omega)
    rcases hxsmall with hxone | hxh
    · exact hnd1.1 hxone hyone
    · exact hndh.2.1 hxh hzh
  · rcases hxyz with ⟨hxrho, hyh, hzone⟩
    have hxsmall := residue_lt_VBot_eq_one_or_h_sub_one hp hx (by omega)
    rcases hxsmall with hxone | hxh
    · exact hnd1.2.1 hxone hzone
    · exact hndh.1 hxh hyh
  · rcases hxyz with ⟨hyrho, hxone, hzh⟩
    have hysmall := residue_lt_VBot_eq_one_or_h_sub_one hp hy (by omega)
    rcases hysmall with hyone | hyh
    · exact hnd1.1 hxone hyone
    · exact hndh.2.2 hyh hzh
  · rcases hxyz with ⟨hyrho, hxh, hzone⟩
    have hysmall := residue_lt_VBot_eq_one_or_h_sub_one hp hy (by omega)
    rcases hysmall with hyone | hyh
    · exact hnd1.2.2 hyone hzone
    · exact hndh.1 hxh hyh
  · rcases hxyz with ⟨hzrho, hxone, hyh⟩
    have hzsmall := residue_lt_VBot_eq_one_or_h_sub_one hp hz (by omega)
    rcases hzsmall with hzone | hzh
    · exact hnd1.2.1 hxone hzone
    · exact hndh.2.2 hyh hzh
  · rcases hxyz with ⟨hzrho, hxh, hyone⟩
    have hzsmall := residue_lt_VBot_eq_one_or_h_sub_one hp hz (by omega)
    rcases hzsmall with hzone | hzh
    · exact hnd1.2.2 hyone hzone
    · exact hndh.2.1 hxh hzh

private theorem h_sub_one_lt_VBot_of_later_index
    {r h e i : Nat} (hp : Params r h e)
    (hi_pos : 1 <= i) (hi : i < r) :
    h - 1 < VBot r h e := by
  have hr2 : 2 <= r := by omega
  have hcoef : 3 <= 2 * r - 1 := by omega
  have hmul : 3 * h <= (2 * r - 1) * h :=
    Nat.mul_le_mul_right h hcoef
  have he := hp.e_pos
  have hh := hp.h_ge_six
  unfold VBot D
  omega

theorem candidate_mod_eq_h_sub_one_of_later_index
    {r h e i n : Nat} (hp : Params r h e)
    (hi_pos : 1 <= i) (hi : i < r)
    (hn : Candidate r h e n) (hnmod : n % M r h e = h - 1) :
    n = h - 1 := by
  have hlow := h_sub_one_lt_VBot_of_later_index hp hi_pos hi
  have hnlt : n % M r h e < VBot r h e := by
    rw [hnmod]
    exact hlow
  exact candidate_mod_eq_h_sub_one_of_lt_VBot hp hn hnlt hnmod

private theorem rho_sub_h_ge_prev_HHi_sub_one
    {r h e i rho : Nat} (hp : Params r h e)
    (hi_pos : 1 <= i) (hrhoI : InI r h e i rho) :
    HHi r h e (i - 1) - 1 <= rho - h := by
  have hlo : HLo r h e i - 2 <= rho := by
    simpa [InI, InInterval, ILo] using hrhoI.1
  have hge0 : HLo r h e i - 2 - h <= rho - h :=
    Nat.sub_le_sub_right hlo h
  have hrew : HLo r h e i - 2 - h = HLo r h e i - h - 2 := by
    rw [Nat.sub_sub, Nat.sub_sub, Nat.add_comm]
  have hge : HLo r h e i - h - 2 <= rho - h := by
    rwa [hrew] at hge0
  rw [HHi_prev_sub_one_eq_HLo_sub_h_sub_two
    (r := r) (h := h) (e := e) hp hi_pos]
  exact hge

private theorem rho_sub_h_le_next_gap
    {r h e i rho : Nat} (hp : Params r h e)
    (hrhoI : InI r h e i rho) :
    rho - h <= HLo r h e i - 3 := by
  have hhi : rho <= HLo r h e i + h - 3 := by
    simpa [InI, InInterval, IHi] using hrhoI.2
  have hsub : rho - h <= HLo r h e i + h - 3 - h :=
    Nat.sub_le_sub_right hhi h
  have hD := D_ge_three hp
  have hh := hp.h_ge_six
  have hrew : HLo r h e i + h - 3 - h = HLo r h e i - 3 := by
    unfold HLo
    omega
  rwa [hrew] at hsub

private theorem inV_below_next_I_le_prev_HHi_sub_two
    {r h e i v : Nat} (hp : Params r h e)
    (hi_pos : 1 <= i) (hv : InV r h e v)
    (hvhi : v <= HLo r h e i - 3) :
    v <= HHi r h e (i - 1) - 2 := by
  rcases hv with ⟨j, _hj, hvI⟩
  by_cases hji : j < i
  · have hjle : j <= i - 1 := by omega
    have hcoef : 2 * j <= 2 * (i - 1) := Nat.mul_le_mul_left 2 hjle
    have hprod : 2 * j * h <= 2 * (i - 1) * h :=
      Nat.mul_le_mul_right h hcoef
    have hD := D_ge_three hp
    have hh := hp.h_ge_six
    unfold InI InInterval IHi HLo at hvI
    unfold HHi HLo
    omega
  · have hij : i <= j := by omega
    have hlo := ILo_mono_index (r := r) (h := h) (e := e) hij
    have hvlo : ILo r h e i <= v := Nat.le_trans hlo hvI.1
    have hD := D_ge_three hp
    unfold ILo at hvlo
    omega

theorem rho_sub_h_not_inV_of_later_index
    {r h e i rho : Nat} (hp : Params r h e)
    (hi_pos : 1 <= i) (hrhoI : InI r h e i rho) :
    ¬ InV r h e (rho - h) := by
  intro hv
  have hge := rho_sub_h_ge_prev_HHi_sub_one hp hi_pos hrhoI
  have hgap := rho_sub_h_le_next_gap hp hrhoI
  have hle := inV_below_next_I_le_prev_HHi_sub_two
    (r := r) (h := h) (e := e) (i := i) (v := rho - h)
    hp hi_pos hv hgap
  have hHlo := HLo_ge_three (r := r) (h := h) (e := e) (i := i - 1) hp
  unfold HHi at hge hle
  omega

theorem candidate_mod_eq_rho_sub_h_of_later_index
    {r h e i rho n : Nat} (hp : Params r h e)
    (hi_pos : 1 <= i) (hrhoI : InI r h e i rho)
    (hn : Candidate r h e n) (hnmod : n % M r h e = rho - h) :
    n = rho - h := by
  rcases hn with hnP | hnBlock
  · have hprefix_mod := prefix_mod_eq hp hnP
    omega
  · rcases hnBlock with ⟨q, _hq, hnq⟩
    rcases in_periodic_block_mod_eq
        (r := r) (h := h) (e := e) (q := q) hp hnq with
      ⟨sigma, hsigma, hnmod_sigma⟩
    have hsigma_eq : sigma = rho - h := by omega
    have hnot := rho_sub_h_not_inV_of_later_index
      (r := r) (h := h) (e := e) (i := i) (rho := rho)
      hp hi_pos hrhoI
    have hsigma' : InV r h e (rho - h) := by
      rwa [← hsigma_eq]
    exact False.elim (hnot hsigma')

private theorem h_le_rho_of_later_inI
    {r h e i rho : Nat} (hp : Params r h e)
    (hi_pos : 1 <= i) (hrhoI : InI r h e i rho) :
    h <= rho := by
  have hD := D_ge_h_add_one hp
  have hi2 : 2 <= 2 * i := by omega
  have hmul : 2 * h <= 2 * i * h := Nat.mul_le_mul_right h hi2
  unfold InI InInterval ILo HLo at hrhoI
  omega

private theorem rho_sub_h_add_one_add_h_sub_one
    {h rho : Nat} (hh : 1 <= h) (hrho_ge_h : h <= rho) :
    rho - h + 1 + (h - 1) = rho := by
  omega

private theorem positive_block_quotient_contradiction
    {r h e q rho target x y z : Nat} (hp : Params r h e)
    (hq : 1 <= q) (htarget : target = q * M r h e + rho)
    (hsum : x + y + z = target) (hactual : x + y + z = rho) :
    False := by
  have hqM_zero : q * M r h e = 0 := by omega
  have hqpos : 0 < q := by omega
  have hMpos := M_pos hp
  have hprod_pos : 0 < q * M r h e := Nat.mul_pos hqpos hMpos
  omega

private theorem later_classification_contradiction
    {r h e i q rho target x y z : Nat} (hp : Params r h e)
    (hi_pos : 1 <= i) (hi : i < r) (hq : 1 <= q)
    (hrhoI : InI r h e i rho)
    (htarget : target = q * M r h e + rho)
    (hx : Candidate r h e x) (hy : Candidate r h e y)
    (hz : Candidate r h e z)
    (hsum : x + y + z = target)
    (hclass : UnorderedResidueClassification h rho
      (x % M r h e) (y % M r h e) (z % M r h e)) :
    False := by
  have hrho_ge_h := h_le_rho_of_later_inI hp hi_pos hrhoI
  have hh_pos : 1 <= h := by
    have hh := hp.h_ge_six
    omega
  have hpattern : rho - h + 1 + (h - 1) = rho :=
    rho_sub_h_add_one_add_h_sub_one hh_pos hrho_ge_h
  rcases hclass with hxyz | hxyz | hxyz | hxyz | hxyz | hxyz
  · rcases hxyz with ⟨hxrho, hyone, hzh⟩
    have hxeq := candidate_mod_eq_rho_sub_h_of_later_index
      (r := r) (h := h) (e := e) (i := i) (rho := rho) hp hi_pos hrhoI hx hxrho
    have hyeq := candidate_mod_eq_one hp hy hyone
    have hzeq := candidate_mod_eq_h_sub_one_of_later_index
      (r := r) (h := h) (e := e) (i := i) hp hi_pos hi hz hzh
    have hactual : x + y + z = rho := by omega
    exact positive_block_quotient_contradiction hp hq htarget hsum hactual
  · rcases hxyz with ⟨hxrho, hyh, hzone⟩
    have hxeq := candidate_mod_eq_rho_sub_h_of_later_index
      (r := r) (h := h) (e := e) (i := i) (rho := rho) hp hi_pos hrhoI hx hxrho
    have hyeq := candidate_mod_eq_h_sub_one_of_later_index
      (r := r) (h := h) (e := e) (i := i) hp hi_pos hi hy hyh
    have hzeq := candidate_mod_eq_one hp hz hzone
    have hactual : x + y + z = rho := by omega
    exact positive_block_quotient_contradiction hp hq htarget hsum hactual
  · rcases hxyz with ⟨hyrho, hxone, hzh⟩
    have hyeq := candidate_mod_eq_rho_sub_h_of_later_index
      (r := r) (h := h) (e := e) (i := i) (rho := rho) hp hi_pos hrhoI hy hyrho
    have hxeq := candidate_mod_eq_one hp hx hxone
    have hzeq := candidate_mod_eq_h_sub_one_of_later_index
      (r := r) (h := h) (e := e) (i := i) hp hi_pos hi hz hzh
    have hactual : x + y + z = rho := by omega
    exact positive_block_quotient_contradiction hp hq htarget hsum hactual
  · rcases hxyz with ⟨hyrho, hxh, hzone⟩
    have hyeq := candidate_mod_eq_rho_sub_h_of_later_index
      (r := r) (h := h) (e := e) (i := i) (rho := rho) hp hi_pos hrhoI hy hyrho
    have hxeq := candidate_mod_eq_h_sub_one_of_later_index
      (r := r) (h := h) (e := e) (i := i) hp hi_pos hi hx hxh
    have hzeq := candidate_mod_eq_one hp hz hzone
    have hactual : x + y + z = rho := by omega
    exact positive_block_quotient_contradiction hp hq htarget hsum hactual
  · rcases hxyz with ⟨hzrho, hxone, hyh⟩
    have hzeq := candidate_mod_eq_rho_sub_h_of_later_index
      (r := r) (h := h) (e := e) (i := i) (rho := rho) hp hi_pos hrhoI hz hzrho
    have hxeq := candidate_mod_eq_one hp hx hxone
    have hyeq := candidate_mod_eq_h_sub_one_of_later_index
      (r := r) (h := h) (e := e) (i := i) hp hi_pos hi hy hyh
    have hactual : x + y + z = rho := by omega
    exact positive_block_quotient_contradiction hp hq htarget hsum hactual
  · rcases hxyz with ⟨hzrho, hxh, hyone⟩
    have hzeq := candidate_mod_eq_rho_sub_h_of_later_index
      (r := r) (h := h) (e := e) (i := i) (rho := rho) hp hi_pos hrhoI hz hzrho
    have hxeq := candidate_mod_eq_h_sub_one_of_later_index
      (r := r) (h := h) (e := e) (i := i) hp hi_pos hi hx hxh
    have hyeq := candidate_mod_eq_one hp hy hyone
    have hactual : x + y + z = rho := by omega
    exact positive_block_quotient_contradiction hp hq htarget hsum hactual

/--
Full periodic safety for regular `r`-bands: no positive periodic target
`q*M+rho`, with `rho` in the periodic residue set `V`, is a sum of three
distinct earlier candidates.
-/
theorem periodic_block_safe
    {r h e q rho target : Nat} (hp : Params r h e)
    (hq : 1 <= q) (hrho : InV r h e rho)
    (htarget : target = q * M r h e + rho) :
    ¬ CandidateTripleSumFrom r h e target := by
  intro htriple
  rcases candidateTripleSumFrom_residue_sum_eq
      (r := r) (h := h) (e := e) (q := q) (rho := rho)
      (target := target) hp hrho htarget htriple with
    ⟨x, y, z, hx, hy, hz, hxy, hyz, hzlt, hsum, hres_sum, hclass⟩
  rcases hrho with ⟨i, hi, hrhoI⟩
  by_cases hi_zero : i = 0
  · subst i
    have hfeasible := candidate_residues_feasible_of_exact_sum
      (r := r) (h := h) (e := e) (rho := rho) (x := x) (y := y) (z := z)
      hp ⟨0, hi, hrhoI⟩ hx hy hz hxy hyz hres_sum
    exact unordered_classification_inI_zero_impossible
      (r := r) (h := h) (e := e) (rho := rho)
      (x := x % M r h e) (y := y % M r h e) (z := z % M r h e)
      hp hfeasible hclass hrhoI
  · have hi_pos : 1 <= i := by omega
    exact later_classification_contradiction
      (r := r) (h := h) (e := e) (i := i) (q := q) (rho := rho)
      (target := target) (x := x) (y := y) (z := z)
      hp hi_pos hi hq hrhoI htarget hx hy hz hsum hclass

end RBand
end GreedyThreeSumfree
