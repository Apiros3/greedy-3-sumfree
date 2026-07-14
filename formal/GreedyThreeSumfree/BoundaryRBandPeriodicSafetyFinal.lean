import GreedyThreeSumfree.BoundaryRBandUnorderedResidues

namespace GreedyThreeSumfree
namespace BoundaryRBand

private theorem candidate_mod_gt_VTop_eq
    {r h n v : Nat} (hp : Params r h)
    (hn : Candidate r h n) (hmod : n % M r h = v)
    (hvgt : VTop r h < v) :
    n = v := by
  rcases hn with hnP | hnBlock
  · have hprefix_mod := prefix_mod_eq hp hnP
    omega
  · rcases hnBlock with ⟨q, _hq, hnq⟩
    rcases in_periodic_block_mod_eq
        (r := r) (h := h) (q := q) hp hnq with
      ⟨rho, hrho, hnmod⟩
    have hrho_hi := inV_upper hp hrho
    omega

theorem candidate_residue_noDuplicate_of_gt_VTop
    {r h x y z v : Nat} (hp : Params r h)
    (hvgt : VTop r h < v)
    (hx : Candidate r h x) (hy : Candidate r h y)
    (hz : Candidate r h z) (hxy : x < y) (hyz : y < z) :
    NoDuplicateValue3
      (x % M r h) (y % M r h) (z % M r h) v := by
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

private theorem sum_le_C_add_T_add_T_sub_one
    {C T x y z : Nat}
    (hTpos : 1 <= T) (_hTltC : T < C)
    (hxleC : x <= C) (hyleC : y <= C) (hzleC : z <= C)
    (hndC : NoDuplicateValue3 x y z C)
    (hndT : NoDuplicateValue3 x y z T)
    (hxltC_leT : x < C → x <= T)
    (hyltC_leT : y < C → y <= T)
    (hzltC_leT : z < C → z <= T) :
    x + y + z <= C + T + (T - 1) := by
  by_cases hxC : x = C
  · have hy_ne_C : y ≠ C := hndC.1 hxC
    have hz_ne_C : z ≠ C := hndC.2.1 hxC
    have hyltC : y < C := by omega
    have hzltC : z < C := by omega
    have hyleT := hyltC_leT hyltC
    have hzleT := hzltC_leT hzltC
    by_cases hyT : y = T
    · have hz_ne_T : z ≠ T := hndT.2.2 hyT
      omega
    · omega
  · have hxltC : x < C := by omega
    have hxleT := hxltC_leT hxltC
    by_cases hyC : y = C
    · have hx_ne_C : x ≠ C := hxC
      have hz_ne_C : z ≠ C := hndC.2.2 hyC
      have hzltC : z < C := by omega
      have hzleT := hzltC_leT hzltC
      by_cases hxT : x = T
      · have hz_ne_T : z ≠ T := hndT.2.1 hxT
        omega
      · omega
    · have hyltC : y < C := by omega
      have hyleT := hyltC_leT hyltC
      by_cases hzC : z = C
      · by_cases hxT : x = T
        · have hy_ne_T : y ≠ T := hndT.1 hxT
          omega
        · omega
      · have hzltC : z < C := by omega
        have hzleT := hzltC_leT hzltC
        omega

private theorem c_add_HHi_last_add_VTop_eq_sum_upper
    {r h : Nat} (hp : Params r h) :
    c r h + HHi r h (r - 1) + VTop r h =
      (12 * r - 2) * h - 6 := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have hH := HHi_last_eq_VTop_add_one (r := r) (h := h) hp
  have hc1 : c r h + 1 = (4 * r) * h := by
    have hcoef4 : 4 <= 4 * r := by omega
    have hmul4 : 4 * h <= (4 * r) * h :=
      Nat.mul_le_mul_right h hcoef4
    have hpos : 1 <= (4 * r) * h := by omega
    unfold c
    omega
  have hv3 : VTop r h + 3 = (4 * r - 1) * h := by
    have hcoef : 2 * r + (2 * r - 1) = 4 * r - 1 := by omega
    have hprod :
        (2 * r) * h + (2 * r - 1) * h = (4 * r - 1) * h := by
      rw [← Nat.add_mul, hcoef]
    have hD1 : D r h + 1 = (2 * r) * h := by
      have hcoef2 : 2 <= 2 * r := by omega
      have hmul2 : 2 * h <= (2 * r) * h :=
        Nat.mul_le_mul_right h hcoef2
      unfold D
      omega
    have hterm_pos : 1 <= (2 * r - 1) * h := by
      have hcoef_pos := two_r_sub_one_pos (r := r) (h := h) hp
      have hmul : 1 * h <= (2 * r - 1) * h :=
        Nat.mul_le_mul_right h hcoef_pos
      omega
    have hbase_ge_two : 2 <= D r h + (2 * r - 1) * h := by
      have hD := D_ge_three hp
      omega
    unfold VTop
    omega
  have hcoef_sum : 4 * r + (4 * r - 1) + (4 * r - 1) = 12 * r - 2 := by
    omega
  have hprod_sum :
      (4 * r) * h + (4 * r - 1) * h + (4 * r - 1) * h =
        (12 * r - 2) * h := by
    calc
      (4 * r) * h + (4 * r - 1) * h + (4 * r - 1) * h
          = (4 * r + (4 * r - 1)) * h + (4 * r - 1) * h := by
              rw [← Nat.add_mul]
      _ = (4 * r + (4 * r - 1) + (4 * r - 1)) * h := by
              rw [← Nat.add_mul]
      _ = (12 * r - 2) * h := by rw [hcoef_sum]
  have hsum_add :
      c r h + HHi r h (r - 1) + VTop r h + 6 =
        (12 * r - 2) * h := by
    rw [hH]
    omega
  have hupper_ge : 6 <= (12 * r - 2) * h := by
    have hcoef : 10 <= 12 * r - 2 := by omega
    have hmul : 10 * h <= (12 * r - 2) * h :=
      Nat.mul_le_mul_right h hcoef
    omega
  omega

theorem candidate_residue_sum_upper
    {r h x y z : Nat} (hp : Params r h)
    (hx : Candidate r h x) (hy : Candidate r h y)
    (hz : Candidate r h z) (hxy : x < y) (hyz : y < z) :
    x % M r h + y % M r h + z % M r h <=
      (12 * r - 2) * h - 6 := by
  let rx := x % M r h
  let ry := y % M r h
  let rz := z % M r h
  have hrx : InResidue r h rx := candidate_mod_in_residue hp hx
  have hry : InResidue r h ry := candidate_mod_in_residue hp hy
  have hrz : InResidue r h rz := candidate_mod_in_residue hp hz
  have hxleC : rx <= c r h := residue_le_c hp hrx
  have hyleC : ry <= c r h := residue_le_c hp hry
  have hzleC : rz <= c r h := residue_le_c hp hrz
  have htop_eq := HHi_last_eq_VTop_add_one hp
  have hTgt : VTop r h < HHi r h (r - 1) := by omega
  have hCgt : VTop r h < c r h := VTop_lt_c hp
  have hndC : NoDuplicateValue3 rx ry rz (c r h) :=
    candidate_residue_noDuplicate_of_gt_VTop
      (r := r) (h := h) (x := x) (y := y) (z := z)
      hp hCgt hx hy hz hxy hyz
  have hndT : NoDuplicateValue3 rx ry rz (HHi r h (r - 1)) :=
    candidate_residue_noDuplicate_of_gt_VTop
      (r := r) (h := h) (x := x) (y := y) (z := z)
      hp hTgt hx hy hz hxy hyz
  have hTpos : 1 <= HHi r h (r - 1) := by
    have hH := HLo_ge_three (r := r) (h := h) (i := r - 1) hp
    have hle := HLo_le_HHi (r := r) (h := h) (i := r - 1) hp
    omega
  have hTltC : HHi r h (r - 1) < c r h := HHi_last_lt_c hp
  have hsum_le :
      rx + ry + rz <=
        c r h + HHi r h (r - 1) + (HHi r h (r - 1) - 1) :=
    sum_le_C_add_T_add_T_sub_one
      (C := c r h) (T := HHi r h (r - 1))
      (x := rx) (y := ry) (z := rz)
      hTpos hTltC hxleC hyleC hzleC hndC hndT
      (fun hxlt => residue_lt_c_le_HHi_last hp hrx hxlt)
      (fun hylt => residue_lt_c_le_HHi_last hp hry hylt)
      (fun hzlt => residue_lt_c_le_HHi_last hp hrz hzlt)
  have hTsub : HHi r h (r - 1) - 1 = VTop r h := by
    rw [VTop_eq_KHi_last hp]
    rfl
  rw [hTsub] at hsum_le
  rw [c_add_HHi_last_add_VTop_eq_sum_upper hp] at hsum_le
  exact hsum_le

theorem candidate_residue_mod_eq_forces_eq
    {r h rho x y z : Nat} (hp : Params r h)
    (hrho : InV r h rho)
    (hx : Candidate r h x) (hy : Candidate r h y)
    (hz : Candidate r h z) (hxy : x < y) (hyz : y < z)
    (hmod :
      (x % M r h + y % M r h + z % M r h) % M r h = rho) :
    x % M r h + y % M r h + z % M r h = rho := by
  let S := x % M r h + y % M r h + z % M r h
  by_cases hEq : S = rho
  · exact hEq
  · by_cases hrho_lt_S : rho < S
    · have hSlo : 1 <= S := by
        have hrx := residue_ge_one hp (candidate_mod_in_residue hp hx)
        have hry := residue_ge_one hp (candidate_mod_in_residue hp hy)
        have hrz := residue_ge_one hp (candidate_mod_in_residue hp hz)
        dsimp [S]
        omega
      have hShi : S <= (12 * r - 2) * h - 6 := by
        dsimp [S]
        exact candidate_residue_sum_upper hp hx hy hz hxy hyz
      exact False.elim
        (residue_mod_contradiction hp hrho hSlo hShi hmod hrho_lt_S)
    · have hS_lt_rho : S < rho := by omega
      exact False.elim (residue_mod_contradiction_below hmod hS_lt_rho)

theorem candidateTripleSumFrom_residue_sum_eq
    {r h q rho target : Nat} (hp : Params r h)
    (hrho : InV r h rho) (htarget : target = q * M r h + rho)
    (htriple : CandidateTripleSumFrom r h target) :
    ∃ x y z : Nat,
      Candidate r h x ∧ Candidate r h y ∧ Candidate r h z ∧
        x < y ∧ y < z ∧ z < target ∧ x + y + z = target ∧
        x % M r h + y % M r h + z % M r h = rho ∧
        UnorderedResidueClassification h rho
          (x % M r h) (y % M r h) (z % M r h) := by
  rcases candidateTripleSumFrom_unordered_residue_bridge
      (r := r) (h := h) (q := q) (rho := rho)
      (target := target) hp hrho htarget htriple with
    ⟨x, y, z, hx, hy, hz, hxy, hyz, hzlt, hsum, hmod, hclass_of_eq⟩
  have hres_sum := candidate_residue_mod_eq_forces_eq
    (r := r) (h := h) (rho := rho) (x := x) (y := y) (z := z)
    hp hrho hx hy hz hxy hyz hmod
  exact ⟨x, y, z, hx, hy, hz, hxy, hyz, hzlt, hsum, hres_sum,
    hclass_of_eq hres_sum⟩

private theorem rho_sub_h_ge_prev_HHi
    {r h i rho : Nat} (hp : Params r h)
    (hi_pos : 1 <= i) (hrhoK : InK r h i rho) :
    HHi r h (i - 1) <= rho - h := by
  have hlo : KLo r h i <= rho := hrhoK.1
  have hprev := HHi_prev_eq_HLo_sub_h_sub_one
    (r := r) (h := h) (i := i) hp hi_pos
  have hH := HLo_ge_three (r := r) (h := h) (i := i) hp
  have hh := hp.h_ge_six
  unfold KLo at hlo
  omega

private theorem rho_sub_h_le_next_gap
    {r h i rho : Nat} (hp : Params r h)
    (hrhoK : InK r h i rho) :
    rho - h <= HLo r h i - 2 := by
  have hhi : rho <= KHi r h i := hrhoK.2
  have hH := HLo_ge_three (r := r) (h := h) (i := i) hp
  have hh := hp.h_ge_six
  unfold KHi HHi at hhi
  omega

private theorem inV_below_next_K_gap_le_prev_KHi
    {r h i v : Nat} (hp : Params r h)
    (hi_pos : 1 <= i) (hv : InV r h v)
    (hvhi : v <= HLo r h i - 2) :
    v <= KHi r h (i - 1) := by
  rcases hv with ⟨j, _hj, hvK⟩
  by_cases hji : j < i
  · have hjle : j <= i - 1 := by omega
    have hcoef : 2 * j <= 2 * (i - 1) := Nat.mul_le_mul_left 2 hjle
    have hprod : 2 * j * h <= 2 * (i - 1) * h :=
      Nat.mul_le_mul_right h hcoef
    have hD := D_ge_three hp
    have hh := hp.h_ge_six
    unfold InK InInterval at hvK
    unfold KHi HHi HLo at hvK ⊢
    omega
  · have hij : i <= j := by omega
    have hlo := KLo_mono_index (r := r) (h := h) hij
    have hvlo : KLo r h i <= v := Nat.le_trans hlo hvK.1
    have hH := HLo_ge_three (r := r) (h := h) (i := i) hp
    unfold KLo at hvlo
    omega

theorem rho_sub_h_not_inV_of_later_index
    {r h i rho : Nat} (hp : Params r h)
    (hi_pos : 1 <= i) (hrhoK : InK r h i rho) :
    ¬ InV r h (rho - h) := by
  intro hv
  have hge := rho_sub_h_ge_prev_HHi hp hi_pos hrhoK
  have hgap := rho_sub_h_le_next_gap hp hrhoK
  have hle := inV_below_next_K_gap_le_prev_KHi
    (r := r) (h := h) (i := i) (v := rho - h)
    hp hi_pos hv hgap
  have hH := HLo_ge_three (r := r) (h := h) (i := i - 1) hp
  have hHle := HLo_le_HHi (r := r) (h := h) (i := i - 1) hp
  have hHpos : 1 <= HHi r h (i - 1) := by omega
  unfold KHi at hle
  omega

theorem candidate_mod_eq_rho_sub_h_of_later_index
    {r h i rho n : Nat} (hp : Params r h)
    (hi_pos : 1 <= i) (hrhoK : InK r h i rho)
    (hn : Candidate r h n) (hnmod : n % M r h = rho - h) :
    n = rho - h := by
  rcases hn with hnP | hnBlock
  · have hprefix_mod := prefix_mod_eq hp hnP
    omega
  · rcases hnBlock with ⟨q, _hq, hnq⟩
    rcases in_periodic_block_mod_eq
        (r := r) (h := h) (q := q) hp hnq with
      ⟨sigma, hsigma, hnmod_sigma⟩
    have hsigma_eq : sigma = rho - h := by omega
    have hnot := rho_sub_h_not_inV_of_later_index
      (r := r) (h := h) (i := i) (rho := rho)
      hp hi_pos hrhoK
    have hsigma' : InV r h (rho - h) := by
      rwa [← hsigma_eq]
    exact False.elim (hnot hsigma')

private theorem h_le_rho_of_later_inK
    {r h i rho : Nat} (hp : Params r h)
    (hi_pos : 1 <= i) (hrhoK : InK r h i rho) :
    h <= rho := by
  have hD := D_ge_h_add_one hp
  have hlo : KLo r h i <= rho := hrhoK.1
  have hi2 : 2 <= 2 * i := by omega
  have hmul : 2 * h <= 2 * i * h := Nat.mul_le_mul_right h hi2
  unfold KLo HLo at hlo
  omega

private theorem rho_sub_h_add_one_add_h_sub_one
    {h rho : Nat} (hh : 1 <= h) (hrho_ge_h : h <= rho) :
    rho - h + 1 + (h - 1) = rho := by
  omega

private theorem positive_block_quotient_contradiction
    {r h q rho target x y z : Nat} (hp : Params r h)
    (hq : 1 <= q) (htarget : target = q * M r h + rho)
    (hsum : x + y + z = target) (hactual : x + y + z = rho) :
    False := by
  have hqM_zero : q * M r h = 0 := by omega
  have hqpos : 0 < q := by omega
  have hMpos := M_pos hp
  have hprod_pos : 0 < q * M r h := Nat.mul_pos hqpos hMpos
  omega

private theorem later_classification_contradiction
    {r h i q rho target x y z : Nat} (hp : Params r h)
    (hi_pos : 1 <= i) (hq : 1 <= q)
    (hrhoK : InK r h i rho)
    (htarget : target = q * M r h + rho)
    (hx : Candidate r h x) (hy : Candidate r h y)
    (hz : Candidate r h z)
    (hsum : x + y + z = target)
    (hclass : UnorderedResidueClassification h rho
      (x % M r h) (y % M r h) (z % M r h)) :
    False := by
  have hrho_ge_h := h_le_rho_of_later_inK hp hi_pos hrhoK
  have hh_pos : 1 <= h := by
    have hh := hp.h_ge_six
    omega
  have hpattern : rho - h + 1 + (h - 1) = rho :=
    rho_sub_h_add_one_add_h_sub_one hh_pos hrho_ge_h
  rcases hclass with hxyz | hxyz | hxyz | hxyz | hxyz | hxyz
  · rcases hxyz with ⟨hxrho, hyone, hzh⟩
    have hxeq := candidate_mod_eq_rho_sub_h_of_later_index
      (r := r) (h := h) (i := i) (rho := rho) hp hi_pos hrhoK hx hxrho
    have hyeq := candidate_mod_eq_one hp hy hyone
    have hzeq := candidate_mod_eq_h_sub_one hp hz hzh
    have hactual : x + y + z = rho := by omega
    exact positive_block_quotient_contradiction hp hq htarget hsum hactual
  · rcases hxyz with ⟨hxrho, hyh, hzone⟩
    have hxeq := candidate_mod_eq_rho_sub_h_of_later_index
      (r := r) (h := h) (i := i) (rho := rho) hp hi_pos hrhoK hx hxrho
    have hyeq := candidate_mod_eq_h_sub_one hp hy hyh
    have hzeq := candidate_mod_eq_one hp hz hzone
    have hactual : x + y + z = rho := by omega
    exact positive_block_quotient_contradiction hp hq htarget hsum hactual
  · rcases hxyz with ⟨hyrho, hxone, hzh⟩
    have hyeq := candidate_mod_eq_rho_sub_h_of_later_index
      (r := r) (h := h) (i := i) (rho := rho) hp hi_pos hrhoK hy hyrho
    have hxeq := candidate_mod_eq_one hp hx hxone
    have hzeq := candidate_mod_eq_h_sub_one hp hz hzh
    have hactual : x + y + z = rho := by omega
    exact positive_block_quotient_contradiction hp hq htarget hsum hactual
  · rcases hxyz with ⟨hyrho, hxh, hzone⟩
    have hyeq := candidate_mod_eq_rho_sub_h_of_later_index
      (r := r) (h := h) (i := i) (rho := rho) hp hi_pos hrhoK hy hyrho
    have hxeq := candidate_mod_eq_h_sub_one hp hx hxh
    have hzeq := candidate_mod_eq_one hp hz hzone
    have hactual : x + y + z = rho := by omega
    exact positive_block_quotient_contradiction hp hq htarget hsum hactual
  · rcases hxyz with ⟨hzrho, hxone, hyh⟩
    have hzeq := candidate_mod_eq_rho_sub_h_of_later_index
      (r := r) (h := h) (i := i) (rho := rho) hp hi_pos hrhoK hz hzrho
    have hxeq := candidate_mod_eq_one hp hx hxone
    have hyeq := candidate_mod_eq_h_sub_one hp hy hyh
    have hactual : x + y + z = rho := by omega
    exact positive_block_quotient_contradiction hp hq htarget hsum hactual
  · rcases hxyz with ⟨hzrho, hxh, hyone⟩
    have hzeq := candidate_mod_eq_rho_sub_h_of_later_index
      (r := r) (h := h) (i := i) (rho := rho) hp hi_pos hrhoK hz hzrho
    have hxeq := candidate_mod_eq_h_sub_one hp hx hxh
    have hyeq := candidate_mod_eq_one hp hy hyone
    have hactual : x + y + z = rho := by omega
    exact positive_block_quotient_contradiction hp hq htarget hsum hactual

/--
Full periodic safety for boundary `r`-bands: no positive periodic target
`q*M+rho`, with `rho` in the periodic residue set `V`, is a sum of three
distinct earlier candidates.
-/
theorem periodic_block_safe
    {r h q rho target : Nat} (hp : Params r h)
    (hq : 1 <= q) (hrho : InV r h rho)
    (htarget : target = q * M r h + rho) :
    ¬ CandidateTripleSumFrom r h target := by
  intro htriple
  rcases candidateTripleSumFrom_residue_sum_eq
      (r := r) (h := h) (q := q) (rho := rho)
      (target := target) hp hrho htarget htriple with
    ⟨x, y, z, hx, hy, hz, hxy, hyz, hzlt, hsum, hres_sum, hclass⟩
  rcases hrho with ⟨i, hi, hrhoK⟩
  by_cases hi_zero : i = 0
  · subst i
    have hfeasible := candidate_residues_feasible_of_exact_sum
      (r := r) (h := h) (rho := rho) (x := x) (y := y) (z := z)
      hp ⟨0, hi, hrhoK⟩ hx hy hz hxy hyz hres_sum
    exact unordered_classification_inK_zero_impossible
      (r := r) (h := h) (rho := rho)
      (x := x % M r h) (y := y % M r h) (z := z % M r h)
      hp hfeasible hclass hrhoK
  · have hi_pos : 1 <= i := by omega
    exact later_classification_contradiction
      (r := r) (h := h) (i := i) (q := q) (rho := rho)
      (target := target) (x := x) (y := y) (z := z)
      hp hi_pos hq hrhoK htarget hx hy hz hsum hclass

end BoundaryRBand
end GreedyThreeSumfree
