import GreedyThreeSumfree.BoundaryRBandSafety

namespace GreedyThreeSumfree
namespace BoundaryRBand

/--
Two residues above the small prefix part already make `1 + y + z` too large to
land back in the periodic residue window `V`.
-/
theorem two_large_residues_exceed_VTop {r h y z : Nat} (hp : Params r h)
    (hy : VBot r h <= y) (hz : VBot r h <= z) :
    VTop r h < 1 + y + z := by
  have hD := D_ge_three hp
  have hbot_eq : VBot r h + 1 = D r h := by
    unfold VBot
    omega
  have hV_eq : VTop r h + 2 = D r h + (2 * r - 1) * h := by
    unfold VTop
    omega
  have hD_eq : D r h + 1 = (2 * r) * h := by
    unfold D at hD ⊢
    omega
  have hcoef_lt : 2 * r - 1 < 2 * r := by
    have hr := hp.r_pos
    omega
  have hprod_lt : (2 * r - 1) * h < (2 * r) * h :=
    Nat.mul_lt_mul_of_pos_right hcoef_lt (by
      have hh := hp.h_ge_six
      omega)
  omega

/--
If an ordered residue triple sums exactly to a residue in `V`, then the middle
term cannot exceed the small prefix residue `h-1`.
-/
theorem ordered_sum_eq_rho_forces_middle_le_h_sub_one
    {r h rho x y z : Nat} (hp : Params r h)
    (hx : InResidue r h x) (hy : InResidue r h y)
    (hz : InResidue r h z) (_hxy : x < y) (hyz : y < z)
    (hsum : x + y + z = rho) (hrho : InV r h rho) :
    y <= h - 1 := by
  by_cases hy_le : y <= h - 1
  · exact hy_le
  · have hy_gt : h - 1 < y := by omega
    have hz_gt : h - 1 < z := by omega
    have hy_large := residue_gt_h_sub_one_ge_VBot hp hy hy_gt
    have hz_large := residue_gt_h_sub_one_ge_VBot hp hz hz_gt
    have htoo_large := two_large_residues_exceed_VTop hp hy_large hz_large
    have hx_lo := residue_ge_one hp hx
    have hrho_hi := inV_upper hp hrho
    omega

/--
An ordered residue triple summing exactly to a residue in `V` must begin with
the two small prefix residues.
-/
theorem ordered_sum_eq_rho_forces_first_two_small
    {r h rho x y z : Nat} (hp : Params r h)
    (hx : InResidue r h x) (hy : InResidue r h y)
    (hz : InResidue r h z) (hxy : x < y) (hyz : y < z)
    (hsum : x + y + z = rho) (hrho : InV r h rho) :
    x = 1 ∧ y = h - 1 := by
  have hy_le := ordered_sum_eq_rho_forces_middle_le_h_sub_one
    (r := r) (h := h) (rho := rho) (x := x) (y := y) (z := z)
    hp hx hy hz hxy hyz hsum hrho
  have hx_eq : x = 1 := by
    by_cases hx_eq : x = 1
    · exact hx_eq
    · have hx_ge := residue_ne_one_ge_h_sub_one hp hx hx_eq
      omega
  have hy_ne_one : y ≠ 1 := by omega
  have hy_ge := residue_ne_one_ge_h_sub_one hp hy hy_ne_one
  exact ⟨hx_eq, by omega⟩

/-- The last term in such a representation is forced to be `rho - h`. -/
theorem ordered_sum_eq_rho_forces_last_eq_rho_sub_h
    {r h rho x y z : Nat} (hp : Params r h)
    (hx : InResidue r h x) (hy : InResidue r h y)
    (hz : InResidue r h z) (hxy : x < y) (hyz : y < z)
    (hsum : x + y + z = rho) (hrho : InV r h rho) :
    z = rho - h := by
  rcases ordered_sum_eq_rho_forces_first_two_small
      (r := r) (h := h) (rho := rho) (x := x) (y := y) (z := z)
      hp hx hy hz hxy hyz hsum hrho with ⟨hx_eq, hy_eq⟩
  have hh := hp.h_ge_six
  subst x
  subst y
  omega

/-- Packaged classification of exact ordered sums landing in `V`. -/
theorem ordered_sum_eq_rho_classification
    {r h rho x y z : Nat} (hp : Params r h)
    (hx : InResidue r h x) (hy : InResidue r h y)
    (hz : InResidue r h z) (hxy : x < y) (hyz : y < z)
    (hsum : x + y + z = rho) (hrho : InV r h rho) :
    x = 1 ∧ y = h - 1 ∧ z = rho - h := by
  have hxy_small := ordered_sum_eq_rho_forces_first_two_small
    (r := r) (h := h) (rho := rho) (x := x) (y := y) (z := z)
    hp hx hy hz hxy hyz hsum hrho
  have hz_eq := ordered_sum_eq_rho_forces_last_eq_rho_sub_h
    (r := r) (h := h) (rho := rho) (x := x) (y := y) (z := z)
    hp hx hy hz hxy hyz hsum hrho
  exact ⟨hxy_small.1, hxy_small.2, hz_eq⟩

theorem HLo_mono_index {r h i j : Nat} (hij : i <= j) :
    HLo r h i <= HLo r h j := by
  have hcoef : 2 * i <= 2 * j := Nat.mul_le_mul_left 2 hij
  have hprod : 2 * i * h <= 2 * j * h := Nat.mul_le_mul_right h hcoef
  unfold HLo
  omega

theorem KLo_mono_index {r h i j : Nat} (hij : i <= j) :
    KLo r h i <= KLo r h j := by
  have hLo := HLo_mono_index (r := r) (h := h) hij
  unfold KLo
  exact Nat.sub_le_sub_right hLo 1

/--
No available residue can sit in the gap after `H_{i-1}` and below the next
shifted interval `K_i`.
-/
theorem residue_below_next_K_gap_le_prev_HHi
    {r h i z : Nat} (hp : Params r h) (hi_pos : 1 <= i) (hi : i < r)
    (hz : InResidue r h z) (hzhi : z <= HLo r h i - 2) :
    z <= HHi r h (i - 1) := by
  rcases hz with hpfx | hV
  · unfold InPrefix at hpfx
    rcases hpfx with rfl | rfl | rfl | hU
    · have hD := D_ge_three hp
      have hh := hp.h_ge_six
      unfold HHi HLo
      omega
    · have hD := D_ge_three hp
      have hh := hp.h_ge_six
      unfold HHi HLo
      omega
    · have hc_hi : c r h > HLo r h i - 2 := by
        have htop := HHi_lt_c hp hi
        have hlole : HLo r h i <= HHi r h i := HLo_le_HHi hp
        omega
      omega
    · rcases hU with ⟨j, _hj, hzH⟩
      by_cases hji : j < i
      · have hjle : j <= i - 1 := by omega
        have htop := HHi_mono_index (r := r) (h := h) hjle
        exact Nat.le_trans hzH.2 htop
      · have hij : i <= j := by omega
        have hlo := HLo_mono_index (r := r) (h := h) hij
        have hzlo : HLo r h i <= z := Nat.le_trans hlo hzH.1
        have hH := HLo_ge_three (r := r) (h := h) (i := i) hp
        omega
  · rcases hV with ⟨j, _hj, hzK⟩
    by_cases hji : j < i
    · have hjle : j <= i - 1 := by omega
      have hKhi_le_HHi : KHi r h j <= HHi r h j := by
        unfold KHi
        omega
      have htop := HHi_mono_index (r := r) (h := h) hjle
      exact Nat.le_trans hzK.2 (Nat.le_trans hKhi_le_HHi htop)
    · have hij : i <= j := by omega
      have hlo := KLo_mono_index (r := r) (h := h) hij
      have hzlo : KLo r h i <= z := Nat.le_trans hlo hzK.1
      have hH := HLo_ge_three (r := r) (h := h) (i := i) hp
      unfold KLo at hzlo
      omega

theorem HHi_prev_eq_HLo_sub_h_sub_one
    {r h i : Nat} (hp : Params r h) (hi_pos : 1 <= i) :
    HHi r h (i - 1) = HLo r h i - h - 1 := by
  have hD := D_ge_three hp
  have hh := hp.h_ge_six
  have hcoef : 2 * i = 2 * (i - 1) + 2 := by omega
  unfold HHi HLo
  rw [hcoef]
  rw [Nat.add_mul]
  omega

/--
If the target residue is in a specific `K_i`, then the forced last term
`rho-h` lies between `HHi_{i-1}` and the gap just before `K_i`.
-/
theorem ordered_sum_eq_rho_inK_last_bounds
    {r h i rho x y z : Nat} (hp : Params r h) (hi : i < r)
    (hx : InResidue r h x) (hy : InResidue r h y)
    (hz : InResidue r h z) (hxy : x < y) (hyz : y < z)
    (hsum : x + y + z = rho) (hrhoK : InK r h i rho) :
    HLo r h i - h - 1 <= z ∧ z <= HLo r h i - 2 := by
  have hrho : InV r h rho := ⟨i, hi, hrhoK⟩
  have hz_eq := ordered_sum_eq_rho_forces_last_eq_rho_sub_h
    (r := r) (h := h) (rho := rho) (x := x) (y := y) (z := z)
    hp hx hy hz hxy hyz hsum hrho
  have hH := HLo_ge_three (r := r) (h := h) (i := i) hp
  have hh := hp.h_ge_six
  unfold InK InInterval KLo KHi HHi at hrhoK
  omega

/-- The `K_0` case cannot occur for an exact ordered residue sum landing in `K_0`. -/
theorem ordered_sum_eq_rho_inK_zero_impossible
    {r h rho x y z : Nat} (hp : Params r h)
    (hx : InResidue r h x) (hy : InResidue r h y)
    (hz : InResidue r h z) (hxy : x < y) (hyz : y < z)
    (hsum : x + y + z = rho) (hrhoK : InK r h 0 rho) :
    False := by
  have hi : 0 < r := by
    have hr := hp.r_pos
    omega
  have hrho : InV r h rho := ⟨0, hi, hrhoK⟩
  have hsmall := ordered_sum_eq_rho_forces_first_two_small
    (r := r) (h := h) (rho := rho) (x := x) (y := y) (z := z)
    hp hx hy hz hxy hyz hsum hrho
  have hbounds := ordered_sum_eq_rho_inK_last_bounds
    (r := r) (h := h) (i := 0) (rho := rho) (x := x) (y := y) (z := z)
    hp hi hx hy hz hxy hyz hsum hrhoK
  have hz_gt : h - 1 < z := by omega
  have hz_large := residue_gt_h_sub_one_ge_VBot hp hz hz_gt
  have hD := D_ge_three hp
  unfold HLo VBot at *
  omega

/--
For `i >= 1`, exact ordered feasibility forces the last residue to be the
upper endpoint of the preceding prefix interval.
-/
theorem ordered_sum_eq_rho_inK_last_prev_HHi
    {r h i rho x y z : Nat} (hp : Params r h) (hi_pos : 1 <= i)
    (hi : i < r) (hx : InResidue r h x) (hy : InResidue r h y)
    (hz : InResidue r h z) (hxy : x < y) (hyz : y < z)
    (hsum : x + y + z = rho) (hrhoK : InK r h i rho) :
    z = HHi r h (i - 1) := by
  have hbounds := ordered_sum_eq_rho_inK_last_bounds
    (r := r) (h := h) (i := i) (rho := rho) (x := x) (y := y) (z := z)
    hp hi hx hy hz hxy hyz hsum hrhoK
  have hupper := residue_below_next_K_gap_le_prev_HHi
    (r := r) (h := h) (i := i) hp hi_pos hi hz hbounds.2
  have hprev := HHi_prev_eq_HLo_sub_h_sub_one
    (r := r) (h := h) (i := i) hp hi_pos
  omega

theorem ordered_sum_eq_rho_inK_last_prefix
    {r h i rho x y z : Nat} (hp : Params r h) (hi_pos : 1 <= i)
    (hi : i < r) (hx : InResidue r h x) (hy : InResidue r h y)
    (hz : InResidue r h z) (hxy : x < y) (hyz : y < z)
    (hsum : x + y + z = rho) (hrhoK : InK r h i rho) :
    InPrefix r h z := by
  have hz_eq := ordered_sum_eq_rho_inK_last_prev_HHi
    (r := r) (h := h) (i := i) (rho := rho) (x := x) (y := y) (z := z)
    hp hi_pos hi hx hy hz hxy hyz hsum hrhoK
  subst z
  right
  right
  right
  refine ⟨i - 1, ?_, ?_⟩
  · omega
  · exact ⟨HLo_le_HHi hp, Nat.le_refl _⟩

theorem ordered_residue_witness_mod_eq_classification
    {r h rho x y z S : Nat} (hp : Params r h)
    (hrho : InV r h rho)
    (hx : InResidue r h x) (hy : InResidue r h y)
    (hz : InResidue r h z) (hxy : x < y) (hyz : y < z)
    (hsum : x + y + z = S) (hmod : S % M r h = rho) :
    x = 1 ∧ y = h - 1 ∧ z = rho - h := by
  have hsum_rho := ordered_residue_witness_mod_eq_forces_eq
    (r := r) (h := h) (rho := rho) (x := x) (y := y) (z := z) (S := S)
    hp hrho hx hy hz hxy hyz hsum hmod
  exact ordered_sum_eq_rho_classification
    (r := r) (h := h) (rho := rho) (x := x) (y := y) (z := z)
    hp hx hy hz hxy hyz hsum_rho hrho

end BoundaryRBand
end GreedyThreeSumfree
