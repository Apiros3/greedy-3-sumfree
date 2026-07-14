import GreedyThreeSumfree.RBandSafety

namespace GreedyThreeSumfree
namespace RBand

/--
Two residues in the large `V` range already make `1 + y + z` too large to land
back in `V`.
-/
theorem two_large_residues_exceed_VTop {r h e y z : Nat} (hp : Params r h e)
    (hy : VBot r h e <= y) (hz : VBot r h e <= z) :
    VTop r h e < 1 + y + z := by
  have hD := D_ge_three hp
  have he := hp.e_pos
  unfold VBot VTop D at *
  omega

/--
If an ordered residue triple sums to a residue in `V`, then the middle term
cannot exceed the small prefix residue `h-1`.
-/
theorem ordered_sum_eq_rho_forces_middle_le_h_sub_one
    {r h e rho x y z : Nat} (hp : Params r h e)
    (hx : InResidue r h e x) (hy : InResidue r h e y)
    (hz : InResidue r h e z) (_hxy : x < y) (hyz : y < z)
    (hsum : x + y + z = rho) (hrho : InV r h e rho) :
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
    {r h e rho x y z : Nat} (hp : Params r h e)
    (hx : InResidue r h e x) (hy : InResidue r h e y)
    (hz : InResidue r h e z) (hxy : x < y) (hyz : y < z)
    (hsum : x + y + z = rho) (hrho : InV r h e rho) :
    x = 1 ∧ y = h - 1 := by
  have hy_le := ordered_sum_eq_rho_forces_middle_le_h_sub_one
    (r := r) (h := h) (e := e) (rho := rho) (x := x) (y := y) (z := z)
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
    {r h e rho x y z : Nat} (hp : Params r h e)
    (hx : InResidue r h e x) (hy : InResidue r h e y)
    (hz : InResidue r h e z) (hxy : x < y) (hyz : y < z)
    (hsum : x + y + z = rho) (hrho : InV r h e rho) :
    z = rho - h := by
  rcases ordered_sum_eq_rho_forces_first_two_small
      (r := r) (h := h) (e := e) (rho := rho) (x := x) (y := y) (z := z)
      hp hx hy hz hxy hyz hsum hrho with ⟨hx_eq, hy_eq⟩
  have hh := hp.h_ge_six
  subst x
  subst y
  omega

/-- Packaged classification of exact ordered sums landing in `V`. -/
theorem ordered_sum_eq_rho_classification
    {r h e rho x y z : Nat} (hp : Params r h e)
    (hx : InResidue r h e x) (hy : InResidue r h e y)
    (hz : InResidue r h e z) (hxy : x < y) (hyz : y < z)
    (hsum : x + y + z = rho) (hrho : InV r h e rho) :
    x = 1 ∧ y = h - 1 ∧ z = rho - h := by
  have hxy_small := ordered_sum_eq_rho_forces_first_two_small
    (r := r) (h := h) (e := e) (rho := rho) (x := x) (y := y) (z := z)
    hp hx hy hz hxy hyz hsum hrho
  have hz_eq := ordered_sum_eq_rho_forces_last_eq_rho_sub_h
    (r := r) (h := h) (e := e) (rho := rho) (x := x) (y := y) (z := z)
    hp hx hy hz hxy hyz hsum hrho
  exact ⟨hxy_small.1, hxy_small.2, hz_eq⟩

/--
If the target residue is in a specific shifted interval `I_i`, then the forced
last term `rho-h` lies in the corresponding translated numeric range.
-/
theorem ordered_sum_eq_rho_inI_last_bounds
    {r h e i rho x y z : Nat} (hp : Params r h e) (hi : i < r)
    (hx : InResidue r h e x) (hy : InResidue r h e y)
    (hz : InResidue r h e z) (hxy : x < y) (hyz : y < z)
    (hsum : x + y + z = rho) (hrhoI : InI r h e i rho) :
    HLo r h e i - h - 2 <= z ∧ z <= HLo r h e i - 3 := by
  have hrho : InV r h e rho := ⟨i, hi, hrhoI⟩
  have hz_eq := ordered_sum_eq_rho_forces_last_eq_rho_sub_h
    (r := r) (h := h) (e := e) (rho := rho) (x := x) (y := y) (z := z)
    hp hx hy hz hxy hyz hsum hrho
  have hH := HLo_ge_three (r := r) (h := h) (e := e) (i := i) hp
  have hh := hp.h_ge_six
  unfold InI InInterval ILo IHi at hrhoI
  omega

theorem HHi_prev_sub_one_eq_HLo_sub_h_sub_two
    {r h e i : Nat} (hp : Params r h e) (hi_pos : 1 <= i) :
    HHi r h e (i - 1) - 1 = HLo r h e i - h - 2 := by
  have hD := D_ge_three hp
  have hh := hp.h_ge_six
  have hcoef : 2 * i = 2 * (i - 1) + 2 := by omega
  unfold HHi HLo
  rw [hcoef]
  rw [Nat.add_mul]
  omega

theorem HHi_prev_eq_HLo_sub_h_sub_one
    {r h e i : Nat} (hp : Params r h e) (hi_pos : 1 <= i) :
    HHi r h e (i - 1) = HLo r h e i - h - 1 := by
  have hD := D_ge_three hp
  have hh := hp.h_ge_six
  have hcoef : 2 * i = 2 * (i - 1) + 2 := by omega
  unfold HHi HLo
  rw [hcoef]
  rw [Nat.add_mul]
  omega

theorem HLo_mono_index {r h e i j : Nat} (hij : i <= j) :
    HLo r h e i <= HLo r h e j := by
  have hcoef : 2 * i <= 2 * j := Nat.mul_le_mul_left 2 hij
  have hprod : 2 * i * h <= 2 * j * h := Nat.mul_le_mul_right h hcoef
  unfold HLo
  omega

theorem HHi_mono_index {r h e i j : Nat} (hij : i <= j) :
    HHi r h e i <= HHi r h e j := by
  have hLo := HLo_mono_index (r := r) (h := h) (e := e) hij
  unfold HHi
  exact Nat.sub_le_sub_right (Nat.add_le_add_right hLo h) 1

theorem ILo_mono_index {r h e i j : Nat} (hij : i <= j) :
    ILo r h e i <= ILo r h e j := by
  have hLo := HLo_mono_index (r := r) (h := h) (e := e) hij
  unfold ILo
  exact Nat.sub_le_sub_right hLo 2

theorem IHi_le_HHi {r h e i : Nat} :
    IHi r h e i <= HHi r h e i := by
  unfold IHi HHi
  omega

/--
No available residue can sit in the gap after `H_{i-1}` and below the next
shifted interval `I_i`.
-/
theorem residue_below_next_I_gap_le_prev_HHi
    {r h e i z : Nat} (hp : Params r h e) (hi_pos : 1 <= i)
    (hz : InResidue r h e z) (hzhi : z <= HLo r h e i - 3) :
    z <= HHi r h e (i - 1) := by
  rcases hz with hpfx | hV
  · unfold InPrefix at hpfx
    rcases hpfx with rfl | rfl | hU
    · have hD := D_ge_three hp
      have hh := hp.h_ge_six
      unfold HHi HLo
      omega
    · have hD := D_ge_three hp
      have hh := hp.h_ge_six
      unfold HHi HLo
      omega
    · rcases hU with ⟨j, _hj, hzH⟩
      by_cases hji : j < i
      · have hjle : j <= i - 1 := by omega
        have htop := HHi_mono_index (r := r) (h := h) (e := e) hjle
        exact Nat.le_trans hzH.2 htop
      · have hij : i <= j := by omega
        have hlo := HLo_mono_index (r := r) (h := h) (e := e) hij
        have hzlo : HLo r h e i <= z := Nat.le_trans hlo hzH.1
        have hH := HLo_ge_three (r := r) (h := h) (e := e) (i := i) hp
        omega
  · rcases hV with ⟨j, _hj, hzI⟩
    by_cases hji : j < i
    · have hjle : j <= i - 1 := by omega
      have hIhi := IHi_le_HHi (r := r) (h := h) (e := e) (i := j)
      have htop := HHi_mono_index (r := r) (h := h) (e := e) hjle
      exact Nat.le_trans hzI.2 (Nat.le_trans hIhi htop)
    · have hij : i <= j := by omega
      have hlo := ILo_mono_index (r := r) (h := h) (e := e) hij
      have hzlo : ILo r h e i <= z := Nat.le_trans hlo hzI.1
      have hH := HLo_ge_three (r := r) (h := h) (e := e) (i := i) hp
      unfold ILo at hzlo
      omega

/--
The same `I_i` bounds, rewritten so the lower endpoint is the lower of the top
two points of the preceding `H_{i-1}` interval.
-/
theorem ordered_sum_eq_rho_inI_last_prev_H_lower_bound
    {r h e i rho x y z : Nat} (hp : Params r h e) (hi_pos : 1 <= i)
    (hi : i < r) (hx : InResidue r h e x) (hy : InResidue r h e y)
    (hz : InResidue r h e z) (hxy : x < y) (hyz : y < z)
    (hsum : x + y + z = rho) (hrhoI : InI r h e i rho) :
    HHi r h e (i - 1) - 1 <= z := by
  have hbounds := ordered_sum_eq_rho_inI_last_bounds
    (r := r) (h := h) (e := e) (i := i) (rho := rho) (x := x) (y := y) (z := z)
    hp hi hx hy hz hxy hyz hsum hrhoI
  rw [HHi_prev_sub_one_eq_HLo_sub_h_sub_two
    (r := r) (h := h) (e := e) hp hi_pos]
  exact hbounds.1

/-- The `V_0` case cannot occur for an exact ordered residue sum landing in `I_0`. -/
theorem ordered_sum_eq_rho_inI_zero_impossible
    {r h e rho x y z : Nat} (hp : Params r h e)
    (hx : InResidue r h e x) (hy : InResidue r h e y)
    (hz : InResidue r h e z) (hxy : x < y) (hyz : y < z)
    (hsum : x + y + z = rho) (hrhoI : InI r h e 0 rho) :
    False := by
  have hi : 0 < r := by
    have hr := hp.r_pos
    omega
  have hrho : InV r h e rho := ⟨0, hi, hrhoI⟩
  have hsmall := ordered_sum_eq_rho_forces_first_two_small
    (r := r) (h := h) (e := e) (rho := rho) (x := x) (y := y) (z := z)
    hp hx hy hz hxy hyz hsum hrho
  have hbounds := ordered_sum_eq_rho_inI_last_bounds
    (r := r) (h := h) (e := e) (i := 0) (rho := rho) (x := x) (y := y) (z := z)
    hp hi hx hy hz hxy hyz hsum hrhoI
  have hz_gt : h - 1 < z := by omega
  have hz_large := residue_gt_h_sub_one_ge_VBot hp hz hz_gt
  have hD := D_ge_three hp
  unfold HLo VBot at *
  omega

/--
For `i >= 1`, the forced last residue lies in the top two points of
`H_{i-1}`.
-/
theorem ordered_sum_eq_rho_inI_last_prev_H_top_two
    {r h e i rho x y z : Nat} (hp : Params r h e) (hi_pos : 1 <= i)
    (hi : i < r) (hx : InResidue r h e x) (hy : InResidue r h e y)
    (hz : InResidue r h e z) (hxy : x < y) (hyz : y < z)
    (hsum : x + y + z = rho) (hrhoI : InI r h e i rho) :
    HHi r h e (i - 1) - 1 <= z ∧ z <= HHi r h e (i - 1) := by
  have hlo := ordered_sum_eq_rho_inI_last_prev_H_lower_bound
    (r := r) (h := h) (e := e) (i := i) (rho := rho) (x := x) (y := y) (z := z)
    hp hi_pos hi hx hy hz hxy hyz hsum hrhoI
  have hbounds := ordered_sum_eq_rho_inI_last_bounds
    (r := r) (h := h) (e := e) (i := i) (rho := rho) (x := x) (y := y) (z := z)
    hp hi hx hy hz hxy hyz hsum hrhoI
  have hhi := residue_below_next_I_gap_le_prev_HHi
    (r := r) (h := h) (e := e) hp hi_pos hz hbounds.2
  exact ⟨hlo, hhi⟩

theorem ordered_sum_eq_rho_inI_last_in_prev_H
    {r h e i rho x y z : Nat} (hp : Params r h e) (hi_pos : 1 <= i)
    (hi : i < r) (hx : InResidue r h e x) (hy : InResidue r h e y)
    (hz : InResidue r h e z) (hxy : x < y) (hyz : y < z)
    (hsum : x + y + z = rho) (hrhoI : InI r h e i rho) :
    InH r h e (i - 1) z := by
  have htop := ordered_sum_eq_rho_inI_last_prev_H_top_two
    (r := r) (h := h) (e := e) (i := i) (rho := rho) (x := x) (y := y) (z := z)
    hp hi_pos hi hx hy hz hxy hyz hsum hrhoI
  have hleft : HLo r h e (i - 1) <= HHi r h e (i - 1) - 1 := by
    have hD := D_ge_three hp
    have hh := hp.h_ge_six
    unfold HHi HLo
    omega
  exact ⟨Nat.le_trans hleft htop.1, htop.2⟩

theorem ordered_sum_eq_rho_inI_last_prefix
    {r h e i rho x y z : Nat} (hp : Params r h e) (hi_pos : 1 <= i)
    (hi : i < r) (hx : InResidue r h e x) (hy : InResidue r h e y)
    (hz : InResidue r h e z) (hxy : x < y) (hyz : y < z)
    (hsum : x + y + z = rho) (hrhoI : InI r h e i rho) :
    InPrefix r h e z := by
  right
  right
  refine ⟨i - 1, ?_, ?_⟩
  · omega
  · exact ordered_sum_eq_rho_inI_last_in_prev_H
      (r := r) (h := h) (e := e) (i := i) (rho := rho) (x := x) (y := y) (z := z)
      hp hi_pos hi hx hy hz hxy hyz hsum hrhoI

end RBand
end GreedyThreeSumfree
