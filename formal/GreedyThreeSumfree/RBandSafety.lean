import GreedyThreeSumfree.RBandBasic

namespace GreedyThreeSumfree
namespace RBand

/--
An ordered sum of three distinct available residues.  The strict order packages
the distinctness needed by the regular r-band safety argument.
-/
def OrderedResidueTripleSum (r h e S : Nat) : Prop :=
  ∃ x y z : Nat,
    InResidue r h e x ∧ InResidue r h e y ∧ InResidue r h e z ∧
      x < y ∧ y < z ∧ x + y + z = S

theorem residue_ge_one {r h e x : Nat} (hp : Params r h e)
    (hx : InResidue r h e x) :
    1 <= x := by
  rcases hx with hpfx | hV
  · unfold InPrefix at hpfx
    rcases hpfx with rfl | rfl | hU
    · omega
    · have hh := hp.h_ge_six
      omega
    · rcases hU with ⟨i, _hi, hxH⟩
      have hH := HLo_ge_three (r := r) (h := h) (e := e) (i := i) hp
      have hxlo : HLo r h e i <= x := hxH.1
      omega
  · have hxlo := inV_lower hp hV
    have hD := D_ge_three hp
    unfold VBot at hxlo
    omega

theorem residue_ne_one_ge_h_sub_one {r h e x : Nat} (hp : Params r h e)
    (hx : InResidue r h e x) (hx_ne_one : x ≠ 1) :
    h - 1 <= x := by
  rcases hx with hpfx | hV
  · unfold InPrefix at hpfx
    rcases hpfx with rfl | rfl | hU
    · contradiction
    · exact Nat.le_refl _
    · rcases hU with ⟨i, _hi, hxH⟩
      have hD := D_ge_h_add_one hp
      unfold InH InInterval HLo at hxH
      omega
  · have hxlo := inV_lower hp hV
    have hD := D_ge_h_add_one hp
    unfold VBot at hxlo
    omega

theorem residue_gt_h_sub_one_ge_VBot {r h e x : Nat} (hp : Params r h e)
    (hx : InResidue r h e x) (hx_gt : h - 1 < x) :
    VBot r h e <= x := by
  rcases hx with hpfx | hV
  · unfold InPrefix at hpfx
    rcases hpfx with rfl | rfl | hU
    · have hh := hp.h_ge_six
      omega
    · omega
    · rcases hU with ⟨i, _hi, hxH⟩
      have hD := D_ge_three hp
      unfold InH InInterval HLo at hxH
      unfold VBot
      omega
  · exact inV_lower hp hV

private theorem HHi_le_VTop_add_two {r h e i : Nat} (hp : Params r h e)
    (hi : i < r) :
    HHi r h e i <= VTop r h e + 2 := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have hD := D_ge_three hp
  have hlast : i <= r - 1 := by omega
  have hcoef : 2 * i + 1 <= 2 * r - 1 := by omega
  have hprod : (2 * i + 1) * h <= (2 * r - 1) * h :=
    Nat.mul_le_mul_right h hcoef
  rw [Nat.add_mul, Nat.one_mul] at hprod
  unfold HHi HLo VTop
  omega

theorem residue_le_VTop_add_two {r h e x : Nat} (hp : Params r h e)
    (hx : InResidue r h e x) :
    x <= VTop r h e + 2 := by
  rcases hx with hpfx | hV
  · unfold InPrefix at hpfx
    rcases hpfx with rfl | rfl | hU
    · have hD := D_ge_h_add_one hp
      have hh := hp.h_ge_six
      unfold VTop
      omega
    · have hD := D_ge_h_add_one hp
      unfold VTop
      omega
    · rcases hU with ⟨i, hi, hxH⟩
      have htop := HHi_le_VTop_add_two (r := r) (h := h) (e := e) (i := i) hp hi
      exact Nat.le_trans hxH.2 htop
  · have htop := inV_upper hp hV
    omega

theorem ordered_residue_bounds {r h e x y z : Nat} (hp : Params r h e)
    (_hx : InResidue r h e x) (_hy : InResidue r h e y)
    (hz : InResidue r h e z) (hxy : x < y) (hyz : y < z) :
    x <= VTop r h e ∧ y <= VTop r h e + 1 ∧ z <= VTop r h e + 2 := by
  have hz_top := residue_le_VTop_add_two hp hz
  constructor
  · omega
  · constructor <;> omega

theorem ordered_residue_first_le_VTop {r h e x y z : Nat} (hp : Params r h e)
    (hx : InResidue r h e x) (hy : InResidue r h e y)
    (hz : InResidue r h e z) (hxy : x < y) (hyz : y < z) :
    x <= VTop r h e :=
  (ordered_residue_bounds hp hx hy hz hxy hyz).1

theorem ordered_residue_middle_le_VTop_add_one {r h e x y z : Nat}
    (hp : Params r h e) (hx : InResidue r h e x) (hy : InResidue r h e y)
    (hz : InResidue r h e z) (hxy : x < y) (hyz : y < z) :
    y <= VTop r h e + 1 :=
  (ordered_residue_bounds hp hx hy hz hxy hyz).2.1

theorem ordered_residue_last_le_VTop_add_two {r h e x y z : Nat}
    (hp : Params r h e) (_hx : InResidue r h e x) (_hy : InResidue r h e y)
    (hz : InResidue r h e z) (_hxy : x < y) (_hyz : y < z) :
    z <= VTop r h e + 2 :=
  residue_le_VTop_add_two hp hz

theorem ordered_residue_sum_lower {r h e S : Nat} (hp : Params r h e)
    (hS : OrderedResidueTripleSum r h e S) :
    D r h e + h - 2 <= S := by
  rcases hS with ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩
  have hxlo := residue_ge_one hp hx
  have hy_ne_one : y ≠ 1 := by omega
  have hylo := residue_ne_one_ge_h_sub_one hp hy hy_ne_one
  have hz_gt : h - 1 < z := by omega
  have hzlo := residue_gt_h_sub_one_ge_VBot hp hz hz_gt
  unfold VBot at hzlo
  omega

private theorem three_VTop_add_three_eq_sum_upper {r h e : Nat} (hp : Params r h e) :
    3 * VTop r h e + 3 = 3 * D r h e + (6 * r - 3) * h - 6 := by
  have hr := hp.r_pos
  have hD := D_ge_three hp
  have hcoef : 3 * (2 * r - 1) = 6 * r - 3 := by omega
  have hprod : 3 * ((2 * r - 1) * h) = (6 * r - 3) * h := by
    rw [← Nat.mul_assoc, hcoef]
  unfold VTop
  omega

theorem ordered_residue_sum_upper {r h e S : Nat} (hp : Params r h e)
    (hS : OrderedResidueTripleSum r h e S) :
    S <= 3 * D r h e + (6 * r - 3) * h - 6 := by
  rcases hS with ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩
  have hbounds := ordered_residue_bounds hp hx hy hz hxy hyz
  have hsum_le : S <= 3 * VTop r h e + 3 := by omega
  rw [three_VTop_add_three_eq_sum_upper hp] at hsum_le
  exact hsum_le

theorem ordered_residue_safety_squeeze {r h e rho S : Nat} (hp : Params r h e)
    (hrho : InV r h e rho) (hS : OrderedResidueTripleSum r h e S) :
    S < rho + M r h e ∧ rho < S + M r h e :=
  residue_safety_squeeze hp hrho
    (ordered_residue_sum_lower hp hS)
    (ordered_residue_sum_upper hp hS)

end RBand
end GreedyThreeSumfree
