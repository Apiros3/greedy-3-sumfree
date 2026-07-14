import GreedyThreeSumfree.BoundaryRBandBasic

namespace GreedyThreeSumfree
namespace BoundaryRBand

/--
An ordered sum of three distinct available residues.  The strict order packages
the distinctness needed by the boundary r-band safety argument.
-/
def OrderedResidueTripleSum (r h S : Nat) : Prop :=
  ∃ x y z : Nat,
    InResidue r h x ∧ InResidue r h y ∧ InResidue r h z ∧
      x < y ∧ y < z ∧ x + y + z = S

/--
An ordered triple of distinct earlier boundary candidates summing to `target`.
-/
def CandidateTripleSumFrom (r h target : Nat) : Prop :=
  ∃ x y z : Nat,
    Candidate r h x ∧ Candidate r h y ∧ Candidate r h z ∧
      x < y ∧ y < z ∧ z < target ∧ x + y + z = target

theorem add_three_mod (x y z m : Nat) :
    (x + y + z) % m = (x % m + y % m + z % m) % m := by
  simp [Nat.add_mod]

theorem triple_sum_mod {x y z target m : Nat} (hsum : x + y + z = target) :
    (x % m + y % m + z % m) % m = target % m := by
  rw [← hsum]
  symm
  exact add_three_mod x y z m

theorem prefix_mod_eq {r h n : Nat} (hp : Params r h)
    (hn : InPrefix r h n) :
    n % M r h = n :=
  Nat.mod_eq_of_lt (prefix_lt_M hp hn)

theorem periodic_block_mod_eq {r h q rho n : Nat} (hp : Params r h)
    (hrho : InV r h rho) (hn : n = q * M r h + rho) :
    n % M r h = rho := by
  rw [hn]
  rw [Nat.mul_comm q (M r h)]
  rw [Nat.mul_add_mod_self_left]
  exact Nat.mod_eq_of_lt (inV_lt_M hp hrho)

theorem in_periodic_block_mod_eq {r h q n : Nat} (hp : Params r h)
    (hn : InPeriodicBlock r h q n) :
    ∃ rho : Nat, InV r h rho ∧ n % M r h = rho := by
  rcases hn with ⟨rho, hrho, hn_eq⟩
  exact ⟨rho, hrho, periodic_block_mod_eq hp hrho hn_eq⟩

/-- Every boundary candidate has a residue modulo `M` lying in `P union V`. -/
theorem candidate_mod_in_residue {r h n : Nat} (hp : Params r h)
    (hn : Candidate r h n) :
    InResidue r h (n % M r h) := by
  rcases hn with hpfx | hblock
  · rw [prefix_mod_eq hp hpfx]
    exact Or.inl hpfx
  · rcases hblock with ⟨q, _hq, hnblock⟩
    rcases in_periodic_block_mod_eq (r := r) (h := h) (q := q) hp hnblock with
      ⟨rho, hrho, hmod⟩
    rw [hmod]
    exact Or.inr hrho

theorem residue_ge_one {r h x : Nat} (hp : Params r h)
    (hx : InResidue r h x) :
    1 <= x := by
  rcases hx with hpfx | hV
  · unfold InPrefix at hpfx
    rcases hpfx with rfl | rfl | rfl | hU
    · omega
    · have hh := hp.h_ge_six
      omega
    · have hc := D_lt_c hp
      have hD := D_ge_three hp
      unfold c at *
      omega
    · rcases hU with ⟨i, _hi, hxH⟩
      have hH := HLo_ge_three (r := r) (h := h) (i := i) hp
      exact Nat.le_trans (by omega) hxH.1
  · have hxlo := inV_lower hp hV
    have hD := D_ge_three hp
    unfold VBot at hxlo
    omega

theorem residue_ne_one_ge_h_sub_one {r h x : Nat} (hp : Params r h)
    (hx : InResidue r h x) (hx_ne_one : x ≠ 1) :
    h - 1 <= x := by
  rcases hx with hpfx | hV
  · unfold InPrefix at hpfx
    rcases hpfx with rfl | rfl | rfl | hU
    · contradiction
    · exact Nat.le_refl _
    · have hD := D_ge_h_add_one hp
      have hDc := D_lt_c hp
      unfold c at *
      omega
    · rcases hU with ⟨i, _hi, hxH⟩
      have hD := D_ge_h_add_one hp
      unfold InH InInterval HLo at hxH
      omega
  · have hxlo := inV_lower hp hV
    have hD := D_ge_h_add_one hp
    unfold VBot at hxlo
    omega

theorem residue_gt_h_sub_one_ge_VBot {r h x : Nat} (hp : Params r h)
    (hx : InResidue r h x) (hx_gt : h - 1 < x) :
    VBot r h <= x := by
  rcases hx with hpfx | hV
  · unfold InPrefix at hpfx
    rcases hpfx with rfl | rfl | rfl | hU
    · have hh := hp.h_ge_six
      omega
    · omega
    · have hDc := D_lt_c hp
      unfold VBot
      omega
    · rcases hU with ⟨i, _hi, hxH⟩
      have hD := D_ge_three hp
      unfold InH InInterval HLo at hxH
      unfold VBot
      omega
  · exact inV_lower hp hV

theorem VTop_lt_c {r h : Nat} (hp : Params r h) :
    VTop r h < c r h := by
  have htop : VTop r h = KHi r h (r - 1) := VTop_eq_KHi_last hp
  have hKltH : KHi r h (r - 1) < HHi r h (r - 1) := by
    have hH := HLo_ge_three (r := r) (h := h) (i := r - 1) hp
    have hle := HLo_le_HHi (r := r) (h := h) (i := r - 1) hp
    have hHpos : 1 <= HHi r h (r - 1) := by omega
    unfold KHi
    omega
  have hHc := HHi_last_lt_c hp
  rw [htop]
  omega

theorem residue_le_c {r h x : Nat} (hp : Params r h)
    (hx : InResidue r h x) :
    x <= c r h := by
  rcases hx with hpfx | hV
  · unfold InPrefix at hpfx
    rcases hpfx with rfl | rfl | rfl | hU
    · have hDc := D_lt_c hp
      have hD := D_ge_h_add_one hp
      omega
    · have hDc := D_lt_c hp
      have hD := D_ge_h_add_one hp
      omega
    · exact Nat.le_refl _
    · have hlt := inU_lt_c hp hU
      omega
  · have htop := inV_upper hp hV
    have htopc := VTop_lt_c hp
    omega

theorem HHi_last_eq_VTop_add_one {r h : Nat} (hp : Params r h) :
    HHi r h (r - 1) = VTop r h + 1 := by
  have htop : VTop r h = KHi r h (r - 1) := VTop_eq_KHi_last hp
  have hH := HLo_ge_three (r := r) (h := h) (i := r - 1) hp
  have hHpos : 1 <= HHi r h (r - 1) := by
    have hle := HLo_le_HHi (r := r) (h := h) (i := r - 1) hp
    omega
  rw [htop]
  unfold KHi
  omega

theorem HHi_mono_index {r h i j : Nat} (hij : i <= j) :
    HHi r h i <= HHi r h j := by
  have hcoef : 2 * i <= 2 * j := Nat.mul_le_mul_left 2 hij
  have hprod : 2 * i * h <= 2 * j * h := Nat.mul_le_mul_right h hcoef
  unfold HHi HLo
  omega

theorem residue_lt_c_le_HHi_last {r h x : Nat} (hp : Params r h)
    (hx : InResidue r h x) (hxltc : x < c r h) :
    x <= HHi r h (r - 1) := by
  rcases hx with hpfx | hV
  · unfold InPrefix at hpfx
    rcases hpfx with rfl | rfl | rfl | hU
    · have hD := D_ge_three hp
      have hH := HLo_le_HHi (r := r) (h := h) (i := r - 1) hp
      have hr := hp.r_pos
      unfold HLo at hH
      omega
    · have hD := D_ge_h_add_one hp
      have hH := HLo_le_HHi (r := r) (h := h) (i := r - 1) hp
      have hr := hp.r_pos
      unfold HLo at hH
      omega
    · omega
    · rcases hU with ⟨i, hi, hxH⟩
      have hlast : i <= r - 1 := by
        have hr := hp.r_pos
        omega
      have hmono := HHi_mono_index (r := r) (h := h) hlast
      exact Nat.le_trans hxH.2 hmono
  · have htop := inV_upper hp hV
    have heq := HHi_last_eq_VTop_add_one hp
    omega

theorem ordered_residue_bounds {r h x y z : Nat} (hp : Params r h)
    (_hx : InResidue r h x) (hy : InResidue r h y)
    (hz : InResidue r h z) (hxy : x < y) (hyz : y < z) :
    x <= VTop r h ∧ y <= HHi r h (r - 1) ∧ z <= c r h := by
  have hzle := residue_le_c hp hz
  have hyltc : y < c r h := by omega
  have hyle := residue_lt_c_le_HHi_last hp hy hyltc
  have hxltH : x < HHi r h (r - 1) := by omega
  have heq := HHi_last_eq_VTop_add_one hp
  constructor
  · omega
  · exact ⟨hyle, hzle⟩

theorem ordered_residue_sum_lower {r h S : Nat} (hp : Params r h)
    (hS : OrderedResidueTripleSum r h S) :
    D r h + h - 1 <= S := by
  rcases hS with ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩
  have hxlo := residue_ge_one hp hx
  have hy_ne_one : y ≠ 1 := by omega
  have hylo := residue_ne_one_ge_h_sub_one hp hy hy_ne_one
  have hz_gt : h - 1 < z := by omega
  have hzlo := residue_gt_h_sub_one_ge_VBot hp hz hz_gt
  unfold VBot at hzlo
  omega

private theorem two_VTop_add_one_add_c_eq_sum_upper {r h : Nat}
    (hp : Params r h) :
    2 * VTop r h + 1 + c r h = (12 * r - 2) * h - 6 := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have hcoefA : 2 * (2 * r) = 4 * r := by omega
  have hprodA : 2 * ((2 * r) * h) = (4 * r) * h := by
    rw [← Nat.mul_assoc, hcoefA]
  have hcoefB : 2 * (2 * r - 1) = 4 * r - 2 := by omega
  have hprodB : 2 * ((2 * r - 1) * h) = (4 * r - 2) * h := by
    rw [← Nat.mul_assoc, hcoefB]
  have hcoefC : 4 * r + (4 * r - 2) + 4 * r = 12 * r - 2 := by omega
  have hprod :
      (4 * r) * h + (4 * r - 2) * h + (4 * r) * h =
          (12 * r - 2) * h := by
    calc
      (4 * r) * h + (4 * r - 2) * h + (4 * r) * h
          = (4 * r + (4 * r - 2)) * h + (4 * r) * h := by
              rw [← Nat.add_mul]
      _ = (4 * r + (4 * r - 2) + 4 * r) * h := by
              rw [← Nat.add_mul]
      _ = (12 * r - 2) * h := by rw [hcoefC]
  have hD_eq : D r h + 1 = (2 * r) * h := by
    have hD := D_ge_three hp
    unfold D at hD ⊢
    omega
  have hV_eq : VTop r h + 2 = D r h + (2 * r - 1) * h := by
    have hD := D_ge_three hp
    unfold VTop at ⊢
    omega
  have hc_eq : c r h + 1 = (4 * r) * h := by
    have hc := D_lt_c hp
    unfold c at hc ⊢
    omega
  omega

private theorem VTop_add_HHi_last_add_c_eq_sum_upper {r h : Nat}
    (hp : Params r h) :
    VTop r h + HHi r h (r - 1) + c r h = (12 * r - 2) * h - 6 := by
  have hH := HHi_last_eq_VTop_add_one hp
  have htwo := two_VTop_add_one_add_c_eq_sum_upper hp
  omega

theorem ordered_residue_sum_upper {r h S : Nat} (hp : Params r h)
    (hS : OrderedResidueTripleSum r h S) :
    S <= (12 * r - 2) * h - 6 := by
  rcases hS with ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩
  have hbounds := ordered_residue_bounds hp hx hy hz hxy hyz
  have hsum_le : S <= VTop r h + HHi r h (r - 1) + c r h := by omega
  rw [VTop_add_HHi_last_add_c_eq_sum_upper hp] at hsum_le
  exact hsum_le

theorem ordered_residue_safety_squeeze {r h rho S : Nat} (hp : Params r h)
    (hrho : InV r h rho) (hS : OrderedResidueTripleSum r h S) :
    S < rho + M r h ∧ rho < S + M r h :=
  residue_safety_squeeze hp hrho
    (by
      have hlo := ordered_residue_sum_lower hp hS
      have hD := D_ge_three hp
      omega)
    (ordered_residue_sum_upper hp hS)

theorem residue_mod_contradiction_below {r h rho S : Nat}
    (hmod : S % M r h = rho) (hS_lt_rho : S < rho) :
    False := by
  have hle : rho <= S := by
    have hmod_le := Nat.mod_le S (M r h)
    simpa [hmod] using hmod_le
  omega

theorem ordered_residue_mod_eq_forces_eq {r h rho S : Nat}
    (hp : Params r h) (hrho : InV r h rho)
    (hS : OrderedResidueTripleSum r h S)
    (hmod : S % M r h = rho) :
    S = rho := by
  by_cases hEq : S = rho
  · exact hEq
  · by_cases hrho_lt_S : rho < S
    · have hlo := ordered_residue_sum_lower hp hS
      have hhi := ordered_residue_sum_upper hp hS
      exact False.elim
        (residue_mod_contradiction hp hrho
          (by
            have hD := D_ge_three hp
            omega)
          hhi hmod hrho_lt_S)
    · have hS_lt_rho : S < rho := by omega
      exact False.elim (residue_mod_contradiction_below hmod hS_lt_rho)

theorem ordered_residue_witness_mod_eq_forces_eq {r h rho x y z S : Nat}
    (hp : Params r h) (hrho : InV r h rho)
    (hx : InResidue r h x) (hy : InResidue r h y)
    (hz : InResidue r h z) (hxy : x < y) (hyz : y < z)
    (hsum : x + y + z = S) (hmod : S % M r h = rho) :
    x + y + z = rho := by
  have hS : OrderedResidueTripleSum r h S :=
    ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩
  have hSeq := ordered_residue_mod_eq_forces_eq hp hrho hS hmod
  omega

end BoundaryRBand
end GreedyThreeSumfree
