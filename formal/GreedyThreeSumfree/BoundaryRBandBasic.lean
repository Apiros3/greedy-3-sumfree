import Std

namespace GreedyThreeSumfree
namespace BoundaryRBand

/--
Normalized boundary `r`-band parameters.

The original variables are `h = g + 1` and, at the boundary,
`D = g + d = 2rh - 1`.
-/
structure Params (r h : Nat) : Prop where
  r_pos : 1 <= r
  h_ge_six : 6 <= h

/-- Closed interval membership for natural numbers. -/
def InInterval (lo hi n : Nat) : Prop := lo <= n ∧ n <= hi

/-- Boundary value `D = g + d = 2rh - 1`. -/
def D (r h : Nat) : Nat := 2 * r * h - 1

/-- The lower endpoint of `H_i`. -/
def HLo (r h i : Nat) : Nat := D r h + 2 * i * h

/-- The upper endpoint of `H_i`. -/
def HHi (r h i : Nat) : Nat := HLo r h i + h - 1

/-- The lower endpoint of `K_i = H_i - 1`. -/
def KLo (r h i : Nat) : Nat := HLo r h i - 1

/-- The upper endpoint of `K_i = H_i - 1`. -/
def KHi (r h i : Nat) : Nat := HHi r h i - 1

/-- The isolated boundary candidate `c = 4rh - 1`. -/
def c (r h : Nat) : Nat := 4 * r * h - 1

/-- The boundary period modulus `M = (10r - 2)h - 3`. -/
def M (r h : Nat) : Nat := (10 * r - 2) * h - 3

/-- The prefix interval `H_i`. -/
def InH (r h i n : Nat) : Prop :=
  InInterval (HLo r h i) (HHi r h i) n

/-- The shifted periodic interval `K_i = H_i - 1`. -/
def InK (r h i n : Nat) : Prop :=
  InInterval (KLo r h i) (KHi r h i) n

/-- Prefix union of the `r` intervals `H_i`. -/
def InU (r h n : Nat) : Prop :=
  ∃ i : Nat, i < r ∧ InH r h i n

/-- Periodic residue union of the shifted intervals `K_i`. -/
def InV (r h n : Nat) : Prop :=
  ∃ i : Nat, i < r ∧ InK r h i n

/-- Prefix set `P = {1,h-1,c} union U`. -/
def InPrefix (r h n : Nat) : Prop :=
  n = 1 ∨ n = h - 1 ∨ n = c r h ∨ InU r h n

/-- Residues available to the prefix or periodic part of the candidate set. -/
def InResidue (r h n : Nat) : Prop :=
  InPrefix r h n ∨ InV r h n

/-- A sum of three available residues. Distinctness/order is intentionally not encoded here. -/
def ResidueTripleSum (r h S : Nat) : Prop :=
  ∃ x y z : Nat,
    InResidue r h x ∧ InResidue r h y ∧ InResidue r h z ∧ x + y + z = S

/-- Periodic block membership `qM + V`. -/
def InPeriodicBlock (r h q n : Nat) : Prop :=
  ∃ rho : Nat, InV r h rho ∧ n = q * M r h + rho

/-- Candidate set `A = P union ⋃_{q>=1}(qM + V)`. -/
def Candidate (r h n : Nat) : Prop :=
  InPrefix r h n ∨ ∃ q : Nat, 1 <= q ∧ InPeriodicBlock r h q n

/-- Bottom endpoint of `V`. -/
def VBot (r h : Nat) : Nat := D r h - 1

/-- Top endpoint of `V`. -/
def VTop (r h : Nat) : Nat := D r h + (2 * r - 1) * h - 2

theorem two_r_pos {r h : Nat} (hp : Params r h) :
    1 <= 2 * r := by
  have hr := hp.r_pos
  omega

theorem two_r_sub_one_pos {r h : Nat} (hp : Params r h) :
    1 <= 2 * r - 1 := by
  have hr := hp.r_pos
  omega

theorem ten_r_sub_two_pos {r h : Nat} (hp : Params r h) :
    1 <= 10 * r - 2 := by
  have hr := hp.r_pos
  omega

theorem D_ge_h_add_one {r h : Nat} (hp : Params r h) :
    h + 1 <= D r h := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have hcoef : 2 <= 2 * r := by omega
  have hprod : 2 * h <= 2 * r * h := Nat.mul_le_mul_right h hcoef
  unfold D
  omega

theorem D_ge_three {r h : Nat} (hp : Params r h) :
    3 <= D r h := by
  have hD := D_ge_h_add_one hp
  have hh := hp.h_ge_six
  omega

theorem D_pos {r h : Nat} (hp : Params r h) :
    0 < D r h := by
  have hD := D_ge_three hp
  omega

/-- Each `H_i` interval is nonempty. -/
theorem HLo_le_HHi {r h i : Nat} (hp : Params r h) :
    HLo r h i <= HHi r h i := by
  have hh := hp.h_ge_six
  unfold HHi
  omega

theorem HLo_ge_three {r h i : Nat} (hp : Params r h) :
    3 <= HLo r h i := by
  have hD := D_ge_three hp
  unfold HLo
  omega

/-- Each shifted `K_i` interval is nonempty. -/
theorem KLo_le_KHi {r h i : Nat} (hp : Params r h) :
    KLo r h i <= KHi r h i := by
  have hh := hp.h_ge_six
  have hH := HLo_ge_three (r := r) (h := h) (i := i) hp
  unfold KLo KHi HHi
  omega

theorem KLo_ge_two {r h i : Nat} (hp : Params r h) :
    2 <= KLo r h i := by
  have hH := HLo_ge_three (r := r) (h := h) (i := i) hp
  unfold KLo
  omega

theorem H_nonempty {r h i : Nat} (hp : Params r h) :
    ∃ n : Nat, InH r h i n := by
  exact ⟨HLo r h i, by exact ⟨Nat.le_refl _, HLo_le_HHi hp⟩⟩

theorem K_nonempty {r h i : Nat} (hp : Params r h) :
    ∃ n : Nat, InK r h i n := by
  exact ⟨KLo r h i, by exact ⟨Nat.le_refl _, KLo_le_KHi hp⟩⟩

theorem M_pos {r h : Nat} (hp : Params r h) :
    0 < M r h := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have hcoef : 8 <= 10 * r - 2 := by omega
  have hprod : 8 * h <= (10 * r - 2) * h :=
    Nat.mul_le_mul_right h hcoef
  unfold M
  omega

theorem M_ge_one {r h : Nat} (hp : Params r h) :
    1 <= M r h := by
  have hM := M_pos hp
  omega

theorem HLo_zero_eq_D (r h : Nat) :
    HLo r h 0 = D r h := by
  unfold HLo
  omega

theorem HHi_eq_HLo_add {r h i : Nat} :
    HHi r h i = HLo r h i + h - 1 := by
  rfl

theorem KLo_eq_HLo_sub_one (r h i : Nat) :
    KLo r h i = HLo r h i - 1 := by
  rfl

theorem KHi_eq_HHi_sub_one (r h i : Nat) :
    KHi r h i = HHi r h i - 1 := by
  rfl

theorem KHi_eq_HLo_add_h_sub_two {r h i : Nat} :
    KHi r h i = HLo r h i + h - 2 := by
  unfold KHi HHi
  omega

theorem VBot_eq_K_zero (r h : Nat) :
    VBot r h = KLo r h 0 := by
  unfold VBot KLo HLo
  omega

theorem VTop_eq_KHi_last {r h : Nat} (hp : Params r h) :
    VTop r h = KHi r h (r - 1) := by
  have hr := hp.r_pos
  have hcoef : 2 * (r - 1) + 1 = 2 * r - 1 := by omega
  unfold VTop KHi HHi HLo
  calc
    D r h + (2 * r - 1) * h - 2
        = D r h + (2 * (r - 1) + 1) * h - 2 := by rw [hcoef]
    _ = D r h + (2 * (r - 1) * h + 1 * h) - 2 := by rw [Nat.add_mul]
    _ = D r h + 2 * (r - 1) * h + h - 2 := by omega

theorem HHi_last_lt_c {r h : Nat} (hp : Params r h) :
    HHi r h (r - 1) < c r h := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have hcoef : 2 * r + (2 * (r - 1) + 1) < 4 * r := by omega
  have hprod : (2 * r + (2 * (r - 1) + 1)) * h < (4 * r) * h :=
    Nat.mul_lt_mul_of_pos_right hcoef (by omega)
  rw [Nat.add_mul] at hprod
  have htail : 2 * (r - 1) * h + h = (2 * (r - 1) + 1) * h := by
    rw [Nat.add_mul]
    omega
  unfold HHi HLo D c
  omega

theorem D_lt_c {r h : Nat} (hp : Params r h) :
    D r h < c r h := by
  have hD := D_ge_three hp
  have hlast := HHi_last_lt_c hp
  have hDle : D r h <= HHi r h (r - 1) := by
    have hr := hp.r_pos
    have hH := HLo_le_HHi (r := r) (h := h) (i := r - 1) hp
    unfold HLo at hH
    omega
  omega

theorem c_lt_M {r h : Nat} (hp : Params r h) :
    c r h < M r h := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have hcoef : 4 * r + 1 <= 10 * r - 2 := by omega
  have hprod : (4 * r + 1) * h <= (10 * r - 2) * h :=
    Nat.mul_le_mul_right h hcoef
  rw [Nat.add_mul] at hprod
  unfold c M
  omega

theorem inV_lower {r h rho : Nat} (hp : Params r h)
    (hrho : InV r h rho) :
    VBot r h <= rho := by
  rcases hrho with ⟨i, _hi, hrhoK⟩
  have hD := D_ge_three hp
  have hlo : KLo r h 0 <= KLo r h i := by
    unfold KLo HLo
    omega
  have hbot : VBot r h = KLo r h 0 := VBot_eq_K_zero r h
  rw [hbot]
  exact Nat.le_trans hlo hrhoK.1

theorem inV_upper {r h rho : Nat} (hp : Params r h)
    (hrho : InV r h rho) :
    rho <= VTop r h := by
  rcases hrho with ⟨i, hi, hrhoK⟩
  have hr := hp.r_pos
  have hlast : i <= r - 1 := by omega
  have hcoef_le : 2 * i <= 2 * (r - 1) := Nat.mul_le_mul_left 2 hlast
  have hprod_le : 2 * i * h <= 2 * (r - 1) * h :=
    Nat.mul_le_mul_right h hcoef_le
  have htopK : KHi r h i <= KHi r h (r - 1) := by
    unfold KHi HHi HLo
    omega
  have htop : KHi r h (r - 1) = VTop r h := by
    exact (VTop_eq_KHi_last hp).symm
  rw [← htop]
  exact Nat.le_trans hrhoK.2 htopK

theorem VBot_inV {r h : Nat} (hp : Params r h) :
    InV r h (VBot r h) := by
  refine ⟨0, ?_, ?_⟩
  · have hr := hp.r_pos
    omega
  · rw [VBot_eq_K_zero]
    unfold InK InInterval
    exact ⟨Nat.le_refl _, KLo_le_KHi hp⟩

theorem VTop_inV {r h : Nat} (hp : Params r h) :
    InV r h (VTop r h) := by
  refine ⟨r - 1, ?_, ?_⟩
  · have hr := hp.r_pos
    omega
  · rw [VTop_eq_KHi_last hp]
    unfold InK InInterval
    exact ⟨KLo_le_KHi hp, Nat.le_refl _⟩

theorem VTop_lt_M {r h : Nat} (hp : Params r h) :
    VTop r h < M r h := by
  have htop : VTop r h = KHi r h (r - 1) := VTop_eq_KHi_last hp
  have hKltH : KHi r h (r - 1) < HHi r h (r - 1) := by
    have hH := HLo_ge_three (r := r) (h := h) (i := r - 1) hp
    unfold KHi HHi
    omega
  have hHc := HHi_last_lt_c hp
  have hcM := c_lt_M hp
  rw [htop]
  omega

theorem inV_lt_M {r h rho : Nat} (hp : Params r h)
    (hrho : InV r h rho) :
    rho < M r h := by
  have hupper := inV_upper hp hrho
  have htop := VTop_lt_M hp
  omega

theorem h_sub_one_lt_M {r h : Nat} (hp : Params r h) :
    h - 1 < M r h := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have hcoef : 8 <= 10 * r - 2 := by omega
  have hprod : 8 * h <= (10 * r - 2) * h :=
    Nat.mul_le_mul_right h hcoef
  unfold M
  omega

theorem one_lt_M {r h : Nat} (hp : Params r h) :
    1 < M r h := by
  have hM := h_sub_one_lt_M hp
  have hh := hp.h_ge_six
  omega

theorem HHi_lt_c {r h i : Nat} (hp : Params r h) (hi : i < r) :
    HHi r h i < c r h := by
  have hr := hp.r_pos
  have hlast : i <= r - 1 := by omega
  have hcoef_i : 2 * i <= 2 * (r - 1) := Nat.mul_le_mul_left 2 hlast
  have hprod_i : 2 * i * h <= 2 * (r - 1) * h :=
    Nat.mul_le_mul_right h hcoef_i
  have hlast_c := HHi_last_lt_c hp
  unfold HHi HLo at *
  omega

theorem HHi_lt_M {r h i : Nat} (hp : Params r h) (hi : i < r) :
    HHi r h i < M r h := by
  have hc := HHi_lt_c hp hi
  have hcm := c_lt_M hp
  omega

theorem inU_lt_c {r h rho : Nat} (hp : Params r h)
    (hrho : InU r h rho) :
    rho < c r h := by
  rcases hrho with ⟨i, hi, hrhoH⟩
  have htop := HHi_lt_c hp hi
  exact Nat.lt_of_le_of_lt hrhoH.2 htop

theorem inU_lt_M {r h rho : Nat} (hp : Params r h)
    (hrho : InU r h rho) :
    rho < M r h := by
  rcases hrho with ⟨i, hi, hrhoH⟩
  have htop := HHi_lt_M hp hi
  exact Nat.lt_of_le_of_lt hrhoH.2 htop

theorem prefix_lt_M {r h rho : Nat} (hp : Params r h)
    (hrho : InPrefix r h rho) :
    rho < M r h := by
  unfold InPrefix at hrho
  rcases hrho with rfl | rfl | rfl | hU
  · exact one_lt_M hp
  · exact h_sub_one_lt_M hp
  · exact c_lt_M hp
  · exact inU_lt_M hp hU

theorem residue_lt_M {r h rho : Nat} (hp : Params r h)
    (hrho : InResidue r h rho) :
    rho < M r h := by
  rcases hrho with hpfx | hV
  · exact prefix_lt_M hp hpfx
  · exact inV_lt_M hp hV

theorem periodic_block_ge_M {r h q n : Nat}
    (hq : 1 <= q) (hn : InPeriodicBlock r h q n) :
    M r h <= n := by
  rcases hn with ⟨rho, _hrho, rfl⟩
  have hM : M r h <= q * M r h := by
    have hmul : 1 * M r h <= q * M r h :=
      Nat.mul_le_mul_right (M r h) hq
    simpa using hmul
  exact Nat.le_trans hM (Nat.le_add_right _ _)

theorem residue_safety_squeeze {r h rho S : Nat} (hp : Params r h)
    (hrho : InV r h rho)
    (hSlo : 1 <= S)
    (hShi : S <= (12 * r - 2) * h - 6) :
    S < rho + M r h ∧ rho < S + M r h := by
  have hrho_lo := inV_lower hp hrho
  have hrho_lt_M := inV_lt_M hp hrho
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have hcoef : 2 * r + (10 * r - 2) = 12 * r - 2 := by omega
  have hprod : (2 * r) * h + (10 * r - 2) * h = (12 * r - 2) * h := by
    rw [← Nat.add_mul, hcoef]
  constructor
  · unfold VBot D M at *
    omega
  · omega

theorem residue_triple_safety_squeeze {r h rho S : Nat} (hp : Params r h)
    (hrho : InV r h rho)
    (_hSsum : ResidueTripleSum r h S)
    (hSlo : 1 <= S)
    (hShi : S <= (12 * r - 2) * h - 6) :
    S < rho + M r h ∧ rho < S + M r h :=
  residue_safety_squeeze hp hrho hSlo hShi

theorem mod_eq_forbidden_between_add {m s rho : Nat}
    (hmod : s % m = rho) (hrho_lt_s : rho < s) (hs_lt : s < rho + m) :
    False := by
  have hdvd : m ∣ s - rho := by
    have h0 : m ∣ s - s % m := Nat.dvd_sub_mod s
    simpa [hmod] using h0
  have hpos : 0 < s - rho := by omega
  have hdiff_lt : s - rho < m := by omega
  have hm_le : m <= s - rho := Nat.le_of_dvd hpos hdvd
  omega

theorem residue_mod_contradiction {r h rho S : Nat} (hp : Params r h)
    (hrho : InV r h rho)
    (hSlo : 1 <= S)
    (hShi : S <= (12 * r - 2) * h - 6)
    (hmod : S % M r h = rho) (hrho_lt_S : rho < S) :
    False := by
  have hsqueeze := residue_safety_squeeze hp hrho hSlo hShi
  exact mod_eq_forbidden_between_add hmod hrho_lt_S hsqueeze.1

theorem residue_triple_mod_contradiction {r h rho S : Nat} (hp : Params r h)
    (hrho : InV r h rho)
    (_hSsum : ResidueTripleSum r h S)
    (hSlo : 1 <= S)
    (hShi : S <= (12 * r - 2) * h - 6)
    (hmod : S % M r h = rho) (hrho_lt_S : rho < S) :
    False :=
  residue_mod_contradiction hp hrho hSlo hShi hmod hrho_lt_S

end BoundaryRBand
end GreedyThreeSumfree
