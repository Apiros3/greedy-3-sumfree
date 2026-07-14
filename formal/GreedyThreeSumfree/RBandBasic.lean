import Std

namespace GreedyThreeSumfree
namespace RBand

/--
Normalized regular `r`-band parameters.

The original variables are `h = g + 1` and `D = g + d`.  The regular band
range is encoded by `D = (2r - 1)h + e`, with `1 <= e <= h - 2`.
-/
structure Params (r h e : Nat) : Prop where
  r_pos : 1 <= r
  h_ge_six : 6 <= h
  e_pos : 1 <= e
  e_le_h_sub_two : e <= h - 2

/-- Closed interval membership for natural numbers. -/
def InInterval (lo hi n : Nat) : Prop := lo <= n ∧ n <= hi

/-- Normalized value `D = g + d = (2r - 1)h + e`. -/
def D (r h e : Nat) : Nat := (2 * r - 1) * h + e

/-- The lower endpoint of `H_i`. -/
def HLo (r h e i : Nat) : Nat := D r h e + 2 * i * h

/-- The upper endpoint of `H_i`. -/
def HHi (r h e i : Nat) : Nat := HLo r h e i + h - 1

/-- The lower endpoint of `I_i = H_i - 2`. -/
def ILo (r h e i : Nat) : Nat := HLo r h e i - 2

/-- The upper endpoint of `I_i = H_i - 2`. -/
def IHi (r h e i : Nat) : Nat := HLo r h e i + h - 3

/-- The period modulus `M = 2D + (6r - 3)h - 3`. -/
def M (r h e : Nat) : Nat := 2 * D r h e + (6 * r - 3) * h - 3

/-- The prefix interval `H_i`. -/
def InH (r h e i n : Nat) : Prop :=
  InInterval (HLo r h e i) (HHi r h e i) n

/-- The shifted periodic interval `I_i = H_i - 2`. -/
def InI (r h e i n : Nat) : Prop :=
  InInterval (ILo r h e i) (IHi r h e i) n

/-- Prefix union of the `r` intervals `H_i`. -/
def InU (r h e n : Nat) : Prop :=
  ∃ i : Nat, i < r ∧ InH r h e i n

/-- Periodic residue union of the shifted intervals `I_i`. -/
def InV (r h e n : Nat) : Prop :=
  ∃ i : Nat, i < r ∧ InI r h e i n

/-- Prefix set `P = {1,h-1} union U`. -/
def InPrefix (r h e n : Nat) : Prop :=
  n = 1 ∨ n = h - 1 ∨ InU r h e n

/-- Residues available to the prefix or periodic part of the candidate set. -/
def InResidue (r h e n : Nat) : Prop :=
  InPrefix r h e n ∨ InV r h e n

/-- A sum of three available residues.  Distinctness/order is intentionally not encoded here. -/
def ResidueTripleSum (r h e S : Nat) : Prop :=
  ∃ x y z : Nat,
    InResidue r h e x ∧ InResidue r h e y ∧ InResidue r h e z ∧
      x + y + z = S

/-- Periodic block membership `qM + V`. -/
def InPeriodicBlock (r h e q n : Nat) : Prop :=
  ∃ rho : Nat, InV r h e rho ∧ n = q * M r h e + rho

/-- Candidate set `A = P union ⋃_{q>=1}(qM + V)`. -/
def Candidate (r h e n : Nat) : Prop :=
  InPrefix r h e n ∨ ∃ q : Nat, 1 <= q ∧ InPeriodicBlock r h e q n

/-- Bottom endpoint of `V`. -/
def VBot (r h e : Nat) : Nat := D r h e - 2

/-- Top endpoint of `V`. -/
def VTop (r h e : Nat) : Nat := D r h e + (2 * r - 1) * h - 3

theorem two_r_sub_one_pos {r h e : Nat} (hp : Params r h e) :
    1 <= 2 * r - 1 := by
  have hr := hp.r_pos
  omega

theorem D_ge_h_add_one {r h e : Nat} (hp : Params r h e) :
    h + 1 <= D r h e := by
  have hcoef := two_r_sub_one_pos hp
  have hmul : 1 * h <= (2 * r - 1) * h :=
    Nat.mul_le_mul_right h hcoef
  have he := hp.e_pos
  unfold D
  omega

theorem D_ge_three {r h e : Nat} (hp : Params r h e) :
    3 <= D r h e := by
  have hD := D_ge_h_add_one hp
  have hh := hp.h_ge_six
  omega

/-- Each `H_i` interval is nonempty. -/
theorem HLo_le_HHi {r h e i : Nat} (hp : Params r h e) :
    HLo r h e i <= HHi r h e i := by
  have hh := hp.h_ge_six
  unfold HHi
  omega

theorem HLo_ge_three {r h e i : Nat} (hp : Params r h e) :
    3 <= HLo r h e i := by
  have hD := D_ge_three hp
  unfold HLo
  omega

/-- Each shifted `I_i` interval is nonempty. -/
theorem ILo_le_IHi {r h e i : Nat} (hp : Params r h e) :
    ILo r h e i <= IHi r h e i := by
  have hh := hp.h_ge_six
  have hH := HLo_ge_three (r := r) (h := h) (e := e) (i := i) hp
  unfold ILo IHi
  omega

theorem H_nonempty {r h e i : Nat} (hp : Params r h e) :
    ∃ n : Nat, InH r h e i n := by
  exact ⟨HLo r h e i, by exact ⟨Nat.le_refl _, HLo_le_HHi hp⟩⟩

theorem I_nonempty {r h e i : Nat} (hp : Params r h e) :
    ∃ n : Nat, InI r h e i n := by
  exact ⟨ILo r h e i, by exact ⟨Nat.le_refl _, ILo_le_IHi hp⟩⟩

theorem M_pos {r h e : Nat} (hp : Params r h e) :
    0 < M r h e := by
  have hD := D_ge_h_add_one hp
  have hh := hp.h_ge_six
  unfold M
  omega

theorem M_ge_one {r h e : Nat} (hp : Params r h e) :
    1 <= M r h e := by
  have hM := M_pos hp
  omega

theorem HHi_eq_HLo_add {r h e i : Nat} :
    HHi r h e i = HLo r h e i + h - 1 := by
  rfl

theorem ILo_eq_HLo_sub_two (r h e i : Nat) :
    ILo r h e i = HLo r h e i - 2 := by
  rfl

theorem IHi_eq_HHi_sub_two (r h e i : Nat) :
    IHi r h e i = HHi r h e i - 2 := by
  unfold IHi HHi
  omega

theorem IHi_eq_HLo_add_h_sub_three {r h e i : Nat} :
    IHi r h e i = HLo r h e i + h - 3 := by
  rfl

theorem VBot_eq_I_zero (r h e : Nat) :
    VBot r h e = ILo r h e 0 := by
  unfold VBot ILo HLo
  omega

theorem VTop_eq_IHi_last {r h e : Nat} (hp : Params r h e) :
    VTop r h e = IHi r h e (r - 1) := by
  have hr := hp.r_pos
  have hcoef : 2 * (r - 1) + 1 = 2 * r - 1 := by omega
  unfold VTop IHi HLo
  calc
    D r h e + (2 * r - 1) * h - 3
        = D r h e + (2 * (r - 1) + 1) * h - 3 := by rw [hcoef]
    _ = D r h e + (2 * (r - 1) * h + 1 * h) - 3 := by rw [Nat.add_mul]
    _ = D r h e + 2 * (r - 1) * h + h - 3 := by omega

theorem inV_lower {r h e rho : Nat} (hp : Params r h e)
    (hrho : InV r h e rho) :
    VBot r h e <= rho := by
  rcases hrho with ⟨i, _hi, hrhoI⟩
  have hD := D_ge_three hp
  have hlo : ILo r h e 0 <= ILo r h e i := by
    unfold ILo HLo
    omega
  have hbot : VBot r h e = ILo r h e 0 := VBot_eq_I_zero r h e
  rw [hbot]
  exact Nat.le_trans hlo hrhoI.1

theorem inV_upper {r h e rho : Nat} (hp : Params r h e)
    (hrho : InV r h e rho) :
    rho <= VTop r h e := by
  rcases hrho with ⟨i, hi, hrhoI⟩
  have hr := hp.r_pos
  have hlast : i <= r - 1 := by omega
  have hcoef_le : 2 * i <= 2 * (r - 1) := Nat.mul_le_mul_left 2 hlast
  have hprod_le : 2 * i * h <= 2 * (r - 1) * h :=
    Nat.mul_le_mul_right h hcoef_le
  have htopI : IHi r h e i <= IHi r h e (r - 1) := by
    unfold IHi HLo
    omega
  have htop : IHi r h e (r - 1) = VTop r h e := by
    exact (VTop_eq_IHi_last hp).symm
  rw [← htop]
  exact Nat.le_trans hrhoI.2 htopI

theorem VBot_inV {r h e : Nat} (hp : Params r h e) :
    InV r h e (VBot r h e) := by
  refine ⟨0, ?_, ?_⟩
  · have hr := hp.r_pos
    omega
  · rw [VBot_eq_I_zero]
    unfold InI InInterval
    exact ⟨Nat.le_refl _, ILo_le_IHi hp⟩

theorem VTop_inV {r h e : Nat} (hp : Params r h e) :
    InV r h e (VTop r h e) := by
  refine ⟨r - 1, ?_, ?_⟩
  · have hr := hp.r_pos
    omega
  · rw [VTop_eq_IHi_last hp]
    unfold InI InInterval
    exact ⟨ILo_le_IHi hp, Nat.le_refl _⟩

theorem VTop_lt_M {r h e : Nat} (hp : Params r h e) :
    VTop r h e < M r h e := by
  have hD := D_ge_h_add_one hp
  have hh := hp.h_ge_six
  have hcoef : 2 * r - 1 <= 6 * r - 3 := by
    have hr := hp.r_pos
    omega
  have hprod : (2 * r - 1) * h <= (6 * r - 3) * h :=
    Nat.mul_le_mul_right h hcoef
  unfold VTop M
  omega

theorem inV_lt_M {r h e rho : Nat} (hp : Params r h e)
    (hrho : InV r h e rho) :
    rho < M r h e := by
  have hupper := inV_upper hp hrho
  have htop := VTop_lt_M hp
  omega

theorem h_sub_one_lt_M {r h e : Nat} (hp : Params r h e) :
    h - 1 < M r h e := by
  have hD := D_ge_h_add_one hp
  have hh := hp.h_ge_six
  unfold M
  omega

theorem one_lt_M {r h e : Nat} (hp : Params r h e) :
    1 < M r h e := by
  have hM := h_sub_one_lt_M hp
  have hh := hp.h_ge_six
  omega

theorem HHi_lt_M {r h e i : Nat} (hp : Params r h e) (hi : i < r) :
    HHi r h e i < M r h e := by
  have hD := D_ge_h_add_one hp
  have hh := hp.h_ge_six
  have hlast : i <= r - 1 := by
    have hr := hp.r_pos
    omega
  have hcoef_i : 2 * i <= 2 * (r - 1) := Nat.mul_le_mul_left 2 hlast
  have hprod_i : 2 * i * h <= 2 * (r - 1) * h :=
    Nat.mul_le_mul_right h hcoef_i
  have hcoef_last : 2 * (r - 1) + 1 = 2 * r - 1 := by
    have hr := hp.r_pos
    omega
  have hcoef_M : 2 * r - 1 <= 6 * r - 3 := by
    have hr := hp.r_pos
    omega
  have hprod_M : (2 * r - 1) * h <= (6 * r - 3) * h :=
    Nat.mul_le_mul_right h hcoef_M
  unfold HHi HLo M
  rw [← hcoef_last] at hprod_M
  rw [Nat.add_mul] at hprod_M
  omega

theorem inU_lt_M {r h e rho : Nat} (hp : Params r h e)
    (hrho : InU r h e rho) :
    rho < M r h e := by
  rcases hrho with ⟨i, hi, hrhoH⟩
  have htop := HHi_lt_M hp hi
  exact Nat.lt_of_le_of_lt hrhoH.2 htop

theorem prefix_lt_M {r h e rho : Nat} (hp : Params r h e)
    (hrho : InPrefix r h e rho) :
    rho < M r h e := by
  unfold InPrefix at hrho
  rcases hrho with rfl | rfl | hU
  · exact one_lt_M hp
  · exact h_sub_one_lt_M hp
  · exact inU_lt_M hp hU

theorem residue_lt_M {r h e rho : Nat} (hp : Params r h e)
    (hrho : InResidue r h e rho) :
    rho < M r h e := by
  rcases hrho with hpfx | hV
  · exact prefix_lt_M hp hpfx
  · exact inV_lt_M hp hV

theorem periodic_block_ge_M {r h e q n : Nat}
    (hq : 1 <= q) (hn : InPeriodicBlock r h e q n) :
    M r h e <= n := by
  rcases hn with ⟨rho, _hrho, rfl⟩
  have hM : M r h e <= q * M r h e := by
    have hmul : 1 * M r h e <= q * M r h e :=
      Nat.mul_le_mul_right (M r h e) hq
    simpa using hmul
  exact Nat.le_trans hM (Nat.le_add_right _ _)

theorem residue_safety_squeeze {r h e rho S : Nat} (hp : Params r h e)
    (hrho : InV r h e rho)
    (hSlo : D r h e + h - 2 <= S)
    (hShi : S <= 3 * D r h e + (6 * r - 3) * h - 6) :
    S < rho + M r h e ∧ rho < S + M r h e := by
  have hrho_lo := inV_lower hp hrho
  have hrho_hi := inV_upper hp hrho
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have he := hp.e_pos
  constructor
  · unfold VBot M D at *
    omega
  · unfold VTop M D at *
    omega

theorem residue_triple_safety_squeeze {r h e rho S : Nat} (hp : Params r h e)
    (hrho : InV r h e rho)
    (_hSsum : ResidueTripleSum r h e S)
    (hSlo : D r h e + h - 2 <= S)
    (hShi : S <= 3 * D r h e + (6 * r - 3) * h - 6) :
    S < rho + M r h e ∧ rho < S + M r h e :=
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

theorem residue_mod_contradiction {r h e rho S : Nat} (hp : Params r h e)
    (hrho : InV r h e rho)
    (hSlo : D r h e + h - 2 <= S)
    (hShi : S <= 3 * D r h e + (6 * r - 3) * h - 6)
    (hmod : S % M r h e = rho) (hrho_lt_S : rho < S) :
    False := by
  have hsqueeze := residue_safety_squeeze hp hrho hSlo hShi
  exact mod_eq_forbidden_between_add hmod hrho_lt_S hsqueeze.1

theorem residue_triple_mod_contradiction {r h e rho S : Nat} (hp : Params r h e)
    (hrho : InV r h e rho)
    (_hSsum : ResidueTripleSum r h e S)
    (hSlo : D r h e + h - 2 <= S)
    (hShi : S <= 3 * D r h e + (6 * r - 3) * h - 6)
    (hmod : S % M r h e = rho) (hrho_lt_S : rho < S) :
    False :=
  residue_mod_contradiction hp hrho hSlo hShi hmod hrho_lt_S

end RBand
end GreedyThreeSumfree
