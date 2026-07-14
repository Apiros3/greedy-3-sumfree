import Std

namespace GreedyThreeSumfree
namespace TransitionDenseCap

/--
Parameters for the dense-cap transition lifting theorem.

The transition seed is `D = 2*r*h + t`; the dense-cap range is encoded as
`h + 2 <= 2*t` and `t <= h - 2`.
-/
structure Params (r h t : Nat) : Prop where
  r_pos : 1 <= r
  h_ge_six : 6 <= h
  dense_lower : h + 2 <= 2 * t
  dense_upper : t <= h - 2

/-- Closed interval membership for natural numbers. -/
def InInterval (lo hi n : Nat) : Prop := lo <= n ∧ n <= hi

/-- Transition seed `D = 2*r*h + t`. -/
def D (r h t : Nat) : Nat := 2 * r * h + t

/-- Dense-cap period modulus `M = 10*D + 3`. -/
def M (r h t : Nat) : Nat := 10 * D r h t + 3

/-- Shift a predicate by an additive base. -/
def Shift (base : Nat) (P : Nat → Prop) (n : Nat) : Prop :=
  ∃ u : Nat, P u ∧ n = base + u

/-- One full `h`-block of the square-wave packet. -/
def InFullPacketRun (r h i n : Nat) : Prop :=
  i < r ∧ InInterval (2 * i * h) (2 * i * h + h - 1) n

/-- The terminal cap of `Q_s`. -/
def InTerminalCap (r h t s n : Nat) : Prop :=
  InInterval (2 * r * h) (2 * r * h + t + 1 - s) n

/--
The square-wave packet

`Q_s = union_{0 <= i < r} [2*i*h, 2*i*h+h-1]
       union [2*r*h, 2*r*h+t+1-s]`.
-/
def InQ (r h t s n : Nat) : Prop :=
  (∃ i : Nat, InFullPacketRun r h i n) ∨ InTerminalCap r h t s n

/-- Prefix packet `E = D + Q_0`. -/
def InE (r h t n : Nat) : Prop := Shift (D r h t) (InQ r h t 0) n

/-- Low tail packet `X = D + Q_1`. -/
def InX (r h t n : Nat) : Prop := Shift (D r h t) (InQ r h t 1) n

/-- Auxiliary packet `W = D + Q_2`. -/
def InW (r h t n : Nat) : Prop := Shift (D r h t) (InQ r h t 2) n

/-- Prefix high packet `F = 5*D + 1 + X`. -/
def InF (r h t n : Nat) : Prop := Shift (5 * D r h t + 1) (InX r h t) n

/-- High tail packet `Y = 5*D + 2 + W`. -/
def InY (r h t n : Nat) : Prop := Shift (5 * D r h t + 2) (InW r h t) n

/-- Tail residue set `R = X union Y`. -/
def InTailResidue (r h t n : Nat) : Prop := InX r h t n ∨ InY r h t n

/-- Periodic block `q*M + R`, with positive block index. -/
def InPeriodicBlock (r h t q n : Nat) : Prop :=
  Shift (q * M r h t) (InTailResidue r h t) n

/-- Dense-cap candidate from the transition lifting theorem. -/
def Candidate (r h t n : Nat) : Prop :=
  n = 1 ∨ n = h - 1 ∨ InE r h t n ∨ InF r h t n ∨
    ∃ q : Nat, 1 <= q ∧ InPeriodicBlock r h t q n

/-- The seed set through `D`. -/
def DenseCapSeed (r h t z : Nat) : Prop :=
  z = 1 ∨ z = h - 1 ∨ z = D r h t

theorem D_ge_t {r h t : Nat} : t <= D r h t := by
  unfold D
  omega

theorem D_ge_three {r h t : Nat} (hp : Params r h t) :
    3 <= D r h t := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have hcoef : 2 <= 2 * r := by omega
  have hprod : 2 * h <= 2 * r * h := Nat.mul_le_mul_right h hcoef
  unfold D
  omega

theorem M_pos {r h t : Nat} : 0 < M r h t := by
  unfold M
  omega

theorem M_ge_one {r h t : Nat} : 1 <= M r h t := by
  have hM : 0 < M r h t := M_pos
  omega

theorem D_lt_M {r h t : Nat} : D r h t < M r h t := by
  unfold M
  omega

theorem one_candidate (r h t : Nat) : Candidate r h t 1 := by
  unfold Candidate
  exact Or.inl rfl

theorem h_sub_one_candidate (r h t : Nat) : Candidate r h t (h - 1) := by
  unfold Candidate
  exact Or.inr (Or.inl rfl)

theorem zero_in_Q_zero {r h t : Nat} (hp : Params r h t) :
    InQ r h t 0 0 := by
  unfold InQ InFullPacketRun InInterval
  left
  refine ⟨0, ?_⟩
  constructor
  · exact hp.r_pos
  · omega

theorem D_in_E {r h t : Nat} (hp : Params r h t) :
    InE r h t (D r h t) := by
  unfold InE Shift
  exact ⟨0, zero_in_Q_zero hp, by omega⟩

theorem D_candidate {r h t : Nat} (hp : Params r h t) :
    Candidate r h t (D r h t) := by
  unfold Candidate
  exact Or.inr (Or.inr (Or.inl (D_in_E hp)))

theorem seed_subset_candidate {r h t z : Nat} (hp : Params r h t)
    (hz : DenseCapSeed r h t z) :
    Candidate r h t z := by
  unfold DenseCapSeed at hz
  rcases hz with rfl | rfl | rfl
  · exact one_candidate r h t
  · exact h_sub_one_candidate r h t
  · exact D_candidate hp

end TransitionDenseCap
end GreedyThreeSumfree
