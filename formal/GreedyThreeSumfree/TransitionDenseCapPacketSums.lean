import GreedyThreeSumfree.TransitionDenseCapBasic

namespace GreedyThreeSumfree
namespace TransitionDenseCap

/-- Ordinary, non-distinct two-sum from `Q_a + Q_b`. -/
def QPairSum (r h t a b n : Nat) : Prop :=
  ∃ x y : Nat,
    InQ r h t a x ∧ InQ r h t b y ∧ x + y = n

/--
Restricted two-sum from `Q_0`, with distinctness encoded by the strict order
`x < y`.
-/
def RestrictedTwoQ0Sum (r h t n : Nat) : Prop :=
  ∃ x y : Nat,
    InQ r h t 0 x ∧ InQ r h t 0 y ∧ x < y ∧ x + y = n

/-- Restricted three-sum from `Q_0`, with `x < y < z`. -/
def RestrictedThreeQ0Sum (r h t n : Nat) : Prop :=
  ∃ x y z : Nat,
    InQ r h t 0 x ∧
    InQ r h t 0 y ∧
    InQ r h t 0 z ∧
    x < y ∧
    y < z ∧
    x + y + z = n

/--
A sum of two distinct `Q_0` positions and one `Q_s` position.

Only the two `Q_0` witnesses are required to be distinct.  The `Q_s` witness
is a separate summand position and is not required to have a different numeric
value from the `Q_0` witnesses.
-/
def RestrictedTwoQ0PlusQSum (r h t s n : Nat) : Prop :=
  ∃ x y z : Nat,
    InQ r h t 0 x ∧
    InQ r h t 0 y ∧
    InQ r h t s z ∧
    x < y ∧
    x + y + z = n

theorem inQ_of_full_packet_run {r h t s i n : Nat}
    (hn : InFullPacketRun r h i n) :
    InQ r h t s n := by
  unfold InQ
  exact Or.inl ⟨i, hn⟩

theorem inQ_of_terminal_cap {r h t s n : Nat}
    (hn : InTerminalCap r h t s n) :
    InQ r h t s n := by
  unfold InQ
  exact Or.inr hn

theorem full_packet_run_left_inQ {r h t s i : Nat}
    (hp : Params r h t) (hi : i < r) :
    InQ r h t s (2 * i * h) := by
  apply inQ_of_full_packet_run (i := i)
  unfold InFullPacketRun InInterval
  constructor
  · exact hi
  · have hh := hp.h_ge_six
    omega

theorem full_packet_run_right_inQ {r h t s i : Nat}
    (hp : Params r h t) (hi : i < r) :
    InQ r h t s (2 * i * h + h - 1) := by
  apply inQ_of_full_packet_run (i := i)
  unfold InFullPacketRun InInterval
  constructor
  · exact hi
  · have hh := hp.h_ge_six
    omega

theorem terminal_cap_left_inQ {r h t s : Nat}
    (hs : s <= t + 1) :
    InQ r h t s (2 * r * h) := by
  apply inQ_of_terminal_cap
  unfold InTerminalCap InInterval
  omega

theorem terminal_cap_right_inQ {r h t s : Nat}
    (hs : s <= t + 1) :
    InQ r h t s (2 * r * h + t + 1 - s) := by
  apply inQ_of_terminal_cap
  unfold InTerminalCap InInterval
  omega

theorem small_in_Q {r h t s k : Nat}
    (hp : Params r h t) (hk : k <= h - 1) :
    InQ r h t s k := by
  unfold InQ InFullPacketRun InInterval
  left
  refine ⟨0, ?_⟩
  constructor
  · exact hp.r_pos
  · constructor
    · omega
    · simpa using hk

theorem zero_in_Q {r h t s : Nat} (hp : Params r h t) :
    InQ r h t s 0 := by
  exact small_in_Q (s := s) hp (Nat.zero_le _)

theorem one_in_Q {r h t s : Nat} (hp : Params r h t) :
    InQ r h t s 1 := by
  apply small_in_Q (s := s) hp
  have hh := hp.h_ge_six
  omega

theorem two_in_Q {r h t s : Nat} (hp : Params r h t) :
    InQ r h t s 2 := by
  apply small_in_Q (s := s) hp
  have hh := hp.h_ge_six
  omega

theorem qPairSum_comm {r h t a b n : Nat}
    (hn : QPairSum r h t a b n) :
    QPairSum r h t b a n := by
  rcases hn with ⟨x, y, hx, hy, hsum⟩
  exact ⟨y, x, hy, hx, by simpa [Nat.add_comm] using hsum⟩

theorem qPairSum_zero {r h t a b : Nat} (hp : Params r h t) :
    QPairSum r h t a b 0 := by
  exact ⟨0, 0, zero_in_Q (s := a) hp, zero_in_Q (s := b) hp, by simp⟩

theorem qPairSum_of_restrictedTwoQ0Sum {r h t n : Nat}
    (hn : RestrictedTwoQ0Sum r h t n) :
    QPairSum r h t 0 0 n := by
  rcases hn with ⟨x, y, hx, hy, _hxy, hsum⟩
  exact ⟨x, y, hx, hy, hsum⟩

theorem restrictedTwoQ0Sum_one {r h t : Nat} (hp : Params r h t) :
    RestrictedTwoQ0Sum r h t 1 := by
  exact
    ⟨0, 1, zero_in_Q (s := 0) hp, one_in_Q (s := 0) hp,
      by omega, by omega⟩

theorem restrictedThreeQ0Sum_three {r h t : Nat} (hp : Params r h t) :
    RestrictedThreeQ0Sum r h t 3 := by
  exact
    ⟨0, 1, 2,
      zero_in_Q (s := 0) hp,
      one_in_Q (s := 0) hp,
      two_in_Q (s := 0) hp,
      by omega, by omega, by omega⟩

theorem restrictedTwoQ0PlusQSum_one {r h t s : Nat} (hp : Params r h t) :
    RestrictedTwoQ0PlusQSum r h t s 1 := by
  exact
    ⟨0, 1, 0,
      zero_in_Q (s := 0) hp,
      one_in_Q (s := 0) hp,
      zero_in_Q (s := s) hp,
      by omega, by omega⟩

theorem restrictedTwoQ0PlusQSum_of_restrictedThreeQ0Sum {r h t n : Nat}
    (hn : RestrictedThreeQ0Sum r h t n) :
    RestrictedTwoQ0PlusQSum r h t 0 n := by
  rcases hn with ⟨x, y, z, hx, hy, hz, hxy, _hyz, hsum⟩
  exact ⟨x, y, z, hx, hy, hz, hxy, hsum⟩

end TransitionDenseCap
end GreedyThreeSumfree
