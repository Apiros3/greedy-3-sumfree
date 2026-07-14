import GreedyThreeSumfree.TransitionDenseCapPacketSums

namespace GreedyThreeSumfree
namespace TransitionDenseCap

/-- Left endpoint of the last mixed slice before the all-terminal slice. -/
def LastMixedTerminalSliceLo (r h : Nat) : Nat :=
  (6 * r - 2) * h + 1

/-- Right endpoint of the last mixed slice before the all-terminal slice. -/
def LastMixedTerminalSliceHi (r h t : Nat) : Nat :=
  (6 * r - 1) * h + 2 * t

/-- Left endpoint of the all-terminal restricted triple slice. -/
def AllTerminalSliceLo (r h : Nat) : Nat :=
  6 * r * h + 3

/-- Right endpoint of the all-terminal restricted triple slice. -/
def AllTerminalSliceHi (r h t : Nat) : Nat :=
  6 * r * h + 3 * t

/-- The terminal slices meet when the all-terminal slice starts before the
previous mixed slice plus one. -/
def TerminalSlicesMeet (r h t : Nat) : Prop :=
  AllTerminalSliceLo r h <= LastMixedTerminalSliceHi r h t + 1

theorem one_le_t_of_params {r h t : Nat} (hp : Params r h t) :
    1 <= t := by
  have hh := hp.h_ge_six
  have hlow := hp.dense_lower
  omega

theorem two_le_t_of_params {r h t : Nat} (hp : Params r h t) :
    2 <= t := by
  have hh := hp.h_ge_six
  have hlow := hp.dense_lower
  omega

theorem lastMixedTerminalSlice_lo_le_hi {r h t : Nat}
    (hp : Params r h t) :
    LastMixedTerminalSliceLo r h <= LastMixedTerminalSliceHi r h t := by
  unfold LastMixedTerminalSliceLo LastMixedTerminalSliceHi
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have hcoef : (6 * r - 2) + 1 = 6 * r - 1 := by omega
  calc
    (6 * r - 2) * h + 1 <= ((6 * r - 2) + 1) * h + 2 * t := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    _ = (6 * r - 1) * h + 2 * t := by rw [hcoef]

theorem allTerminalSlice_lo_le_hi {r h t : Nat}
    (hp : Params r h t) :
    AllTerminalSliceLo r h <= AllTerminalSliceHi r h t := by
  unfold AllTerminalSliceLo AllTerminalSliceHi
  have ht : 1 <= t := one_le_t_of_params hp
  omega

theorem dense_lower_iff_terminalSlicesMeet {r h t : Nat}
    (hr : 1 <= r) :
    h + 2 <= 2 * t ↔ TerminalSlicesMeet r h t := by
  unfold TerminalSlicesMeet AllTerminalSliceLo LastMixedTerminalSliceHi
  have hcoef : (6 * r - 1) + 1 = 6 * r := by omega
  have hlo : 6 * r * h + 3 = (6 * r - 1) * h + h + 3 := by
    calc
      6 * r * h + 3 = ((6 * r - 1) + 1) * h + 3 := by rw [hcoef]
      _ = (6 * r - 1) * h + h + 3 := by rw [Nat.add_mul, Nat.one_mul]
  rw [hlo]
  omega

theorem terminalSlicesMeet_iff_dense_lower {r h t : Nat}
    (hr : 1 <= r) :
    TerminalSlicesMeet r h t ↔ h + 2 <= 2 * t := by
  exact (dense_lower_iff_terminalSlicesMeet (r := r) (h := h) (t := t) hr).symm

theorem terminalSlicesMeet_of_params {r h t : Nat}
    (hp : Params r h t) :
    TerminalSlicesMeet r h t := by
  exact
    (dense_lower_iff_terminalSlicesMeet (r := r) (h := h) (t := t) hp.r_pos).mp
      hp.dense_lower

theorem dense_lower_terminal_join_ineq {r h t : Nat}
    (hp : Params r h t) :
    6 * r * h + 3 <= (6 * r - 1) * h + 2 * t + 1 := by
  exact terminalSlicesMeet_of_params hp

theorem terminalCap_q0_offset_inQ {r h t k : Nat}
    (hk : k <= t + 1) :
    InQ r h t 0 (2 * r * h + k) := by
  apply inQ_of_terminal_cap
  unfold InTerminalCap InInterval
  omega

theorem terminalCap_q0_left_one_inQ {r h t : Nat} :
    InQ r h t 0 (2 * r * h + 1) := by
  exact terminalCap_q0_offset_inQ (r := r) (h := h) (t := t) (k := 1) (by omega)

theorem terminalCap_q0_left_two_inQ {r h t : Nat}
    (ht : 1 <= t) :
    InQ r h t 0 (2 * r * h + 2) := by
  exact terminalCap_q0_offset_inQ (r := r) (h := h) (t := t) (k := 2) (by omega)

theorem terminalCap_q0_right_minus_one_inQ {r h t : Nat}
    (ht : 1 <= t) :
    InQ r h t 0 (2 * r * h + (t - 1)) := by
  exact
    terminalCap_q0_offset_inQ (r := r) (h := h) (t := t) (k := t - 1)
      (by omega)

theorem terminalCap_q0_right_inQ {r h t : Nat} :
    InQ r h t 0 (2 * r * h + t) := by
  exact terminalCap_q0_offset_inQ (r := r) (h := h) (t := t) (k := t) (by omega)

theorem terminalCap_q0_far_right_inQ {r h t : Nat} :
    InQ r h t 0 (2 * r * h + t + 1) := by
  exact terminalCap_q0_offset_inQ (r := r) (h := h) (t := t) (k := t + 1) (by omega)

theorem lastFullPacket_left_inQ {r h t : Nat}
    (hp : Params r h t) :
    InQ r h t 0 (2 * (r - 1) * h) := by
  apply full_packet_run_left_inQ (r := r) (h := h) (t := t) (s := 0)
    (i := r - 1) hp
  have hr := hp.r_pos
  omega

theorem lastFullPacket_right_inQ {r h t : Nat}
    (hp : Params r h t) :
    InQ r h t 0 (2 * (r - 1) * h + h - 1) := by
  apply full_packet_run_right_inQ (r := r) (h := h) (t := t) (s := 0)
    (i := r - 1) hp
  have hr := hp.r_pos
  omega

theorem lastMixedTerminalSlice_left_restrictedThreeQ0Sum {r h t : Nat}
    (hp : Params r h t) :
    RestrictedThreeQ0Sum r h t (LastMixedTerminalSliceLo r h) := by
  refine
    ⟨2 * (r - 1) * h, 2 * r * h, 2 * r * h + 1,
      lastFullPacket_left_inQ hp,
      terminal_cap_left_inQ (r := r) (h := h) (t := t) (s := 0) (by omega),
      terminalCap_q0_left_one_inQ (r := r) (h := h) (t := t),
      ?_, ?_, ?_⟩
  · have hr := hp.r_pos
    have hh := hp.h_ge_six
    have hcoef : 2 * (r - 1) + 2 = 2 * r := by omega
    calc
      2 * (r - 1) * h < (2 * (r - 1) + 2) * h := by
        rw [Nat.add_mul]
        omega
      _ = 2 * r * h := by rw [hcoef]
  · omega
  · unfold LastMixedTerminalSliceLo
    have hr := hp.r_pos
    have hcoef : 2 * (r - 1) + 2 * r + 2 * r = 6 * r - 2 := by omega
    calc
      2 * (r - 1) * h + 2 * r * h + (2 * r * h + 1)
          = (2 * (r - 1) * h + 2 * r * h + 2 * r * h) + 1 := by
        omega
      _ = ((2 * (r - 1) + 2 * r + 2 * r) * h) + 1 := by
        rw [Nat.add_mul, Nat.add_mul]
      _ = (6 * r - 2) * h + 1 := by rw [hcoef]

theorem lastMixedTerminalSlice_right_restrictedThreeQ0Sum {r h t : Nat}
    (hp : Params r h t) :
    RestrictedThreeQ0Sum r h t (LastMixedTerminalSliceHi r h t) := by
  refine
    ⟨2 * (r - 1) * h + h - 1, 2 * r * h + t, 2 * r * h + t + 1,
      lastFullPacket_right_inQ hp,
      terminalCap_q0_right_inQ (r := r) (h := h) (t := t),
      terminalCap_q0_far_right_inQ (r := r) (h := h) (t := t),
      ?_, ?_, ?_⟩
  · have hr := hp.r_pos
    have hh := hp.h_ge_six
    have hcoef : 2 * (r - 1) + 2 = 2 * r := by omega
    have hprod : 2 * r * h = 2 * (r - 1) * h + 2 * h := by
      calc
        2 * r * h = (2 * (r - 1) + 2) * h := by rw [hcoef]
        _ = 2 * (r - 1) * h + 2 * h := by rw [Nat.add_mul]
    rw [hprod]
    omega
  · omega
  · unfold LastMixedTerminalSliceHi
    have hr := hp.r_pos
    have hh := hp.h_ge_six
    have hcoef : 2 * (r - 1) + 1 + 2 * r + 2 * r = 6 * r - 1 := by omega
    calc
      (2 * (r - 1) * h + h - 1) + (2 * r * h + t) +
          (2 * r * h + t + 1)
          = (2 * (r - 1) * h + h + 2 * r * h + 2 * r * h) + 2 * t := by
        omega
      _ = ((2 * (r - 1) + 1 + 2 * r + 2 * r) * h) + 2 * t := by
        rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.one_mul]
      _ = (6 * r - 1) * h + 2 * t := by rw [hcoef]

theorem allTerminalSlice_left_restrictedThreeQ0Sum {r h t : Nat}
    (hp : Params r h t) :
    RestrictedThreeQ0Sum r h t (AllTerminalSliceLo r h) := by
  have ht : 1 <= t := one_le_t_of_params hp
  refine
    ⟨2 * r * h, 2 * r * h + 1, 2 * r * h + 2,
      terminal_cap_left_inQ (r := r) (h := h) (t := t) (s := 0) (by omega),
      terminalCap_q0_left_one_inQ (r := r) (h := h) (t := t),
      terminalCap_q0_left_two_inQ (r := r) (h := h) (t := t) ht,
      ?_, ?_, ?_⟩
  · omega
  · omega
  · unfold AllTerminalSliceLo
    have hcoef : 2 * r + 2 * r + 2 * r = 6 * r := by omega
    calc
      2 * r * h + (2 * r * h + 1) + (2 * r * h + 2)
          = (2 * r * h + 2 * r * h + 2 * r * h) + 3 := by
        omega
      _ = ((2 * r + 2 * r + 2 * r) * h) + 3 := by
        rw [Nat.add_mul, Nat.add_mul]
      _ = 6 * r * h + 3 := by rw [hcoef]

theorem allTerminalSlice_right_restrictedThreeQ0Sum {r h t : Nat}
    (hp : Params r h t) :
    RestrictedThreeQ0Sum r h t (AllTerminalSliceHi r h t) := by
  have ht : 1 <= t := one_le_t_of_params hp
  refine
    ⟨2 * r * h + (t - 1), 2 * r * h + t, 2 * r * h + t + 1,
      terminalCap_q0_right_minus_one_inQ (r := r) (h := h) (t := t) ht,
      terminalCap_q0_right_inQ (r := r) (h := h) (t := t),
      terminalCap_q0_far_right_inQ (r := r) (h := h) (t := t),
      ?_, ?_, ?_⟩
  · omega
  · omega
  · unfold AllTerminalSliceHi
    have hcoef : 2 * r + 2 * r + 2 * r = 6 * r := by omega
    calc
      (2 * r * h + (t - 1)) + (2 * r * h + t) + (2 * r * h + t + 1)
          = (2 * r * h + 2 * r * h + 2 * r * h) + 3 * t := by
        omega
      _ = ((2 * r + 2 * r + 2 * r) * h) + 3 * t := by
        rw [Nat.add_mul, Nat.add_mul]
      _ = 6 * r * h + 3 * t := by rw [hcoef]

end TransitionDenseCap
end GreedyThreeSumfree
