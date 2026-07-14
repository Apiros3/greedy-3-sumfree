import GreedyThreeSumfree.IntervalSumWitnesses
import GreedyThreeSumfree.TransitionDenseCapPacketSums

namespace GreedyThreeSumfree
namespace TransitionDenseCap

/-- Pointwise form of `(Q_a+Q_b) ∪ (h-2+Q_a+Q_b)`. -/
def QPairSumOrShift (r h t a b n : Nat) : Prop :=
  QPairSum r h t a b n ∨
    ∃ m : Nat, QPairSum r h t a b m ∧ n = h - 2 + m

/-- Pointwise form of `(^2 Q_0) ∪ (h-2+ ^2 Q_0)`. -/
def RestrictedTwoQ0SumOrShift (r h t n : Nat) : Prop :=
  RestrictedTwoQ0Sum r h t n ∨
    ∃ m : Nat, RestrictedTwoQ0Sum r h t m ∧ n = h - 2 + m

/--
Every target in the sum interval of two closed intervals has a constructive
two-summand witness.
-/
theorem interval_pair_sum {L1 U1 L2 U2 n : Nat} (h1 : L1 <= U1) (h2 : L2 <= U2)
    (hn : InInterval (L1 + L2) (U1 + U2) n) :
    ∃ x y : Nat, InInterval L1 U1 x ∧ InInterval L2 U2 y ∧ x + y = n := by
  have hnlo : L1 + L2 <= n := hn.1
  have hnhi : n <= U1 + U2 := hn.2
  by_cases hleft : n <= U1 + L2
  · let x := n - L2
    let y := L2
    have hL2n : L2 <= n := by omega
    have hxlo : L1 <= x := by
      dsimp [x]
      apply Nat.le_sub_of_add_le
      omega
    have hxhi : x <= U1 := by
      dsimp [x]
      rw [Nat.sub_le_iff_le_add]
      omega
    have hsum : x + y = n := by
      dsimp [x, y]
      exact Nat.sub_add_cancel hL2n
    exact ⟨x, y, ⟨hxlo, hxhi⟩, ⟨by omega, by omega⟩, hsum⟩
  · let x := U1
    let y := n - U1
    have hU1n : U1 <= n := by omega
    have hylo : L2 <= y := by
      dsimp [y]
      apply Nat.le_sub_of_add_le
      omega
    have hyhi : y <= U2 := by
      dsimp [y]
      rw [Nat.sub_le_iff_le_add]
      omega
    have hsum : x + y = n := by
      dsimp [x, y]
      exact Nat.add_sub_of_le hU1n
    exact ⟨x, y, ⟨by omega, by omega⟩, ⟨hylo, hyhi⟩, hsum⟩

theorem bounded_pair_indices {r m : Nat} (hr : 1 <= r) (hm : m <= 2 * r - 2) :
    ∃ i j : Nat, i < r ∧ j < r ∧ i + j = m := by
  by_cases hm_lt : m < r
  · exact ⟨0, m, by omega, hm_lt, by omega⟩
  · refine ⟨m - (r - 1), r - 1, ?_, ?_, ?_⟩ <;> omega

theorem qPairSum_full_full_of_indices {r h t a b i j n : Nat}
    (hp : Params r h t) (hi : i < r) (hj : j < r)
    (hn :
      InInterval (2 * i * h + 2 * j * h)
        ((2 * i * h + h - 1) + (2 * j * h + h - 1)) n) :
    QPairSum r h t a b n := by
  have hI : 2 * i * h <= 2 * i * h + h - 1 := by
    have hh := hp.h_ge_six
    omega
  have hJ : 2 * j * h <= 2 * j * h + h - 1 := by
    have hh := hp.h_ge_six
    omega
  rcases interval_pair_sum hI hJ hn with ⟨x, y, hx, hy, hsum⟩
  refine ⟨x, y, ?_, ?_, hsum⟩
  · apply inQ_of_full_packet_run (i := i)
    exact ⟨hi, hx⟩
  · apply inQ_of_full_packet_run (i := j)
    exact ⟨hj, hy⟩

theorem qPairSum_full_full_slice {r h t a b m n : Nat}
    (hp : Params r h t) (hm : m <= 2 * r - 2)
    (hn : InInterval (2 * m * h) (2 * m * h + 2 * h - 2) n) :
    QPairSum r h t a b n := by
  rcases bounded_pair_indices (r := r) (m := m) hp.r_pos hm with
    ⟨i, j, hi, hj, hij⟩
  have hlo : 2 * i * h + 2 * j * h = 2 * m * h := by
    rw [← hij, Nat.left_distrib, Nat.right_distrib]
  have hhi :
      (2 * i * h + h - 1) + (2 * j * h + h - 1) =
        2 * m * h + 2 * h - 2 := by
    rw [← hij, Nat.left_distrib, Nat.right_distrib]
    have hh := hp.h_ge_six
    omega
  apply qPairSum_full_full_of_indices
      (r := r) (h := h) (t := t) (a := a) (b := b) (i := i) (j := j) hp hi hj
  unfold InInterval at *
  constructor
  · rw [hlo]
    exact hn.1
  · rw [hhi]
    exact hn.2

theorem qPairSum_or_shift_full_full_slice {r h t a b m n : Nat}
    (hp : Params r h t) (hm : m <= 2 * r - 2)
    (hn : InInterval (2 * m * h) (2 * m * h + 3 * h - 4) n) :
    QPairSumOrShift r h t a b n := by
  by_cases hdirect : n <= 2 * m * h + 2 * h - 2
  · exact Or.inl
      (qPairSum_full_full_slice
        (r := r) (h := h) (t := t) (a := a) (b := b) (m := m) (n := n)
        hp hm ⟨hn.1, hdirect⟩)
  · let n0 := n - (h - 2)
    have hn0 :
        InInterval (2 * m * h) (2 * m * h + 2 * h - 2) n0 := by
      have hh := hp.h_ge_six
      unfold InInterval at *
      dsimp [n0]
      constructor <;> omega
    have hshift : n = h - 2 + n0 := by
      have hh := hp.h_ge_six
      dsimp [n0]
      omega
    exact Or.inr
      ⟨n0,
        qPairSum_full_full_slice
          (r := r) (h := h) (t := t) (a := a) (b := b) (m := m) (n := n0)
          hp hm hn0,
        hshift⟩

theorem fullFullShiftSlice_next_lo_le_hi {h m : Nat} (hh : 6 <= h) :
    2 * (m + 1) * h <= 2 * m * h + 3 * h - 4 := by
  rw [Nat.left_distrib, Nat.right_distrib]
  omega

theorem fullFullShiftSlice_chain_cover {h a k n : Nat} (hh : 6 <= h)
    (hn :
      InInterval (2 * a * h) (2 * (a + k) * h + 3 * h - 4) n) :
    ∃ m : Nat,
      a <= m ∧ m <= a + k ∧
        InInterval (2 * m * h) (2 * m * h + 3 * h - 4) n := by
  induction k with
  | zero =>
      exact ⟨a, by omega, by omega, by simpa using hn⟩
  | succ k ih =>
      by_cases hleft : n <= 2 * (a + k) * h + 3 * h - 4
      · rcases ih ⟨hn.1, hleft⟩ with ⟨m, hma, hmk, hm⟩
        exact ⟨m, hma, by omega, hm⟩
      · have hlo : 2 * ((a + k) + 1) * h <= n := by
          have hover := fullFullShiftSlice_next_lo_le_hi (h := h) (m := a + k) hh
          omega
        have hidx : (a + k) + 1 = a + (k + 1) := by omega
        have hhi : n <= 2 * ((a + k) + 1) * h + 3 * h - 4 := by
          simpa [hidx] using hn.2
        exact ⟨(a + k) + 1, by omega, by omega, ⟨hlo, hhi⟩⟩

theorem qPairSum_or_shift_full_full_chain {r h t a b n : Nat}
    (hp : Params r h t)
    (hn : n <= 2 * (2 * r - 2) * h + 3 * h - 4) :
    QPairSumOrShift r h t a b n := by
  rcases fullFullShiftSlice_chain_cover
      (h := h) (a := 0) (k := 2 * r - 2) (n := n) hp.h_ge_six
      ⟨by omega, by simpa using hn⟩ with
    ⟨m, _hmlo, hmhi, hmSlice⟩
  exact qPairSum_or_shift_full_full_slice
    (r := r) (h := h) (t := t) (a := a) (b := b) (m := m) (n := n)
    hp (by simpa using hmhi) hmSlice

theorem qPairSum_terminal_full_of_index {r h t a b j n : Nat}
    (hp : Params r h t) (ha : a <= 1) (hj : j < r)
    (hn :
      InInterval (2 * r * h + 2 * j * h)
        ((2 * r * h + t + 1 - a) + (2 * j * h + h - 1)) n) :
    QPairSum r h t a b n := by
  have hT : 2 * r * h <= 2 * r * h + t + 1 - a := by omega
  have hJ : 2 * j * h <= 2 * j * h + h - 1 := by
    have hh := hp.h_ge_six
    omega
  rcases interval_pair_sum hT hJ hn with ⟨x, y, hx, hy, hsum⟩
  refine ⟨x, y, ?_, ?_, hsum⟩
  · apply inQ_of_terminal_cap
    exact hx
  · apply inQ_of_full_packet_run (i := j)
    exact ⟨hj, hy⟩

theorem qPairSum_or_shift_terminal_full_slice {r h t a b j n : Nat}
    (hp : Params r h t) (ha : a <= 1) (hj : j < r)
    (hn : InInterval (2 * r * h + 2 * j * h)
        (2 * r * h + 2 * j * h + 2 * h + t - a - 2) n) :
    QPairSumOrShift r h t a b n := by
  by_cases hdirect : n <= 2 * r * h + 2 * j * h + h + t - a
  · exact Or.inl
      (qPairSum_terminal_full_of_index
        (r := r) (h := h) (t := t) (a := a) (b := b) (j := j) (n := n)
        hp ha hj (by
          unfold InInterval at *
          constructor <;> omega))
  · let n0 := n - (h - 2)
    have hn0 :
        InInterval (2 * r * h + 2 * j * h)
          ((2 * r * h + t + 1 - a) + (2 * j * h + h - 1)) n0 := by
      have hh := hp.h_ge_six
      unfold InInterval at *
      dsimp [n0]
      constructor <;> omega
    have hshift : n = h - 2 + n0 := by
      have hh := hp.h_ge_six
      dsimp [n0]
      omega
    exact Or.inr
      ⟨n0,
        qPairSum_terminal_full_of_index
          (r := r) (h := h) (t := t) (a := a) (b := b) (j := j) (n := n0)
          hp ha hj hn0,
        hshift⟩

theorem terminalFullShiftSlice_next_lo_le_hi {r h t a j : Nat}
    (hp : Params r h t) (ha : a <= 1) :
    2 * r * h + 2 * (j + 1) * h <=
      2 * r * h + 2 * j * h + 2 * h + t - a - 2 := by
  have hh := hp.h_ge_six
  have hlower := hp.dense_lower
  rw [Nat.left_distrib, Nat.right_distrib]
  omega

theorem terminalFullShiftSlice_chain_cover {r h t a k n : Nat}
    (hp : Params r h t) (ha : a <= 1)
    (hn :
      InInterval (2 * r * h)
        (2 * r * h + 2 * k * h + 2 * h + t - a - 2) n) :
    ∃ j : Nat,
      j <= k ∧
        InInterval (2 * r * h + 2 * j * h)
          (2 * r * h + 2 * j * h + 2 * h + t - a - 2) n := by
  induction k with
  | zero =>
      exact ⟨0, by omega, by simpa using hn⟩
  | succ k ih =>
      by_cases hleft : n <= 2 * r * h + 2 * k * h + 2 * h + t - a - 2
      · rcases ih ⟨hn.1, hleft⟩ with ⟨j, hjk, hj⟩
        exact ⟨j, by omega, hj⟩
      · have hlo : 2 * r * h + 2 * (k + 1) * h <= n := by
          have hover :=
            terminalFullShiftSlice_next_lo_le_hi
              (r := r) (h := h) (t := t) (a := a) (j := k) hp ha
          omega
        have hhi :
            n <= 2 * r * h + 2 * (k + 1) * h + 2 * h + t - a - 2 := by
          simpa using hn.2
        exact ⟨k + 1, by omega, ⟨hlo, hhi⟩⟩

theorem qPairSum_or_shift_terminal_full_chain {r h t a b n : Nat}
    (hp : Params r h t) (ha : a <= 1)
    (hn :
      InInterval (2 * r * h)
        (2 * r * h + 2 * (r - 1) * h + 2 * h + t - a - 2) n) :
    QPairSumOrShift r h t a b n := by
  rcases terminalFullShiftSlice_chain_cover
      (r := r) (h := h) (t := t) (a := a) (k := r - 1) (n := n) hp ha hn with
    ⟨j, hj, hjSlice⟩
  exact qPairSum_or_shift_terminal_full_slice
    (r := r) (h := h) (t := t) (a := a) (b := b) (j := j) (n := n)
    hp ha (by
      have hr := hp.r_pos
      omega) hjSlice

theorem qPairSum_terminal_terminal {r h t a b n : Nat}
    (_hp : Params r h t) (ha : a <= 1) (hb : b <= 1)
    (hn : InInterval (4 * r * h) (4 * r * h + 2 * t + 2 - a - b) n) :
    QPairSum r h t a b n := by
  have hA : 2 * r * h <= 2 * r * h + t + 1 - a := by omega
  have hB : 2 * r * h <= 2 * r * h + t + 1 - b := by omega
  have h4 : 4 * r * h = 2 * r * h + 2 * r * h := by
    rw [← Nat.add_mul]
    congr
    omega
  rcases interval_pair_sum hA hB (by
      unfold InInterval at *
      constructor
      · rw [← h4]
        exact hn.1
      · rw [h4] at hn
        omega) with
    ⟨x, y, hx, hy, hsum⟩
  refine ⟨x, y, ?_, ?_, hsum⟩
  · apply inQ_of_terminal_cap
    exact hx
  · apply inQ_of_terminal_cap
    exact hy

theorem qPairSum_or_shift_terminal_terminal {r h t a b n : Nat}
    (hp : Params r h t) (ha : a <= 1) (hb : b <= 1)
    (hn : InInterval (4 * r * h) (2 * D r h t + h - a - b) n) :
    QPairSumOrShift r h t a b n := by
  by_cases hdirect : n <= 4 * r * h + 2 * t + 2 - a - b
  · exact Or.inl
      (qPairSum_terminal_terminal
        (r := r) (h := h) (t := t) (a := a) (b := b) (n := n)
        hp ha hb ⟨hn.1, hdirect⟩)
  · let n0 := n - (h - 2)
    have hn0 : InInterval (4 * r * h) (4 * r * h + 2 * t + 2 - a - b) n0 := by
      have hh := hp.h_ge_six
      have hlower := hp.dense_lower
      have h4 : 4 * r * h = 2 * r * h + 2 * r * h := by
        rw [← Nat.add_mul]
        congr
        omega
      unfold D InInterval at *
      dsimp [n0]
      constructor <;> omega
    have hshift : n = h - 2 + n0 := by
      have hh := hp.h_ge_six
      have hr := hp.r_pos
      have hnlo := hn.1
      have h2rh : h <= 2 * r * h := by
        simpa [Nat.one_mul] using
          Nat.mul_le_mul_right h (by omega : 1 <= 2 * r)
      have h4 : 4 * r * h = 2 * r * h + 2 * r * h := by
        rw [← Nat.add_mul]
        congr
        omega
      have hle : h - 2 <= n := by
        rw [h4] at hnlo
        omega
      dsimp [n0]
      rw [Nat.add_comm]
      exact (Nat.sub_add_cancel hle).symm
    exact Or.inr
      ⟨n0,
        qPairSum_terminal_terminal
          (r := r) (h := h) (t := t) (a := a) (b := b) (n := n0)
          hp ha hb hn0,
        hshift⟩

/--
Dense-cap packet-sum identity `(1b)`, in pointwise coverage form, for
`a,b in {0,1}`.
-/
theorem qPairSum_or_shift_dense_cap_coverage {r h t a b n : Nat}
    (hp : Params r h t) (ha : a <= 1) (hb : b <= 1)
    (hn : n <= 2 * D r h t + h - a - b) :
    QPairSumOrShift r h t a b n := by
  have hfull_ge_terminal_lo :
      2 * r * h <= 2 * (2 * r - 2) * h + 3 * h - 4 := by
    have hr := hp.r_pos
    have hh := hp.h_ge_six
    have h2 : 2 * r * h = 2 * (r - 1) * h + 2 * h := by
      have hrSub : r - 1 + 1 = r := Nat.sub_add_cancel hr
      calc
        2 * r * h = 2 * ((r - 1) + 1) * h := by rw [hrSub]
        _ = 2 * (r - 1) * h + 2 * h := by
          rw [Nat.left_distrib, Nat.right_distrib]
    have hcoef : 2 * (r - 1) <= 2 * r - 2 := by omega
    have hmul : 2 * (r - 1) * h <= (2 * r - 2) * h :=
      Nat.mul_le_mul_right h hcoef
    have hmul2 : (2 * r - 2) * h <= 2 * (2 * r - 2) * h := by
      have htmp := Nat.le_mul_of_pos_left ((2 * r - 2) * h) (by omega : 0 < 2)
      simpa [Nat.mul_assoc] using htmp
    omega
  have hterminal_ge_terminal_terminal_lo :
      4 * r * h <=
        2 * r * h + 2 * (r - 1) * h + 2 * h + t - a - 2 := by
    have hr := hp.r_pos
    have hh := hp.h_ge_six
    have hlower := hp.dense_lower
    have h2 : 2 * r * h = 2 * (r - 1) * h + 2 * h := by
      have hrSub : r - 1 + 1 = r := Nat.sub_add_cancel hr
      calc
        2 * r * h = 2 * ((r - 1) + 1) * h := by rw [hrSub]
        _ = 2 * (r - 1) * h + 2 * h := by
          rw [Nat.left_distrib, Nat.right_distrib]
    have h4 : 4 * r * h = 2 * r * h + 2 * r * h := by
      rw [← Nat.add_mul]
      congr
      omega
    rw [h4, h2]
    omega
  by_cases hfull : n <= 2 * (2 * r - 2) * h + 3 * h - 4
  · exact qPairSum_or_shift_full_full_chain
      (r := r) (h := h) (t := t) (a := a) (b := b) (n := n) hp hfull
  · by_cases hterm :
        n <= 2 * r * h + 2 * (r - 1) * h + 2 * h + t - a - 2
    · exact qPairSum_or_shift_terminal_full_chain
        (r := r) (h := h) (t := t) (a := a) (b := b) (n := n) hp ha
        (by
          have hh := hp.h_ge_six
          unfold InInterval
          constructor
          · omega
          · exact hterm)
    · exact qPairSum_or_shift_terminal_terminal
        (r := r) (h := h) (t := t) (a := a) (b := b) (n := n) hp ha hb
        (by
          have hh := hp.h_ge_six
          have hlower := hp.dense_lower
          unfold D InInterval at *
          constructor
          · omega
          · exact hn)

theorem restrictedTwoQ0Sum_full_same_index {r h t i n : Nat}
    (hp : Params r h t) (hi : i < r)
    (hn :
      NatInterval (2 * (2 * i * h) + 1) (2 * (2 * i * h + h - 1) - 1) n) :
    RestrictedTwoQ0Sum r h t n := by
  have hlt : 2 * i * h < 2 * i * h + h - 1 := by
    have hh := hp.h_ge_six
    omega
  rcases interval_pair_sum_distinct hlt hn with ⟨x, y, hx, hy, hxy, hsum⟩
  refine ⟨x, y, ?_, ?_, hxy, hsum⟩
  · apply inQ_of_full_packet_run (i := i)
    exact ⟨hi, hx⟩
  · apply inQ_of_full_packet_run (i := i)
    exact ⟨hi, hy⟩

theorem restrictedTwoQ0Sum_full_strict_indices {r h t i j n : Nat}
    (hp : Params r h t) (hi : i < r) (hj : j < r) (hij : i < j)
    (hn :
      InInterval (2 * i * h + 2 * j * h)
        ((2 * i * h + h - 1) + (2 * j * h + h - 1)) n) :
    RestrictedTwoQ0Sum r h t n := by
  have hI : 2 * i * h <= 2 * i * h + h - 1 := by
    have hh := hp.h_ge_six
    omega
  have hJ : 2 * j * h <= 2 * j * h + h - 1 := by
    have hh := hp.h_ge_six
    omega
  rcases interval_pair_sum hI hJ hn with ⟨x, y, hx, hy, hsum⟩
  have hxy : x < y := by
    have hh := hp.h_ge_six
    have hxhi := hx.2
    have hylo := hy.1
    have hgap : 2 * i * h + h - 1 < 2 * j * h := by
      have hmul : 2 * (i + 1) * h <= 2 * j * h :=
        Nat.mul_le_mul_right h (by omega : 2 * (i + 1) <= 2 * j)
      rw [Nat.left_distrib, Nat.right_distrib] at hmul
      omega
    omega
  refine ⟨x, y, ?_, ?_, hxy, hsum⟩
  · apply inQ_of_full_packet_run (i := i)
    exact ⟨hi, hx⟩
  · apply inQ_of_full_packet_run (i := j)
    exact ⟨hj, hy⟩

theorem restrictedTwoQ0Sum_full_terminal {r h t i n : Nat}
    (hp : Params r h t) (hi : i < r)
    (hn :
      InInterval (2 * i * h + 2 * r * h)
        ((2 * i * h + h - 1) + (2 * r * h + t + 1)) n) :
    RestrictedTwoQ0Sum r h t n := by
  have hI : 2 * i * h <= 2 * i * h + h - 1 := by
    have hh := hp.h_ge_six
    omega
  have hT : 2 * r * h <= 2 * r * h + t + 1 := by omega
  rcases interval_pair_sum hI hT hn with ⟨x, y, hx, hy, hsum⟩
  have hxy : x < y := by
    have hh := hp.h_ge_six
    have hxhi := hx.2
    have hylo := hy.1
    have hgap : 2 * i * h + h - 1 < 2 * r * h := by
      have hmul : 2 * (i + 1) * h <= 2 * r * h :=
        Nat.mul_le_mul_right h (by omega : 2 * (i + 1) <= 2 * r)
      rw [Nat.left_distrib, Nat.right_distrib] at hmul
      omega
    omega
  refine ⟨x, y, ?_, ?_, hxy, hsum⟩
  · apply inQ_of_full_packet_run (i := i)
    exact ⟨hi, hx⟩
  · apply inQ_of_terminal_cap
    exact hy

theorem restrictedTwoQ0Sum_terminal_terminal {r h t n : Nat}
    (hp : Params r h t)
    (hn : NatInterval (2 * (2 * r * h) + 1) (2 * (2 * r * h + t + 1) - 1) n) :
    RestrictedTwoQ0Sum r h t n := by
  have hlt : 2 * r * h < 2 * r * h + t + 1 := by
    have hh := hp.h_ge_six
    have hlower := hp.dense_lower
    omega
  rcases interval_pair_sum_distinct hlt hn with ⟨x, y, hx, hy, hxy, hsum⟩
  refine ⟨x, y, ?_, ?_, hxy, hsum⟩
  · apply inQ_of_terminal_cap
    exact hx
  · apply inQ_of_terminal_cap
    exact hy

theorem bounded_strict_pair_indices {r m : Nat} (hr : 1 <= r) (hmlo : 1 <= m)
    (hmhi : m <= 2 * r - 3) :
    ∃ i j : Nat, i < r ∧ j < r ∧ i < j ∧ i + j = m := by
  by_cases hm_lt : m < r
  · exact ⟨0, m, by omega, hm_lt, by omega, by omega⟩
  · refine ⟨m - (r - 1), r - 1, ?_, ?_, ?_, ?_⟩ <;> omega

theorem restrictedTwoQ0Sum_or_shift_full_same_index {r h t i n : Nat}
    (hp : Params r h t) (hi : i < r)
    (hn :
      InInterval (2 * (2 * i * h) + 1) (2 * (2 * i * h) + 3 * h - 5) n) :
    RestrictedTwoQ0SumOrShift r h t n := by
  by_cases hdirect : n <= 2 * (2 * i * h + h - 1) - 1
  · exact Or.inl
      (restrictedTwoQ0Sum_full_same_index
        (r := r) (h := h) (t := t) (i := i) (n := n) hp hi
        (by
          unfold NatInterval
          exact ⟨hn.1, hdirect⟩))
  · let n0 := n - (h - 2)
    have hn0 :
        NatInterval (2 * (2 * i * h) + 1) (2 * (2 * i * h + h - 1) - 1) n0 := by
      have hh := hp.h_ge_six
      unfold InInterval at hn
      unfold NatInterval
      dsimp [n0]
      constructor <;> omega
    have hshift : n = h - 2 + n0 := by
      have hh := hp.h_ge_six
      have hle : h - 2 <= n := by omega
      dsimp [n0]
      rw [Nat.add_comm]
      exact (Nat.sub_add_cancel hle).symm
    exact Or.inr
      ⟨n0,
        restrictedTwoQ0Sum_full_same_index
          (r := r) (h := h) (t := t) (i := i) (n := n0) hp hi hn0,
        hshift⟩

theorem restrictedTwoQ0Sum_or_shift_full_strict_indices {r h t i j n : Nat}
    (hp : Params r h t) (hi : i < r) (hj : j < r) (hij : i < j)
    (hn :
      InInterval (2 * i * h + 2 * j * h)
        ((2 * i * h + h - 1) + (2 * j * h + h - 1) + (h - 2)) n) :
    RestrictedTwoQ0SumOrShift r h t n := by
  by_cases hdirect : n <= (2 * i * h + h - 1) + (2 * j * h + h - 1)
  · exact Or.inl
      (restrictedTwoQ0Sum_full_strict_indices
        (r := r) (h := h) (t := t) (i := i) (j := j) (n := n)
        hp hi hj hij ⟨hn.1, hdirect⟩)
  · let n0 := n - (h - 2)
    have hn0 :
        InInterval (2 * i * h + 2 * j * h)
          ((2 * i * h + h - 1) + (2 * j * h + h - 1)) n0 := by
      have hh := hp.h_ge_six
      unfold InInterval at *
      dsimp [n0]
      constructor <;> omega
    have hshift : n = h - 2 + n0 := by
      have hh := hp.h_ge_six
      have hle : h - 2 <= n := by
        unfold InInterval at hn
        omega
      dsimp [n0]
      rw [Nat.add_comm]
      exact (Nat.sub_add_cancel hle).symm
    exact Or.inr
      ⟨n0,
        restrictedTwoQ0Sum_full_strict_indices
          (r := r) (h := h) (t := t) (i := i) (j := j) (n := n0)
          hp hi hj hij hn0,
        hshift⟩

theorem restrictedTwoQ0Sum_or_shift_full_strict_slice {r h t m n : Nat}
    (hp : Params r h t) (hmlo : 1 <= m) (hmhi : m <= 2 * r - 3)
    (hn : InInterval (2 * m * h) (2 * m * h + 3 * h - 4) n) :
    RestrictedTwoQ0SumOrShift r h t n := by
  rcases bounded_strict_pair_indices (r := r) (m := m) hp.r_pos hmlo hmhi with
    ⟨i, j, hi, hj, hij, hsum⟩
  have hlo : 2 * i * h + 2 * j * h = 2 * m * h := by
    rw [← hsum, Nat.left_distrib, Nat.right_distrib]
  have hhi :
      (2 * i * h + h - 1) + (2 * j * h + h - 1) + (h - 2) =
        2 * m * h + 3 * h - 4 := by
    rw [← hsum, Nat.left_distrib, Nat.right_distrib]
    have hh := hp.h_ge_six
    omega
  exact restrictedTwoQ0Sum_or_shift_full_strict_indices
    (r := r) (h := h) (t := t) (i := i) (j := j) (n := n) hp hi hj hij
    (by
      unfold InInterval at *
      constructor
      · rw [hlo]
        exact hn.1
      · rw [hhi]
        exact hn.2)

theorem restrictedTwoQ0Sum_or_shift_full_strict_chain {r h t n : Nat}
    (hp : Params r h t) (hr : 2 <= r)
    (hn : InInterval (2 * h) (2 * (2 * r - 3) * h + 3 * h - 4) n) :
    RestrictedTwoQ0SumOrShift r h t n := by
  rcases fullFullShiftSlice_chain_cover
      (h := h) (a := 1) (k := 2 * r - 4) (n := n) hp.h_ge_six
      (by
        have hidx : 1 + (2 * r - 4) = 2 * r - 3 := by omega
        simpa [hidx] using hn) with
    ⟨m, hmlo, hmhi, hmSlice⟩
  exact restrictedTwoQ0Sum_or_shift_full_strict_slice
    (r := r) (h := h) (t := t) (m := m) (n := n) hp hmlo (by omega) hmSlice

theorem restrictedTwoQ0Sum_or_shift_full_terminal_slice {r h t i n : Nat}
    (hp : Params r h t) (hi : i < r)
    (hn :
      InInterval (2 * i * h + 2 * r * h)
        ((2 * i * h + h - 1) + (2 * r * h + t + 1) + (h - 2)) n) :
    RestrictedTwoQ0SumOrShift r h t n := by
  by_cases hdirect : n <= (2 * i * h + h - 1) + (2 * r * h + t + 1)
  · exact Or.inl
      (restrictedTwoQ0Sum_full_terminal
        (r := r) (h := h) (t := t) (i := i) (n := n) hp hi
        ⟨hn.1, hdirect⟩)
  · let n0 := n - (h - 2)
    have hn0 :
        InInterval (2 * i * h + 2 * r * h)
          ((2 * i * h + h - 1) + (2 * r * h + t + 1)) n0 := by
      have hh := hp.h_ge_six
      unfold InInterval at *
      dsimp [n0]
      constructor <;> omega
    have hshift : n = h - 2 + n0 := by
      have hh := hp.h_ge_six
      have hle : h - 2 <= n := by
        unfold InInterval at hn
        omega
      dsimp [n0]
      rw [Nat.add_comm]
      exact (Nat.sub_add_cancel hle).symm
    exact Or.inr
      ⟨n0,
        restrictedTwoQ0Sum_full_terminal
          (r := r) (h := h) (t := t) (i := i) (n := n0) hp hi hn0,
        hshift⟩

theorem restrictedTwoQ0Sum_or_shift_full_terminal_chain {r h t n : Nat}
    (hp : Params r h t)
    (hn : InInterval (2 * r * h)
        (2 * r * h + 2 * (r - 1) * h + 2 * h + t - 2) n) :
    RestrictedTwoQ0SumOrShift r h t n := by
  rcases terminalFullShiftSlice_chain_cover
      (r := r) (h := h) (t := t) (a := 0) (k := r - 1) (n := n)
      hp (by omega) (by simpa using hn) with
    ⟨i, hi, hiSlice⟩
  exact restrictedTwoQ0Sum_or_shift_full_terminal_slice
    (r := r) (h := h) (t := t) (i := i) (n := n) hp (by
      have hr := hp.r_pos
      omega)
    (by
      unfold InInterval at *
      constructor <;> omega)

theorem restrictedTwoQ0Sum_or_shift_terminal_terminal {r h t n : Nat}
    (hp : Params r h t)
    (hn : InInterval (4 * r * h + 1) (2 * D r h t + h - 1) n) :
    RestrictedTwoQ0SumOrShift r h t n := by
  have h4 : 2 * (2 * r * h) = 4 * r * h := by
    rw [Nat.two_mul]
    rw [← Nat.add_mul]
    congr
    omega
  have hDirectHi : 2 * (2 * r * h + t + 1) - 1 = 4 * r * h + 2 * t + 1 := by
    rw [Nat.mul_add, Nat.mul_add, h4]
    omega
  by_cases hdirect : n <= 4 * r * h + 2 * t + 1
  · exact Or.inl
      (restrictedTwoQ0Sum_terminal_terminal
        (r := r) (h := h) (t := t) (n := n) hp
        (by
          unfold NatInterval
          constructor
          · unfold InInterval at hn
            rw [h4]
            exact hn.1
          · rw [hDirectHi]
            exact hdirect))
  · let n0 := n - (h - 2)
    have hn0 :
        NatInterval (2 * (2 * r * h) + 1) (2 * (2 * r * h + t + 1) - 1) n0 := by
      have hh := hp.h_ge_six
      have hlower := hp.dense_lower
      unfold D InInterval at hn
      unfold NatInterval
      dsimp [n0]
      constructor
      · rw [h4]
        omega
      · rw [hDirectHi]
        omega
    have hshift : n = h - 2 + n0 := by
      have hh := hp.h_ge_six
      have hr := hp.r_pos
      have h2rh : h <= 2 * r * h := by
        simpa [Nat.one_mul] using
          Nat.mul_le_mul_right h (by omega : 1 <= 2 * r)
      have hle : h - 2 <= n := by
        unfold InInterval at hn
        omega
      dsimp [n0]
      rw [Nat.add_comm]
      exact (Nat.sub_add_cancel hle).symm
    exact Or.inr
      ⟨n0,
        restrictedTwoQ0Sum_terminal_terminal
          (r := r) (h := h) (t := t) (n := n0) hp hn0,
        hshift⟩

/--
Dense-cap packet-sum identity `(1a)`, in pointwise coverage form.

Every `n` in `[1, 2D+h-1]` is either a restricted two-sum from `Q_0`, or is
an `(h-2)` translate of one.
-/
theorem restrictedTwoQ0Sum_or_shift_dense_cap_coverage {r h t n : Nat}
    (hp : Params r h t) (hn : InInterval 1 (2 * D r h t + h - 1) n) :
    RestrictedTwoQ0SumOrShift r h t n := by
  by_cases hsame : n <= 3 * h - 5
  · exact restrictedTwoQ0Sum_or_shift_full_same_index
      (r := r) (h := h) (t := t) (i := 0) (n := n) hp (by exact hp.r_pos)
      (by
        unfold InInterval at *
        constructor
        · simpa using hn.1
        · simpa using hsame)
  · have hh := hp.h_ge_six
    have hn_ge_two_h : 2 * h <= n := by omega
    by_cases hr2 : 2 <= r
    · by_cases hstrict : n <= 2 * (2 * r - 3) * h + 3 * h - 4
      · exact restrictedTwoQ0Sum_or_shift_full_strict_chain
          (r := r) (h := h) (t := t) (n := n) hp hr2
          ⟨hn_ge_two_h, hstrict⟩
      · have hstrict_ge_terminal_lo :
            2 * r * h <= 2 * (2 * r - 3) * h + 3 * h - 4 := by
          have hcoef : 2 * r + 1 <= 2 * (2 * r - 3) + 3 := by omega
          have hmul : (2 * r + 1) * h <= (2 * (2 * r - 3) + 3) * h :=
            Nat.mul_le_mul_right h hcoef
          have hlhs : (2 * r + 1) * h = 2 * r * h + h := by
            rw [Nat.add_mul]
            simp
          have hrhs :
              (2 * (2 * r - 3) + 3) * h = 2 * (2 * r - 3) * h + 3 * h := by
            rw [Nat.add_mul]
          rw [hlhs, hrhs] at hmul
          omega
        have hn_ge_terminal_lo : 2 * r * h <= n := by omega
        by_cases hterm :
            n <= 2 * r * h + 2 * (r - 1) * h + 2 * h + t - 2
        · exact restrictedTwoQ0Sum_or_shift_full_terminal_chain
            (r := r) (h := h) (t := t) (n := n) hp
            ⟨hn_ge_terminal_lo, hterm⟩
        · exact restrictedTwoQ0Sum_or_shift_terminal_terminal
            (r := r) (h := h) (t := t) (n := n) hp
            (by
              have hr := hp.r_pos
              have hlower := hp.dense_lower
              have h2 : 2 * r * h = 2 * (r - 1) * h + 2 * h := by
                have hrSub : r - 1 + 1 = r := Nat.sub_add_cancel hr
                calc
                  2 * r * h = 2 * ((r - 1) + 1) * h := by rw [hrSub]
                  _ = 2 * (r - 1) * h + 2 * h := by
                    rw [Nat.left_distrib, Nat.right_distrib]
              have h4 : 4 * r * h = 2 * r * h + 2 * r * h := by
                rw [← Nat.add_mul]
                congr
                omega
              unfold InInterval at *
              constructor
              · rw [h4, h2]
                omega
              · exact hn.2)
    · have hr_eq : r = 1 := by
        have hr := hp.r_pos
        omega
      have hn_ge_terminal_lo : 2 * r * h <= n := by
        rw [hr_eq]
        simpa using hn_ge_two_h
      by_cases hterm :
          n <= 2 * r * h + 2 * (r - 1) * h + 2 * h + t - 2
      · exact restrictedTwoQ0Sum_or_shift_full_terminal_chain
          (r := r) (h := h) (t := t) (n := n) hp
          ⟨hn_ge_terminal_lo, hterm⟩
      · exact restrictedTwoQ0Sum_or_shift_terminal_terminal
          (r := r) (h := h) (t := t) (n := n) hp
          (by
            have hr := hp.r_pos
            have hlower := hp.dense_lower
            have h2 : 2 * r * h = 2 * (r - 1) * h + 2 * h := by
              have hrSub : r - 1 + 1 = r := Nat.sub_add_cancel hr
              calc
                2 * r * h = 2 * ((r - 1) + 1) * h := by rw [hrSub]
                _ = 2 * (r - 1) * h + 2 * h := by
                  rw [Nat.left_distrib, Nat.right_distrib]
            have h4 : 4 * r * h = 2 * r * h + 2 * r * h := by
              rw [← Nat.add_mul]
              congr
              omega
            unfold InInterval at *
            constructor
            · rw [h4, h2]
              omega
            · exact hn.2)

end TransitionDenseCap
end GreedyThreeSumfree
