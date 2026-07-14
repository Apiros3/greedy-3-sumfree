import GreedyThreeSumfree.TransitionDenseCapPairPlusQ
import GreedyThreeSumfree.TransitionDenseCapTripleJoin

namespace GreedyThreeSumfree
namespace TransitionDenseCap

def fullTripleSliceLo (h m : Nat) : Nat := 2 * m * h

def fullTripleSliceHi (h m : Nat) : Nat := 2 * m * h + 3 * h - 3

def InFullTripleOneTrimSlice (h m n : Nat) : Prop :=
  InInterval (fullTripleSliceLo h m + 1) (fullTripleSliceHi h m - 1) n

def fullPacketTripleHi (r h : Nat) : Nat :=
  fullTripleSliceHi h (3 * r - 3) - 3

def twoFullOneTerminalSliceLo (r h m : Nat) : Nat :=
  2 * r * h + 2 * m * h + 1

def twoFullOneTerminalSliceHi (r h t m : Nat) : Nat :=
  2 * r * h + 2 * m * h + 2 * h + t - 2

def InTwoFullOneTerminalSlice (r h t m n : Nat) : Prop :=
  InInterval (twoFullOneTerminalSliceLo r h m)
    (twoFullOneTerminalSliceHi r h t m) n

def oneFullTwoTerminalSliceLo (r h m : Nat) : Nat :=
  4 * r * h + 2 * m * h + 1

def oneFullTwoTerminalSliceHi (r h t m : Nat) : Nat :=
  4 * r * h + 2 * m * h + h + 2 * t

def InOneFullTwoTerminalSlice (r h t m n : Nat) : Prop :=
  InInterval (oneFullTwoTerminalSliceLo r h m)
    (oneFullTwoTerminalSliceHi r h t m) n

theorem offset_plus_distinct_pair_offsets {a b q : Nat} (ha : 1 <= a)
    (hqlo : 1 <= q) (hqhi : q <= b + (2 * a - 1)) :
    ∃ x y z : Nat, x <= b ∧ y <= a ∧ z <= a ∧ y < z ∧ x + y + z = q := by
  have hqhi' : q <= 2 * a - 1 + b := by omega
  rcases distinct_pair_plus_offset (a := a) (b := b) (q := q) ha hqlo hqhi' with
    ⟨y, z, x, hy, hz, hx, hyz, hsum⟩
  exact ⟨x, y, z, hx, hy, hz, hyz, by omega⟩

theorem add_sub_one_right {a h : Nat} (hh : 1 <= h) :
    a + (h - 1) = a + h - 1 := by
  omega

theorem restrictedThreeQ0Sum_full_same_index {r h t i n : Nat}
    (hp : Params r h t) (hi : i < r)
    (hn :
      InInterval (3 * (2 * i * h) + 3)
        (3 * (2 * i * h + h - 1) - 3) n) :
    RestrictedThreeQ0Sum r h t n := by
  have hwidth : 2 * i * h + 2 <= 2 * i * h + h - 1 := by
    have hh := hp.h_ge_six
    omega
  have hnNat :
      NatInterval (3 * (2 * i * h) + 3)
        (3 * (2 * i * h + h - 1) - 3) n := by
    simpa [NatInterval, InInterval] using hn
  rcases interval_triple_sum_distinct hwidth hnNat with
    ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩
  refine ⟨x, y, z, ?_, ?_, ?_, hxy, hyz, hsum⟩
  · apply full_packet_interval_inQ (r := r) (h := h) (t := t) (s := 0) hi
    simpa [NatInterval, InInterval] using hx
  · apply full_packet_interval_inQ (r := r) (h := h) (t := t) (s := 0) hi
    simpa [NatInterval, InInterval] using hy
  · apply full_packet_interval_inQ (r := r) (h := h) (t := t) (s := 0) hi
    simpa [NatInterval, InInterval] using hz

theorem restrictedThreeQ0Sum_full_two_left_slice {r h t i j m n : Nat}
    (hp : Params r h t) (hi : i < r) (hj : j < r) (hij : i < j)
    (hm : i + i + j = m) (hn : InFullTripleOneTrimSlice h m n) :
    RestrictedThreeQ0Sum r h t n := by
  let B := 2 * i * h + 2 * i * h + 2 * j * h
  have hB : B = fullTripleSliceLo h m := by
    dsimp [B]
    unfold fullTripleSliceLo
    rw [← hm]
    simp [Nat.left_distrib, Nat.right_distrib]
  have hnB : InInterval (B + 1) (B + 3 * h - 4) n := by
    unfold InFullTripleOneTrimSlice at hn
    have hhi : fullTripleSliceHi h m - 1 = B + 3 * h - 4 := by
      unfold fullTripleSliceHi
      unfold fullTripleSliceLo at hB
      rw [← hB]
      have hh := hp.h_ge_six
      omega
    simpa [hB, hhi] using hn
  let q := n - B
  have hqlo : 1 <= q := by
    dsimp [q]
    unfold InInterval at hnB
    omega
  have hqhi : q <= 2 * (h - 1) - 1 + (h - 1) := by
    dsimp [q]
    unfold InInterval at hnB
    have hh := hp.h_ge_six
    omega
  have ha : 1 <= h - 1 := by
    have hh := hp.h_ge_six
    omega
  rcases distinct_pair_plus_offset (a := h - 1) (b := h - 1) (q := q)
      ha hqlo hqhi with
    ⟨u, v, w, hu, hv, hw, huv, hsum⟩
  let x := 2 * i * h + u
  let y := 2 * i * h + v
  let z := 2 * j * h + w
  have hgap := full_run_hi_lt_full_run_lo_of_lt (r := r) (h := h) (t := t) hp hij
  have hxy : x < y := by
    dsimp [x, y]
    omega
  have hyz : y < z := by
    dsimp [y, z]
    omega
  have hsum_xyz : x + y + z = n := by
    dsimp [x, y, z, q, B] at *
    omega
  refine ⟨x, y, z, ?_, ?_, ?_, hxy, hyz, hsum_xyz⟩
  · apply full_packet_interval_inQ (r := r) (h := h) (t := t) (s := 0) hi
    unfold InInterval
    dsimp [x]
    omega
  · apply full_packet_interval_inQ (r := r) (h := h) (t := t) (s := 0) hi
    unfold InInterval
    dsimp [y]
    omega
  · apply full_packet_interval_inQ (r := r) (h := h) (t := t) (s := 0) hj
    unfold InInterval
    dsimp [z]
    omega

theorem restrictedThreeQ0Sum_full_two_right_slice {r h t i j m n : Nat}
    (hp : Params r h t) (hi : i < r) (hj : j < r) (hij : i < j)
    (hm : i + j + j = m) (hn : InFullTripleOneTrimSlice h m n) :
    RestrictedThreeQ0Sum r h t n := by
  let B := 2 * i * h + 2 * j * h + 2 * j * h
  have hB : B = fullTripleSliceLo h m := by
    dsimp [B]
    unfold fullTripleSliceLo
    rw [← hm]
    simp [Nat.left_distrib, Nat.right_distrib]
  have hnB : InInterval (B + 1) (B + 3 * h - 4) n := by
    unfold InFullTripleOneTrimSlice at hn
    have hhi : fullTripleSliceHi h m - 1 = B + 3 * h - 4 := by
      unfold fullTripleSliceHi
      unfold fullTripleSliceLo at hB
      rw [← hB]
      have hh := hp.h_ge_six
      omega
    simpa [hB, hhi] using hn
  let q := n - B
  have hqlo : 1 <= q := by
    dsimp [q]
    unfold InInterval at hnB
    omega
  have hqhi : q <= 2 * (h - 1) - 1 + (h - 1) := by
    dsimp [q]
    unfold InInterval at hnB
    have hh := hp.h_ge_six
    omega
  have ha : 1 <= h - 1 := by
    have hh := hp.h_ge_six
    omega
  rcases distinct_pair_plus_offset (a := h - 1) (b := h - 1) (q := q)
      ha hqlo hqhi with
    ⟨u, v, w, hu, hv, hw, huv, hsum⟩
  let x := 2 * i * h + w
  let y := 2 * j * h + u
  let z := 2 * j * h + v
  have hgap := full_run_hi_lt_full_run_lo_of_lt (r := r) (h := h) (t := t) hp hij
  have hxy : x < y := by
    dsimp [x, y]
    omega
  have hyz : y < z := by
    dsimp [y, z]
    omega
  have hsum_xyz : x + y + z = n := by
    dsimp [x, y, z, q, B] at *
    omega
  refine ⟨x, y, z, ?_, ?_, ?_, hxy, hyz, hsum_xyz⟩
  · apply full_packet_interval_inQ (r := r) (h := h) (t := t) (s := 0) hi
    unfold InInterval
    dsimp [x]
    omega
  · apply full_packet_interval_inQ (r := r) (h := h) (t := t) (s := 0) hj
    unfold InInterval
    dsimp [y]
    omega
  · apply full_packet_interval_inQ (r := r) (h := h) (t := t) (s := 0) hj
    unfold InInterval
    dsimp [z]
    omega

theorem restrictedThreeQ0Sum_full_strict_slice {r h t i j k m n : Nat}
    (hp : Params r h t) (hi : i < r) (hj : j < r) (hk : k < r)
    (hij : i < j) (hjk : j < k)
    (hm : i + j + k = m) (hn : InFullTripleOneTrimSlice h m n) :
    RestrictedThreeQ0Sum r h t n := by
  let B := 2 * i * h + 2 * j * h + 2 * k * h
  have hB : B = fullTripleSliceLo h m := by
    dsimp [B]
    unfold fullTripleSliceLo
    rw [← hm]
    simp [Nat.left_distrib, Nat.right_distrib]
  have hnB : InInterval B (B + 3 * h - 3) n := by
    unfold InFullTripleOneTrimSlice at hn
    have hhi : fullTripleSliceHi h m - 1 <= B + 3 * h - 3 := by
      unfold fullTripleSliceHi
      unfold fullTripleSliceLo at hB
      rw [← hB]
      have hh := hp.h_ge_six
      omega
    unfold InInterval at *
    constructor
    · rw [hB]
      omega
    · omega
  let q := n - B
  have hq : InInterval (0 + 0 + 0) ((h - 1) + (h - 1) + (h - 1)) q := by
    unfold InInterval at *
    dsimp [q]
    have hh := hp.h_ge_six
    constructor <;> omega
  have hnon : 0 <= h - 1 := by omega
  rcases interval_triple_sum hnon hnon hnon hq with
    ⟨u, v, w, hu, hv, hw, hsum⟩
  unfold InInterval at hu hv hw
  let x := 2 * i * h + u
  let y := 2 * j * h + v
  let z := 2 * k * h + w
  have hgapxy := full_run_hi_lt_full_run_lo_of_lt (r := r) (h := h) (t := t) hp hij
  have hgapyz := full_run_hi_lt_full_run_lo_of_lt (r := r) (h := h) (t := t) hp hjk
  have hpos : 1 <= h := by
    have hh := hp.h_ge_six
    omega
  have hxy : x < y := by
    have hxhi : x <= 2 * i * h + h - 1 := by
      dsimp [x]
      have hxhi0 : 2 * i * h + u <= 2 * i * h + (h - 1) :=
        Nat.add_le_add_left hu.2 (2 * i * h)
      rwa [add_sub_one_right (a := 2 * i * h) (h := h) hpos] at hxhi0
    have hylo : 2 * j * h <= y := by
      dsimp [y]
      omega
    exact Nat.lt_of_le_of_lt hxhi (Nat.lt_of_lt_of_le hgapxy hylo)
  have hyz : y < z := by
    have hyhi : y <= 2 * j * h + h - 1 := by
      dsimp [y]
      have hyhi0 : 2 * j * h + v <= 2 * j * h + (h - 1) :=
        Nat.add_le_add_left hv.2 (2 * j * h)
      rwa [add_sub_one_right (a := 2 * j * h) (h := h) hpos] at hyhi0
    have hzlo : 2 * k * h <= z := by
      dsimp [z]
      omega
    exact Nat.lt_of_le_of_lt hyhi (Nat.lt_of_lt_of_le hgapyz hzlo)
  have hn_eq : n = B + q := by
    dsimp [q]
    unfold InInterval at hnB
    omega
  have hsum_xyz : x + y + z = n := by
    dsimp [x, y, z, q, B] at *
    omega
  refine ⟨x, y, z, ?_, ?_, ?_, hxy, hyz, hsum_xyz⟩
  · apply full_packet_interval_inQ (r := r) (h := h) (t := t) (s := 0) hi
    unfold InInterval
    dsimp [x]
    constructor
    · omega
    · have hxhi0 : 2 * i * h + u <= 2 * i * h + (h - 1) :=
        Nat.add_le_add_left hu.2 (2 * i * h)
      rwa [add_sub_one_right (a := 2 * i * h) (h := h) hpos] at hxhi0
  · apply full_packet_interval_inQ (r := r) (h := h) (t := t) (s := 0) hj
    unfold InInterval
    dsimp [y]
    constructor
    · omega
    · have hyhi0 : 2 * j * h + v <= 2 * j * h + (h - 1) :=
        Nat.add_le_add_left hv.2 (2 * j * h)
      rwa [add_sub_one_right (a := 2 * j * h) (h := h) hpos] at hyhi0
  · apply full_packet_interval_inQ (r := r) (h := h) (t := t) (s := 0) hk
    unfold InInterval
    dsimp [z]
    constructor
    · omega
    · have hzhi0 : 2 * k * h + w <= 2 * k * h + (h - 1) :=
        Nat.add_le_add_left hw.2 (2 * k * h)
      rwa [add_sub_one_right (a := 2 * k * h) (h := h) hpos] at hzhi0

theorem restrictedThreeQ0Sum_full_oneTrim_slice {r h t m n : Nat}
    (hp : Params r h t) (hr2 : 2 <= r) (hmlo : 1 <= m) (hmhi : m <= 3 * r - 4)
    (hn : InFullTripleOneTrimSlice h m n) :
    RestrictedThreeQ0Sum r h t n := by
  by_cases hm_low : m <= r - 1
  · have hm_pos : 0 < m := by omega
    have hslice : InFullTripleOneTrimSlice h (0 + 0 + m) n := by
      simpa using hn
    exact restrictedThreeQ0Sum_full_two_left_slice
      (r := r) (h := h) (t := t) (i := 0) (j := m) (m := 0 + 0 + m)
      (n := n) hp (by omega) (by omega) hm_pos rfl hslice
  · by_cases hm_mid : m <= 2 * r - 2
    · let a := m - (r - 1)
      have ha_pos : 0 < a := by
        dsimp [a]
        omega
      have ha_lt_r : a < r := by
        dsimp [a]
        omega
      have hlast_lt : r - 1 < r := by omega
      by_cases ha_last : a = r - 1
      · have hm_eq : 0 + (r - 1) + (r - 1) = m := by
          dsimp [a] at ha_last
          omega
        have hslice : InFullTripleOneTrimSlice h (0 + (r - 1) + (r - 1)) n := by
          simpa [← hm_eq] using hn
        exact restrictedThreeQ0Sum_full_two_right_slice
          (r := r) (h := h) (t := t) (i := 0) (j := r - 1)
          (m := 0 + (r - 1) + (r - 1)) (n := n)
          hp (by omega) hlast_lt (by omega) rfl hslice
      · have ha_lt_last : a < r - 1 := by omega
        have hm_eq : 0 + a + (r - 1) = m := by
          dsimp [a]
          omega
        have hslice : InFullTripleOneTrimSlice h (0 + a + (r - 1)) n := by
          simpa [← hm_eq] using hn
        exact restrictedThreeQ0Sum_full_strict_slice
          (r := r) (h := h) (t := t) (i := 0) (j := a) (k := r - 1)
          (m := 0 + a + (r - 1)) (n := n)
          hp (by omega) ha_lt_r hlast_lt ha_pos ha_lt_last rfl hslice
    · let a := m - (2 * r - 2)
      have ha_pos : 0 < a := by
        dsimp [a]
        omega
      have ha_lt_last : a < r - 1 := by
        dsimp [a]
        omega
      have ha_lt_r : a < r := by omega
      have hlast_lt : r - 1 < r := by omega
      have hm_eq : a + (r - 1) + (r - 1) = m := by
        dsimp [a]
        omega
      have hslice : InFullTripleOneTrimSlice h (a + (r - 1) + (r - 1)) n := by
        simpa [← hm_eq] using hn
      exact restrictedThreeQ0Sum_full_two_right_slice
        (r := r) (h := h) (t := t) (i := a) (j := r - 1)
        (m := a + (r - 1) + (r - 1)) (n := n)
        hp ha_lt_r hlast_lt ha_lt_last rfl hslice

theorem fullTripleSlice_oneTrim_next_lo_le_hi_succ {h m : Nat} (hh : 6 <= h) :
    fullTripleSliceLo h (m + 1) + 1 <= (fullTripleSliceHi h m - 1) + 1 := by
  have hhi_pos : 1 <= fullTripleSliceHi h m := by
    unfold fullTripleSliceHi
    omega
  have hstep : 2 * (m + 1) * h = 2 * m * h + 2 * h := by
    simp [Nat.left_distrib, Nat.right_distrib]
  rw [Nat.sub_add_cancel hhi_pos]
  unfold fullTripleSliceLo fullTripleSliceHi
  rw [hstep]
  omega

theorem fullTripleSlice_oneTrim_chain_cover {h a k n : Nat} (hh : 6 <= h)
    (hn :
      InInterval (fullTripleSliceLo h a + 1)
        (fullTripleSliceHi h (a + k) - 1) n) :
    ∃ m : Nat, a <= m ∧ m <= a + k ∧ InFullTripleOneTrimSlice h m n := by
  induction k with
  | zero =>
      exact ⟨a, by omega, by omega, by simpa [InFullTripleOneTrimSlice] using hn⟩
  | succ k ih =>
      by_cases hleft : n <= fullTripleSliceHi h (a + k) - 1
      · rcases ih ⟨hn.1, hleft⟩ with ⟨m, hma, hmk, hmem⟩
        exact ⟨m, hma, by omega, hmem⟩
      · have hsucc :
            (fullTripleSliceHi h (a + k) - 1) + 1 <= n :=
          Nat.succ_le_of_lt (Nat.lt_of_not_ge hleft)
        have hbridge :
            fullTripleSliceLo h ((a + k) + 1) + 1 <=
              (fullTripleSliceHi h (a + k) - 1) + 1 :=
          fullTripleSlice_oneTrim_next_lo_le_hi_succ (h := h) (m := a + k) hh
        have hlo : fullTripleSliceLo h ((a + k) + 1) + 1 <= n :=
          Nat.le_trans hbridge hsucc
        have hidx : (a + k) + 1 = a + (k + 1) := by omega
        have hhi : n <= fullTripleSliceHi h ((a + k) + 1) - 1 := by
          simpa [hidx] using hn.2
        exact ⟨(a + k) + 1, by omega, by omega, ⟨hlo, hhi⟩⟩

theorem restrictedThreeQ0Sum_first_full_block_slice {r h t n : Nat}
    (hp : Params r h t) (hn : InInterval 3 (3 * h - 6) n) :
    RestrictedThreeQ0Sum r h t n := by
  have hn0 :
      InInterval (3 * (2 * 0 * h) + 3)
        (3 * (2 * 0 * h + h - 1) - 3) n := by
    have hh := hp.h_ge_six
    unfold InInterval at *
    constructor <;> omega
  exact restrictedThreeQ0Sum_full_same_index
    (r := r) (h := h) (t := t) (i := 0) (n := n) hp (by exact hp.r_pos) hn0

theorem restrictedThreeQ0Sum_regular_full_block_chain {r h t n : Nat}
    (hp : Params r h t) (hr2 : 2 <= r)
    (hn :
      InInterval (fullTripleSliceLo h 1 + 1)
        (fullTripleSliceHi h (3 * r - 4) - 1) n) :
    RestrictedThreeQ0Sum r h t n := by
  have hlast : 1 + (3 * r - 5) = 3 * r - 4 := by omega
  have hn' :
      InInterval (fullTripleSliceLo h 1 + 1)
        (fullTripleSliceHi h (1 + (3 * r - 5)) - 1) n := by
    simpa [hlast] using hn
  rcases fullTripleSlice_oneTrim_chain_cover
      (h := h) (a := 1) (k := 3 * r - 5) (n := n) hp.h_ge_six hn' with
    ⟨m, hmlo, hmhi, hmem⟩
  exact restrictedThreeQ0Sum_full_oneTrim_slice
    (r := r) (h := h) (t := t) (m := m) (n := n)
    hp hr2 hmlo (by omega) hmem

theorem restrictedThreeQ0Sum_last_full_block_slice {r h t n : Nat}
    (hp : Params r h t)
    (hn :
      InInterval (fullTripleSliceLo h (3 * r - 3) + 3)
        (fullTripleSliceHi h (3 * r - 3) - 3) n) :
    RestrictedThreeQ0Sum r h t n := by
  have hidx : (r - 1) + (r - 1) + (r - 1) = 3 * r - 3 := by
    have hr := hp.r_pos
    omega
  have hn' :
      InInterval (3 * (2 * (r - 1) * h) + 3)
        (3 * (2 * (r - 1) * h + h - 1) - 3) n := by
    have hlo :
        3 * (2 * (r - 1) * h) + 3 =
          fullTripleSliceLo h (3 * r - 3) + 3 := by
      unfold fullTripleSliceLo
      rw [← hidx]
      simp [Nat.left_distrib, Nat.right_distrib]
      omega
    have hhi :
        3 * (2 * (r - 1) * h + h - 1) - 3 =
          fullTripleSliceHi h (3 * r - 3) - 3 := by
      unfold fullTripleSliceHi
      rw [← hidx]
      simp [Nat.left_distrib, Nat.right_distrib]
      have hh := hp.h_ge_six
      omega
    simpa [hlo, hhi] using hn
  exact restrictedThreeQ0Sum_full_same_index
    (r := r) (h := h) (t := t) (i := r - 1) (n := n) hp (by
      have hr := hp.r_pos
      omega) hn'

theorem restrictedThreeQ0Sum_full_packet_chain {r h t n : Nat}
    (hp : Params r h t) (hn : InInterval 3 (fullPacketTripleHi r h) n) :
    RestrictedThreeQ0Sum r h t n := by
  by_cases hfirst : n <= 3 * h - 6
  · exact restrictedThreeQ0Sum_first_full_block_slice
      (r := r) (h := h) (t := t) (n := n) hp ⟨hn.1, hfirst⟩
  · by_cases hr1 : r = 1
    · subst r
      have hcontr : n <= 3 * h - 6 := by
        have hh := hp.h_ge_six
        have hhi : fullPacketTripleHi 1 h = 3 * h - 6 := by
          unfold fullPacketTripleHi fullTripleSliceHi
          simp
          omega
        simpa [hhi] using hn.2
      exact False.elim (hfirst hcontr)
    · have hr2 : 2 <= r := by
        have hr := hp.r_pos
        omega
      by_cases hreg : n <= fullTripleSliceHi h (3 * r - 4) - 1
      · have hlo : fullTripleSliceLo h 1 + 1 <= n := by
          have hsucc : (3 * h - 6) + 1 <= n :=
            Nat.succ_le_of_lt (Nat.lt_of_not_ge hfirst)
          unfold fullTripleSliceLo
          have hh := hp.h_ge_six
          omega
        exact restrictedThreeQ0Sum_regular_full_block_chain
          (r := r) (h := h) (t := t) (n := n) hp hr2 ⟨hlo, hreg⟩
      · have hlo : fullTripleSliceLo h (3 * r - 3) + 3 <= n := by
          have hsucc :
              (fullTripleSliceHi h (3 * r - 4) - 1) + 1 <= n :=
            Nat.succ_le_of_lt (Nat.lt_of_not_ge hreg)
          have hbridge :
              fullTripleSliceLo h (3 * r - 3) + 3 <=
                (fullTripleSliceHi h (3 * r - 4) - 1) + 1 := by
            have hh := hp.h_ge_six
            have hhi_pos : 1 <= fullTripleSliceHi h (3 * r - 4) := by
              unfold fullTripleSliceHi
              omega
            have hcoef : 3 * r - 3 = (3 * r - 4) + 1 := by omega
            have hstep :
                2 * (3 * r - 3) * h =
                  2 * (3 * r - 4) * h + 2 * h := by
              rw [hcoef]
              simp [Nat.left_distrib, Nat.right_distrib]
            rw [Nat.sub_add_cancel hhi_pos]
            unfold fullTripleSliceLo fullTripleSliceHi
            rw [hstep]
            omega
          exact Nat.le_trans hbridge hsucc
        exact restrictedThreeQ0Sum_last_full_block_slice
          (r := r) (h := h) (t := t) (n := n) hp ⟨hlo, hn.2⟩

theorem twoFullOneTerminalSlice_next_lo_le_hi_succ {r h t m : Nat}
    (hp : Params r h t) :
    twoFullOneTerminalSliceLo r h (m + 1) <=
      twoFullOneTerminalSliceHi r h t m + 1 := by
  have ht2 : 2 <= t := two_le_t_of_params hp
  unfold twoFullOneTerminalSliceLo twoFullOneTerminalSliceHi
  simp [Nat.left_distrib, Nat.right_distrib]
  omega

theorem twoFullOneTerminalSlice_chain_cover {r h t a k n : Nat}
    (hp : Params r h t)
    (hn :
      InInterval (twoFullOneTerminalSliceLo r h a)
        (twoFullOneTerminalSliceHi r h t (a + k)) n) :
    ∃ m : Nat, a <= m ∧ m <= a + k ∧ InTwoFullOneTerminalSlice r h t m n := by
  induction k with
  | zero =>
      exact ⟨a, by omega, by omega, by simpa [InTwoFullOneTerminalSlice] using hn⟩
  | succ k ih =>
      by_cases hleft : n <= twoFullOneTerminalSliceHi r h t (a + k)
      · rcases ih ⟨hn.1, hleft⟩ with ⟨m, hma, hmk, hmem⟩
        exact ⟨m, hma, by omega, hmem⟩
      · have hsucc :
            twoFullOneTerminalSliceHi r h t (a + k) + 1 <= n :=
          Nat.succ_le_of_lt (Nat.lt_of_not_ge hleft)
        have hbridge :
            twoFullOneTerminalSliceLo r h ((a + k) + 1) <=
              twoFullOneTerminalSliceHi r h t (a + k) + 1 :=
          twoFullOneTerminalSlice_next_lo_le_hi_succ
            (r := r) (h := h) (t := t) (m := a + k) hp
        have hlo : twoFullOneTerminalSliceLo r h ((a + k) + 1) <= n :=
          Nat.le_trans hbridge hsucc
        have hidx : (a + k) + 1 = a + (k + 1) := by omega
        have hhi : n <= twoFullOneTerminalSliceHi r h t ((a + k) + 1) := by
          simpa [hidx] using hn.2
        exact ⟨(a + k) + 1, by omega, by omega, ⟨hlo, hhi⟩⟩

theorem restrictedThreeQ0Sum_two_full_same_terminal_slice {r h t i m n : Nat}
    (hp : Params r h t) (hi : i < r) (hm : i + i = m)
    (hn : InTwoFullOneTerminalSlice r h t m n) :
    RestrictedThreeQ0Sum r h t n := by
  let B := 2 * i * h + 2 * i * h + 2 * r * h
  have hB : B + 1 = twoFullOneTerminalSliceLo r h m := by
    dsimp [B]
    unfold twoFullOneTerminalSliceLo
    rw [← hm]
    simp [Nat.left_distrib, Nat.right_distrib]
    omega
  have hnB : InInterval (B + 1) (B + 2 * h + t - 2) n := by
    unfold InTwoFullOneTerminalSlice at hn
    have hhi :
        twoFullOneTerminalSliceHi r h t m = B + 2 * h + t - 2 := by
      dsimp [B]
      unfold twoFullOneTerminalSliceHi
      rw [← hm]
      simp [Nat.left_distrib, Nat.right_distrib]
      omega
    simpa [← hB, hhi] using hn
  let q := n - B
  have hqlo : 1 <= q := by
    dsimp [q]
    unfold InInterval at hnB
    omega
  have hqhi : q <= 2 * (h - 1) - 1 + (t + 1) := by
    dsimp [q]
    unfold InInterval at hnB
    have hh := hp.h_ge_six
    omega
  have ha : 1 <= h - 1 := by
    have hh := hp.h_ge_six
    omega
  rcases distinct_pair_plus_offset (a := h - 1) (b := t + 1) (q := q)
      ha hqlo hqhi with
    ⟨u, v, w, hu, hv, hw, huv, hsum⟩
  let x := 2 * i * h + u
  let y := 2 * i * h + v
  let z := 2 * r * h + w
  have hgap := full_run_hi_lt_terminal_cap_lo (r := r) (h := h) (t := t) (i := i) hp hi
  have hxy : x < y := by
    dsimp [x, y]
    omega
  have hyz : y < z := by
    dsimp [y, z]
    omega
  have hsum_xyz : x + y + z = n := by
    dsimp [x, y, z, q, B] at *
    omega
  refine ⟨x, y, z, ?_, ?_, ?_, hxy, hyz, hsum_xyz⟩
  · apply full_packet_interval_inQ (r := r) (h := h) (t := t) (s := 0) hi
    unfold InInterval
    dsimp [x]
    omega
  · apply full_packet_interval_inQ (r := r) (h := h) (t := t) (s := 0) hi
    unfold InInterval
    dsimp [y]
    omega
  · apply terminal_cap_interval_inQ (r := r) (h := h) (t := t) (s := 0)
    unfold InInterval
    dsimp [z]
    omega

theorem restrictedThreeQ0Sum_two_full_strict_terminal_slice {r h t i j m n : Nat}
    (hp : Params r h t) (hi : i < r) (hj : j < r) (hij : i < j)
    (hm : i + j = m) (hn : InTwoFullOneTerminalSlice r h t m n) :
    RestrictedThreeQ0Sum r h t n := by
  let B := 2 * i * h + 2 * j * h + 2 * r * h
  have hB : B + 1 = twoFullOneTerminalSliceLo r h m := by
    dsimp [B]
    unfold twoFullOneTerminalSliceLo
    rw [← hm]
    simp [Nat.left_distrib, Nat.right_distrib]
    omega
  have hnB : InInterval B (B + 2 * h + t - 1) n := by
    unfold InTwoFullOneTerminalSlice at hn
    have hhi :
        twoFullOneTerminalSliceHi r h t m <= B + 2 * h + t - 1 := by
      dsimp [B]
      unfold twoFullOneTerminalSliceHi
      rw [← hm]
      simp [Nat.left_distrib, Nat.right_distrib]
      omega
    unfold InInterval at *
    constructor
    · rw [← hB] at hn
      omega
    · omega
  let q := n - B
  have hq : InInterval (0 + 0 + 0) ((h - 1) + (h - 1) + (t + 1)) q := by
    unfold InInterval at *
    dsimp [q]
    have hh := hp.h_ge_six
    constructor <;> omega
  have hfull : 0 <= h - 1 := by omega
  have hterm : 0 <= t + 1 := by omega
  rcases interval_triple_sum hfull hfull hterm hq with
    ⟨u, v, w, hu, hv, hw, hsum⟩
  unfold InInterval at hu hv hw
  let x := 2 * i * h + u
  let y := 2 * j * h + v
  let z := 2 * r * h + w
  have hgapxy := full_run_hi_lt_full_run_lo_of_lt (r := r) (h := h) (t := t) hp hij
  have hgapyz := full_run_hi_lt_terminal_cap_lo (r := r) (h := h) (t := t) (i := j) hp hj
  have hpos : 1 <= h := by
    have hh := hp.h_ge_six
    omega
  have hxy : x < y := by
    have hxhi : x <= 2 * i * h + h - 1 := by
      dsimp [x]
      have hxhi0 : 2 * i * h + u <= 2 * i * h + (h - 1) :=
        Nat.add_le_add_left hu.2 (2 * i * h)
      rwa [add_sub_one_right (a := 2 * i * h) (h := h) hpos] at hxhi0
    have hylo : 2 * j * h <= y := by
      dsimp [y]
      omega
    exact Nat.lt_of_le_of_lt hxhi (Nat.lt_of_lt_of_le hgapxy hylo)
  have hyz : y < z := by
    have hyhi : y <= 2 * j * h + h - 1 := by
      dsimp [y]
      have hyhi0 : 2 * j * h + v <= 2 * j * h + (h - 1) :=
        Nat.add_le_add_left hv.2 (2 * j * h)
      rwa [add_sub_one_right (a := 2 * j * h) (h := h) hpos] at hyhi0
    have hzlo : 2 * r * h <= z := by
      dsimp [z]
      omega
    exact Nat.lt_of_le_of_lt hyhi (Nat.lt_of_lt_of_le hgapyz hzlo)
  have hn_eq : n = B + q := by
    dsimp [q]
    unfold InInterval at hnB
    omega
  have hsum_xyz : x + y + z = n := by
    dsimp [x, y, z, q, B] at *
    omega
  refine ⟨x, y, z, ?_, ?_, ?_, hxy, hyz, hsum_xyz⟩
  · apply full_packet_interval_inQ (r := r) (h := h) (t := t) (s := 0) hi
    unfold InInterval
    dsimp [x]
    constructor
    · omega
    · have hxhi0 : 2 * i * h + u <= 2 * i * h + (h - 1) :=
        Nat.add_le_add_left hu.2 (2 * i * h)
      rwa [add_sub_one_right (a := 2 * i * h) (h := h) hpos] at hxhi0
  · apply full_packet_interval_inQ (r := r) (h := h) (t := t) (s := 0) hj
    unfold InInterval
    dsimp [y]
    constructor
    · omega
    · have hyhi0 : 2 * j * h + v <= 2 * j * h + (h - 1) :=
        Nat.add_le_add_left hv.2 (2 * j * h)
      rwa [add_sub_one_right (a := 2 * j * h) (h := h) hpos] at hyhi0
  · apply terminal_cap_interval_inQ (r := r) (h := h) (t := t) (s := 0)
    unfold InInterval
    dsimp [z]
    constructor
    · omega
    · exact Nat.add_le_add_left hw.2 (2 * r * h)

theorem restrictedThreeQ0Sum_two_full_one_terminal_slice {r h t m n : Nat}
    (hp : Params r h t) (hm : m <= 2 * r - 2)
    (hn : InTwoFullOneTerminalSlice r h t m n) :
    RestrictedThreeQ0Sum r h t n := by
  by_cases hsmall : m <= r - 1
  · by_cases hm0 : m = 0
    · have hslice : InTwoFullOneTerminalSlice r h t (0 + 0) n := by
        simpa [hm0] using hn
      exact restrictedThreeQ0Sum_two_full_same_terminal_slice
        (r := r) (h := h) (t := t) (i := 0) (m := 0 + 0) (n := n)
        hp (by exact hp.r_pos) rfl hslice
    · have hm_pos : 0 < m := by omega
      have hslice : InTwoFullOneTerminalSlice r h t (0 + m) n := by
        simpa using hn
      exact restrictedThreeQ0Sum_two_full_strict_terminal_slice
        (r := r) (h := h) (t := t) (i := 0) (j := m) (m := 0 + m) (n := n)
        hp (by omega) (by omega) hm_pos rfl hslice
  · let i := m - (r - 1)
    have hi : i < r := by
      dsimp [i]
      omega
    have hlast : r - 1 < r := by omega
    by_cases hitop : i = r - 1
    · have hm_eq : (r - 1) + (r - 1) = m := by
        dsimp [i] at hitop
        omega
      have hslice : InTwoFullOneTerminalSlice r h t ((r - 1) + (r - 1)) n := by
        simpa [hm_eq] using hn
      exact restrictedThreeQ0Sum_two_full_same_terminal_slice
        (r := r) (h := h) (t := t) (i := r - 1)
        (m := (r - 1) + (r - 1)) (n := n)
        hp hlast rfl hslice
    · have hij : i < r - 1 := by
        dsimp [i]
        omega
      have hm_eq : i + (r - 1) = m := by
        dsimp [i]
        omega
      have hslice : InTwoFullOneTerminalSlice r h t (i + (r - 1)) n := by
        simpa [hm_eq] using hn
      exact restrictedThreeQ0Sum_two_full_strict_terminal_slice
        (r := r) (h := h) (t := t) (i := i) (j := r - 1)
        (m := i + (r - 1)) (n := n)
        hp hi hlast hij rfl hslice

theorem restrictedThreeQ0Sum_two_full_one_terminal_chain {r h t n : Nat}
    (hp : Params r h t)
    (hn :
      InInterval (twoFullOneTerminalSliceLo r h 0)
        (twoFullOneTerminalSliceHi r h t (2 * r - 2)) n) :
    RestrictedThreeQ0Sum r h t n := by
  have hlast : 0 + (2 * r - 2) = 2 * r - 2 := by omega
  have hn' :
      InInterval (twoFullOneTerminalSliceLo r h 0)
        (twoFullOneTerminalSliceHi r h t (0 + (2 * r - 2))) n := by
    simpa [hlast] using hn
  rcases twoFullOneTerminalSlice_chain_cover
      (r := r) (h := h) (t := t) (a := 0) (k := 2 * r - 2) (n := n) hp hn' with
    ⟨m, _hmlo, hmhi, hmem⟩
  exact restrictedThreeQ0Sum_two_full_one_terminal_slice
    (r := r) (h := h) (t := t) (m := m) (n := n) hp (by omega) hmem

theorem oneFullTwoTerminalSlice_next_lo_le_hi_succ {r h t m : Nat}
    (hp : Params r h t) :
    oneFullTwoTerminalSliceLo r h (m + 1) <=
      oneFullTwoTerminalSliceHi r h t m + 1 := by
  have hlow := hp.dense_lower
  unfold oneFullTwoTerminalSliceLo oneFullTwoTerminalSliceHi
  simp [Nat.left_distrib, Nat.right_distrib]
  omega

theorem oneFullTwoTerminalSlice_chain_cover {r h t a k n : Nat}
    (hp : Params r h t)
    (hn :
      InInterval (oneFullTwoTerminalSliceLo r h a)
        (oneFullTwoTerminalSliceHi r h t (a + k)) n) :
    ∃ m : Nat, a <= m ∧ m <= a + k ∧ InOneFullTwoTerminalSlice r h t m n := by
  induction k with
  | zero =>
      exact ⟨a, by omega, by omega, by simpa [InOneFullTwoTerminalSlice] using hn⟩
  | succ k ih =>
      by_cases hleft : n <= oneFullTwoTerminalSliceHi r h t (a + k)
      · rcases ih ⟨hn.1, hleft⟩ with ⟨m, hma, hmk, hmem⟩
        exact ⟨m, hma, by omega, hmem⟩
      · have hsucc :
            oneFullTwoTerminalSliceHi r h t (a + k) + 1 <= n :=
          Nat.succ_le_of_lt (Nat.lt_of_not_ge hleft)
        have hbridge :
            oneFullTwoTerminalSliceLo r h ((a + k) + 1) <=
              oneFullTwoTerminalSliceHi r h t (a + k) + 1 :=
          oneFullTwoTerminalSlice_next_lo_le_hi_succ
            (r := r) (h := h) (t := t) (m := a + k) hp
        have hlo : oneFullTwoTerminalSliceLo r h ((a + k) + 1) <= n :=
          Nat.le_trans hbridge hsucc
        have hidx : (a + k) + 1 = a + (k + 1) := by omega
        have hhi : n <= oneFullTwoTerminalSliceHi r h t ((a + k) + 1) := by
          simpa [hidx] using hn.2
        exact ⟨(a + k) + 1, by omega, by omega, ⟨hlo, hhi⟩⟩

theorem restrictedThreeQ0Sum_one_full_two_terminal_slice {r h t i n : Nat}
    (hp : Params r h t) (hi : i < r)
    (hn : InOneFullTwoTerminalSlice r h t i n) :
    RestrictedThreeQ0Sum r h t n := by
  let B := 2 * i * h + 2 * r * h + 2 * r * h
  have hrr : 2 * r * h + 2 * r * h = 4 * r * h := by
    rw [← Nat.add_mul]
    have hc : 2 * r + 2 * r = 4 * r := by omega
    rw [hc]
  have hBLo : B + 1 = oneFullTwoTerminalSliceLo r h i := by
    dsimp [B]
    unfold oneFullTwoTerminalSliceLo
    omega
  have hBHi : oneFullTwoTerminalSliceHi r h t i = B + h + 2 * t := by
    dsimp [B]
    unfold oneFullTwoTerminalSliceHi
    omega
  let q := n - B
  have hqlo : 1 <= q := by
    dsimp [q]
    unfold InOneFullTwoTerminalSlice InInterval at hn
    rw [← hBLo] at hn
    omega
  have hqhi : q <= (h - 1) + (2 * (t + 1) - 1) := by
    dsimp [q]
    unfold InOneFullTwoTerminalSlice InInterval at hn
    rw [hBHi] at hn
    have hh := hp.h_ge_six
    omega
  have htA : 1 <= t + 1 := by omega
  rcases offset_plus_distinct_pair_offsets (a := t + 1) (b := h - 1) (q := q)
      htA hqlo hqhi with
    ⟨u, v, w, hu, hv, hw, hvw, hsum⟩
  let x := 2 * i * h + u
  let y := 2 * r * h + v
  let z := 2 * r * h + w
  have hgap := full_run_hi_lt_terminal_cap_lo (r := r) (h := h) (t := t)
    (i := i) hp hi
  have hpos : 1 <= h := by
    have hh := hp.h_ge_six
    omega
  have hxy : x < y := by
    have hxhi : x <= 2 * i * h + h - 1 := by
      dsimp [x]
      have hxhi0 : 2 * i * h + u <= 2 * i * h + (h - 1) :=
        Nat.add_le_add_left hu (2 * i * h)
      rwa [add_sub_one_right (a := 2 * i * h) (h := h) hpos] at hxhi0
    have hylo : 2 * r * h <= y := by
      dsimp [y]
      omega
    exact Nat.lt_of_le_of_lt hxhi (Nat.lt_of_lt_of_le hgap hylo)
  have hyz : y < z := by
    dsimp [y, z]
    omega
  have hn_eq : n = B + q := by
    dsimp [q]
    unfold InOneFullTwoTerminalSlice InInterval at hn
    rw [← hBLo] at hn
    omega
  have hsum_xyz : x + y + z = n := by
    dsimp [x, y, z, q, B] at *
    omega
  refine ⟨x, y, z, ?_, ?_, ?_, hxy, hyz, hsum_xyz⟩
  · apply full_packet_interval_inQ (r := r) (h := h) (t := t) (s := 0) hi
    unfold InInterval
    dsimp [x]
    constructor
    · omega
    · have hxhi0 : 2 * i * h + u <= 2 * i * h + (h - 1) :=
        Nat.add_le_add_left hu (2 * i * h)
      rwa [add_sub_one_right (a := 2 * i * h) (h := h) hpos] at hxhi0
  · apply terminal_cap_interval_inQ (r := r) (h := h) (t := t) (s := 0)
    unfold InInterval
    dsimp [y]
    exact ⟨by omega, Nat.add_le_add_left hv (2 * r * h)⟩
  · apply terminal_cap_interval_inQ (r := r) (h := h) (t := t) (s := 0)
    unfold InInterval
    dsimp [z]
    exact ⟨by omega, Nat.add_le_add_left hw (2 * r * h)⟩

theorem restrictedThreeQ0Sum_one_full_two_terminal_chain {r h t n : Nat}
    (hp : Params r h t)
    (hn :
      InInterval (oneFullTwoTerminalSliceLo r h 0)
        (oneFullTwoTerminalSliceHi r h t (r - 1)) n) :
    RestrictedThreeQ0Sum r h t n := by
  have hlast : 0 + (r - 1) = r - 1 := by omega
  have hn' :
      InInterval (oneFullTwoTerminalSliceLo r h 0)
        (oneFullTwoTerminalSliceHi r h t (0 + (r - 1))) n := by
    simpa [hlast] using hn
  rcases oneFullTwoTerminalSlice_chain_cover
      (r := r) (h := h) (t := t) (a := 0) (k := r - 1) (n := n) hp hn' with
    ⟨m, _hmlo, hmhi, hmem⟩
  have hm_lt : m < r := by
    have hr := hp.r_pos
    omega
  exact restrictedThreeQ0Sum_one_full_two_terminal_slice
    (r := r) (h := h) (t := t) (i := m) (n := n) hp hm_lt hmem

theorem restrictedThreeQ0Sum_one_full_two_terminal_final_mixed_slice {r h t n : Nat}
    (hp : Params r h t)
    (hn : InInterval (LastMixedTerminalSliceLo r h) (LastMixedTerminalSliceHi r h t) n) :
    RestrictedThreeQ0Sum r h t n := by
  let B := 2 * (r - 1) * h + 2 * r * h + 2 * r * h
  have hBLo : B + 1 = LastMixedTerminalSliceLo r h := by
    dsimp [B]
    unfold LastMixedTerminalSliceLo
    have hr := hp.r_pos
    have hcoef : 2 * (r - 1) + 2 * r + 2 * r = 6 * r - 2 := by omega
    calc
      2 * (r - 1) * h + 2 * r * h + 2 * r * h + 1 =
          ((2 * (r - 1) + 2 * r + 2 * r) * h) + 1 := by
            rw [Nat.add_mul, Nat.add_mul]
      _ = (6 * r - 2) * h + 1 := by rw [hcoef]
  have hBHi : LastMixedTerminalSliceHi r h t = B + h + 2 * t := by
    dsimp [B]
    unfold LastMixedTerminalSliceHi
    have hr := hp.r_pos
    have hcoef : 2 * (r - 1) + 1 + 2 * r + 2 * r = 6 * r - 1 := by omega
    calc
      (6 * r - 1) * h + 2 * t =
          ((2 * (r - 1) + 1 + 2 * r + 2 * r) * h) + 2 * t := by rw [hcoef]
      _ = 2 * (r - 1) * h + h + 2 * r * h + 2 * r * h + 2 * t := by
            rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.one_mul]
      _ = 2 * (r - 1) * h + 2 * r * h + 2 * r * h + h + 2 * t := by omega
  let q := n - B
  have hqlo : 1 <= q := by
    dsimp [q]
    unfold InInterval at hn
    rw [← hBLo] at hn
    omega
  have hqhi : q <= (h - 1) + (2 * (t + 1) - 1) := by
    dsimp [q]
    unfold InInterval at hn
    rw [hBHi] at hn
    have hh := hp.h_ge_six
    omega
  have htA : 1 <= t + 1 := by omega
  rcases offset_plus_distinct_pair_offsets (a := t + 1) (b := h - 1) (q := q)
      htA hqlo hqhi with
    ⟨u, v, w, hu, hv, hw, hvw, hsum⟩
  let x := 2 * (r - 1) * h + u
  let y := 2 * r * h + v
  let z := 2 * r * h + w
  have hlast : r - 1 < r := by
    have hr := hp.r_pos
    omega
  have hgap := full_run_hi_lt_terminal_cap_lo (r := r) (h := h) (t := t)
    (i := r - 1) hp hlast
  have hpos : 1 <= h := by
    have hh := hp.h_ge_six
    omega
  have hxy : x < y := by
    have hxhi : x <= 2 * (r - 1) * h + h - 1 := by
      dsimp [x]
      have hxhi0 : 2 * (r - 1) * h + u <= 2 * (r - 1) * h + (h - 1) :=
        Nat.add_le_add_left hu (2 * (r - 1) * h)
      rwa [add_sub_one_right (a := 2 * (r - 1) * h) (h := h) hpos] at hxhi0
    have hylo : 2 * r * h <= y := by
      dsimp [y]
      omega
    exact Nat.lt_of_le_of_lt hxhi (Nat.lt_of_lt_of_le hgap hylo)
  have hyz : y < z := by
    dsimp [y, z]
    omega
  have hn_eq : n = B + q := by
    dsimp [q]
    unfold InInterval at hn
    rw [← hBLo] at hn
    omega
  have hsum_xyz : x + y + z = n := by
    dsimp [x, y, z, q, B] at *
    omega
  refine ⟨x, y, z, ?_, ?_, ?_, hxy, hyz, hsum_xyz⟩
  · apply full_packet_interval_inQ (r := r) (h := h) (t := t) (s := 0) hlast
    unfold InInterval
    dsimp [x]
    constructor
    · omega
    · have hxhi0 : 2 * (r - 1) * h + u <= 2 * (r - 1) * h + (h - 1) :=
        Nat.add_le_add_left hu (2 * (r - 1) * h)
      rwa [add_sub_one_right (a := 2 * (r - 1) * h) (h := h) hpos] at hxhi0
  · apply terminal_cap_interval_inQ (r := r) (h := h) (t := t) (s := 0)
    unfold InInterval
    dsimp [y]
    exact ⟨by omega, Nat.add_le_add_left hv (2 * r * h)⟩
  · apply terminal_cap_interval_inQ (r := r) (h := h) (t := t) (s := 0)
    unfold InInterval
    dsimp [z]
    exact ⟨by omega, Nat.add_le_add_left hw (2 * r * h)⟩

theorem restrictedThreeQ0Sum_all_terminal_slice {r h t n : Nat}
    (hp : Params r h t)
    (hn : InInterval (AllTerminalSliceLo r h) (AllTerminalSliceHi r h t) n) :
    RestrictedThreeQ0Sum r h t n := by
  have hwidth : 2 * r * h + 2 <= 2 * r * h + t + 1 := by
    have ht : 1 <= t := one_le_t_of_params hp
    omega
  have hnNat :
      NatInterval (3 * (2 * r * h) + 3)
        (3 * (2 * r * h + t + 1) - 3) n := by
    have hlo : 3 * (2 * r * h) + 3 = AllTerminalSliceLo r h := by
      unfold AllTerminalSliceLo
      calc
        3 * (2 * r * h) + 3 = (3 * (2 * r)) * h + 3 := by
          rw [← Nat.mul_assoc]
        _ = (6 * r) * h + 3 := by
          have hc : 3 * (2 * r) = 6 * r := by omega
          rw [hc]
        _ = 6 * r * h + 3 := by
          rw [Nat.mul_assoc]
    have hhi : 3 * (2 * r * h + t + 1) - 3 = AllTerminalSliceHi r h t := by
      unfold AllTerminalSliceHi
      have hbase : 3 * (2 * r * h) = 6 * r * h := by
        calc
          3 * (2 * r * h) = (3 * (2 * r)) * h := by
            rw [← Nat.mul_assoc]
          _ = (6 * r) * h := by
            have hc : 3 * (2 * r) = 6 * r := by omega
            rw [hc]
          _ = 6 * r * h := by
            rw [Nat.mul_assoc]
      rw [Nat.mul_add, Nat.mul_add, hbase]
      omega
    simpa [NatInterval, InInterval, hlo, hhi] using hn
  rcases interval_triple_sum_distinct hwidth hnNat with
    ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩
  refine ⟨x, y, z, ?_, ?_, ?_, hxy, hyz, hsum⟩
  · apply terminal_cap_interval_inQ (r := r) (h := h) (t := t) (s := 0)
    simpa [NatInterval, InInterval] using hx
  · apply terminal_cap_interval_inQ (r := r) (h := h) (t := t) (s := 0)
    simpa [NatInterval, InInterval] using hy
  · apply terminal_cap_interval_inQ (r := r) (h := h) (t := t) (s := 0)
    simpa [NatInterval, InInterval] using hz

theorem full_packet_to_two_full_one_terminal_overlap {r h t : Nat}
    (hp : Params r h t) :
    twoFullOneTerminalSliceLo r h 0 <= fullPacketTripleHi r h + 1 := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have hcoef : 2 * (3 * r - 3) + 3 = 6 * r - 3 := by omega
  have hprod : 2 * (3 * r - 3) * h + 3 * h = (6 * r - 3) * h := by
    rw [← Nat.add_mul, hcoef]
  have hfull : fullPacketTripleHi r h + 1 = (6 * r - 3) * h - 5 := by
    unfold fullPacketTripleHi fullTripleSliceHi
    rw [hprod]
    omega
  have hcoef_le : 2 * r + 1 <= 6 * r - 3 := by omega
  have hmul := Nat.mul_le_mul_right h hcoef_le
  have hleft : twoFullOneTerminalSliceLo r h 0 <= (2 * r + 1) * h - 5 := by
    unfold twoFullOneTerminalSliceLo
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hright : (2 * r + 1) * h - 5 <= (6 * r - 3) * h - 5 := by
    omega
  rw [hfull]
  exact Nat.le_trans hleft hright

theorem two_full_one_terminal_to_final_mixed_overlap {r h t : Nat}
    (hp : Params r h t) :
    LastMixedTerminalSliceLo r h <=
      twoFullOneTerminalSliceHi r h t (2 * r - 2) + 1 := by
  have ht2 : 2 <= t := two_le_t_of_params hp
  have hcoef : 2 * r + 2 * (2 * r - 2) + 2 = 6 * r - 2 := by
    have hr := hp.r_pos
    omega
  have hprod :
      2 * r * h + 2 * (2 * r - 2) * h + 2 * h = (6 * r - 2) * h := by
    rw [← Nat.add_mul, ← Nat.add_mul, hcoef]
  unfold LastMixedTerminalSliceLo twoFullOneTerminalSliceHi
  rw [hprod]
  omega

theorem oneFullTwoTerminal_final_hi_eq_lastMixedTerminalSliceHi {r h t : Nat}
    (hp : Params r h t) :
    oneFullTwoTerminalSliceHi r h t (r - 1) = LastMixedTerminalSliceHi r h t := by
  have hcoef : (4 * r + 2 * (r - 1)) + 1 = 6 * r - 1 := by
    have hr := hp.r_pos
    omega
  have hprod :
      4 * r * h + 2 * (r - 1) * h + h = (6 * r - 1) * h := by
    calc
      4 * r * h + 2 * (r - 1) * h + h =
          (4 * r * h + 2 * (r - 1) * h) + 1 * h := by simp
      _ = (4 * r + 2 * (r - 1)) * h + 1 * h := by
        rw [← Nat.add_mul]
      _ = ((4 * r + 2 * (r - 1)) + 1) * h := by
        rw [← Nat.add_mul]
      _ = (6 * r - 1) * h := by rw [hcoef]
  unfold oneFullTwoTerminalSliceHi LastMixedTerminalSliceHi
  rw [hprod]

theorem two_full_one_terminal_to_one_full_two_terminal_overlap {r h t : Nat}
    (hp : Params r h t) :
    oneFullTwoTerminalSliceLo r h 0 <=
      twoFullOneTerminalSliceHi r h t (2 * r - 2) + 1 := by
  have hone_to_last :
      oneFullTwoTerminalSliceLo r h 0 <= LastMixedTerminalSliceLo r h := by
    unfold oneFullTwoTerminalSliceLo LastMixedTerminalSliceLo
    have hcoef : 4 * r <= 6 * r - 2 := by
      have hr := hp.r_pos
      omega
    have hmul := Nat.mul_le_mul_right h hcoef
    omega
  exact Nat.le_trans hone_to_last
    (two_full_one_terminal_to_final_mixed_overlap (r := r) (h := h) (t := t) hp)

theorem final_mixed_to_all_terminal_overlap {r h t : Nat}
    (hp : Params r h t) :
    AllTerminalSliceLo r h <= LastMixedTerminalSliceHi r h t + 1 := by
  exact terminalSlicesMeet_of_params hp

theorem restrictedThreeQ0Sum_dense_cap_pointwise {r h t n : Nat}
    (hp : Params r h t) (hn : InInterval 3 (3 * D r h t) n) :
    RestrictedThreeQ0Sum r h t n := by
  by_cases hfull : n <= fullPacketTripleHi r h
  · exact restrictedThreeQ0Sum_full_packet_chain
      (r := r) (h := h) (t := t) (n := n) hp ⟨hn.1, hfull⟩
  · have hafter_full : fullPacketTripleHi r h + 1 <= n :=
      Nat.succ_le_of_lt (Nat.lt_of_not_ge hfull)
    by_cases htwo : n <= twoFullOneTerminalSliceHi r h t (2 * r - 2)
    · apply restrictedThreeQ0Sum_two_full_one_terminal_chain
        (r := r) (h := h) (t := t) (n := n) hp
      constructor
      · exact Nat.le_trans
          (full_packet_to_two_full_one_terminal_overlap (r := r) (h := h) (t := t) hp)
          hafter_full
      · exact htwo
    · have hafter_two : twoFullOneTerminalSliceHi r h t (2 * r - 2) + 1 <= n :=
        Nat.succ_le_of_lt (Nat.lt_of_not_ge htwo)
      by_cases hmixed : n <= LastMixedTerminalSliceHi r h t
      · apply restrictedThreeQ0Sum_one_full_two_terminal_chain
          (r := r) (h := h) (t := t) (n := n) hp
        constructor
        · exact Nat.le_trans
            (two_full_one_terminal_to_one_full_two_terminal_overlap
              (r := r) (h := h) (t := t) hp)
            hafter_two
        · have hhi := oneFullTwoTerminal_final_hi_eq_lastMixedTerminalSliceHi
            (r := r) (h := h) (t := t) hp
          simpa [hhi] using hmixed
      · have hafter_mixed : LastMixedTerminalSliceHi r h t + 1 <= n :=
          Nat.succ_le_of_lt (Nat.lt_of_not_ge hmixed)
        apply restrictedThreeQ0Sum_all_terminal_slice
          (r := r) (h := h) (t := t) (n := n) hp
        constructor
        · exact Nat.le_trans
            (final_mixed_to_all_terminal_overlap (r := r) (h := h) (t := t) hp)
            hafter_mixed
        · have htop : AllTerminalSliceHi r h t = 3 * D r h t := by
            unfold AllTerminalSliceHi D
            have hbase : 3 * (2 * r * h) = 6 * r * h := by
              calc
                3 * (2 * r * h) = (3 * (2 * r)) * h := by
                  rw [← Nat.mul_assoc]
                _ = (6 * r) * h := by
                  have hc : 3 * (2 * r) = 6 * r := by omega
                  rw [hc]
                _ = 6 * r * h := by
                  rw [Nat.mul_assoc]
            rw [Nat.mul_add, hbase]
          simpa [htop] using hn.2

end TransitionDenseCap
end GreedyThreeSumfree
