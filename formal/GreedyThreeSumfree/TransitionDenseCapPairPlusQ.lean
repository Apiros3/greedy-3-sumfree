import GreedyThreeSumfree.TransitionDenseCapPairSums

set_option linter.unusedVariables false

namespace GreedyThreeSumfree
namespace TransitionDenseCap

theorem full_packet_interval_inQ {r h t s i n : Nat} (hi : i < r)
    (hn : InInterval (2 * i * h) (2 * i * h + h - 1) n) :
    InQ r h t s n := by
  apply inQ_of_full_packet_run (i := i)
  unfold InFullPacketRun
  exact ⟨hi, hn⟩

theorem terminal_cap_interval_inQ {r h t s n : Nat}
    (hn : InInterval (2 * r * h) (2 * r * h + t + 1 - s) n) :
    InQ r h t s n := by
  apply inQ_of_terminal_cap
  unfold InTerminalCap
  exact hn

theorem interval_triple_sum {L1 U1 L2 U2 L3 U3 n : Nat}
    (h1 : L1 <= U1) (h2 : L2 <= U2) (h3 : L3 <= U3)
    (hn : InInterval (L1 + L2 + L3) (U1 + U2 + U3) n) :
    ∃ x y z : Nat,
      InInterval L1 U1 x ∧
      InInterval L2 U2 y ∧
      InInterval L3 U3 z ∧
      x + y + z = n := by
  have h12 : L1 + L2 <= U1 + U2 := by omega
  have hn' : InInterval ((L1 + L2) + L3) ((U1 + U2) + U3) n := by
    unfold InInterval at *
    constructor <;> omega
  rcases interval_pair_sum h12 h3 hn' with ⟨xy, z, hxy, hz, hsum_xy_z⟩
  rcases interval_pair_sum h1 h2 hxy with ⟨x, y, hx, hy, hsum_xy⟩
  exact ⟨x, y, z, hx, hy, hz, by omega⟩

theorem full_run_hi_lt_full_run_lo_of_lt {r h t i j : Nat}
    (hp : Params r h t) (hij : i < j) :
    2 * i * h + h - 1 < 2 * j * h := by
  have hh := hp.h_ge_six
  have hij_le : i + 1 <= j := by omega
  have hcoef : 2 * (i + 1) <= 2 * j := Nat.mul_le_mul_left 2 hij_le
  have hprod : 2 * (i + 1) * h <= 2 * j * h :=
    Nat.mul_le_mul_right h hcoef
  have hprod_eq : 2 * (i + 1) * h = 2 * i * h + 2 * h := by
    simp [Nat.left_distrib, Nat.right_distrib]
  rw [hprod_eq] at hprod
  have hlt : 2 * i * h + h - 1 < 2 * i * h + 2 * h := by omega
  exact Nat.lt_of_lt_of_le hlt hprod

theorem full_run_hi_lt_terminal_cap_lo {r h t i : Nat}
    (hp : Params r h t) (hi : i < r) :
    2 * i * h + h - 1 < 2 * r * h := by
  exact full_run_hi_lt_full_run_lo_of_lt (r := r + 1) (h := h) (t := t)
    { r_pos := by omega
      h_ge_six := hp.h_ge_six
      dense_lower := hp.dense_lower
      dense_upper := hp.dense_upper } hi

theorem distinct_pair_offsets {a q : Nat} (ha : 1 <= a)
    (hqlo : 1 <= q) (hqhi : q <= 2 * a - 1) :
    ∃ x y : Nat, x <= a ∧ y <= a ∧ x < y ∧ x + y = q := by
  by_cases hqa : q <= a
  · exact ⟨0, q, by omega, hqa, by omega, by omega⟩
  · refine ⟨q - a, a, ?_, by omega, ?_, ?_⟩
    · omega
    · omega
    · omega

theorem distinct_pair_plus_offset {a b q : Nat} (ha : 1 <= a)
    (hqlo : 1 <= q) (hqhi : q <= 2 * a - 1 + b) :
    ∃ x y z : Nat, x <= a ∧ y <= a ∧ z <= b ∧ x < y ∧ x + y + z = q := by
  by_cases hqpair : q <= 2 * a - 1
  · rcases distinct_pair_offsets (a := a) (q := q) ha hqlo hqpair with
      ⟨x, y, hx, hy, hxy, hsum⟩
    exact ⟨x, y, 0, hx, hy, by omega, hxy, by omega⟩
  · refine ⟨a - 1, a, q - (2 * a - 1), ?_, by omega, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · omega

theorem restrictedTwoQ0PlusQSum_first_full_run {r h t s n : Nat}
    (hp : Params r h t) (hnlo : 1 <= n) (hnhi : n <= 3 * h - 4) :
    RestrictedTwoQ0PlusQSum r h t s n := by
  have hh := hp.h_ge_six
  have ha : 1 <= h - 1 := by omega
  have hqhi : n <= 2 * (h - 1) - 1 + (h - 1) := by omega
  rcases distinct_pair_plus_offset (a := h - 1) (b := h - 1) (q := n) ha hnlo hqhi with
    ⟨x, y, z, hx, hy, hz, hxy, hsum⟩
  exact
    ⟨x, y, z,
      small_in_Q (s := 0) hp hx,
      small_in_Q (s := 0) hp hy,
      small_in_Q (s := s) hp hz,
      hxy, hsum⟩

def regularFullSliceLo (r h m : Nat) : Nat := 2 * m * h

def regularFullSliceHi (r h m : Nat) : Nat := 2 * m * h + 3 * h - 3

def InRegularFullSlice (r h m n : Nat) : Prop :=
  InInterval (regularFullSliceLo r h m) (regularFullSliceHi r h m) n

theorem regularFullSlice_nonempty {r h m : Nat} (hp : Params r h 0) :
    regularFullSliceLo r h m <= regularFullSliceHi r h m := by
  have hh := hp.h_ge_six
  unfold regularFullSliceLo regularFullSliceHi
  omega

theorem regularFullSlice_next_lo_le_hi {r h t m : Nat} (hp : Params r h t) :
    regularFullSliceLo r h (m + 1) <= regularFullSliceHi r h m := by
  have hh := hp.h_ge_six
  unfold regularFullSliceLo regularFullSliceHi
  simp [Nat.left_distrib, Nat.right_distrib]
  omega

theorem regularFullSlice_chain_cover {r h t a k n : Nat} (hp : Params r h t)
    (hn :
      InInterval (regularFullSliceLo r h a) (regularFullSliceHi r h (a + k)) n) :
    ∃ m : Nat, a <= m ∧ m <= a + k ∧ InRegularFullSlice r h m n := by
  induction k with
  | zero =>
      exact ⟨a, by omega, by omega, hn⟩
  | succ k ih =>
      by_cases hnleft : n <= regularFullSliceHi r h (a + k)
      · rcases ih ⟨hn.1, hnleft⟩ with ⟨m, hma, hmk, hm⟩
        exact ⟨m, hma, by omega, hm⟩
      · have hlo : regularFullSliceLo r h ((a + k) + 1) <= n := by
          have hover :=
            regularFullSlice_next_lo_le_hi (r := r) (h := h) (t := t) (m := a + k) hp
          omega
        have hidx : (a + k) + 1 = a + (k + 1) := by omega
        have hhi : n <= regularFullSliceHi r h ((a + k) + 1) := by
          simpa [hidx] using hn.2
        exact ⟨(a + k) + 1, by omega, by omega, ⟨hlo, hhi⟩⟩

theorem bounded_pair_indices_strict {r p : Nat} (hr : 2 <= r)
    (hplo : 1 <= p) (hphi : p <= 2 * r - 3) :
    ∃ i j : Nat, i < r ∧ j < r ∧ i < j ∧ i + j = p := by
  by_cases hsmall : p <= r - 1
  · exact ⟨0, p, by omega, by omega, by omega, by omega⟩
  · refine ⟨p - (r - 1), r - 1, ?_, ?_, ?_, ?_⟩ <;> omega

theorem bounded_triple_indices_distinct_pair {r m : Nat} (hr : 2 <= r)
    (hmlo : 1 <= m) (hmhi : m <= 3 * r - 4) :
    ∃ i j k : Nat, i < r ∧ j < r ∧ k < r ∧ i < j ∧ i + j + k = m := by
  by_cases hsmall : m <= 2 * r - 3
  · rcases bounded_pair_indices_strict (r := r) (p := m) hr hmlo hsmall with
      ⟨i, j, hi, hj, hij, hsum⟩
    exact ⟨i, j, 0, hi, hj, by omega, hij, by omega⟩
  · have hp_lo : 1 <= 2 * r - 3 := by omega
    have hp_hi : 2 * r - 3 <= 2 * r - 3 := by omega
    rcases bounded_pair_indices_strict (r := r) (p := 2 * r - 3) hr hp_lo hp_hi with
      ⟨i, j, hi, hj, hij, hsum⟩
    refine ⟨i, j, m - (2 * r - 3), hi, hj, ?_, hij, ?_⟩ <;> omega

theorem restrictedTwoQ0PlusQSum_regular_full_slice {r h t s m n : Nat}
    (hp : Params r h t) (hr : 2 <= r) (hmlo : 1 <= m) (hmhi : m <= 3 * r - 4)
    (hn : InRegularFullSlice r h m n) :
    RestrictedTwoQ0PlusQSum r h t s n := by
  rcases bounded_triple_indices_distinct_pair (r := r) (m := m) hr hmlo hmhi with
    ⟨i, j, k, hi, hj, hk, hij, hijk⟩
  let Lx := 2 * i * h
  let Ux := 2 * i * h + h - 1
  let Ly := 2 * j * h
  let Uy := 2 * j * h + h - 1
  let Lz := 2 * k * h
  let Uz := 2 * k * h + h - 1
  have hnon_x : Lx <= Ux := by
    dsimp [Lx, Ux]
    have hh := hp.h_ge_six
    omega
  have hnon_y : Ly <= Uy := by
    dsimp [Ly, Uy]
    have hh := hp.h_ge_six
    omega
  have hnon_z : Lz <= Uz := by
    dsimp [Lz, Uz]
    have hh := hp.h_ge_six
    omega
  have hlo :
      Lx + Ly + Lz = regularFullSliceLo r h m := by
    dsimp [Lx, Ly, Lz]
    unfold regularFullSliceLo
    rw [← hijk]
    simp [Nat.left_distrib, Nat.right_distrib]
  have hhi :
      Ux + Uy + Uz = regularFullSliceHi r h m := by
    dsimp [Ux, Uy, Uz]
    unfold regularFullSliceHi
    rw [← hijk]
    simp [Nat.left_distrib, Nat.right_distrib]
    have hh := hp.h_ge_six
    omega
  have hn' : InInterval (Lx + Ly + Lz) (Ux + Uy + Uz) n := by
    unfold InRegularFullSlice at hn
    simpa [hlo, hhi] using hn
  rcases interval_triple_sum hnon_x hnon_y hnon_z hn' with
    ⟨x, y, z, hx, hy, hz, hsum⟩
  have hgap := full_run_hi_lt_full_run_lo_of_lt (r := r) (h := h) (t := t) hp hij
  have hxy : x < y := by
    exact Nat.lt_of_le_of_lt hx.2 (Nat.lt_of_lt_of_le hgap hy.1)
  exact
    ⟨x, y, z,
      full_packet_interval_inQ (r := r) (h := h) (t := t) (s := 0) hi hx,
      full_packet_interval_inQ (r := r) (h := h) (t := t) (s := 0) hj hy,
      full_packet_interval_inQ (r := r) (h := h) (t := t) (s := s) hk hz,
      hxy, hsum⟩

theorem restrictedTwoQ0PlusQSum_regular_full_chain {r h t s n : Nat}
    (hp : Params r h t) (hr : 2 <= r)
    (hn :
      InInterval (regularFullSliceLo r h 1) (regularFullSliceHi r h (3 * r - 4)) n) :
    RestrictedTwoQ0PlusQSum r h t s n := by
  have hlast : 1 + (3 * r - 5) = 3 * r - 4 := by omega
  have hn' :
      InInterval (regularFullSliceLo r h 1)
        (regularFullSliceHi r h (1 + (3 * r - 5))) n := by
    simpa [hlast] using hn
  rcases regularFullSlice_chain_cover
      (r := r) (h := h) (t := t) (a := 1) (k := 3 * r - 5) (n := n) hp hn' with
    ⟨m, hmlo, hmhi, hmem⟩
  have hmhi' : m <= 3 * r - 4 := by omega
  exact restrictedTwoQ0PlusQSum_regular_full_slice
    (r := r) (h := h) (t := t) (s := s) (m := m) hp hr hmlo hmhi' hmem

def oneQ0CapFullSliceLo (r h m : Nat) : Nat := 2 * m * h

def oneQ0CapFullSliceHi (r h t m : Nat) : Nat := 2 * m * h + 2 * h + t - 1

def InOneQ0CapFullSlice (r h t m n : Nat) : Prop :=
  InInterval (oneQ0CapFullSliceLo r h m) (oneQ0CapFullSliceHi r h t m) n

theorem oneQ0CapFullSlice_next_lo_le_hi {r h t m : Nat} (hp : Params r h t) :
    oneQ0CapFullSliceLo r h (m + 1) <= oneQ0CapFullSliceHi r h t m := by
  have htpos : 1 <= t := by
    have hh := hp.h_ge_six
    have hdl := hp.dense_lower
    omega
  unfold oneQ0CapFullSliceLo oneQ0CapFullSliceHi
  simp [Nat.left_distrib, Nat.right_distrib]
  omega

theorem oneQ0CapFullSlice_chain_cover {r h t a k n : Nat} (hp : Params r h t)
    (hn :
      InInterval (oneQ0CapFullSliceLo r h a) (oneQ0CapFullSliceHi r h t (a + k)) n) :
    ∃ m : Nat, a <= m ∧ m <= a + k ∧ InOneQ0CapFullSlice r h t m n := by
  induction k with
  | zero =>
      exact ⟨a, by omega, by omega, hn⟩
  | succ k ih =>
      by_cases hnleft : n <= oneQ0CapFullSliceHi r h t (a + k)
      · rcases ih ⟨hn.1, hnleft⟩ with ⟨m, hma, hmk, hm⟩
        exact ⟨m, hma, by omega, hm⟩
      · have hlo : oneQ0CapFullSliceLo r h ((a + k) + 1) <= n := by
          have hover :=
            oneQ0CapFullSlice_next_lo_le_hi
              (r := r) (h := h) (t := t) (m := a + k) hp
          omega
        have hidx : (a + k) + 1 = a + (k + 1) := by omega
        have hhi : n <= oneQ0CapFullSliceHi r h t ((a + k) + 1) := by
          simpa [hidx] using hn.2
        exact ⟨(a + k) + 1, by omega, by omega, ⟨hlo, hhi⟩⟩

theorem bounded_pair_indices_nonstrict {r p : Nat} (hr : 1 <= r) (hp : p <= 2 * r - 2) :
    ∃ i k : Nat, i < r ∧ k < r ∧ i + k = p := by
  by_cases hsmall : p <= r - 1
  · exact ⟨p, 0, by omega, by omega, by omega⟩
  · refine ⟨r - 1, p - (r - 1), ?_, ?_, ?_⟩ <;> omega

theorem restrictedTwoQ0PlusQSum_one_q0_cap_full_slice {r h t s m n : Nat}
    (hp : Params r h t) (hmlo : r <= m) (hmhi : m <= 3 * r - 2)
    (hn : InOneQ0CapFullSlice r h t m n) :
    RestrictedTwoQ0PlusQSum r h t s n := by
  have hpidx : m - r <= 2 * r - 2 := by omega
  rcases bounded_pair_indices_nonstrict (r := r) (p := m - r) hp.r_pos hpidx with
    ⟨i, k, hi, hk, hik⟩
  have hindex : i + r + k = m := by omega
  let Lx := 2 * i * h
  let Ux := 2 * i * h + h - 1
  let Ly := 2 * r * h
  let Uy := 2 * r * h + t + 1
  let Lz := 2 * k * h
  let Uz := 2 * k * h + h - 1
  have hnon_x : Lx <= Ux := by
    dsimp [Lx, Ux]
    have hh := hp.h_ge_six
    omega
  have hnon_y : Ly <= Uy := by
    dsimp [Ly, Uy]
    omega
  have hnon_z : Lz <= Uz := by
    dsimp [Lz, Uz]
    have hh := hp.h_ge_six
    omega
  have hlo :
      Lx + Ly + Lz = oneQ0CapFullSliceLo r h m := by
    dsimp [Lx, Ly, Lz]
    unfold oneQ0CapFullSliceLo
    rw [← hindex]
    simp [Nat.left_distrib, Nat.right_distrib]
  have hhi :
      Ux + Uy + Uz = oneQ0CapFullSliceHi r h t m := by
    dsimp [Ux, Uy, Uz]
    unfold oneQ0CapFullSliceHi
    rw [← hindex]
    simp [Nat.left_distrib, Nat.right_distrib]
    have hh := hp.h_ge_six
    omega
  have hn' : InInterval (Lx + Ly + Lz) (Ux + Uy + Uz) n := by
    unfold InOneQ0CapFullSlice at hn
    simpa [hlo, hhi] using hn
  rcases interval_triple_sum hnon_x hnon_y hnon_z hn' with
    ⟨x, y, z, hx, hy, hz, hsum⟩
  have hgap := full_run_hi_lt_terminal_cap_lo (r := r) (h := h) (t := t) (i := i) hp hi
  have hxy : x < y := by
    exact Nat.lt_of_le_of_lt hx.2 (Nat.lt_of_lt_of_le hgap hy.1)
  have hyQ : InQ r h t 0 y := by
    apply terminal_cap_interval_inQ (s := 0)
    simpa [Ly, Uy] using hy
  exact
    ⟨x, y, z,
      full_packet_interval_inQ (r := r) (h := h) (t := t) (s := 0) hi hx,
      hyQ,
      full_packet_interval_inQ (r := r) (h := h) (t := t) (s := s) hk hz,
      hxy, hsum⟩

theorem restrictedTwoQ0PlusQSum_one_q0_cap_full_chain {r h t s n : Nat}
    (hp : Params r h t)
    (hn :
      InInterval (oneQ0CapFullSliceLo r h r)
        (oneQ0CapFullSliceHi r h t (3 * r - 2)) n) :
    RestrictedTwoQ0PlusQSum r h t s n := by
  have hlast : r + (2 * r - 2) = 3 * r - 2 := by omega
  have hn' :
      InInterval (oneQ0CapFullSliceLo r h r)
        (oneQ0CapFullSliceHi r h t (r + (2 * r - 2))) n := by
    simpa [hlast] using hn
  rcases oneQ0CapFullSlice_chain_cover
      (r := r) (h := h) (t := t) (a := r) (k := 2 * r - 2) (n := n) hp hn' with
    ⟨m, hmlo, hmhi, hmem⟩
  have hmhi' : m <= 3 * r - 2 := by omega
  exact restrictedTwoQ0PlusQSum_one_q0_cap_full_slice
    (r := r) (h := h) (t := t) (s := s) (m := m) hp hmlo hmhi' hmem

theorem dense_cap_s_le_t_add_one {r h t s : Nat} (hp : Params r h t) (hs : s <= 2) :
    s <= t + 1 := by
  have hh := hp.h_ge_six
  have hdl := hp.dense_lower
  have ht4 : 4 <= t := by omega
  exact Nat.le_trans hs (by omega)

def fullQ0CapQCapSliceLo (r h m : Nat) : Nat := 2 * m * h

def fullQ0CapQCapSliceHi (r h t s m : Nat) : Nat :=
  2 * m * h + h + 2 * t + 1 - s

def InFullQ0CapQCapSlice (r h t s m n : Nat) : Prop :=
  InInterval (fullQ0CapQCapSliceLo r h m) (fullQ0CapQCapSliceHi r h t s m) n

theorem fullQ0CapQCapSlice_next_lo_le_hi {r h t s m : Nat}
    (hp : Params r h t) (hs : s <= 2) :
    fullQ0CapQCapSliceLo r h (m + 1) <= fullQ0CapQCapSliceHi r h t s m := by
  have hh := hp.h_ge_six
  have hdl := hp.dense_lower
  unfold fullQ0CapQCapSliceLo fullQ0CapQCapSliceHi
  simp [Nat.left_distrib, Nat.right_distrib]
  omega

theorem fullQ0CapQCapSlice_chain_cover {r h t s a k n : Nat}
    (hp : Params r h t) (hs : s <= 2)
    (hn :
      InInterval (fullQ0CapQCapSliceLo r h a)
        (fullQ0CapQCapSliceHi r h t s (a + k)) n) :
    ∃ m : Nat, a <= m ∧ m <= a + k ∧ InFullQ0CapQCapSlice r h t s m n := by
  induction k with
  | zero =>
      exact ⟨a, by omega, by omega, hn⟩
  | succ k ih =>
      by_cases hnleft : n <= fullQ0CapQCapSliceHi r h t s (a + k)
      · rcases ih ⟨hn.1, hnleft⟩ with ⟨m, hma, hmk, hm⟩
        exact ⟨m, hma, by omega, hm⟩
      · have hlo : fullQ0CapQCapSliceLo r h ((a + k) + 1) <= n := by
          have hover :=
            fullQ0CapQCapSlice_next_lo_le_hi
              (r := r) (h := h) (t := t) (s := s) (m := a + k) hp hs
          omega
        have hidx : (a + k) + 1 = a + (k + 1) := by omega
        have hhi : n <= fullQ0CapQCapSliceHi r h t s ((a + k) + 1) := by
          simpa [hidx] using hn.2
        exact ⟨(a + k) + 1, by omega, by omega, ⟨hlo, hhi⟩⟩

theorem restrictedTwoQ0PlusQSum_full_q0_cap_q_cap_slice {r h t s m n : Nat}
    (hp : Params r h t) (hs : s <= 2) (hmlo : 2 * r <= m) (hmhi : m <= 3 * r - 1)
    (hn : InFullQ0CapQCapSlice r h t s m n) :
    RestrictedTwoQ0PlusQSum r h t s n := by
  have hscap : s <= t + 1 := dense_cap_s_le_t_add_one (r := r) (h := h) (t := t) hp hs
  let i := m - 2 * r
  have hi : i < r := by
    dsimp [i]
    have hr := hp.r_pos
    omega
  have hindex : i + 2 * r = m := by
    dsimp [i]
    omega
  let Lx := 2 * i * h
  let Ux := 2 * i * h + h - 1
  let Ly := 2 * r * h
  let Uy := 2 * r * h + t + 1
  let Lz := 2 * r * h
  let Uz := 2 * r * h + t + 1 - s
  have hbase : 2 * i * h + 2 * r * h + 2 * r * h = 2 * m * h := by
    have hrr : 2 * r * h + 2 * r * h = 2 * (2 * r) * h := by
      rw [← Nat.add_mul]
      have hc : 2 * r + 2 * r = 2 * (2 * r) := by omega
      rw [hc]
    have hir : 2 * i * h + 2 * (2 * r) * h = 2 * (i + 2 * r) * h := by
      rw [← Nat.add_mul]
      have hc : 2 * i + 2 * (2 * r) = 2 * (i + 2 * r) := by omega
      rw [hc]
    calc
      2 * i * h + 2 * r * h + 2 * r * h =
          2 * i * h + (2 * r * h + 2 * r * h) := by rw [Nat.add_assoc]
      _ = 2 * i * h + 2 * (2 * r) * h := by rw [hrr]
      _ = 2 * (i + 2 * r) * h := hir
      _ = 2 * m * h := by rw [hindex]
  have hnon_x : Lx <= Ux := by
    dsimp [Lx, Ux]
    have hh := hp.h_ge_six
    omega
  have hnon_y : Ly <= Uy := by
    dsimp [Ly, Uy]
    omega
  have hnon_z : Lz <= Uz := by
    dsimp [Lz, Uz]
    omega
  have hlo :
      Lx + Ly + Lz = fullQ0CapQCapSliceLo r h m := by
    dsimp [Lx, Ly, Lz]
    unfold fullQ0CapQCapSliceLo
    simpa [Nat.add_assoc] using hbase
  have hhi :
      Ux + Uy + Uz = fullQ0CapQCapSliceHi r h t s m := by
    have hleft :
        Ux + Uy + Uz =
          (2 * i * h + 2 * r * h + 2 * r * h) + h + 2 * t + 1 - s := by
      dsimp [Ux, Uy, Uz]
      have hh := hp.h_ge_six
      omega
    unfold fullQ0CapQCapSliceHi
    have hh := hp.h_ge_six
    rw [hleft, hbase]
  have hn' : InInterval (Lx + Ly + Lz) (Ux + Uy + Uz) n := by
    unfold InFullQ0CapQCapSlice at hn
    simpa [hlo, hhi] using hn
  rcases interval_triple_sum hnon_x hnon_y hnon_z hn' with
    ⟨x, y, z, hx, hy, hz, hsum⟩
  have hgap := full_run_hi_lt_terminal_cap_lo (r := r) (h := h) (t := t) (i := i) hp hi
  have hxy : x < y := by
    exact Nat.lt_of_le_of_lt hx.2 (Nat.lt_of_lt_of_le hgap hy.1)
  have hyQ : InQ r h t 0 y := by
    apply terminal_cap_interval_inQ (s := 0)
    simpa [Ly, Uy] using hy
  have hzQ : InQ r h t s z := by
    apply terminal_cap_interval_inQ (s := s)
    simpa [Lz, Uz] using hz
  exact
    ⟨x, y, z,
      full_packet_interval_inQ (r := r) (h := h) (t := t) (s := 0) hi hx,
      hyQ, hzQ, hxy, hsum⟩

theorem restrictedTwoQ0PlusQSum_full_q0_cap_q_cap_chain {r h t s n : Nat}
    (hp : Params r h t) (hs : s <= 2)
    (hn :
      InInterval (fullQ0CapQCapSliceLo r h (2 * r))
        (fullQ0CapQCapSliceHi r h t s (3 * r - 1)) n) :
    RestrictedTwoQ0PlusQSum r h t s n := by
  have hlast : 2 * r + (r - 1) = 3 * r - 1 := by
    have hr := hp.r_pos
    omega
  have hn' :
      InInterval (fullQ0CapQCapSliceLo r h (2 * r))
        (fullQ0CapQCapSliceHi r h t s (2 * r + (r - 1))) n := by
    simpa [hlast] using hn
  rcases fullQ0CapQCapSlice_chain_cover
      (r := r) (h := h) (t := t) (s := s) (a := 2 * r) (k := r - 1) (n := n)
      hp hs hn' with
    ⟨m, hmlo, hmhi, hmem⟩
  have hmhi' : m <= 3 * r - 1 := by omega
  exact restrictedTwoQ0PlusQSum_full_q0_cap_q_cap_slice
    (r := r) (h := h) (t := t) (s := s) (m := m) hp hs hmlo hmhi' hmem

def terminalTripleCapLo (r h : Nat) : Nat := 3 * (2 * r * h) + 1

def terminalTripleCapHi (r h t s : Nat) : Nat := 3 * D r h t + 2 - s

theorem restrictedTwoQ0PlusQSum_terminal_caps {r h t s n : Nat}
    (hp : Params r h t) (hs : s <= 2)
    (hn : InInterval (terminalTripleCapLo r h) (terminalTripleCapHi r h t s) n) :
    RestrictedTwoQ0PlusQSum r h t s n := by
  have hscap : s <= t + 1 := dense_cap_s_le_t_add_one (r := r) (h := h) (t := t) hp hs
  let L := 2 * r * h
  let q := n - 3 * L
  have ha : 1 <= t + 1 := by omega
  have hqlo : 1 <= q := by
    have hnlo := hn.1
    unfold terminalTripleCapLo at hnlo
    dsimp [q, L]
    omega
  have hqhi : q <= 2 * (t + 1) - 1 + (t + 1 - s) := by
    have hnhi := hn.2
    unfold terminalTripleCapHi D at hnhi
    dsimp [q, L]
    omega
  rcases distinct_pair_plus_offset
      (a := t + 1) (b := t + 1 - s) (q := q) ha hqlo hqhi with
    ⟨u, v, w, hu, hv, hw, huv, hsum⟩
  let x := L + u
  let y := L + v
  let z := L + w
  have hxint : InInterval L (L + t + 1) x := by
    dsimp [x]
    constructor <;> omega
  have hyint : InInterval L (L + t + 1) y := by
    dsimp [y]
    constructor <;> omega
  have hzint : InInterval L (L + t + 1 - s) z := by
    dsimp [z]
    constructor <;> omega
  have hxQ : InQ r h t 0 x := by
    apply terminal_cap_interval_inQ (s := 0)
    simpa [L] using hxint
  have hyQ : InQ r h t 0 y := by
    apply terminal_cap_interval_inQ (s := 0)
    simpa [L] using hyint
  have hzQ : InQ r h t s z := by
    apply terminal_cap_interval_inQ (s := s)
    simpa [L] using hzint
  have hxy : x < y := by
    dsimp [x, y]
    omega
  have hn_eq : n = 3 * L + q := by
    dsimp [q]
    unfold terminalTripleCapLo at hn
    omega
  have hxyz : x + y + z = n := by
    dsimp [x, y, z]
    omega
  exact ⟨x, y, z, hxQ, hyQ, hzQ, hxy, hxyz⟩

theorem regular_to_one_q0_cap_full_overlap {r h t : Nat}
    (hp : Params r h t) (hr : 2 <= r) :
    oneQ0CapFullSliceLo r h r <= regularFullSliceHi r h (3 * r - 4) + 1 := by
  have hh := hp.h_ge_six
  have hcoef : 2 * r + 1 <= 2 * (3 * r - 4) + 3 := by omega
  have hmul : (2 * r + 1) * h <= (2 * (3 * r - 4) + 3) * h :=
    Nat.mul_le_mul_right h hcoef
  have hleft : 2 * r * h + 2 <= (2 * r + 1) * h := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hsum : 2 * r * h + 2 <= 2 * (3 * r - 4) * h + 3 * h := by
    have hmul' := Nat.le_trans hleft hmul
    rw [Nat.add_mul] at hmul'
    exact hmul'
  unfold oneQ0CapFullSliceLo regularFullSliceHi
  omega

theorem one_q0_cap_full_to_full_q0_cap_q_cap_overlap {r h t s : Nat}
    (hp : Params r h t) :
    fullQ0CapQCapSliceLo r h (2 * r) <=
      oneQ0CapFullSliceHi r h t (3 * r - 2) + 1 := by
  have hr := hp.r_pos
  have hcoef : 2 * (2 * r) <= 2 * (3 * r - 2) + 2 := by omega
  have hmul : 2 * (2 * r) * h <= (2 * (3 * r - 2) + 2) * h :=
    Nat.mul_le_mul_right h hcoef
  have hsum : 2 * (2 * r) * h <= 2 * (3 * r - 2) * h + 2 * h := by
    rw [Nat.add_mul] at hmul
    exact hmul
  unfold fullQ0CapQCapSliceLo oneQ0CapFullSliceHi
  omega

theorem full_q0_cap_q_cap_to_terminal_overlap {r h t s : Nat}
    (hp : Params r h t) (hs : s <= 2) :
    terminalTripleCapLo r h <= fullQ0CapQCapSliceHi r h t s (3 * r - 1) + 1 := by
  have hr := hp.r_pos
  have hh := hp.h_ge_six
  have hdl := hp.dense_lower
  have hbase : 3 * (2 * r * h) = 2 * (3 * r - 1) * h + 2 * h := by
    have hcoef : 3 * (2 * r) = 2 * (3 * r - 1) + 2 := by omega
    calc
      3 * (2 * r * h) = (3 * (2 * r)) * h := by
        simp [Nat.mul_assoc]
      _ = (2 * (3 * r - 1) + 2) * h := by rw [hcoef]
      _ = 2 * (3 * r - 1) * h + 2 * h := by rw [Nat.add_mul]
  have htail : 2 * h + 1 <= h + 2 * t + 2 - s := by omega
  unfold terminalTripleCapLo fullQ0CapQCapSliceHi
  omega

theorem restrictedTwoQ0PlusQSum_dense_cap_pointwise {r h t s n : Nat}
    (hp : Params r h t) (hs : s <= 2)
    (hnlo : 1 <= n) (hnhi : n <= 3 * D r h t + 2 - s) :
    RestrictedTwoQ0PlusQSum r h t s n := by
  by_cases hfirst : n <= 3 * h - 4
  · exact restrictedTwoQ0PlusQSum_first_full_run
      (r := r) (h := h) (t := t) (s := s) (n := n) hp hnlo hfirst
  · have hafter_first : 3 * h - 3 <= n := by omega
    by_cases hr_one : r = 1
    · subst r
      by_cases hone : n <= oneQ0CapFullSliceHi 1 h t (3 * 1 - 2)
      · apply restrictedTwoQ0PlusQSum_one_q0_cap_full_chain
          (r := 1) (h := h) (t := t) (s := s) hp
        constructor
        · unfold oneQ0CapFullSliceLo
          have hh := hp.h_ge_six
          omega
        · simpa using hone
      · have hafter_one : oneQ0CapFullSliceHi 1 h t (3 * 1 - 2) + 1 <= n := by
          omega
        by_cases htwo : n <= fullQ0CapQCapSliceHi 1 h t s (3 * 1 - 1)
        · apply restrictedTwoQ0PlusQSum_full_q0_cap_q_cap_chain
            (r := 1) (h := h) (t := t) (s := s) hp hs
          constructor
          · unfold fullQ0CapQCapSliceLo oneQ0CapFullSliceHi at *
            omega
          · simpa using htwo
        · have hafter_two : fullQ0CapQCapSliceHi 1 h t s (3 * 1 - 1) + 1 <= n := by
            omega
          apply restrictedTwoQ0PlusQSum_terminal_caps
            (r := 1) (h := h) (t := t) (s := s) hp hs
          constructor
          · have hover :=
              full_q0_cap_q_cap_to_terminal_overlap
                (r := 1) (h := h) (t := t) (s := s) hp hs
            omega
          · unfold terminalTripleCapHi
            simpa using hnhi
    · have hr_two : 2 <= r := by
        have hr := hp.r_pos
        omega
      by_cases hreg : n <= regularFullSliceHi r h (3 * r - 4)
      · apply restrictedTwoQ0PlusQSum_regular_full_chain
          (r := r) (h := h) (t := t) (s := s) hp hr_two
        constructor
        · unfold regularFullSliceLo
          have hh := hp.h_ge_six
          omega
        · exact hreg
      · have hafter_reg : regularFullSliceHi r h (3 * r - 4) + 1 <= n := by
          omega
        by_cases hone : n <= oneQ0CapFullSliceHi r h t (3 * r - 2)
        · apply restrictedTwoQ0PlusQSum_one_q0_cap_full_chain
            (r := r) (h := h) (t := t) (s := s) hp
          constructor
          · have hover :=
              regular_to_one_q0_cap_full_overlap (r := r) (h := h) (t := t) hp hr_two
            omega
          · exact hone
        · have hafter_one : oneQ0CapFullSliceHi r h t (3 * r - 2) + 1 <= n := by
            omega
          by_cases htwo : n <= fullQ0CapQCapSliceHi r h t s (3 * r - 1)
          · apply restrictedTwoQ0PlusQSum_full_q0_cap_q_cap_chain
              (r := r) (h := h) (t := t) (s := s) hp hs
            constructor
            · have hover :=
                one_q0_cap_full_to_full_q0_cap_q_cap_overlap
                  (r := r) (h := h) (t := t) (s := s) hp
              omega
            · exact htwo
          · have hafter_two :
              fullQ0CapQCapSliceHi r h t s (3 * r - 1) + 1 <= n := by
              omega
            apply restrictedTwoQ0PlusQSum_terminal_caps
              (r := r) (h := h) (t := t) (s := s) hp hs
            constructor
            · have hover :=
                full_q0_cap_q_cap_to_terminal_overlap
                  (r := r) (h := h) (t := t) (s := s) hp hs
              omega
            · unfold terminalTripleCapHi
              simpa using hnhi

theorem restrictedTwoQ0PlusQSum_dense_cap_pointwise_s0 {r h t n : Nat}
    (hp : Params r h t) (hnlo : 1 <= n) (hnhi : n <= 3 * D r h t + 2) :
    RestrictedTwoQ0PlusQSum r h t 0 n := by
  exact restrictedTwoQ0PlusQSum_dense_cap_pointwise
    (r := r) (h := h) (t := t) (s := 0) (n := n) hp (by omega) hnlo (by omega)

theorem restrictedTwoQ0PlusQSum_dense_cap_pointwise_s1 {r h t n : Nat}
    (hp : Params r h t) (hnlo : 1 <= n) (hnhi : n <= 3 * D r h t + 1) :
    RestrictedTwoQ0PlusQSum r h t 1 n := by
  exact restrictedTwoQ0PlusQSum_dense_cap_pointwise
    (r := r) (h := h) (t := t) (s := 1) (n := n) hp (by omega) hnlo (by omega)

theorem restrictedTwoQ0PlusQSum_dense_cap_pointwise_s2 {r h t n : Nat}
    (hp : Params r h t) (hnlo : 1 <= n) (hnhi : n <= 3 * D r h t) :
    RestrictedTwoQ0PlusQSum r h t 2 n := by
  exact restrictedTwoQ0PlusQSum_dense_cap_pointwise
    (r := r) (h := h) (t := t) (s := 2) (n := n) hp (by omega) hnlo (by omega)

end TransitionDenseCap
end GreedyThreeSumfree
