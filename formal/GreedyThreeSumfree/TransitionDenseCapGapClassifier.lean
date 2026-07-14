import GreedyThreeSumfree.TransitionDenseCapInternalGaps

namespace GreedyThreeSumfree.TransitionDenseCap

/-- The internal open packet gaps, written as closed natural intervals. -/
def InQInternalGap (h i u : Nat) : Prop :=
  InInterval (2 * i * h + h) (2 * i * h + 2 * h - 1) u

/-- The hull of `Q_s`, from the first full run through its terminal cap. -/
def InQHull (r h t s u : Nat) : Prop :=
  InInterval 0 (D r h t + 1 - s) u

/-- Internal gap intervals inside the prefix packet `E = D + Q_0`. -/
def InEInternalGap (r h t i n : Nat) : Prop :=
  InInterval (D r h t + (2 * i * h + h))
    (D r h t + (2 * i * h + 2 * h - 1)) n

/-- Internal gap intervals inside the prefix high packet `F = 6D+1+Q_1`. -/
def InFInternalGap (r h t i n : Nat) : Prop :=
  InInterval (6 * D r h t + 1 + (2 * i * h + h))
    (6 * D r h t + 1 + (2 * i * h + 2 * h - 1)) n

/-- Internal low-tail offset gaps inside `X = D + Q_1`. -/
def InXInternalGapOffset (r h t i o : Nat) : Prop :=
  InInterval (D r h t + (2 * i * h + h))
    (D r h t + (2 * i * h + 2 * h - 1)) o

/-- Internal high-tail offset gaps inside `Y = 6D+2+Q_2`. -/
def InYInternalGapOffset (r h t i o : Nat) : Prop :=
  InInterval (6 * D r h t + 2 + (2 * i * h + h))
    (6 * D r h t + 2 + (2 * i * h + 2 * h - 1)) o

def InEHull (r h t n : Nat) : Prop :=
  InInterval (D r h t) (2 * D r h t + 1) n

def InFHull (r h t n : Nat) : Prop :=
  InInterval (6 * D r h t + 1) (7 * D r h t + 1) n

def InXHullOffset (r h t o : Nat) : Prop :=
  InInterval (D r h t) (2 * D r h t) o

def InYHullOffset (r h t o : Nat) : Prop :=
  InInterval (6 * D r h t + 2) (7 * D r h t + 1) o

def InTailHullOffset (r h t o : Nat) : Prop :=
  InXHullOffset r h t o ∨ InYHullOffset r h t o

def InTailInternalGapOffset (r h t o : Nat) : Prop :=
  (∃ i : Nat, i < r ∧ InXInternalGapOffset r h t i o) ∨
    ∃ i : Nat, i < r ∧ InYInternalGapOffset r h t i o

private theorem full_window_classified_to_index {r h t s i u : Nat}
    (hp : Params r h t) (hi : i < r)
    (hu : InInterval 0 (2 * i * h + h - 1) u) :
    InQ r h t s u ∨ ∃ j : Nat, j < i ∧ InQInternalGap h j u := by
  induction i with
  | zero =>
      left
      apply inQ_of_full_packet_run (i := 0)
      unfold InFullPacketRun InInterval at *
      constructor
      · exact hp.r_pos
      · constructor
        · omega
        · simpa using hu.2
  | succ i ih =>
      by_cases hprev : u <= 2 * i * h + h - 1
      · have hi_prev : i < r := by omega
        have hu_prev : InInterval 0 (2 * i * h + h - 1) u := ⟨hu.1, hprev⟩
        rcases ih hi_prev hu_prev with hQ | hgap
        · exact Or.inl hQ
        · rcases hgap with ⟨j, hj, hmem⟩
          exact Or.inr ⟨j, by omega, hmem⟩
      · by_cases hnext : 2 * (i + 1) * h <= u
        · left
          apply inQ_of_full_packet_run (i := i + 1)
          unfold InFullPacketRun InInterval at *
          constructor
          · exact hi
          · constructor
            · exact hnext
            · simpa [Nat.left_distrib, Nat.right_distrib] using hu.2
        · right
          refine ⟨i, by omega, ?_⟩
          unfold InQInternalGap InInterval
          have hgt_prev : 2 * i * h + h - 1 < u := Nat.lt_of_not_ge hprev
          have hlt_next : u < 2 * (i + 1) * h := Nat.lt_of_not_ge hnext
          constructor
          · have hh := hp.h_ge_six
            omega
          · have hnext_eq : 2 * (i + 1) * h = 2 * i * h + 2 * h := by
              simp [Nat.left_distrib, Nat.right_distrib]
            rw [hnext_eq] at hlt_next
            omega

theorem inQ_hull_not_inQ_internal_gap {r h t s u : Nat}
    (hp : Params r h t) (hs : s <= 2) (hu : InQHull r h t s u)
    (hnot : ¬ InQ r h t s u) :
    ∃ i : Nat, i < r ∧ InQInternalGap h i u := by
  have hlast : r - 1 < r := by
    have hr := hp.r_pos
    omega
  by_cases hbeforeLast : u <= 2 * (r - 1) * h + h - 1
  · have hu_prefix : InInterval 0 (2 * (r - 1) * h + h - 1) u :=
      ⟨hu.1, hbeforeLast⟩
    rcases full_window_classified_to_index
        (r := r) (h := h) (t := t) (s := s) (i := r - 1) (u := u)
        hp hlast hu_prefix with hQ | hgap
    · exact False.elim (hnot hQ)
    · rcases hgap with ⟨i, hi, hmem⟩
      exact ⟨i, by omega, hmem⟩
  · by_cases htermLo : 2 * r * h <= u
    · have hterm : InTerminalCap r h t s u := by
        unfold InTerminalCap InInterval InQHull D at *
        have hs_term : s <= t + 1 := by
          have hdense := hp.dense_lower
          have hh := hp.h_ge_six
          omega
        constructor
        · exact htermLo
        · exact hu.2
      exact False.elim (hnot (inQ_of_terminal_cap hterm))
    · refine ⟨r - 1, hlast, ?_⟩
      unfold InQInternalGap InQHull InInterval D at *
      have hlo : 2 * (r - 1) * h + h <= u := by
        have hh := hp.h_ge_six
        omega
      have hhi : u <= 2 * (r - 1) * h + 2 * h - 1 := by
        have hlt : u < 2 * r * h := Nat.lt_of_not_ge htermLo
        have hr := hp.r_pos
        have hblock_eq : 2 * r * h = 2 * (r - 1) * h + 2 * h := by
          have hr_eq : r = (r - 1) + 1 := by omega
          calc
            2 * r * h = 2 * ((r - 1) + 1) * h := by rw [← hr_eq]
            _ = (2 * (r - 1) + 2 * 1) * h := by rw [Nat.left_distrib]
            _ = 2 * (r - 1) * h + 2 * h := by
              rw [Nat.add_mul]
        rw [hblock_eq] at hlt
        omega
      exact ⟨hlo, hhi⟩

theorem inQ_zero_hull_not_inQ_internal_gap {r h t u : Nat}
    (hp : Params r h t) (hu : InQHull r h t 0 u)
    (hnot : ¬ InQ r h t 0 u) :
    ∃ i : Nat, i < r ∧ InQInternalGap h i u :=
  inQ_hull_not_inQ_internal_gap
    (r := r) (h := h) (t := t) (s := 0) (u := u) hp (by omega) hu hnot

theorem inQ_one_hull_not_inQ_internal_gap {r h t u : Nat}
    (hp : Params r h t) (hu : InQHull r h t 1 u)
    (hnot : ¬ InQ r h t 1 u) :
    ∃ i : Nat, i < r ∧ InQInternalGap h i u :=
  inQ_hull_not_inQ_internal_gap
    (r := r) (h := h) (t := t) (s := 1) (u := u) hp (by omega) hu hnot

theorem inQ_two_hull_not_inQ_internal_gap {r h t u : Nat}
    (hp : Params r h t) (hu : InQHull r h t 2 u)
    (hnot : ¬ InQ r h t 2 u) :
    ∃ i : Nat, i < r ∧ InQInternalGap h i u :=
  inQ_hull_not_inQ_internal_gap
    (r := r) (h := h) (t := t) (s := 2) (u := u) hp (by omega) hu hnot

theorem E_hull_not_inE_internal_gap {r h t n : Nat}
    (hp : Params r h t) (hn : InEHull r h t n) (hnot : ¬ InE r h t n) :
    ∃ i : Nat, i < r ∧ InEInternalGap r h t i n := by
  let u := n - D r h t
  have huHull : InQHull r h t 0 u := by
    unfold InQHull InEHull InInterval at *
    dsimp [u]
    constructor <;> omega
  have hn_eq : n = D r h t + u := by
    unfold InEHull InInterval at hn
    dsimp [u]
    omega
  have huNot : ¬ InQ r h t 0 u := by
    intro hu
    exact hnot (by
      unfold InE Shift
      exact ⟨u, hu, hn_eq⟩)
  rcases inQ_zero_hull_not_inQ_internal_gap
      (r := r) (h := h) (t := t) (u := u) hp huHull huNot with
    ⟨i, hi, hgap⟩
  refine ⟨i, hi, ?_⟩
  unfold InEInternalGap InQInternalGap InInterval at *
  omega

theorem E_hull_not_candidate_internal_gap {r h t n : Nat}
    (hp : Params r h t) (hn : InEHull r h t n)
    (hnot : ¬ Candidate r h t n) :
    ∃ i : Nat, i < r ∧ InEInternalGap r h t i n := by
  exact
    E_hull_not_inE_internal_gap
      (r := r) (h := h) (t := t) (n := n) hp hn
      (by
        intro hE
        exact hnot (candidate_of_inE hE))

theorem F_hull_not_inF_internal_gap {r h t n : Nat}
    (hp : Params r h t) (hn : InFHull r h t n) (hnot : ¬ InF r h t n) :
    ∃ i : Nat, i < r ∧ InFInternalGap r h t i n := by
  let u := n - (6 * D r h t + 1)
  have huHull : InQHull r h t 1 u := by
    unfold InQHull InFHull InInterval at *
    dsimp [u]
    constructor <;> omega
  have hn_eq : n = 6 * D r h t + 1 + u := by
    unfold InFHull InInterval at hn
    dsimp [u]
    omega
  have huNot : ¬ InQ r h t 1 u := by
    intro hu
    have hx : InX r h t (D r h t + u) := by
      unfold InX Shift
      exact ⟨u, hu, rfl⟩
    have hf : InF r h t (5 * D r h t + 1 + (D r h t + u)) := by
      unfold InF Shift
      exact ⟨D r h t + u, hx, rfl⟩
    have htarget :
        5 * D r h t + 1 + (D r h t + u) =
          6 * D r h t + 1 + u := by
      omega
    exact hnot (by
      rw [hn_eq, ← htarget]
      exact hf)
  rcases inQ_one_hull_not_inQ_internal_gap
      (r := r) (h := h) (t := t) (u := u) hp huHull huNot with
    ⟨i, hi, hgap⟩
  refine ⟨i, hi, ?_⟩
  unfold InFInternalGap InQInternalGap InInterval at *
  omega

theorem F_hull_not_candidate_internal_gap {r h t n : Nat}
    (hp : Params r h t) (hn : InFHull r h t n)
    (hnot : ¬ Candidate r h t n) :
    ∃ i : Nat, i < r ∧ InFInternalGap r h t i n := by
  exact
    F_hull_not_inF_internal_gap
      (r := r) (h := h) (t := t) (n := n) hp hn
      (by
        intro hF
        exact hnot (candidate_of_inF hF))

theorem X_hull_offset_not_inX_internal_gap {r h t o : Nat}
    (hp : Params r h t) (ho : InXHullOffset r h t o) (hnot : ¬ InX r h t o) :
    ∃ i : Nat, i < r ∧ InXInternalGapOffset r h t i o := by
  let u := o - D r h t
  have huHull : InQHull r h t 1 u := by
    unfold InQHull InXHullOffset InInterval at *
    dsimp [u]
    constructor <;> omega
  have ho_eq : o = D r h t + u := by
    unfold InXHullOffset InInterval at ho
    dsimp [u]
    omega
  have huNot : ¬ InQ r h t 1 u := by
    intro hu
    exact hnot (by
      unfold InX Shift
      exact ⟨u, hu, ho_eq⟩)
  rcases inQ_one_hull_not_inQ_internal_gap
      (r := r) (h := h) (t := t) (u := u) hp huHull huNot with
    ⟨i, hi, hgap⟩
  refine ⟨i, hi, ?_⟩
  unfold InXInternalGapOffset InQInternalGap InInterval at *
  omega

theorem X_hull_offset_not_tailResidue_internal_gap {r h t o : Nat}
    (hp : Params r h t) (ho : InXHullOffset r h t o)
    (hnot : ¬ InTailResidue r h t o) :
    ∃ i : Nat, i < r ∧ InXInternalGapOffset r h t i o := by
  exact
    X_hull_offset_not_inX_internal_gap
      (r := r) (h := h) (t := t) (o := o) hp ho
      (by
        intro hX
        exact hnot (Or.inl hX))

theorem Y_hull_offset_not_inY_internal_gap {r h t o : Nat}
    (hp : Params r h t) (ho : InYHullOffset r h t o) (hnot : ¬ InY r h t o) :
    ∃ i : Nat, i < r ∧ InYInternalGapOffset r h t i o := by
  let u := o - (6 * D r h t + 2)
  have huHull : InQHull r h t 2 u := by
    unfold InQHull InYHullOffset InInterval at *
    dsimp [u]
    constructor <;> omega
  have ho_eq : o = 6 * D r h t + 2 + u := by
    unfold InYHullOffset InInterval at ho
    dsimp [u]
    omega
  have huNot : ¬ InQ r h t 2 u := by
    intro hu
    have hw : InW r h t (D r h t + u) := by
      unfold InW Shift
      exact ⟨u, hu, rfl⟩
    have hy : InY r h t (5 * D r h t + 2 + (D r h t + u)) := by
      unfold InY Shift
      exact ⟨D r h t + u, hw, rfl⟩
    have htarget :
        5 * D r h t + 2 + (D r h t + u) =
          6 * D r h t + 2 + u := by
      omega
    exact hnot (by
      rw [ho_eq, ← htarget]
      exact hy)
  rcases inQ_two_hull_not_inQ_internal_gap
      (r := r) (h := h) (t := t) (u := u) hp huHull huNot with
    ⟨i, hi, hgap⟩
  refine ⟨i, hi, ?_⟩
  unfold InYInternalGapOffset InQInternalGap InInterval at *
  omega

theorem Y_hull_offset_not_tailResidue_internal_gap {r h t o : Nat}
    (hp : Params r h t) (ho : InYHullOffset r h t o)
    (hnot : ¬ InTailResidue r h t o) :
    ∃ i : Nat, i < r ∧ InYInternalGapOffset r h t i o := by
  exact
    Y_hull_offset_not_inY_internal_gap
      (r := r) (h := h) (t := t) (o := o) hp ho
      (by
        intro hY
        exact hnot (Or.inr hY))

theorem tail_hull_offset_not_tailResidue_internal_gap {r h t o : Nat}
    (hp : Params r h t) (ho : InTailHullOffset r h t o)
    (hnot : ¬ InTailResidue r h t o) :
    InTailInternalGapOffset r h t o := by
  rcases ho with hoX | hoY
  · exact Or.inl
      (X_hull_offset_not_tailResidue_internal_gap
        (r := r) (h := h) (t := t) (o := o) hp hoX hnot)
  · exact Or.inr
      (Y_hull_offset_not_tailResidue_internal_gap
        (r := r) (h := h) (t := t) (o := o) hp hoY hnot)

end GreedyThreeSumfree.TransitionDenseCap
