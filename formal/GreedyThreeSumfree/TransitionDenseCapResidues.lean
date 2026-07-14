import GreedyThreeSumfree.TransitionDenseCapCoveragePredicates

namespace GreedyThreeSumfree
namespace TransitionDenseCap

/-- The two small seed residues used in the dense-cap tail audit. -/
def SmallResidue (h n : Nat) : Prop :=
  n = 1 ∨ n = h - 1

/-- The coarse low residue band containing `E` and `X`. -/
def LowResidue (r h t n : Nat) : Prop :=
  InInterval (D r h t) (2 * D r h t + 1) n

/-- The coarse high residue band containing `F` and `Y`. -/
def HighResidue (r h t n : Nat) : Prop :=
  InInterval (6 * D r h t + 1) (7 * D r h t + 1) n

/-- Occupied tail residues, before period translation. -/
def OccupiedTailResidue (r h t n : Nat) : Prop :=
  InX r h t n ∨ InY r h t n

/-- Allowed residues in the dense-cap quotient audit. -/
def SigmaResidue (r h t n : Nat) : Prop :=
  SmallResidue h n ∨
    InE r h t n ∨ InF r h t n ∨ InX r h t n ∨ InY r h t n

/-- Alias for the allowed residue predicate. -/
def AllowedResidue (r h t n : Nat) : Prop :=
  SigmaResidue r h t n

private theorem h_le_D_of_params {r h t : Nat} (hp : Params r h t) :
    h <= D r h t := by
  have hcoef : 1 <= 2 * r := by
    have hr := hp.r_pos
    omega
  have hmul : h <= 2 * r * h := by
    simpa [Nat.one_mul, Nat.mul_assoc] using Nat.mul_le_mul_right h hcoef
  unfold D
  omega

theorem smallResidue_range {r h t n : Nat} (hp : Params r h t)
    (hn : SmallResidue h n) :
    InInterval 1 (h - 1) n := by
  unfold SmallResidue at hn
  unfold InInterval
  rcases hn with rfl | rfl
  · have hh := hp.h_ge_six
    omega
  · have hh := hp.h_ge_six
    omega

theorem inQ_zero_residue_range {r h t u : Nat} (hp : Params r h t)
    (hu : InQ r h t 0 u) :
    InInterval 0 (D r h t + 1) u := by
  constructor
  · omega
  · rcases hu with hfull | hterm
    · rcases hfull with ⟨i, hi⟩
      rcases hi with ⟨hir, hI⟩
      have hsucc : i + 1 <= r := by omega
      have hcoef : 2 * (i + 1) <= 2 * r := Nat.mul_le_mul_left 2 hsucc
      have hmul : 2 * (i + 1) * h <= 2 * r * h :=
        Nat.mul_le_mul_right h hcoef
      have hrew : 2 * (i + 1) * h = 2 * i * h + 2 * h := by
        simp [Nat.left_distrib, Nat.right_distrib]
      unfold InInterval at hI
      unfold D
      rw [hrew] at hmul
      have hh := hp.h_ge_six
      omega
    · unfold InTerminalCap InInterval at hterm
      unfold D
      omega

theorem inQ_one_residue_range {r h t u : Nat} (hp : Params r h t)
    (hu : InQ r h t 1 u) :
    InInterval 0 (D r h t) u := by
  constructor
  · omega
  · rcases hu with hfull | hterm
    · rcases hfull with ⟨i, hi⟩
      rcases hi with ⟨hir, hI⟩
      have hsucc : i + 1 <= r := by omega
      have hcoef : 2 * (i + 1) <= 2 * r := Nat.mul_le_mul_left 2 hsucc
      have hmul : 2 * (i + 1) * h <= 2 * r * h :=
        Nat.mul_le_mul_right h hcoef
      have hrew : 2 * (i + 1) * h = 2 * i * h + 2 * h := by
        simp [Nat.left_distrib, Nat.right_distrib]
      unfold InInterval at hI
      unfold D
      rw [hrew] at hmul
      have hh := hp.h_ge_six
      omega
    · unfold InTerminalCap InInterval at hterm
      unfold D
      omega

theorem inQ_two_residue_range {r h t u : Nat} (hp : Params r h t)
    (hu : InQ r h t 2 u) :
    InInterval 0 (D r h t - 1) u := by
  constructor
  · omega
  · rcases hu with hfull | hterm
    · rcases hfull with ⟨i, hi⟩
      rcases hi with ⟨hir, hI⟩
      have hsucc : i + 1 <= r := by omega
      have hcoef : 2 * (i + 1) <= 2 * r := Nat.mul_le_mul_left 2 hsucc
      have hmul : 2 * (i + 1) * h <= 2 * r * h :=
        Nat.mul_le_mul_right h hcoef
      have hrew : 2 * (i + 1) * h = 2 * i * h + 2 * h := by
        simp [Nat.left_distrib, Nat.right_distrib]
      unfold InInterval at hI
      unfold D
      rw [hrew] at hmul
      have hh := hp.h_ge_six
      omega
    · unfold InTerminalCap InInterval at hterm
      unfold D
      omega

theorem inE_residue_range {r h t n : Nat} (hp : Params r h t)
    (hn : InE r h t n) :
    LowResidue r h t n := by
  unfold InE Shift at hn
  unfold LowResidue InInterval
  rcases hn with ⟨u, hu, rfl⟩
  have huI := inQ_zero_residue_range (r := r) (h := h) (t := t) hp hu
  unfold InInterval at huI
  omega

theorem inX_residue_range {r h t n : Nat} (hp : Params r h t)
    (hn : InX r h t n) :
    LowResidue r h t n := by
  unfold InX Shift at hn
  unfold LowResidue InInterval
  rcases hn with ⟨u, hu, rfl⟩
  have huI := inQ_one_residue_range (r := r) (h := h) (t := t) hp hu
  unfold InInterval at huI
  omega

theorem inX_residue_tight_range {r h t n : Nat} (hp : Params r h t)
    (hn : InX r h t n) :
    InInterval (D r h t) (2 * D r h t) n := by
  unfold InX Shift at hn
  unfold InInterval
  rcases hn with ⟨u, hu, rfl⟩
  have huI := inQ_one_residue_range (r := r) (h := h) (t := t) hp hu
  unfold InInterval at huI
  omega

theorem inW_residue_range {r h t n : Nat} (hp : Params r h t)
    (hn : InW r h t n) :
    InInterval (D r h t) (2 * D r h t - 1) n := by
  unfold InW Shift at hn
  unfold InInterval
  rcases hn with ⟨u, hu, rfl⟩
  have hD := D_ge_three (r := r) (h := h) (t := t) hp
  have huI := inQ_two_residue_range (r := r) (h := h) (t := t) hp hu
  unfold InInterval at huI
  omega

theorem inF_residue_range {r h t n : Nat} (hp : Params r h t)
    (hn : InF r h t n) :
    HighResidue r h t n := by
  unfold InF Shift at hn
  unfold HighResidue InInterval
  rcases hn with ⟨u, hu, rfl⟩
  have hD := D_ge_three (r := r) (h := h) (t := t) hp
  have huI := inX_residue_tight_range (r := r) (h := h) (t := t) hp hu
  unfold InInterval at huI
  constructor <;> omega

theorem inY_residue_range {r h t n : Nat} (hp : Params r h t)
    (hn : InY r h t n) :
    HighResidue r h t n := by
  unfold InY Shift at hn
  unfold HighResidue InInterval
  rcases hn with ⟨u, hu, rfl⟩
  have hD := D_ge_three (r := r) (h := h) (t := t) hp
  have huI := inW_residue_range (r := r) (h := h) (t := t) hp hu
  unfold InInterval at huI
  constructor <;> omega

theorem inX_occupiedTailResidue {r h t n : Nat} (hn : InX r h t n) :
    OccupiedTailResidue r h t n := by
  exact Or.inl hn

theorem inY_occupiedTailResidue {r h t n : Nat} (hn : InY r h t n) :
    OccupiedTailResidue r h t n := by
  exact Or.inr hn

theorem occupiedTailResidue_range {r h t n : Nat} (hp : Params r h t)
    (hn : OccupiedTailResidue r h t n) :
    LowResidue r h t n ∨ HighResidue r h t n := by
  rcases hn with hx | hy
  · exact Or.inl (inX_residue_range (r := r) (h := h) (t := t) hp hx)
  · exact Or.inr (inY_residue_range (r := r) (h := h) (t := t) hp hy)

theorem sigmaResidue_category {r h t n : Nat} (hp : Params r h t)
    (hn : SigmaResidue r h t n) :
    SmallResidue h n ∨ LowResidue r h t n ∨ HighResidue r h t n := by
  unfold SigmaResidue at hn
  rcases hn with hs | he | hf | hx | hy
  · exact Or.inl hs
  · exact Or.inr (Or.inl (inE_residue_range (r := r) (h := h) (t := t) hp he))
  · exact Or.inr (Or.inr (inF_residue_range (r := r) (h := h) (t := t) hp hf))
  · exact Or.inr (Or.inl (inX_residue_range (r := r) (h := h) (t := t) hp hx))
  · exact Or.inr (Or.inr (inY_residue_range (r := r) (h := h) (t := t) hp hy))

theorem allowedResidue_category {r h t n : Nat} (hp : Params r h t)
    (hn : AllowedResidue r h t n) :
    SmallResidue h n ∨ LowResidue r h t n ∨ HighResidue r h t n := by
  exact sigmaResidue_category (r := r) (h := h) (t := t) hp hn

theorem small_small_small_sum_range {r h t a b c : Nat} (hp : Params r h t)
    (ha : SmallResidue h a) (hb : SmallResidue h b) (hc : SmallResidue h c) :
    InInterval 3 (3 * h - 3) (a + b + c) := by
  have haI := smallResidue_range (r := r) (h := h) (t := t) hp ha
  have hbI := smallResidue_range (r := r) (h := h) (t := t) hp hb
  have hcI := smallResidue_range (r := r) (h := h) (t := t) hp hc
  unfold InInterval at haI hbI hcI ⊢
  have hh := hp.h_ge_six
  omega

theorem small_small_low_sum_range {r h t a b c : Nat} (hp : Params r h t)
    (ha : SmallResidue h a) (hb : SmallResidue h b)
    (hc : LowResidue r h t c) :
    InInterval (D r h t + 2) (2 * D r h t + 2 * h - 1) (a + b + c) := by
  have haI := smallResidue_range (r := r) (h := h) (t := t) hp ha
  have hbI := smallResidue_range (r := r) (h := h) (t := t) hp hb
  unfold LowResidue InInterval at hc
  unfold InInterval at haI hbI ⊢
  have hh := hp.h_ge_six
  omega

theorem small_small_high_sum_range {r h t a b c : Nat} (hp : Params r h t)
    (ha : SmallResidue h a) (hb : SmallResidue h b)
    (hc : HighResidue r h t c) :
    InInterval (6 * D r h t + 3) (7 * D r h t + 2 * h - 1) (a + b + c) := by
  have haI := smallResidue_range (r := r) (h := h) (t := t) hp ha
  have hbI := smallResidue_range (r := r) (h := h) (t := t) hp hb
  unfold HighResidue InInterval at hc
  unfold InInterval at haI hbI ⊢
  have hh := hp.h_ge_six
  omega

theorem small_low_low_sum_range {r h t a b c : Nat} (hp : Params r h t)
    (ha : SmallResidue h a) (hb : LowResidue r h t b)
    (hc : LowResidue r h t c) :
    InInterval (2 * D r h t + 1) (4 * D r h t + h + 1) (a + b + c) := by
  have haI := smallResidue_range (r := r) (h := h) (t := t) hp ha
  unfold LowResidue InInterval at hb hc
  unfold InInterval at haI ⊢
  have hh := hp.h_ge_six
  omega

theorem small_low_high_sum_range {r h t a b c : Nat} (hp : Params r h t)
    (ha : SmallResidue h a) (hb : LowResidue r h t b)
    (hc : HighResidue r h t c) :
    InInterval (7 * D r h t + 2) (9 * D r h t + h + 1) (a + b + c) := by
  have haI := smallResidue_range (r := r) (h := h) (t := t) hp ha
  unfold LowResidue InInterval at hb
  unfold HighResidue InInterval at hc
  unfold InInterval at haI ⊢
  have hh := hp.h_ge_six
  omega

theorem small_high_high_sum_range {r h t a b c : Nat} (hp : Params r h t)
    (ha : SmallResidue h a) (hb : HighResidue r h t b)
    (hc : HighResidue r h t c) :
    InInterval (12 * D r h t + 3) (14 * D r h t + h + 1) (a + b + c) := by
  have haI := smallResidue_range (r := r) (h := h) (t := t) hp ha
  unfold HighResidue InInterval at hb hc
  unfold InInterval at haI ⊢
  have hh := hp.h_ge_six
  omega

theorem low_low_low_sum_range {r h t a b c : Nat}
    (ha : LowResidue r h t a) (hb : LowResidue r h t b)
    (hc : LowResidue r h t c) :
    InInterval (3 * D r h t) (6 * D r h t + 3) (a + b + c) := by
  unfold LowResidue InInterval at ha hb hc
  unfold InInterval
  omega

theorem low_low_high_sum_range {r h t a b c : Nat}
    (ha : LowResidue r h t a) (hb : LowResidue r h t b)
    (hc : HighResidue r h t c) :
    InInterval (8 * D r h t + 1) (11 * D r h t + 3) (a + b + c) := by
  unfold LowResidue InInterval at ha hb
  unfold HighResidue InInterval at hc
  unfold InInterval
  omega

theorem low_high_high_sum_range {r h t a b c : Nat}
    (ha : LowResidue r h t a) (hb : HighResidue r h t b)
    (hc : HighResidue r h t c) :
    InInterval (13 * D r h t + 2) (16 * D r h t + 3) (a + b + c) := by
  unfold LowResidue InInterval at ha
  unfold HighResidue InInterval at hb hc
  unfold InInterval
  omega

theorem high_high_high_sum_range {r h t a b c : Nat}
    (ha : HighResidue r h t a) (hb : HighResidue r h t b)
    (hc : HighResidue r h t c) :
    InInterval (18 * D r h t + 3) (21 * D r h t + 3) (a + b + c) := by
  unfold HighResidue InInterval at ha hb hc
  unfold InInterval
  omega

end TransitionDenseCap
end GreedyThreeSumfree
