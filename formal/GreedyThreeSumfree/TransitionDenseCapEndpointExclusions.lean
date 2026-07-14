import GreedyThreeSumfree.TransitionDenseCapResidues

namespace GreedyThreeSumfree
namespace TransitionDenseCap

theorem D_add_one_inQ_zero {r h t : Nat} :
    InQ r h t 0 (D r h t + 1) := by
  unfold InQ InTerminalCap InInterval D
  exact Or.inr (by omega)

theorem twoD_add_one_inE {r h t : Nat} :
    InE r h t (2 * D r h t + 1) := by
  unfold InE Shift
  exact ⟨D r h t + 1, D_add_one_inQ_zero (r := r) (h := h) (t := t), by omega⟩

theorem zero_inQ_one {r h t : Nat} (hp : Params r h t) :
    InQ r h t 1 0 := by
  unfold InQ InFullPacketRun InInterval
  exact Or.inl ⟨0, hp.r_pos, by
    constructor <;>
      omega⟩

theorem D_inX {r h t : Nat} (hp : Params r h t) :
    InX r h t (D r h t) := by
  unfold InX Shift
  exact ⟨0, zero_inQ_one (r := r) (h := h) (t := t) hp, by omega⟩

theorem sixD_add_one_inF {r h t : Nat} (hp : Params r h t) :
    InF r h t (6 * D r h t + 1) := by
  unfold InF Shift
  exact ⟨D r h t, D_inX (r := r) (h := h) (t := t) hp, by omega⟩

theorem inY_ge_sixD_add_two {r h t n : Nat} (hn : InY r h t n) :
    6 * D r h t + 2 <= n := by
  unfold InY Shift at hn
  rcases hn with ⟨w, hw, rfl⟩
  unfold InW Shift at hw
  rcases hw with ⟨u, _hu, hshift⟩
  rw [hshift]
  omega

theorem twoD_add_one_not_inTailResidue {r h t : Nat} (hp : Params r h t) :
    ¬ InTailResidue r h t (2 * D r h t + 1) := by
  intro htail
  rcases htail with hx | hy
  · have hxI := inX_residue_tight_range (r := r) (h := h) (t := t) hp hx
    unfold InInterval at hxI
    omega
  · have hylo := inY_ge_sixD_add_two (r := r) (h := h) (t := t) hy
    omega

theorem sixD_add_one_not_inTailResidue {r h t : Nat} (hp : Params r h t) :
    ¬ InTailResidue r h t (6 * D r h t + 1) := by
  intro htail
  rcases htail with hx | hy
  · have hxI := inX_residue_tight_range (r := r) (h := h) (t := t) hp hx
    have hD := D_ge_three (r := r) (h := h) (t := t) hp
    unfold InInterval at hxI
    omega
  · have hylo := inY_ge_sixD_add_two (r := r) (h := h) (t := t) hy
    omega

theorem twoD_add_one_not_occupiedTailResidue {r h t : Nat} (hp : Params r h t) :
    ¬ OccupiedTailResidue r h t (2 * D r h t + 1) := by
  simpa [OccupiedTailResidue, InTailResidue] using
    twoD_add_one_not_inTailResidue (r := r) (h := h) (t := t) hp

theorem sixD_add_one_not_occupiedTailResidue {r h t : Nat} (hp : Params r h t) :
    ¬ OccupiedTailResidue r h t (6 * D r h t + 1) := by
  simpa [OccupiedTailResidue, InTailResidue] using
    sixD_add_one_not_inTailResidue (r := r) (h := h) (t := t) hp

theorem twoD_add_one_prefixOnlyResidue {r h t : Nat} (hp : Params r h t) :
    (InE r h t (2 * D r h t + 1) ∨ InF r h t (2 * D r h t + 1)) ∧
      ¬ OccupiedTailResidue r h t (2 * D r h t + 1) := by
  constructor
  · exact Or.inl (twoD_add_one_inE (r := r) (h := h) (t := t))
  · exact twoD_add_one_not_occupiedTailResidue (r := r) (h := h) (t := t) hp

theorem sixD_add_one_prefixOnlyResidue {r h t : Nat} (hp : Params r h t) :
    (InE r h t (6 * D r h t + 1) ∨ InF r h t (6 * D r h t + 1)) ∧
      ¬ OccupiedTailResidue r h t (6 * D r h t + 1) := by
  constructor
  · exact Or.inr (sixD_add_one_inF (r := r) (h := h) (t := t) hp)
  · exact sixD_add_one_not_occupiedTailResidue (r := r) (h := h) (t := t) hp

/--
If one small and two high residues hit tail offset `2D`, the hit is the lower
endpoint `1 + (6D+1) + (6D+1) = M + 2D`.
-/
theorem shh_tailHit_twoD_forces_duplicate_sixD_add_one
    {r h t a b c : Nat} (hp : Params r h t)
    (ha : SmallResidue h a)
    (hb : HighResidue r h t b) (hc : HighResidue r h t c)
    (hsum : a + b + c = M r h t + 2 * D r h t) :
    a = 1 ∧ b = 6 * D r h t + 1 ∧ c = 6 * D r h t + 1 := by
  have haI := smallResidue_range (r := r) (h := h) (t := t) hp ha
  unfold InInterval at haI
  unfold HighResidue InInterval at hb hc
  unfold M at hsum
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- A low-low-low hit to `6D+2` has at least two top low endpoints. -/
theorem lll_hit_sixD_add_two_forces_duplicate_twoD_add_one
    {r h t a b c : Nat}
    (ha : LowResidue r h t a)
    (hb : LowResidue r h t b) (hc : LowResidue r h t c)
    (hsum : a + b + c = 6 * D r h t + 2) :
    (a = 2 * D r h t + 1 ∧ b = 2 * D r h t + 1) ∨
      (a = 2 * D r h t + 1 ∧ c = 2 * D r h t + 1) ∨
        (b = 2 * D r h t + 1 ∧ c = 2 * D r h t + 1) := by
  unfold LowResidue InInterval at ha hb hc
  by_cases haTop : a = 2 * D r h t + 1
  · by_cases hbTop : b = 2 * D r h t + 1
    · exact Or.inl ⟨haTop, hbTop⟩
    · have hbLt : b < 2 * D r h t + 1 := by omega
      have hcTop : c = 2 * D r h t + 1 := by omega
      exact Or.inr (Or.inl ⟨haTop, hcTop⟩)
  · have haLt : a < 2 * D r h t + 1 := by omega
    by_cases hbTop : b = 2 * D r h t + 1
    · have hcTop : c = 2 * D r h t + 1 := by omega
      exact Or.inr (Or.inr ⟨hbTop, hcTop⟩)
    · have hbLt : b < 2 * D r h t + 1 := by omega
      have hfalse : False := by omega
      exact False.elim hfalse

/-- A low-low-low hit to `6D+3` is exactly the triple top low endpoint. -/
theorem lll_hit_sixD_add_three_forces_all_twoD_add_one
    {r h t a b c : Nat}
    (ha : LowResidue r h t a)
    (hb : LowResidue r h t b) (hc : LowResidue r h t c)
    (hsum : a + b + c = 6 * D r h t + 3) :
    a = 2 * D r h t + 1 ∧
      b = 2 * D r h t + 1 ∧
        c = 2 * D r h t + 1 := by
  unfold LowResidue InInterval at ha hb hc
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- A low-low-low hit to `6D+3` also gives the duplicate top low endpoint. -/
theorem lll_hit_sixD_add_three_forces_duplicate_twoD_add_one
    {r h t a b c : Nat}
    (ha : LowResidue r h t a)
    (hb : LowResidue r h t b) (hc : LowResidue r h t c)
    (hsum : a + b + c = 6 * D r h t + 3) :
    (a = 2 * D r h t + 1 ∧ b = 2 * D r h t + 1) ∨
      (a = 2 * D r h t + 1 ∧ c = 2 * D r h t + 1) ∨
        (b = 2 * D r h t + 1 ∧ c = 2 * D r h t + 1) := by
  rcases lll_hit_sixD_add_three_forces_all_twoD_add_one
      (r := r) (h := h) (t := t) (a := a) (b := b) (c := c)
      ha hb hc hsum with ⟨haTop, hbTop, _hcTop⟩
  exact Or.inl ⟨haTop, hbTop⟩

/--
If two low residues and one high residue hit tail offset `D`, all three are at
their top endpoints, so the arithmetic identity is the memo endpoint.
-/
theorem llh_tailHit_D_forces_endpoint_identity
    {r h t a b c : Nat}
    (ha : LowResidue r h t a) (hb : LowResidue r h t b)
    (hc : HighResidue r h t c)
    (hsum : a + b + c = M r h t + D r h t) :
    a = 2 * D r h t + 1 ∧
      b = 2 * D r h t + 1 ∧
        c = 7 * D r h t + 1 ∧
          (2 * D r h t + 1) + (2 * D r h t + 1) + (7 * D r h t + 1) =
            M r h t + D r h t := by
  unfold LowResidue InInterval at ha hb
  unfold HighResidue InInterval at hc
  unfold M at hsum ⊢
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

end TransitionDenseCap
end GreedyThreeSumfree
