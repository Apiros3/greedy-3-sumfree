import GreedyThreeSumfree.RBandMixedDistinctCoverage

namespace GreedyThreeSumfree
namespace RBand

/-- The sorted two-equal pattern `{a,a,b}` with `a < b`, in any input order. -/
def TwoLeftIndexPattern (a b i j k : Nat) : Prop :=
  (i = a ∧ j = a ∧ k = b) ∨
  (i = a ∧ j = b ∧ k = a) ∨
  (i = b ∧ j = a ∧ k = a)

/-- The sorted two-equal pattern `{a,b,b}` with `a < b`, in any input order. -/
def TwoRightIndexPattern (a b i j k : Nat) : Prop :=
  (i = a ∧ j = b ∧ k = b) ∨
  (i = b ∧ j = a ∧ k = b) ∨
  (i = b ∧ j = b ∧ k = a)

/-- The sorted all-distinct pattern `{a,b,c}` with `a < b < c`, in any input order. -/
def StrictIndexPattern (a b c i j k : Nat) : Prop :=
  (i = a ∧ j = b ∧ k = c) ∨
  (i = a ∧ j = c ∧ k = b) ∨
  (i = b ∧ j = a ∧ k = c) ∨
  (i = b ∧ j = c ∧ k = a) ∨
  (i = c ∧ j = a ∧ k = b) ∨
  (i = c ∧ j = b ∧ k = a)

/--
Every bounded index triple is, after sorting, either all equal, has exactly two
equal indices, or is strictly increasing.
-/
theorem bounded_triple_indices_sorted_cases {r i j k : Nat}
    (hi : i < r) (hj : j < r) (hk : k < r) :
    (∃ a : Nat, a < r ∧ i = a ∧ j = a ∧ k = a) ∨
    (∃ a b : Nat,
      a < b ∧
      a < r ∧
      b < r ∧
      (TwoLeftIndexPattern a b i j k ∨ TwoRightIndexPattern a b i j k)) ∨
    (∃ a b c : Nat,
      a < b ∧
      b < c ∧
      a < r ∧
      b < r ∧
      c < r ∧
      StrictIndexPattern a b c i j k) := by
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      exact Or.inl ⟨i, hi, rfl, rfl, rfl⟩
    · by_cases hik_lt : i < k
      · exact Or.inr (Or.inl
          ⟨i, k, hik_lt, hi, hk, Or.inl (Or.inl ⟨rfl, rfl, rfl⟩)⟩)
      · have hki : k < i := by omega
        exact Or.inr (Or.inl
          ⟨k, i, hki, hk, hi,
            Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))⟩)
  · by_cases hik : i = k
    · subst k
      by_cases hij_lt : i < j
      · exact Or.inr (Or.inl
          ⟨i, j, hij_lt, hi, hj,
            Or.inl (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))⟩)
      · have hji : j < i := by omega
        exact Or.inr (Or.inl
          ⟨j, i, hji, hj, hi,
            Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))⟩)
    · by_cases hjk : j = k
      · subst k
        by_cases hji : j < i
        · exact Or.inr (Or.inl
            ⟨j, i, hji, hj, hi,
              Or.inl (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))⟩)
        · have hij_lt : i < j := by omega
          exact Or.inr (Or.inl
            ⟨i, j, hij_lt, hi, hj,
              Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩)
      · by_cases hij_lt : i < j
        · by_cases hjk_lt : j < k
          · exact Or.inr (Or.inr
              ⟨i, j, k, hij_lt, hjk_lt, hi, hj, hk,
                Or.inl ⟨rfl, rfl, rfl⟩⟩)
          · have hkj : k < j := by omega
            by_cases hik_lt : i < k
            · exact Or.inr (Or.inr
                ⟨i, k, j, hik_lt, hkj, hi, hk, hj,
                  Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩)
            · have hki : k < i := by omega
              exact Or.inr (Or.inr
                ⟨k, i, j, hki, hij_lt, hk, hi, hj,
                  Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))⟩)
        · have hji : j < i := by omega
          by_cases hik_lt : i < k
          · exact Or.inr (Or.inr
              ⟨j, i, k, hji, hik_lt, hj, hi, hk,
                Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))⟩)
          · have hki : k < i := by omega
            by_cases hjk_lt : j < k
            · exact Or.inr (Or.inr
                ⟨j, k, i, hjk_lt, hki, hj, hk, hi,
                  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))⟩)
            · have hkj : k < j := by omega
              exact Or.inr (Or.inr
                ⟨k, j, i, hkj, hji, hk, hj, hi,
                  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))⟩)

/-- Same-index slice interior, repackaged as an ordered distinct `U` witness. -/
theorem tripleHSlice_distinct_same_inU {r h e i t : Nat}
    (hp : Params r h e) (hi : i < r)
    (ht :
      InInterval (tripleHSliceLo r h e (i + i + i) + 3)
        (tripleHSliceHi r h e (i + i + i) - 3) t) :
    ∃ x y z : Nat,
      InU r h e x ∧
      InU r h e y ∧
      InU r h e z ∧
      x < y ∧
      y < z ∧
      x + y + z = t := by
  have hlo :
      3 * HLo r h e i + 3 =
        tripleHSliceLo r h e (i + i + i) + 3 := by
    unfold HLo tripleHSliceLo
    simp [Nat.left_distrib, Nat.right_distrib]
    omega
  have hhi :
      3 * HHi r h e i - 3 =
        tripleHSliceHi r h e (i + i + i) - 3 := by
    have hh := hp.h_ge_six
    unfold HHi HLo tripleHSliceHi
    simp [Nat.left_distrib, Nat.right_distrib]
    omega
  have htSame :
      InInterval (3 * HLo r h e i + 3) (3 * HHi r h e i - 3) t := by
    rw [hlo, hhi]
    exact ht
  rcases H_triple_sum_distinct_same_index
      (r := r) (h := h) (e := e) (i := i) (t := t) hp htSame with
    ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩
  exact
    ⟨x, y, z, ⟨i, hi, hx⟩, ⟨i, hi, hy⟩, ⟨i, hi, hz⟩, hxy, hyz, hsum⟩

/-- Strict-index slice coverage, repackaged as an ordered distinct `U` witness. -/
theorem tripleHSlice_distinct_strict_inU {r h e i j k t : Nat}
    (hp : Params r h e) (hi : i < r) (hj : j < r) (hk : k < r)
    (hij : i < j) (hjk : j < k)
    (ht : InTripleHSlice r h e (i + j + k) t) :
    ∃ x y z : Nat,
      InU r h e x ∧
      InU r h e y ∧
      InU r h e z ∧
      x < y ∧
      y < z ∧
      x + y + z = t := by
  rcases H_triple_sum_distinct_of_strict_indices
      (r := r) (h := h) (e := e) (i := i) (j := j) (k := k) (t := t)
      hp hij hjk ht with
    ⟨x, y, z, hx, hy, hz, hxy, hyz, hsum⟩
  exact
    ⟨x, y, z, ⟨i, hi, hx⟩, ⟨j, hj, hy⟩, ⟨k, hk, hz⟩, hxy, hyz, hsum⟩

/--
The endpoint-trimmed three-`H` slice condition for an explicit bounded index
triple.

The active clause is determined by sorting `(i,j,k)`: same-index slices use
the `[lo+3, hi-3]` trim, two-equal slices use `[lo+1, hi-1]`, and strictly
increasing slices are untrimmed.
-/
def InEndpointTrimmedTripleHSlice
    (r h e i j k t : Nat) : Prop :=
  (∀ a : Nat, i = a → j = a → k = a →
    InInterval (tripleHSliceLo r h e (a + a + a) + 3)
      (tripleHSliceHi r h e (a + a + a) - 3) t) ∧
  (∀ a b : Nat, a < b → TwoLeftIndexPattern a b i j k →
    InInterval (tripleHSliceLo r h e (a + a + b) + 1)
      (tripleHSliceHi r h e (a + a + b) - 1) t) ∧
  (∀ a b : Nat, a < b → TwoRightIndexPattern a b i j k →
    InInterval (tripleHSliceLo r h e (a + b + b) + 1)
      (tripleHSliceHi r h e (a + b + b) - 1) t) ∧
  (∀ a b c : Nat, a < b → b < c → StrictIndexPattern a b c i j k →
    InTripleHSlice r h e (a + b + c) t)

/--
Fixed explicit-index distinct coverage for the endpoint-trimmed slice selected
by the sorted equality pattern of `(i,j,k)`.

This is not a global final-prefix-gap coverage theorem: it returns an ordered
distinct `x < y < z` witness only after explicit bounded indices and the
corresponding trimmed slice condition are supplied.
-/
theorem tripleHSlice_distinct_inU_of_explicit_indices {r h e i j k t : Nat}
    (hp : Params r h e) (hi : i < r) (hj : j < r) (hk : k < r)
    (ht : InEndpointTrimmedTripleHSlice r h e i j k t) :
    ∃ x y z : Nat,
      InU r h e x ∧
      InU r h e y ∧
      InU r h e z ∧
      x < y ∧
      y < z ∧
      x + y + z = t := by
  rcases ht with ⟨hSame, hTwoLeft, hTwoRight, hStrict⟩
  rcases bounded_triple_indices_sorted_cases
      (r := r) (i := i) (j := j) (k := k) hi hj hk with hsame | hrest
  · rcases hsame with ⟨a, ha, hia, hja, hka⟩
    exact tripleHSlice_distinct_same_inU
      (r := r) (h := h) (e := e) (i := a) (t := t) hp ha
      (hSame a hia hja hka)
  · rcases hrest with htwo | hstrict
    · rcases htwo with ⟨a, b, hab, ha, hb, hpat⟩
      rcases hpat with hleft | hright
      · exact tripleHSlice_distinct_two_left_inU
          (r := r) (h := h) (e := e) (i := a) (j := b) (t := t)
          hp ha hb hab (hTwoLeft a b hab hleft)
      · exact tripleHSlice_distinct_two_right_inU
          (r := r) (h := h) (e := e) (i := a) (j := b) (t := t)
          hp ha hb hab (hTwoRight a b hab hright)
    · rcases hstrict with ⟨a, b, c, hab, hbc, ha, hb, hc, hpat⟩
      exact tripleHSlice_distinct_strict_inU
        (r := r) (h := h) (e := e) (i := a) (j := b) (k := c) (t := t)
        hp ha hb hc hab hbc (hStrict a b c hab hbc hpat)

end RBand
end GreedyThreeSumfree
