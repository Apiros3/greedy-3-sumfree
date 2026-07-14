import GreedyThreeSumfree.TransitionDenseCapEndpointExclusions
import GreedyThreeSumfree.TransitionDenseCapPrefixSafety

namespace GreedyThreeSumfree
namespace TransitionDenseCap

/-- Residues available only from the finite prefix, not from a positive tail block. -/
def PrefixOnlyResidue (r h t n : Nat) : Prop :=
  AllowedResidue r h t n ∧ ¬ OccupiedTailResidue r h t n

/-- No two entries of a three-residue tuple equal the distinguished value. -/
def NoDuplicateValue3 (x y z v : Nat) : Prop :=
  (x = v → y ≠ v) ∧ (x = v → z ≠ v) ∧ (y = v → z ≠ v)

/--
Admissible residue triples for the dense-tail audit. Tail residues may repeat
because they can occur in different positive blocks; prefix-only residues may
not repeat.
-/
def AdmissibleResidueTriple (r h t a b c : Nat) : Prop :=
  AllowedResidue r h t a ∧
    AllowedResidue r h t b ∧
      AllowedResidue r h t c ∧
        ∀ v : Nat, PrefixOnlyResidue r h t v → NoDuplicateValue3 a b c v

/-- Oriented small-small-high tail hit: two small residues and an `F \ Y` predecessor. -/
def SmallSmallFGapHit (r h t rho x y z : Nat) : Prop :=
  ((x = 1 ∧ y = h - 1) ∨ (x = h - 1 ∧ y = 1)) ∧
    InF r h t z ∧ ¬ InY r h t z ∧ rho = z + h

/-- The small-small-`F \ Y` hit, with the high residue in any position. -/
def PermutedSmallSmallFGapHit (r h t rho a b c : Nat) : Prop :=
  SmallSmallFGapHit r h t rho a b c ∨
    SmallSmallFGapHit r h t rho a c b ∨
      SmallSmallFGapHit r h t rho b c a

private theorem h_le_D_classification {r h t : Nat} (hp : Params r h t) :
    h <= D r h t := by
  have hr := hp.r_pos
  have hcoef : 1 <= 2 * r := by omega
  have hmul : 1 * h <= 2 * r * h := Nat.mul_le_mul_right h hcoef
  unfold D
  omega

theorem occupiedTailResidue_tight_range {r h t n : Nat} (hp : Params r h t)
    (hn : OccupiedTailResidue r h t n) :
    InInterval (D r h t) (2 * D r h t) n ∨
      InInterval (6 * D r h t + 2) (7 * D r h t + 1) n := by
  rcases hn with hx | hy
  · exact Or.inl (inX_residue_tight_range (r := r) (h := h) (t := t) hp hx)
  · right
    have hylo : 6 * D r h t + 2 <= n := by
      unfold InY Shift at hy
      rcases hy with ⟨w, hw, rfl⟩
      unfold InW Shift at hw
      rcases hw with ⟨u, _hu, hshift⟩
      rw [hshift]
      omega
    have hyhi := inY_residue_range (r := r) (h := h) (t := t) hp hy
    unfold HighResidue InInterval at hyhi
    exact ⟨hylo, hyhi.2⟩

theorem smallResidue_not_occupiedTailResidue {r h t n : Nat}
    (hp : Params r h t) (hn : SmallResidue h n) :
    ¬ OccupiedTailResidue r h t n := by
  intro htail
  have hnI := smallResidue_range (r := r) (h := h) (t := t) hp hn
  have htight := occupiedTailResidue_tight_range (r := r) (h := h) (t := t) hp htail
  have hleD := h_le_D_classification (r := r) (h := h) (t := t) hp
  unfold InInterval at hnI
  rcases htight with hx | hy
  · unfold InInterval at hx
    omega
  · unfold InInterval at hy
    omega

theorem smallResidue_prefixOnlyResidue {r h t n : Nat}
    (hp : Params r h t) (hn : SmallResidue h n) :
    PrefixOnlyResidue r h t n := by
  constructor
  · unfold AllowedResidue SigmaResidue
    exact Or.inl hn
  · exact smallResidue_not_occupiedTailResidue (r := r) (h := h) (t := t) hp hn

theorem one_prefixOnlyResidue {r h t : Nat} (hp : Params r h t) :
    PrefixOnlyResidue r h t 1 := by
  exact smallResidue_prefixOnlyResidue (r := r) (h := h) (t := t) hp (Or.inl rfl)

theorem h_sub_one_prefixOnlyResidue {r h t : Nat} (hp : Params r h t) :
    PrefixOnlyResidue r h t (h - 1) := by
  exact smallResidue_prefixOnlyResidue (r := r) (h := h) (t := t) hp (Or.inr rfl)

theorem admissible_noDuplicate_of_prefixOnly {r h t a b c v : Nat}
    (hA : AdmissibleResidueTriple r h t a b c)
    (hv : PrefixOnlyResidue r h t v) :
    NoDuplicateValue3 a b c v := by
  exact hA.2.2.2 v hv

theorem noDuplicateValue3_pair12_false {x y z v : Nat}
    (hnd : NoDuplicateValue3 x y z v) (hx : x = v) (hy : y = v) :
    False := by
  exact hnd.1 hx hy

theorem noDuplicateValue3_pair13_false {x y z v : Nat}
    (hnd : NoDuplicateValue3 x y z v) (hx : x = v) (hz : z = v) :
    False := by
  exact hnd.2.1 hx hz

theorem noDuplicateValue3_pair23_false {x y z v : Nat}
    (hnd : NoDuplicateValue3 x y z v) (hy : y = v) (hz : z = v) :
    False := by
  exact hnd.2.2 hy hz

theorem two_small_residue_sum_eq_h
    {r h t a b c : Nat} (hp : Params r h t)
    (hA : AdmissibleResidueTriple r h t a b c)
    (ha : SmallResidue h a) (hb : SmallResidue h b) :
    (((a = 1 ∧ b = h - 1) ∨ (a = h - 1 ∧ b = 1)) ∧ a + b = h) := by
  rcases ha with rfl | rfl
  · rcases hb with hb | hb
    · have hnd := admissible_noDuplicate_of_prefixOnly hA
        (one_prefixOnlyResidue (r := r) (h := h) (t := t) hp)
      exact False.elim (noDuplicateValue3_pair12_false hnd rfl hb)
    · refine ⟨Or.inl ⟨rfl, hb⟩, ?_⟩
      rw [hb]
      have hh := hp.h_ge_six
      omega
  · rcases hb with hb | hb
    · refine ⟨Or.inr ⟨rfl, hb⟩, ?_⟩
      rw [hb]
      have hh := hp.h_ge_six
      omega
    · have hnd := admissible_noDuplicate_of_prefixOnly hA
        (h_sub_one_prefixOnlyResidue (r := r) (h := h) (t := t) hp)
      exact False.elim (noDuplicateValue3_pair12_false hnd rfl hb)

theorem admissible_not_all_three_small
    {r h t a b c : Nat} (hp : Params r h t)
    (hA : AdmissibleResidueTriple r h t a b c)
    (ha : SmallResidue h a) (hb : SmallResidue h b) (hc : SmallResidue h c) :
    False := by
  rcases ha with rfl | rfl
  · rcases hb with hb | hb
    · have hnd := admissible_noDuplicate_of_prefixOnly hA
        (one_prefixOnlyResidue (r := r) (h := h) (t := t) hp)
      exact noDuplicateValue3_pair12_false hnd rfl hb
    · rcases hc with hc1 | hch
      · have hnd := admissible_noDuplicate_of_prefixOnly hA
          (one_prefixOnlyResidue (r := r) (h := h) (t := t) hp)
        exact noDuplicateValue3_pair13_false hnd rfl hc1
      · have hnd := admissible_noDuplicate_of_prefixOnly hA
          (h_sub_one_prefixOnlyResidue (r := r) (h := h) (t := t) hp)
        exact noDuplicateValue3_pair23_false hnd hb hch
  · rcases hb with hb | hb
    · rcases hc with hc1 | hch
      · have hnd := admissible_noDuplicate_of_prefixOnly hA
          (one_prefixOnlyResidue (r := r) (h := h) (t := t) hp)
        exact noDuplicateValue3_pair23_false hnd hb hc1
      · have hnd := admissible_noDuplicate_of_prefixOnly hA
          (h_sub_one_prefixOnlyResidue (r := r) (h := h) (t := t) hp)
        exact noDuplicateValue3_pair13_false hnd rfl hch
    · have hnd := admissible_noDuplicate_of_prefixOnly hA
        (h_sub_one_prefixOnlyResidue (r := r) (h := h) (t := t) hp)
      exact noDuplicateValue3_pair12_false hnd rfl hb

theorem allowed_low_inE {r h t n : Nat} (hp : Params r h t)
    (hn : AllowedResidue r h t n) (hlo : LowResidue r h t n) :
    InE r h t n := by
  unfold AllowedResidue SigmaResidue at hn
  rcases hn with hs | hE | hF | hX | hY
  · have hsI := smallResidue_range (r := r) (h := h) (t := t) hp hs
    have hleD := h_le_D_classification (r := r) (h := h) (t := t) hp
    unfold LowResidue InInterval at hlo
    unfold InInterval at hsI
    omega
  · exact hE
  · have hFI := inF_residue_range (r := r) (h := h) (t := t) hp hF
    unfold LowResidue InInterval at hlo
    unfold HighResidue InInterval at hFI
    have hD := D_ge_three (r := r) (h := h) (t := t) hp
    omega
  · exact inE_of_inX hX
  · have hYI := inY_residue_range (r := r) (h := h) (t := t) hp hY
    unfold LowResidue InInterval at hlo
    unfold HighResidue InInterval at hYI
    have hD := D_ge_three (r := r) (h := h) (t := t) hp
    omega

theorem allowed_high_inF_or_inY {r h t n : Nat} (hp : Params r h t)
    (hn : AllowedResidue r h t n) (hhi : HighResidue r h t n) :
    InF r h t n ∨ InY r h t n := by
  unfold AllowedResidue SigmaResidue at hn
  rcases hn with hs | hE | hF | hX | hY
  · have hsI := smallResidue_range (r := r) (h := h) (t := t) hp hs
    have hleD := h_le_D_classification (r := r) (h := h) (t := t) hp
    unfold HighResidue InInterval at hhi
    unfold InInterval at hsI
    omega
  · have hEI := inE_residue_range (r := r) (h := h) (t := t) hp hE
    unfold LowResidue InInterval at hEI
    unfold HighResidue InInterval at hhi
    have hD := D_ge_three (r := r) (h := h) (t := t) hp
    omega
  · exact Or.inl hF
  · have hXI := inX_residue_range (r := r) (h := h) (t := t) hp hX
    unfold LowResidue InInterval at hXI
    unfold HighResidue InInterval at hhi
    have hD := D_ge_three (r := r) (h := h) (t := t) hp
    omega
  · exact Or.inr hY

theorem occupied_low_inX {r h t rho : Nat} (hp : Params r h t)
    (hrho : OccupiedTailResidue r h t rho) (hrhoLow : LowResidue r h t rho) :
    InX r h t rho := by
  rcases hrho with hx | hy
  · exact hx
  · have hyI := inY_residue_range (r := r) (h := h) (t := t) hp hy
    unfold LowResidue InInterval at hrhoLow
    unfold HighResidue InInterval at hyI
    have hD := D_ge_three (r := r) (h := h) (t := t) hp
    omega

theorem occupied_high_inY {r h t rho : Nat} (hp : Params r h t)
    (hrho : OccupiedTailResidue r h t rho) (hrhoHigh : HighResidue r h t rho) :
    InY r h t rho := by
  rcases hrho with hx | hy
  · have hxI := inX_residue_range (r := r) (h := h) (t := t) hp hx
    unfold LowResidue InInterval at hxI
    unfold HighResidue InInterval at hrhoHigh
    have hD := D_ge_three (r := r) (h := h) (t := t) hp
    omega
  · exact hy

private theorem full_run_h_shift_not_full_run {r h t i j u v : Nat}
    (hp : Params r h t)
    (_hi : i < r) (_hj : j < r)
    (hu : InInterval (2 * i * h) (2 * i * h + h - 1) u)
    (hv : InInterval (2 * j * h) (2 * j * h + h - 1) v)
    (hshift : v = u + h) :
    False := by
  by_cases hij : i < j
  · have hij_succ : i + 1 <= j := by omega
    have hcoef : 2 * (i + 1) <= 2 * j := by omega
    have hprod : 2 * (i + 1) * h <= 2 * j * h :=
      Nat.mul_le_mul_right h hcoef
    have hprod_eq : 2 * (i + 1) * h = 2 * i * h + 2 * h := by
      rw [Nat.left_distrib, Nat.right_distrib]
    rw [hprod_eq] at hprod
    have hvlo : 2 * j * h <= v := hv.1
    have huhi : u <= 2 * i * h + h - 1 := hu.2
    have hpos : 1 <= h := by
      have hh := hp.h_ge_six
      omega
    have hstep : u + h < 2 * i * h + 2 * h := by omega
    omega
  · have hji : j <= i := by omega
    have hcoef : 2 * j <= 2 * i := by omega
    have hprod : 2 * j * h <= 2 * i * h :=
      Nat.mul_le_mul_right h hcoef
    have hulo : 2 * i * h <= u := hu.1
    have hvhi : v <= 2 * j * h + h - 1 := hv.2
    have hpos : 1 <= h := by
      have hh := hp.h_ge_six
      omega
    have hstep : 2 * i * h + h <= u + h := by omega
    have hhi : 2 * j * h + h - 1 < 2 * i * h + h := by omega
    omega

private theorem full_run_h_shift_not_terminal {r h t s i u v : Nat}
    (hp : Params r h t)
    (hi : i < r)
    (hu : InInterval (2 * i * h) (2 * i * h + h - 1) u)
    (hv : InInterval (2 * r * h) (2 * r * h + t + 1 - s) v)
    (hshift : v = u + h) :
    False := by
  have hi_succ : i + 1 <= r := by omega
  have hcoef : 2 * (i + 1) <= 2 * r := by omega
  have hprod : 2 * (i + 1) * h <= 2 * r * h :=
    Nat.mul_le_mul_right h hcoef
  have hprod_eq : 2 * (i + 1) * h = 2 * i * h + 2 * h := by
    rw [Nat.left_distrib, Nat.right_distrib]
  rw [hprod_eq] at hprod
  have huhi : u <= 2 * i * h + h - 1 := hu.2
  have hvlo : 2 * r * h <= v := hv.1
  have hpos : 1 <= h := by
    have hh := hp.h_ge_six
    omega
  have hstep : u + h < 2 * i * h + 2 * h := by omega
  omega

private theorem terminal_h_shift_not_full_run {r h t s j u v : Nat}
    (hp : Params r h t)
    (hj : j < r)
    (hu : InInterval (2 * r * h) (2 * r * h + t + 1 - s) u)
    (hv : InInterval (2 * j * h) (2 * j * h + h - 1) v)
    (hshift : v = u + h) :
    False := by
  have hgap := full_run_hi_lt_terminal_cap_lo
    (r := r) (h := h) (t := t) (i := j) hp hj
  have hulo : 2 * r * h <= u := hu.1
  have hvhi : v <= 2 * j * h + h - 1 := hv.2
  omega

private theorem terminal_h_shift_not_terminal_of_s_le_two
    {r h t s u v : Nat}
    (hp : Params r h t) (hs : s <= 2)
    (hu : InInterval (2 * r * h) (2 * r * h + t + 1 - s) u)
    (hv : InInterval (2 * r * h) (2 * r * h + t + 1 - s) v)
    (hshift : v = u + h) :
    False := by
  have hh := hp.h_ge_six
  have ht := hp.dense_upper
  have hulo : 2 * r * h <= u := hu.1
  have hvhi : v <= 2 * r * h + t + 1 - s := hv.2
  have ht_s : t + 1 - s <= h - 1 := by omega
  omega

theorem inQ_no_h_shift_of_s_le_two {r h t s u v : Nat}
    (hp : Params r h t) (hs : s <= 2)
    (hu : InQ r h t s u) (hv : InQ r h t s v)
    (hshift : v = u + h) :
    False := by
  unfold InQ at hu hv
  rcases hu with hfullU | htermU
  · rcases hfullU with ⟨i, hi, huI⟩
    rcases hv with hfullV | htermV
    · rcases hfullV with ⟨j, hj, hvI⟩
      exact full_run_h_shift_not_full_run
        (r := r) (h := h) (t := t) (i := i) (j := j)
        (u := u) (v := v) hp hi hj huI hvI hshift
    · exact full_run_h_shift_not_terminal
        (r := r) (h := h) (t := t) (s := s) (i := i)
        (u := u) (v := v) hp hi huI htermV hshift
  · rcases hv with hfullV | htermV
    · rcases hfullV with ⟨j, hj, hvI⟩
      exact terminal_h_shift_not_full_run
        (r := r) (h := h) (t := t) (s := s) (j := j)
        (u := u) (v := v) hp hj htermU hvI hshift
    · exact terminal_h_shift_not_terminal_of_s_le_two
        (r := r) (h := h) (t := t) (s := s)
        (u := u) (v := v) hp hs htermU htermV hshift

theorem inW_no_h_shift {r h t u v : Nat}
    (hp : Params r h t)
    (hu : InW r h t u) (hv : InW r h t v)
    (hshift : v = u + h) :
    False := by
  unfold InW Shift at hu hv
  rcases hu with ⟨u0, hu0, huEq⟩
  rcases hv with ⟨v0, hv0, hvEq⟩
  have hshift0 : v0 = u0 + h := by omega
  exact inQ_no_h_shift_of_s_le_two
    (r := r) (h := h) (t := t) (s := 2)
    (u := u0) (v := v0) hp (by omega) hu0 hv0 hshift0

theorem inY_no_h_shift {r h t u v : Nat}
    (hp : Params r h t)
    (hu : InY r h t u) (hv : InY r h t v)
    (hshift : v = u + h) :
    False := by
  unfold InY Shift at hu hv
  rcases hu with ⟨uw, huW, huEq⟩
  rcases hv with ⟨vw, hvW, hvEq⟩
  have hshift0 : vw = uw + h := by omega
  exact inW_no_h_shift
    (r := r) (h := h) (t := t) (u := uw) (v := vw)
    hp huW hvW hshift0

theorem twoD_add_one_prefixOnlyResidue_for_tail_classification {r h t : Nat}
    (hp : Params r h t) :
    PrefixOnlyResidue r h t (2 * D r h t + 1) := by
  have hprefix := twoD_add_one_prefixOnlyResidue (r := r) (h := h) (t := t) hp
  constructor
  · rcases hprefix.1 with hE | hF
    · unfold AllowedResidue SigmaResidue
      exact Or.inr (Or.inl hE)
    · unfold AllowedResidue SigmaResidue
      exact Or.inr (Or.inr (Or.inl hF))
  · exact hprefix.2

theorem sixD_add_one_prefixOnlyResidue_for_tail_classification {r h t : Nat}
    (hp : Params r h t) :
    PrefixOnlyResidue r h t (6 * D r h t + 1) := by
  have hprefix := sixD_add_one_prefixOnlyResidue (r := r) (h := h) (t := t) hp
  constructor
  · rcases hprefix.1 with hE | hF
    · unfold AllowedResidue SigmaResidue
      exact Or.inr (Or.inl hE)
    · unfold AllowedResidue SigmaResidue
      exact Or.inr (Or.inr (Or.inl hF))
  · exact hprefix.2

private theorem duplicate_twoD_add_one_false
    {r h t a b c : Nat} (hp : Params r h t)
    (hA : AdmissibleResidueTriple r h t a b c)
    (hdup :
      (a = 2 * D r h t + 1 ∧ b = 2 * D r h t + 1) ∨
        (a = 2 * D r h t + 1 ∧ c = 2 * D r h t + 1) ∨
          (b = 2 * D r h t + 1 ∧ c = 2 * D r h t + 1)) :
    False := by
  have hnd := admissible_noDuplicate_of_prefixOnly
    (r := r) (h := h) (t := t) (a := a) (b := b) (c := c)
    (v := 2 * D r h t + 1) hA
    (twoD_add_one_prefixOnlyResidue_for_tail_classification
      (r := r) (h := h) (t := t) hp)
  rcases hdup with hab | hac | hbc
  · exact noDuplicateValue3_pair12_false hnd hab.1 hab.2
  · exact noDuplicateValue3_pair13_false hnd hac.1 hac.2
  · exact noDuplicateValue3_pair23_false hnd hbc.1 hbc.2

private theorem duplicate_sixD_add_one_false
    {r h t a b c : Nat} (hp : Params r h t)
    (hA : AdmissibleResidueTriple r h t a b c)
    (hbtop : b = 6 * D r h t + 1) (hctop : c = 6 * D r h t + 1) :
    False := by
  have hnd := admissible_noDuplicate_of_prefixOnly
    (r := r) (h := h) (t := t) (a := a) (b := b) (c := c)
    (v := 6 * D r h t + 1) hA
    (sixD_add_one_prefixOnlyResidue_for_tail_classification
      (r := r) (h := h) (t := t) hp)
  exact noDuplicateValue3_pair23_false hnd hbtop hctop

theorem small_small_low_tail_hit_false
    {r h t rho carry a b c : Nat} (hp : Params r h t)
    (hA : AdmissibleResidueTriple r h t a b c)
    (ha : SmallResidue h a) (hb : SmallResidue h b)
    (hcLow : LowResidue r h t c)
    (hrho : OccupiedTailResidue r h t rho)
    (hsum : a + b + c = rho + carry * M r h t) :
    False := by
  have hsmall := two_small_residue_sum_eq_h
    (r := r) (h := h) (t := t) (a := a) (b := b) (c := c) hp hA ha hb
  have habsum : a + b = h := hsmall.2
  have hcE := allowed_low_inE (r := r) (h := h) (t := t) hp hA.2.2.1 hcLow
  have hcRange := small_small_low_sum_range
    (r := r) (h := h) (t := t) (a := a) (b := b) (c := c) hp ha hb hcLow
  have htight := occupiedTailResidue_tight_range (r := r) (h := h) (t := t) hp hrho
  have hleD := h_le_D_classification (r := r) (h := h) (t := t) hp
  by_cases hcarry0 : carry = 0
  · rw [hcarry0] at hsum
    simp at hsum
    have hrhoLow : LowResidue r h t rho := by
      unfold LowResidue InInterval
      rcases htight with hx | hy
      · exact ⟨hx.1, by
          have hxhi := hx.2
          omega⟩
      · unfold InInterval at hy
        unfold InInterval at hcRange
        omega
    have hrhoX := occupied_low_inX
      (r := r) (h := h) (t := t) (rho := rho) hp hrho hrhoLow
    have hrhoE := inE_of_inX hrhoX
    have hshift : rho = c + h := by omega
    exact inE_no_h_shift
      (r := r) (h := h) (t := t) (u := c) (v := rho)
      hp hcE hrhoE hshift
  · have hcarry : 1 <= carry := by omega
    have hMle : M r h t <= carry * M r h t := by
      have hmul : 1 * M r h t <= carry * M r h t :=
        Nat.mul_le_mul_right (M r h t) hcarry
      simpa using hmul
    have hsumLower : rho + M r h t <= a + b + c := by omega
    rcases htight with hx | hy
    · unfold InInterval at hx hcRange
      unfold M at hsumLower
      omega
    · unfold InInterval at hy hcRange
      unfold M at hsumLower
      omega

theorem small_small_high_tail_hit_classification
    {r h t rho carry a b c : Nat} (hp : Params r h t)
    (hA : AdmissibleResidueTriple r h t a b c)
    (ha : SmallResidue h a) (hb : SmallResidue h b)
    (hcHigh : HighResidue r h t c)
    (hrho : OccupiedTailResidue r h t rho)
    (hsum : a + b + c = rho + carry * M r h t) :
    carry = 0 ∧ SmallSmallFGapHit r h t rho a b c := by
  have hsmall := two_small_residue_sum_eq_h
    (r := r) (h := h) (t := t) (a := a) (b := b) (c := c) hp hA ha hb
  have hsmallPattern := hsmall.1
  have habsum : a + b = h := hsmall.2
  have hcRange := small_small_high_sum_range
    (r := r) (h := h) (t := t) (a := a) (b := b) (c := c) hp ha hb hcHigh
  have htight := occupiedTailResidue_tight_range (r := r) (h := h) (t := t) hp hrho
  have hleD := h_le_D_classification (r := r) (h := h) (t := t) hp
  have hcarry0 : carry = 0 := by
    by_cases hcarry0 : carry = 0
    · exact hcarry0
    have hcarry : 1 <= carry := by omega
    have hMle : M r h t <= carry * M r h t := by
      have hmul : 1 * M r h t <= carry * M r h t :=
        Nat.mul_le_mul_right (M r h t) hcarry
      simpa using hmul
    have hsumLower : rho + M r h t <= a + b + c := by omega
    rcases htight with hx | hy
    · unfold InInterval at hx hcRange
      unfold M at hsumLower
      exact False.elim (by omega)
    · unfold InInterval at hy hcRange
      unfold M at hsumLower
      exact False.elim (by omega)
  rw [hcarry0] at hsum
  simp at hsum
  have hrhoHigh : HighResidue r h t rho := by
    unfold HighResidue InInterval
    rcases htight with hx | hy
    · unfold InInterval at hx hcRange
      omega
    · exact ⟨by
        have hylo := hy.1
        omega, hy.2⟩
  have hrhoY := occupied_high_inY
    (r := r) (h := h) (t := t) (rho := rho) hp hrho hrhoHigh
  have hshift : rho = c + h := by omega
  have hcFY : InF r h t c ∧ ¬ InY r h t c := by
    rcases allowed_high_inF_or_inY
        (r := r) (h := h) (t := t) (n := c) hp hA.2.2.1 hcHigh with hcF | hcY
    · refine ⟨hcF, ?_⟩
      intro hcY
      exact inY_no_h_shift
        (r := r) (h := h) (t := t) (u := c) (v := rho)
        hp hcY hrhoY hshift
    · exact False.elim
        (inY_no_h_shift
          (r := r) (h := h) (t := t) (u := c) (v := rho)
          hp hcY hrhoY hshift)
  exact ⟨hcarry0, hsmallPattern, hcFY.1, hcFY.2, hshift⟩

theorem small_low_low_tail_hit_false
    {r h t rho carry a b c : Nat} (hp : Params r h t)
    (ha : SmallResidue h a) (hb : LowResidue r h t b)
    (hc : LowResidue r h t c)
    (hrho : OccupiedTailResidue r h t rho)
    (hsum : a + b + c = rho + carry * M r h t) :
    False := by
  have hsumRange := small_low_low_sum_range
    (r := r) (h := h) (t := t) (a := a) (b := b) (c := c) hp ha hb hc
  have htight := occupiedTailResidue_tight_range (r := r) (h := h) (t := t) hp hrho
  have hleD := h_le_D_classification (r := r) (h := h) (t := t) hp
  by_cases hcarry0 : carry = 0
  · rw [hcarry0] at hsum
    simp at hsum
    rcases htight with hx | hy
    · unfold InInterval at hx hsumRange
      have hD := D_ge_three (r := r) (h := h) (t := t) hp
      omega
    · unfold InInterval at hy hsumRange
      omega
  · have hcarry : 1 <= carry := by omega
    have hMle : M r h t <= carry * M r h t := by
      have hmul : 1 * M r h t <= carry * M r h t :=
        Nat.mul_le_mul_right (M r h t) hcarry
      simpa using hmul
    have hsumLower : rho + M r h t <= a + b + c := by omega
    rcases htight with hx | hy
    · unfold InInterval at hx hsumRange
      unfold M at hsumLower
      omega
    · unfold InInterval at hy hsumRange
      unfold M at hsumLower
      omega

theorem small_low_high_tail_hit_false
    {r h t rho carry a b c : Nat} (hp : Params r h t)
    (ha : SmallResidue h a) (hb : LowResidue r h t b)
    (hc : HighResidue r h t c)
    (hrho : OccupiedTailResidue r h t rho)
    (hsum : a + b + c = rho + carry * M r h t) :
    False := by
  have hsumRange := small_low_high_sum_range
    (r := r) (h := h) (t := t) (a := a) (b := b) (c := c) hp ha hb hc
  have htight := occupiedTailResidue_tight_range (r := r) (h := h) (t := t) hp hrho
  have hleD := h_le_D_classification (r := r) (h := h) (t := t) hp
  by_cases hcarry0 : carry = 0
  · rw [hcarry0] at hsum
    simp at hsum
    rcases htight with hx | hy
    · unfold InInterval at hx hsumRange
      have hD := D_ge_three (r := r) (h := h) (t := t) hp
      omega
    · unfold InInterval at hy hsumRange
      omega
  · have hcarry : 1 <= carry := by omega
    have hMle : M r h t <= carry * M r h t := by
      have hmul : 1 * M r h t <= carry * M r h t :=
        Nat.mul_le_mul_right (M r h t) hcarry
      simpa using hmul
    have hsumLower : rho + M r h t <= a + b + c := by omega
    rcases htight with hx | hy
    · unfold InInterval at hx hsumRange
      unfold M at hsumLower
      have hD := D_ge_three (r := r) (h := h) (t := t) hp
      omega
    · unfold InInterval at hy hsumRange
      unfold M at hsumLower
      have hD := D_ge_three (r := r) (h := h) (t := t) hp
      omega

theorem small_high_high_tail_hit_false
    {r h t rho carry a b c : Nat} (hp : Params r h t)
    (hA : AdmissibleResidueTriple r h t a b c)
    (ha : SmallResidue h a) (hb : HighResidue r h t b)
    (hc : HighResidue r h t c)
    (hrho : OccupiedTailResidue r h t rho)
    (hsum : a + b + c = rho + carry * M r h t) :
    False := by
  have hsumRange := small_high_high_sum_range
    (r := r) (h := h) (t := t) (a := a) (b := b) (c := c) hp ha hb hc
  have htight := occupiedTailResidue_tight_range (r := r) (h := h) (t := t) hp hrho
  have hleD := h_le_D_classification (r := r) (h := h) (t := t) hp
  by_cases hcarry0 : carry = 0
  · rw [hcarry0] at hsum
    simp at hsum
    rcases htight with hx | hy
    · unfold InInterval at hx hsumRange
      have hD := D_ge_three (r := r) (h := h) (t := t) hp
      omega
    · unfold InInterval at hy hsumRange
      omega
  · by_cases hcarry1 : carry = 1
    · rw [hcarry1] at hsum
      simp at hsum
      rcases htight with hx | hy
      · have hrhoTop : rho = 2 * D r h t := by
          unfold InInterval at hx hsumRange
          unfold M at hsum
          omega
        have hendpoint : a + b + c = M r h t + 2 * D r h t := by
          rw [hrhoTop] at hsum
          omega
        rcases shh_tailHit_twoD_forces_duplicate_sixD_add_one
            (r := r) (h := h) (t := t) (a := a) (b := b) (c := c)
            hp ha hb hc hendpoint with ⟨_ha, hbtop, hctop⟩
        exact duplicate_sixD_add_one_false
          (r := r) (h := h) (t := t) (a := a) (b := b) (c := c)
          hp hA hbtop hctop
      · unfold InInterval at hy hsumRange
        unfold M at hsum
        omega
    · have hcarry : 2 <= carry := by omega
      have hMle : 2 * M r h t <= carry * M r h t := by
        exact Nat.mul_le_mul_right (M r h t) hcarry
      have hsumLower : rho + 2 * M r h t <= a + b + c := by omega
      rcases htight with hx | hy
      · unfold InInterval at hx hsumRange
        unfold M at hsumLower
        omega
      · unfold InInterval at hy hsumRange
        unfold M at hsumLower
        omega

theorem low_low_low_tail_hit_false
    {r h t rho carry a b c : Nat} (hp : Params r h t)
    (hA : AdmissibleResidueTriple r h t a b c)
    (ha : LowResidue r h t a) (hb : LowResidue r h t b)
    (hc : LowResidue r h t c)
    (hrho : OccupiedTailResidue r h t rho)
    (hsum : a + b + c = rho + carry * M r h t) :
    False := by
  have hsumRange := low_low_low_sum_range
    (r := r) (h := h) (t := t) (a := a) (b := b) (c := c) ha hb hc
  have htight := occupiedTailResidue_tight_range (r := r) (h := h) (t := t) hp hrho
  by_cases hcarry0 : carry = 0
  · rw [hcarry0] at hsum
    simp at hsum
    rcases htight with hx | hy
    · unfold InInterval at hx hsumRange
      have hD := D_ge_three (r := r) (h := h) (t := t) hp
      omega
    · have hrhoEndpoint : rho = 6 * D r h t + 2 ∨ rho = 6 * D r h t + 3 := by
        unfold InInterval at hy hsumRange
        omega
      rcases hrhoEndpoint with hrho2 | hrho3
      · have hdup := lll_hit_sixD_add_two_forces_duplicate_twoD_add_one
          (r := r) (h := h) (t := t) (a := a) (b := b) (c := c)
          ha hb hc (by omega)
        exact duplicate_twoD_add_one_false
          (r := r) (h := h) (t := t) (a := a) (b := b) (c := c)
          hp hA hdup
      · have hdup := lll_hit_sixD_add_three_forces_duplicate_twoD_add_one
          (r := r) (h := h) (t := t) (a := a) (b := b) (c := c)
          ha hb hc (by omega)
        exact duplicate_twoD_add_one_false
          (r := r) (h := h) (t := t) (a := a) (b := b) (c := c)
          hp hA hdup
  · have hcarry : 1 <= carry := by omega
    have hMle : M r h t <= carry * M r h t := by
      have hmul : 1 * M r h t <= carry * M r h t :=
        Nat.mul_le_mul_right (M r h t) hcarry
      simpa using hmul
    have hsumLower : rho + M r h t <= a + b + c := by omega
    rcases htight with hx | hy
    · unfold InInterval at hx hsumRange
      unfold M at hsumLower
      have hD := D_ge_three (r := r) (h := h) (t := t) hp
      omega
    · unfold InInterval at hy hsumRange
      unfold M at hsumLower
      omega

theorem low_low_high_tail_hit_false
    {r h t rho carry a b c : Nat} (hp : Params r h t)
    (hA : AdmissibleResidueTriple r h t a b c)
    (ha : LowResidue r h t a) (hb : LowResidue r h t b)
    (hc : HighResidue r h t c)
    (hrho : OccupiedTailResidue r h t rho)
    (hsum : a + b + c = rho + carry * M r h t) :
    False := by
  have hsumRange := low_low_high_sum_range
    (r := r) (h := h) (t := t) (a := a) (b := b) (c := c) ha hb hc
  have htight := occupiedTailResidue_tight_range (r := r) (h := h) (t := t) hp hrho
  by_cases hcarry0 : carry = 0
  · rw [hcarry0] at hsum
    simp at hsum
    rcases htight with hx | hy
    · unfold InInterval at hx hsumRange
      omega
    · unfold InInterval at hy hsumRange
      omega
  · by_cases hcarry1 : carry = 1
    · rw [hcarry1] at hsum
      simp at hsum
      rcases htight with hx | hy
      · have hrhoBot : rho = D r h t := by
          unfold InInterval at hx hsumRange
          unfold M at hsum
          omega
        have hendpoint : a + b + c = M r h t + D r h t := by
          rw [hrhoBot] at hsum
          omega
        rcases llh_tailHit_D_forces_endpoint_identity
            (r := r) (h := h) (t := t) (a := a) (b := b) (c := c)
            ha hb hc hendpoint with ⟨hatop, hbtop, _hctop⟩
        exact duplicate_twoD_add_one_false
          (r := r) (h := h) (t := t) (a := a) (b := b) (c := c)
          hp hA (Or.inl ⟨hatop, hbtop⟩)
      · unfold InInterval at hy hsumRange
        unfold M at hsum
        omega
    · have hcarry : 2 <= carry := by omega
      have hMle : 2 * M r h t <= carry * M r h t := by
        exact Nat.mul_le_mul_right (M r h t) hcarry
      have hsumLower : rho + 2 * M r h t <= a + b + c := by omega
      rcases htight with hx | hy
      · unfold InInterval at hx hsumRange
        unfold M at hsumLower
        omega
      · unfold InInterval at hy hsumRange
        unfold M at hsumLower
        omega

theorem low_high_high_tail_hit_false
    {r h t rho carry a b c : Nat} (hp : Params r h t)
    (ha : LowResidue r h t a) (hb : HighResidue r h t b)
    (hc : HighResidue r h t c)
    (hrho : OccupiedTailResidue r h t rho)
    (hsum : a + b + c = rho + carry * M r h t) :
    False := by
  have hsumRange := low_high_high_sum_range
    (r := r) (h := h) (t := t) (a := a) (b := b) (c := c) ha hb hc
  have htight := occupiedTailResidue_tight_range (r := r) (h := h) (t := t) hp hrho
  by_cases hcarry0 : carry = 0
  · rw [hcarry0] at hsum
    simp at hsum
    rcases htight with hx | hy
    · unfold InInterval at hx hsumRange
      omega
    · unfold InInterval at hy hsumRange
      omega
  · by_cases hcarry1 : carry = 1
    · rw [hcarry1] at hsum
      simp at hsum
      rcases htight with hx | hy
      · unfold InInterval at hx hsumRange
        unfold M at hsum
        have hD := D_ge_three (r := r) (h := h) (t := t) hp
        omega
      · unfold InInterval at hy hsumRange
        unfold M at hsum
        omega
    · have hcarry : 2 <= carry := by omega
      have hMle : 2 * M r h t <= carry * M r h t := by
        exact Nat.mul_le_mul_right (M r h t) hcarry
      have hsumLower : rho + 2 * M r h t <= a + b + c := by omega
      rcases htight with hx | hy
      · unfold InInterval at hx hsumRange
        unfold M at hsumLower
        omega
      · unfold InInterval at hy hsumRange
        unfold M at hsumLower
        omega

theorem high_high_high_tail_hit_false
    {r h t rho carry a b c : Nat} (hp : Params r h t)
    (ha : HighResidue r h t a) (hb : HighResidue r h t b)
    (hc : HighResidue r h t c)
    (hrho : OccupiedTailResidue r h t rho)
    (hsum : a + b + c = rho + carry * M r h t) :
    False := by
  have hsumRange := high_high_high_sum_range
    (r := r) (h := h) (t := t) (a := a) (b := b) (c := c) ha hb hc
  have htight := occupiedTailResidue_tight_range (r := r) (h := h) (t := t) hp hrho
  by_cases hcarry0 : carry = 0
  · rw [hcarry0] at hsum
    simp at hsum
    rcases htight with hx | hy
    · unfold InInterval at hx hsumRange
      have hD := D_ge_three (r := r) (h := h) (t := t) hp
      omega
    · unfold InInterval at hy hsumRange
      omega
  · by_cases hcarry1 : carry = 1
    · rw [hcarry1] at hsum
      simp at hsum
      rcases htight with hx | hy
      · unfold InInterval at hx hsumRange
        unfold M at hsum
        have hD := D_ge_three (r := r) (h := h) (t := t) hp
        omega
      · unfold InInterval at hy hsumRange
        unfold M at hsum
        have hD := D_ge_three (r := r) (h := h) (t := t) hp
        omega
    · by_cases hcarry2 : carry = 2
      · rw [hcarry2] at hsum
        rcases htight with hx | hy
        · unfold InInterval at hx hsumRange
          unfold M at hsum
          have hD := D_ge_three (r := r) (h := h) (t := t) hp
          omega
        · unfold InInterval at hy hsumRange
          unfold M at hsum
          have hD := D_ge_three (r := r) (h := h) (t := t) hp
          omega
      · have hcarry : 3 <= carry := by omega
        have hMle : 3 * M r h t <= carry * M r h t := by
          exact Nat.mul_le_mul_right (M r h t) hcarry
        have hsumLower : rho + 3 * M r h t <= a + b + c := by omega
        rcases htight with hx | hy
        · unfold InInterval at hx hsumRange
          unfold M at hsumLower
          omega
        · unfold InInterval at hy hsumRange
          unfold M at hsumLower
          omega

theorem tail_residue_hit_classification
    {r h t rho carry a b c : Nat} (hp : Params r h t)
    (hA : AdmissibleResidueTriple r h t a b c)
    (hrho : OccupiedTailResidue r h t rho)
    (hsum : a + b + c = rho + carry * M r h t) :
    carry = 0 ∧ PermutedSmallSmallFGapHit r h t rho a b c := by
  have haCat := allowedResidue_category
    (r := r) (h := h) (t := t) (n := a) hp hA.1
  have hbCat := allowedResidue_category
    (r := r) (h := h) (t := t) (n := b) hp hA.2.1
  have hcCat := allowedResidue_category
    (r := r) (h := h) (t := t) (n := c) hp hA.2.2.1
  rcases haCat with haS | haL | haH
  · rcases hbCat with hbS | hbL | hbH
    · rcases hcCat with hcS | hcL | hcH
      · exact False.elim
          (admissible_not_all_three_small
            (r := r) (h := h) (t := t) (a := a) (b := b) (c := c)
            hp hA haS hbS hcS)
      · exact False.elim
          (small_small_low_tail_hit_false
            (r := r) (h := h) (t := t) (rho := rho) (carry := carry)
            (a := a) (b := b) (c := c) hp hA haS hbS hcL hrho hsum)
      · have hclass := small_small_high_tail_hit_classification
          (r := r) (h := h) (t := t) (rho := rho) (carry := carry)
          (a := a) (b := b) (c := c) hp hA haS hbS hcH hrho hsum
        exact ⟨hclass.1, Or.inl hclass.2⟩
    · rcases hcCat with hcS | hcL | hcH
      · have hsum' : a + c + b = rho + carry * M r h t := by omega
        exact False.elim
          (small_small_low_tail_hit_false
            (r := r) (h := h) (t := t) (rho := rho) (carry := carry)
            (a := a) (b := c) (c := b) hp
            ⟨hA.1, hA.2.2.1, hA.2.1, by
              intro v hv
              have hnd := hA.2.2.2 v hv
              constructor
              · exact hnd.2.1
              · constructor
                · exact hnd.1
                · intro hcv hbv
                  exact hnd.2.2 hbv hcv⟩
            haS hcS hbL hrho hsum')
      · exact False.elim
          (small_low_low_tail_hit_false
            (r := r) (h := h) (t := t) (rho := rho) (carry := carry)
            (a := a) (b := b) (c := c) hp haS hbL hcL hrho hsum)
      · exact False.elim
          (small_low_high_tail_hit_false
            (r := r) (h := h) (t := t) (rho := rho) (carry := carry)
            (a := a) (b := b) (c := c) hp haS hbL hcH hrho hsum)
    · rcases hcCat with hcS | hcL | hcH
      · have hsum' : a + c + b = rho + carry * M r h t := by omega
        have hA' : AdmissibleResidueTriple r h t a c b := by
          refine ⟨hA.1, hA.2.2.1, hA.2.1, ?_⟩
          intro v hv
          have hnd := hA.2.2.2 v hv
          constructor
          · exact hnd.2.1
          · constructor
            · exact hnd.1
            · intro hcv hbv
              exact hnd.2.2 hbv hcv
        have hclass := small_small_high_tail_hit_classification
          (r := r) (h := h) (t := t) (rho := rho) (carry := carry)
          (a := a) (b := c) (c := b) hp hA' haS hcS hbH hrho hsum'
        exact ⟨hclass.1, Or.inr (Or.inl hclass.2)⟩
      · exact False.elim
          (small_low_high_tail_hit_false
            (r := r) (h := h) (t := t) (rho := rho) (carry := carry)
            (a := a) (b := c) (c := b) hp haS hcL hbH hrho (by omega))
      · exact False.elim
          (small_high_high_tail_hit_false
            (r := r) (h := h) (t := t) (rho := rho) (carry := carry)
            (a := a) (b := b) (c := c) hp hA haS hbH hcH hrho hsum)
  · rcases hbCat with hbS | hbL | hbH
    · rcases hcCat with hcS | hcL | hcH
      · have hsum' : b + c + a = rho + carry * M r h t := by omega
        have hA' : AdmissibleResidueTriple r h t b c a := by
          refine ⟨hA.2.1, hA.2.2.1, hA.1, ?_⟩
          intro v hv
          have hnd := hA.2.2.2 v hv
          constructor
          · exact hnd.2.2
          · constructor
            · intro hbv hav
              exact hnd.1 hav hbv
            · intro hcv hav
              exact hnd.2.1 hav hcv
        exact False.elim
          (small_small_low_tail_hit_false
            (r := r) (h := h) (t := t) (rho := rho) (carry := carry)
            (a := b) (b := c) (c := a) hp hA' hbS hcS haL hrho hsum')
      · exact False.elim
          (small_low_low_tail_hit_false
            (r := r) (h := h) (t := t) (rho := rho) (carry := carry)
            (a := b) (b := a) (c := c) hp hbS haL hcL hrho (by omega))
      · exact False.elim
          (small_low_high_tail_hit_false
            (r := r) (h := h) (t := t) (rho := rho) (carry := carry)
            (a := b) (b := a) (c := c) hp hbS haL hcH hrho (by omega))
    · rcases hcCat with hcS | hcL | hcH
      · exact False.elim
          (small_low_low_tail_hit_false
            (r := r) (h := h) (t := t) (rho := rho) (carry := carry)
            (a := c) (b := a) (c := b) hp hcS haL hbL hrho (by omega))
      · exact False.elim
          (low_low_low_tail_hit_false
            (r := r) (h := h) (t := t) (rho := rho) (carry := carry)
            (a := a) (b := b) (c := c) hp hA haL hbL hcL hrho hsum)
      · exact False.elim
          (low_low_high_tail_hit_false
            (r := r) (h := h) (t := t) (rho := rho) (carry := carry)
            (a := a) (b := b) (c := c) hp hA haL hbL hcH hrho hsum)
    · rcases hcCat with hcS | hcL | hcH
      · exact False.elim
          (small_low_high_tail_hit_false
            (r := r) (h := h) (t := t) (rho := rho) (carry := carry)
            (a := c) (b := a) (c := b) hp hcS haL hbH hrho (by omega))
      · exact False.elim
          (low_low_high_tail_hit_false
            (r := r) (h := h) (t := t) (rho := rho) (carry := carry)
            (a := a) (b := c) (c := b) hp
            ⟨hA.1, hA.2.2.1, hA.2.1, by
              intro v hv
              have hnd := hA.2.2.2 v hv
              constructor
              · exact hnd.2.1
              · constructor
                · exact hnd.1
                · intro hcv hbv
                  exact hnd.2.2 hbv hcv⟩
            haL hcL hbH hrho (by omega))
      · exact False.elim
          (low_high_high_tail_hit_false
            (r := r) (h := h) (t := t) (rho := rho) (carry := carry)
            (a := a) (b := b) (c := c) hp haL hbH hcH hrho hsum)
  · rcases hbCat with hbS | hbL | hbH
    · rcases hcCat with hcS | hcL | hcH
      · have hsum' : b + c + a = rho + carry * M r h t := by omega
        have hA' : AdmissibleResidueTriple r h t b c a := by
          refine ⟨hA.2.1, hA.2.2.1, hA.1, ?_⟩
          intro v hv
          have hnd := hA.2.2.2 v hv
          constructor
          · exact hnd.2.2
          · constructor
            · intro hbv hav
              exact hnd.1 hav hbv
            · intro hcv hav
              exact hnd.2.1 hav hcv
        have hclass := small_small_high_tail_hit_classification
          (r := r) (h := h) (t := t) (rho := rho) (carry := carry)
          (a := b) (b := c) (c := a) hp hA' hbS hcS haH hrho hsum'
        exact ⟨hclass.1, Or.inr (Or.inr hclass.2)⟩
      · exact False.elim
          (small_low_high_tail_hit_false
            (r := r) (h := h) (t := t) (rho := rho) (carry := carry)
            (a := b) (b := c) (c := a) hp hbS hcL haH hrho (by omega))
      · exact False.elim
          (small_high_high_tail_hit_false
            (r := r) (h := h) (t := t) (rho := rho) (carry := carry)
            (a := b) (b := a) (c := c) hp
            ⟨hA.2.1, hA.1, hA.2.2.1, by
              intro v hv
              have hnd := hA.2.2.2 v hv
              constructor
              · intro hbv hav
                exact hnd.1 hav hbv
              · constructor
                · exact hnd.2.2
                · exact hnd.2.1⟩
            hbS haH hcH hrho (by omega))
    · rcases hcCat with hcS | hcL | hcH
      · exact False.elim
          (small_low_high_tail_hit_false
            (r := r) (h := h) (t := t) (rho := rho) (carry := carry)
            (a := c) (b := b) (c := a) hp hcS hbL haH hrho (by omega))
      · exact False.elim
          (low_low_high_tail_hit_false
            (r := r) (h := h) (t := t) (rho := rho) (carry := carry)
            (a := b) (b := c) (c := a) hp
            ⟨hA.2.1, hA.2.2.1, hA.1, by
              intro v hv
              have hnd := hA.2.2.2 v hv
              constructor
              · exact hnd.2.2
              · constructor
                · intro hbv hav
                  exact hnd.1 hav hbv
                · intro hcv hav
                  exact hnd.2.1 hav hcv⟩
            hbL hcL haH hrho (by omega))
      · exact False.elim
          (low_high_high_tail_hit_false
            (r := r) (h := h) (t := t) (rho := rho) (carry := carry)
            (a := b) (b := a) (c := c) hp hbL haH hcH hrho (by omega))
    · rcases hcCat with hcS | hcL | hcH
      · exact False.elim
          (small_high_high_tail_hit_false
            (r := r) (h := h) (t := t) (rho := rho) (carry := carry)
            (a := c) (b := a) (c := b) hp
            ⟨hA.2.2.1, hA.1, hA.2.1, by
              intro v hv
              have hnd := hA.2.2.2 v hv
              constructor
              · intro hcv hav
                exact hnd.2.1 hav hcv
              · constructor
                · intro hcv hbv
                  exact hnd.2.2 hbv hcv
                · exact hnd.1⟩
            hcS haH hbH hrho (by omega))
      · exact False.elim
          (low_high_high_tail_hit_false
            (r := r) (h := h) (t := t) (rho := rho) (carry := carry)
            (a := c) (b := a) (c := b) hp hcL haH hbH hrho (by omega))
      · exact False.elim
          (high_high_high_tail_hit_false
            (r := r) (h := h) (t := t) (rho := rho) (carry := carry)
            (a := a) (b := b) (c := c) hp haH hbH hcH hrho hsum)

end TransitionDenseCap
end GreedyThreeSumfree
