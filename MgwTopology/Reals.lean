/-
A Mathlib-free construction of the real numbers for the MgwTopology port.

We follow the Cauchy-sequence construction: real numbers are equivalence
classes of Cauchy sequences over `Rat` (Lean core's rationals), where two
sequences are equivalent iff their pointwise difference tends to zero.

The file is organised into six sections (`section`/`end` blocks):

1. `Rat` extras — absolute value, triangle inequality, and small helpers.
2. `IsCauchy`, `MyPrereal := { f // IsCauchy f }`, boundedness lemma.
3. The setoid `R` and the quotient `MyReal`.
4. Field structure (pointwise `+`, `-`, `*`, conditional `⁻¹`).
5. Order on `MyReal`, linear order, Archimedean property.
6. Rational embedding, density, and Cauchy completeness.

Style mirrors `MgwTopology/SetLib.lean`: a single file, only `import
Batteries`, `namespace Mgw.Reals`, terse doc-comments, no Mathlib.
-/
import Batteries

namespace Mgw.Reals

/-! ## Section 1 — Rat extras.

`Rat` ships in Lean core with the full ring API and a linear order, but it
does *not* ship `|·|`. We define `absRat` and prove the four properties we
need: nonnegativity, triangle inequality, sub-symmetry, and the
multiplicative law. We also add a `Rat.archimedean` and a `List`-based
finite-max helper for the bounded-Cauchy lemma. -/

section RatExtras

/-! ### Tiny order helpers for `Rat`.

Lean core gives us `Rat.le_trans`, `Rat.le_of_lt`, etc., but no
`lt_of_lt_of_le`/`lt_of_le_of_lt` specialised to `Rat`. We provide them. -/

/-- Strict-then-weak transitivity for `Rat`. -/
protected theorem Rat.lt_of_lt_of_le {a b c : Rat} (h₁ : a < b) (h₂ : b ≤ c) : a < c := by
  rw [Rat.lt_iff_le_and_ne] at *
  refine ⟨Rat.le_trans h₁.1 h₂, ?_⟩
  intro hac
  rcases h₁ with ⟨h1le, h1ne⟩
  -- a = c, c ≤ b combined gives a = b, contradiction
  apply h1ne
  apply Rat.le_antisymm h1le
  rw [hac]; exact h₂

/-- Weak-then-strict transitivity for `Rat`. -/
protected theorem Rat.lt_of_le_of_lt {a b c : Rat} (h₁ : a ≤ b) (h₂ : b < c) : a < c := by
  rw [Rat.lt_iff_le_and_ne] at *
  refine ⟨Rat.le_trans h₁ h₂.1, ?_⟩
  intro hac
  rcases h₂ with ⟨h2le, h2ne⟩
  apply h2ne
  apply Rat.le_antisymm h2le
  rw [← hac]; exact h₁

/-- Strict transitivity for `Rat`. -/
protected theorem Rat.lt_trans {a b c : Rat} (h₁ : a < b) (h₂ : b < c) : a < c :=
  Rat.lt_of_lt_of_le h₁ (Rat.le_of_lt h₂)

/-- Convert `¬ (a ≤ b)` for `Rat` into `b ≤ a`. -/
protected theorem Rat.le_of_not_le {a b : Rat} (h : ¬ a ≤ b) : b ≤ a :=
  Rat.le_of_lt (Rat.not_le.mp h)

/-- Absolute value on `Rat`. -/
def absRat (x : Rat) : Rat := if 0 ≤ x then x else -x

/-- `absRat` of a nonnegative number is itself. -/
theorem absRat_of_nonneg {x : Rat} (h : 0 ≤ x) : absRat x = x := by
  unfold absRat; simp [h]

/-- `absRat` of a non-positive number flips the sign. -/
theorem absRat_of_nonpos {x : Rat} (h : x ≤ 0) : absRat x = -x := by
  unfold absRat
  by_cases hx : 0 ≤ x
  · have hxz : x = 0 := Rat.le_antisymm h hx
    simp [hxz, hx]
  · simp [hx]

/-- The absolute value is always nonnegative. -/
theorem absRat_nonneg (x : Rat) : 0 ≤ absRat x := by
  unfold absRat
  by_cases h : 0 ≤ x
  · simp [h]
  · simp [h]
    have hx : x ≤ 0 := Rat.le_of_lt (Rat.not_le.mp h)
    have : -0 ≤ -x := Rat.neg_le_neg hx
    simpa using this

/-- `absRat 0 = 0`. -/
@[simp] theorem absRat_zero : absRat (0 : Rat) = 0 := by
  unfold absRat; simp

/-- `absRat 1 = 1`. -/
@[simp] theorem absRat_one : absRat (1 : Rat) = 1 := by
  unfold absRat; decide

/-- `absRat (-x) = absRat x`. -/
@[simp] theorem absRat_neg (x : Rat) : absRat (-x) = absRat x := by
  unfold absRat
  by_cases h : 0 ≤ x
  · by_cases h' : 0 ≤ -x
    · have hx : x ≤ 0 := by
        have := Rat.neg_le_neg h'
        simpa using this
      have : x = 0 := Rat.le_antisymm hx h
      simp [this]
    · simp [h, h']
  · have hx : x ≤ 0 := Rat.le_of_lt (Rat.not_le.mp h)
    have h' : 0 ≤ -x := by
      have := Rat.neg_le_neg hx
      simpa using this
    simp [h, h']

/-- `x ≤ absRat x`. -/
theorem le_absRat (x : Rat) : x ≤ absRat x := by
  unfold absRat
  by_cases h : 0 ≤ x
  · simp [h]
  · simp [h]
    have hx : x ≤ 0 := Rat.le_of_lt (Rat.not_le.mp h)
    have h0 : (0 : Rat) ≤ -x := by
      have := Rat.neg_le_neg hx
      simpa using this
    exact Rat.le_trans hx h0

/-- `-x ≤ absRat x`. -/
theorem neg_le_absRat (x : Rat) : -x ≤ absRat x := by
  have := le_absRat (-x)
  rw [absRat_neg] at this
  exact this

/-- `absRat x ≤ y ↔ -y ≤ x ∧ x ≤ y`. -/
theorem absRat_le_iff {x y : Rat} : absRat x ≤ y ↔ -y ≤ x ∧ x ≤ y := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · -- -y ≤ x, since -x ≤ absRat x ≤ y means -y ≤ x
      have h1 : -x ≤ y := Rat.le_trans (neg_le_absRat x) h
      have : -y ≤ -(-x) := Rat.neg_le_neg h1
      simpa using this
    · exact Rat.le_trans (le_absRat x) h
  · rintro ⟨hyx, hxy⟩
    unfold absRat
    by_cases h : 0 ≤ x
    · simp [h]; exact hxy
    · simp [h]
      -- Need -x ≤ y from -y ≤ x
      have : -x ≤ -(-y) := Rat.neg_le_neg hyx
      simpa using this

/-- `absRat x < y ↔ -y < x ∧ x < y`. -/
theorem absRat_lt_iff {x y : Rat} : absRat x < y ↔ -y < x ∧ x < y := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h1 : -x ≤ absRat x := neg_le_absRat x
      have h2 : -x < y := Rat.lt_of_le_of_lt h1 h
      have : -y < -(-x) := Rat.neg_lt_neg h2
      simpa using this
    · have h1 : x ≤ absRat x := le_absRat x
      exact Rat.lt_of_le_of_lt h1 h
  · rintro ⟨hyx, hxy⟩
    unfold absRat
    by_cases h : 0 ≤ x
    · simp [h]; exact hxy
    · simp [h]
      have : -x < -(-y) := Rat.neg_lt_neg hyx
      simpa using this

/-- Triangle inequality for `absRat`. -/
theorem absRat_add_le (a b : Rat) : absRat (a + b) ≤ absRat a + absRat b := by
  rw [absRat_le_iff]
  refine ⟨?_, ?_⟩
  · -- -(absRat a + absRat b) ≤ a + b
    have h1 : -absRat a ≤ a := by
      have := neg_le_absRat a
      have h2 : -absRat a ≤ -(-a) := Rat.neg_le_neg this
      simpa using h2
    have h2 : -absRat b ≤ b := by
      have := neg_le_absRat b
      have h3 : -absRat b ≤ -(-b) := Rat.neg_le_neg this
      simpa using h3
    have h3 : -absRat a + -absRat b ≤ a + -absRat b :=
      Rat.add_le_add_right.mpr h1
    have h4 : a + -absRat b ≤ a + b := Rat.add_le_add_left.mpr h2
    have h5 : -absRat a + -absRat b ≤ a + b := Rat.le_trans h3 h4
    have heq : -(absRat a + absRat b) = -absRat a + -absRat b := Rat.neg_add
    rw [heq]; exact h5
  · -- a + b ≤ absRat a + absRat b
    have h1 : a ≤ absRat a := le_absRat a
    have h2 : b ≤ absRat b := le_absRat b
    have h3 : a + b ≤ absRat a + b := Rat.add_le_add_right.mpr h1
    have h4 : absRat a + b ≤ absRat a + absRat b := Rat.add_le_add_left.mpr h2
    exact Rat.le_trans h3 h4

/-- The "swap" symmetry for `absRat` of a difference. -/
theorem absRat_sub_comm (a b : Rat) : absRat (a - b) = absRat (b - a) := by
  have h : -(a - b) = b - a := by
    rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg, Rat.neg_add, Rat.neg_neg, Rat.add_comm]
  calc absRat (a - b) = absRat (-(a - b)) := (absRat_neg _).symm
    _ = absRat (b - a) := by rw [h]

/-- `absRat` is multiplicative. -/
theorem absRat_mul (a b : Rat) : absRat (a * b) = absRat a * absRat b := by
  unfold absRat
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · have hab : 0 ≤ a * b := Rat.mul_nonneg ha hb
      simp [ha, hb, hab]
    · have hb' : b ≤ 0 := Rat.le_of_lt (Rat.not_le.mp hb)
      have hnb : 0 ≤ -b := by
        have := Rat.neg_le_neg hb'; simpa using this
      have hab : a * b ≤ 0 := by
        have h1 : 0 ≤ a * (-b) := Rat.mul_nonneg ha hnb
        have h2 : a * (-b) = -(a * b) := Rat.mul_neg a b
        rw [h2] at h1
        have := Rat.neg_le_neg h1
        simpa using this
      simp [ha, hb]
      by_cases hab' : 0 ≤ a * b
      · have heq : a * b = 0 := Rat.le_antisymm hab hab'
        simp [heq]
        rcases Rat.mul_eq_zero.mp heq with h0 | h0
        · simp [h0]
        · simp [h0]
      · simp [hab']
        exact (Rat.mul_neg a b).symm
  · have ha' : a ≤ 0 := Rat.le_of_lt (Rat.not_le.mp ha)
    have hna : 0 ≤ -a := by
      have := Rat.neg_le_neg ha'; simpa using this
    by_cases hb : 0 ≤ b
    · have hab : a * b ≤ 0 := by
        have h1 : 0 ≤ (-a) * b := Rat.mul_nonneg hna hb
        have h2 : (-a) * b = -(a * b) := Rat.neg_mul a b
        rw [h2] at h1
        have := Rat.neg_le_neg h1
        simpa using this
      simp [ha, hb]
      by_cases hab' : 0 ≤ a * b
      · have heq : a * b = 0 := Rat.le_antisymm hab hab'
        simp [heq]
        rcases Rat.mul_eq_zero.mp heq with h0 | h0
        · simp [h0]
        · simp [h0]
      · simp [hab']
        exact (Rat.neg_mul a b).symm
    · have hb' : b ≤ 0 := Rat.le_of_lt (Rat.not_le.mp hb)
      have hnb : 0 ≤ -b := by
        have := Rat.neg_le_neg hb'; simpa using this
      have hab : 0 ≤ a * b := by
        have h0 : 0 ≤ (-a) * (-b) := Rat.mul_nonneg hna hnb
        have heq : (-a) * (-b) = a * b := by
          rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]
        rw [heq] at h0; exact h0
      simp [ha, hb, hab]
      rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

/-- `absRat x = 0 ↔ x = 0`. -/
theorem absRat_eq_zero_iff {x : Rat} : absRat x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  unfold absRat at h
  by_cases hx : 0 ≤ x
  · simp [hx] at h; exact h
  · simp [hx] at h
    have : x = -0 := by rw [← h, Rat.neg_neg]
    simpa using this

/-- `absRat x ≠ 0 ↔ x ≠ 0`. -/
theorem absRat_ne_zero_iff {x : Rat} : absRat x ≠ 0 ↔ x ≠ 0 :=
  not_congr absRat_eq_zero_iff

/-- `0 < absRat x ↔ x ≠ 0`. -/
theorem absRat_pos_iff {x : Rat} : 0 < absRat x ↔ x ≠ 0 := by
  refine ⟨fun h hx => ?_, fun h => ?_⟩
  · rw [hx, absRat_zero] at h; exact Rat.lt_irrefl h
  · have h0 : 0 ≤ absRat x := absRat_nonneg x
    rcases Rat.le_iff_lt_or_eq.mp h0 with h1 | h1
    · exact h1
    · exfalso; exact h (absRat_eq_zero_iff.mp h1.symm)

/-- Archimedean property of `Rat`: every rational is below some natural. -/
theorem Rat.archimedean (q : Rat) : ∃ n : Nat, q < (n : Rat) := by
  by_cases hq : 0 ≤ q
  · refine ⟨q.num.toNat + 1, ?_⟩
    have hden : (1 : Int) ≤ (q.den : Int) := by
      have := q.den_pos; omega
    have hnumnn : 0 ≤ q.num := by rwa [Rat.num_nonneg]
    have htoNat : (q.num.toNat : Int) = q.num := Int.toNat_of_nonneg hnumnn
    -- Step 1: q ≤ (q.num.toNat : Rat)
    have hle : q ≤ ((q.num.toNat : Nat) : Rat) := by
      rw [Rat.le_iff]
      have hd : ((q.num.toNat : Nat) : Rat).den = 1 := by simp
      have hn : ((q.num.toNat : Nat) : Rat).num = (q.num.toNat : Int) := by simp
      rw [hd, hn, htoNat]
      -- Goal: q.num * (1 : Nat) ≤ q.num * q.den
      have hmul : q.num * 1 ≤ q.num * (q.den : Int) :=
        Int.mul_le_mul_of_nonneg_left hden hnumnn
      have hcast : ((1 : Nat) : Int) = 1 := by simp
      rw [hcast]
      exact hmul
    -- Step 2: (q.num.toNat : Rat) < (q.num.toNat + 1 : Rat)
    have hlt : ((q.num.toNat : Nat) : Rat) < ((q.num.toNat + 1 : Nat) : Rat) := by
      have hcast : ((q.num.toNat + 1 : Nat) : Rat) = ((q.num.toNat : Nat) : Rat) + 1 := by
        rw [Rat.natCast_add]; rfl
      rw [hcast]
      rw [Rat.lt_iff_sub_pos]
      have heq : (((q.num.toNat : Nat) : Rat) + 1) - ((q.num.toNat : Nat) : Rat) = 1 := by
        rw [Rat.sub_eq_add_neg, Rat.add_comm, ← Rat.add_assoc, Rat.neg_add_cancel, Rat.zero_add]
      rw [heq]
      decide
    exact Rat.lt_of_le_of_lt hle hlt
  · refine ⟨1, ?_⟩
    have hq' : q < 0 := Rat.not_le.mp hq
    have h01 : (0 : Rat) < ((1 : Nat) : Rat) := by decide
    exact Rat.lt_trans hq' h01

/-! ### `List`-based finite max helper. -/

/-- Maximum of a `List Rat`, returning `d` for the empty list. -/
def listMax (d : Rat) : List Rat → Rat
  | [] => d
  | x :: xs => if listMax d xs ≤ x then x else listMax d xs

/-- Every element of a list is `≤` the list's `listMax` (with any default). -/
theorem le_listMax (d : Rat) : ∀ {l : List Rat} {x : Rat}, x ∈ l → x ≤ listMax d l
  | [], _, h => by cases h
  | y :: ys, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hxys
    · -- x = y; goal: x ≤ listMax d (x :: ys)
      show x ≤ if listMax d ys ≤ x then x else listMax d ys
      by_cases h : listMax d ys ≤ x
      · simp [h]
      · simp [h]; exact Rat.le_of_lt (Rat.not_le.mp h)
    · have ih := le_listMax d hxys
      show x ≤ if listMax d ys ≤ y then y else listMax d ys
      by_cases h : listMax d ys ≤ y
      · simp [h]; exact Rat.le_trans ih h
      · simp [h]; exact ih

/-- `listMax d l` is `≥ d`, hence `≥ 0` if `d ≥ 0`. -/
theorem le_listMax_default (d : Rat) : ∀ l : List Rat, d ≤ listMax d l
  | [] => Rat.le_refl
  | x :: xs => by
    show d ≤ if listMax d xs ≤ x then x else listMax d xs
    by_cases h : listMax d xs ≤ x
    · simp [h]; exact Rat.le_trans (le_listMax_default d xs) h
    · simp [h]; exact le_listMax_default d xs

end RatExtras

end Mgw.Reals
