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
  grind

/-- Weak-then-strict transitivity for `Rat`. -/
protected theorem Rat.lt_of_le_of_lt {a b c : Rat} (h₁ : a ≤ b) (h₂ : b < c) : a < c := by
  grind

/-- Strict transitivity for `Rat`. -/
protected theorem Rat.lt_trans {a b c : Rat} (h₁ : a < b) (h₂ : b < c) : a < c := by grind

/-- Convert `¬ (a ≤ b)` for `Rat` into `b ≤ a`. -/
protected theorem Rat.le_of_not_le {a b : Rat} (h : ¬ a ≤ b) : b ≤ a := by grind

/-- Absolute value on `Rat`. -/
def absRat (x : Rat) : Rat := if 0 ≤ x then x else -x

/-- `absRat` of a nonnegative number is itself. -/
theorem absRat_of_nonneg {x : Rat} (h : 0 ≤ x) : absRat x = x := by
  unfold absRat; simp [h]

/-- `absRat` of a non-positive number flips the sign. -/
theorem absRat_of_nonpos {x : Rat} (h : x ≤ 0) : absRat x = -x := by
  unfold absRat; by_cases hx : 0 ≤ x <;> grind

/-- The absolute value is always nonnegative. -/
theorem absRat_nonneg (x : Rat) : 0 ≤ absRat x := by
  unfold absRat; by_cases h : 0 ≤ x <;> grind

/-- `absRat 0 = 0`. -/
@[simp] theorem absRat_zero : absRat (0 : Rat) = 0 := by
  unfold absRat; simp

/-- `absRat 1 = 1`. -/
@[simp] theorem absRat_one : absRat (1 : Rat) = 1 := by
  unfold absRat; decide

/-- `absRat (-x) = absRat x`. -/
@[simp] theorem absRat_neg (x : Rat) : absRat (-x) = absRat x := by
  unfold absRat
  by_cases h : 0 ≤ x <;> by_cases h' : 0 ≤ -x <;> grind

/-- `x ≤ absRat x`. -/
theorem le_absRat (x : Rat) : x ≤ absRat x := by
  unfold absRat; by_cases h : 0 ≤ x <;> grind

/-- `-x ≤ absRat x`. -/
theorem neg_le_absRat (x : Rat) : -x ≤ absRat x := by
  have := le_absRat (-x); rw [absRat_neg] at this; exact this

/-- `absRat x ≤ y ↔ -y ≤ x ∧ x ≤ y`. -/
theorem absRat_le_iff {x y : Rat} : absRat x ≤ y ↔ -y ≤ x ∧ x ≤ y := by
  unfold absRat; by_cases h : 0 ≤ x <;> grind

/-- `absRat x < y ↔ -y < x ∧ x < y`. -/
theorem absRat_lt_iff {x y : Rat} : absRat x < y ↔ -y < x ∧ x < y := by
  unfold absRat; by_cases h : 0 ≤ x <;> grind

/-- Triangle inequality for `absRat`. -/
theorem absRat_add_le (a b : Rat) : absRat (a + b) ≤ absRat a + absRat b := by
  have ha := le_absRat a
  have hb := le_absRat b
  have hna := neg_le_absRat a
  have hnb := neg_le_absRat b
  rw [absRat_le_iff]; grind

/-- The "swap" symmetry for `absRat` of a difference. -/
theorem absRat_sub_comm (a b : Rat) : absRat (a - b) = absRat (b - a) := by
  have h : -(a - b) = b - a := by grind
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
  by_cases hx : 0 ≤ x <;> grind

/-- `absRat x ≠ 0 ↔ x ≠ 0`. -/
theorem absRat_ne_zero_iff {x : Rat} : absRat x ≠ 0 ↔ x ≠ 0 :=
  not_congr absRat_eq_zero_iff

/-- `0 < absRat x ↔ x ≠ 0`. -/
theorem absRat_pos_iff {x : Rat} : 0 < absRat x ↔ x ≠ 0 := by
  have h0 := absRat_nonneg x
  have hez := @absRat_eq_zero_iff x
  refine ⟨fun h hx => ?_, fun h => ?_⟩
  · rw [hx, absRat_zero] at h; exact Rat.lt_irrefl h
  · rcases Rat.le_iff_lt_or_eq.mp h0 with h1 | h1
    · exact h1
    · exfalso; exact h (hez.mp h1.symm)

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
      rw [hcast, Rat.lt_iff_sub_pos]
      have heq : (((q.num.toNat : Nat) : Rat) + 1) - ((q.num.toNat : Nat) : Rat) = 1 := by grind
      rw [heq]; decide
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

/-! ## Section 2 — IsCauchy and MyPrereal.

A Cauchy sequence over `Rat` is one whose tail differences become small.
`MyPrereal` packages such a sequence with its proof. Every Cauchy sequence
is bounded (Lemma `MyPrereal.bounded`); we prove this via the `listMax`
helper from §1. -/

section Cauchy

/-- A sequence `x : Nat → Rat` is Cauchy iff for every `ε > 0` there is an
index past which all pairwise differences are bounded by `ε`. -/
def IsCauchy (x : Nat → Rat) : Prop :=
  ∀ ε : Rat, 0 < ε → ∃ N : Nat, ∀ p q : Nat, N ≤ p → N ≤ q → absRat (x p - x q) ≤ ε

/-- The constant sequence is Cauchy. -/
theorem isCauchy_const (c : Rat) : IsCauchy (fun _ => c) := by
  intro ε hε
  refine ⟨0, fun p q _ _ => ?_⟩
  rw [Rat.sub_self, absRat_zero]; grind

/-- A pre-real number: a Cauchy sequence over `Rat`. -/
structure MyPrereal where
  /-- The underlying sequence. -/
  val : Nat → Rat
  /-- The Cauchy property. -/
  isCauchy : IsCauchy val

namespace MyPrereal

/-- Apply the underlying sequence at an index. -/
@[coe] def toFun (x : MyPrereal) : Nat → Rat := x.val

instance : CoeFun MyPrereal (fun _ => Nat → Rat) := ⟨MyPrereal.val⟩

@[simp] theorem coe_mk (f : Nat → Rat) (h : IsCauchy f) :
    ((⟨f, h⟩ : MyPrereal) : Nat → Rat) = f := rfl

/-- Repackage the Cauchy property of a `MyPrereal`. -/
theorem prop (x : MyPrereal) :
    ∀ ε : Rat, 0 < ε → ∃ N : Nat, ∀ p q : Nat, N ≤ p → N ≤ q → absRat (x p - x q) ≤ ε :=
  x.isCauchy

/-- Build the `List Rat` of the first `n+1` absolute values of `x`. -/
private def absList (x : Nat → Rat) : Nat → List Rat
  | 0 => [absRat (x 0)]
  | n+1 => absRat (x (n+1)) :: absList x n

private theorem mem_absList_of_le (x : Nat → Rat) :
    ∀ {n k : Nat}, k ≤ n → absRat (x k) ∈ absList x n
  | 0, k, hk => by
    have hk0 : k = 0 := by omega
    subst hk0; simp [absList]
  | n+1, k, hk => by
    by_cases h : k = n + 1
    · subst h; simp [absList]
    · have hk' : k ≤ n := by omega
      have := mem_absList_of_le x hk'
      simp [absList]; right; exact this

/-- Every Cauchy sequence is bounded (above in `absRat`). -/
theorem isCauchy_bounded {x : Nat → Rat} (hx : IsCauchy x) :
    ∃ B : Rat, 0 < B ∧ ∀ n, absRat (x n) ≤ B := by
  rcases hx 1 (by decide) with ⟨A, hA⟩
  -- Up to index A, we use the listMax over the list of absolute values.
  let M : Rat := listMax 0 (absList x A)
  -- M ≥ 0 because default is 0.
  have hM0 : (0 : Rat) ≤ M := le_listMax_default 0 _
  -- Helper: M < M + 1
  have hMM1 : M < M + 1 := by
    have h01 : (0 : Rat) < 1 := by decide
    have hM1 : M + 0 < M + 1 := Rat.add_lt_add_left.mpr h01
    grind
  have hMM1le : M ≤ M + 1 := Rat.le_of_lt hMM1
  refine ⟨M + 1, ?_, ?_⟩
  · -- 0 < M + 1
    exact Rat.lt_of_le_of_lt hM0 hMM1
  · intro n
    by_cases hnA : n ≤ A
    · -- |x n| ≤ M ≤ M + 1
      have hmem : absRat (x n) ∈ absList x A := mem_absList_of_le x hnA
      have hle : absRat (x n) ≤ M := le_listMax 0 hmem
      exact Rat.le_trans hle hMM1le
    · -- n > A. |x n| ≤ |x A| + |x n - x A| ≤ M + 1
      have hnA' : A < n := Nat.lt_of_not_le hnA
      have hAn : A ≤ n := Nat.le_of_lt hnA'
      have hAA : A ≤ A := Nat.le_refl _
      have hdiff : absRat (x n - x A) ≤ 1 := hA n A hAn hAA
      -- |x n| = |x A + (x n - x A)| ≤ |x A| + |x n - x A|
      have heq : x A + (x n - x A) = x n := by grind
      have htri : absRat (x n) ≤ absRat (x A) + absRat (x n - x A) := by
        have := absRat_add_le (x A) (x n - x A)
        rw [heq] at this; exact this
      have hxA : absRat (x A) ≤ M := by
        have hmem : absRat (x A) ∈ absList x A := mem_absList_of_le x hAA
        exact le_listMax 0 hmem
      -- combine
      have h1 : absRat (x A) + absRat (x n - x A) ≤ M + absRat (x n - x A) :=
        Rat.add_le_add_right.mpr hxA
      have h2 : M + absRat (x n - x A) ≤ M + 1 :=
        Rat.add_le_add_left.mpr hdiff
      exact Rat.le_trans htri (Rat.le_trans h1 h2)

/-- Convenience version on a `MyPrereal`. -/
theorem bounded (x : MyPrereal) : ∃ B : Rat, 0 < B ∧ ∀ n, absRat (x n) ≤ B :=
  isCauchy_bounded x.isCauchy

end MyPrereal

end Cauchy

/-! ## Section 3 — The setoid `R` and the quotient `MyReal`.

Two pre-reals are equivalent iff their pointwise difference tends to zero.
We show this is an equivalence relation, register it as a `Setoid`, and
quotient. -/

section Quotient

namespace MyPrereal

/-- The equivalence relation on `MyPrereal`: pointwise difference tends to
zero. -/
def R (x y : MyPrereal) : Prop :=
  ∀ ε : Rat, 0 < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n → absRat (x n - y n) ≤ ε

/-- Defining lemma for `R`. -/
theorem R_def (x y : MyPrereal) :
    R x y ↔ ∀ ε : Rat, 0 < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n → absRat (x n - y n) ≤ ε :=
  Iff.rfl

/-- `R` is reflexive. -/
theorem R_refl (x : MyPrereal) : R x x := by
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  rw [Rat.sub_self, absRat_zero]; grind

/-- `R` is symmetric. -/
theorem R_symm {x y : MyPrereal} (h : R x y) : R y x := by
  intro ε hε
  rcases h ε hε with ⟨N, HN⟩
  refine ⟨N, fun n hn => ?_⟩
  rw [absRat_sub_comm]; exact HN n hn

/-- Halving a positive rational gives a positive rational. -/
private theorem half_pos {ε : Rat} (hε : 0 < ε) : 0 < ε / 2 := by
  rw [Rat.div_def]
  have h2pos : (0 : Rat) < 2 := by decide
  have h2inv : 0 < (2 : Rat)⁻¹ := Rat.inv_pos.mpr h2pos
  exact Rat.mul_pos hε h2inv

/-- `1 + 1 = 2` over `Rat`. -/
private theorem one_add_one_eq_two : (1 : Rat) + 1 = 2 := by grind

/-- `(2:Rat)⁻¹ + (2:Rat)⁻¹ = 1`. -/
private theorem inv_two_add_inv_two : ((2 : Rat)⁻¹ + (2 : Rat)⁻¹) = 1 := by
  have h2ne : (2 : Rat) ≠ 0 := by decide
  have h2i : (2 : Rat) * (2 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ h2ne
  have h2j : (2 : Rat)⁻¹ * 2 = 1 := Rat.inv_mul_cancel _ h2ne
  grind

private theorem half_add_half (ε : Rat) : ε / 2 + ε / 2 = ε := by
  rw [Rat.div_def, ← Rat.mul_add, inv_two_add_inv_two, Rat.mul_one]

/-- `R` is transitive. -/
theorem R_trans {x y z : MyPrereal} (hxy : R x y) (hyz : R y z) : R x z := by
  intro ε hε
  rcases hxy (ε / 2) (half_pos hε) with ⟨N, HN⟩
  rcases hyz (ε / 2) (half_pos hε) with ⟨M, HM⟩
  refine ⟨max N M, fun n hn => ?_⟩
  have hN : N ≤ n := Nat.le_trans (Nat.le_max_left N M) hn
  have hM' : M ≤ n := Nat.le_trans (Nat.le_max_right N M) hn
  -- |x n - z n| = |(x n - y n) + (y n - z n)| ≤ |x n - y n| + |y n - z n| ≤ ε/2 + ε/2 = ε
  have heq : (x n - y n) + (y n - z n) = x n - z n := by grind
  have htri : absRat (x n - z n) ≤ absRat (x n - y n) + absRat (y n - z n) := by
    have := absRat_add_le (x n - y n) (y n - z n)
    rw [heq] at this; exact this
  have h1 := HN n hN
  have h2 := HM n hM'
  have hsum : ε / 2 + ε / 2 = ε := half_add_half ε
  grind

/-- `R` is an equivalence relation. -/
theorem R_equiv : Equivalence R :=
  ⟨R_refl, R_symm, R_trans⟩

end MyPrereal

/-- The setoid on `MyPrereal`. -/
instance instSetoidMyPrereal : Setoid MyPrereal where
  r := MyPrereal.R
  iseqv := MyPrereal.R_equiv

/-- `(x ≈ y)` unfolds to the `R` predicate. -/
theorem MyPrereal.equiv_def (x y : MyPrereal) :
    x ≈ y ↔ ∀ ε : Rat, 0 < ε → ∃ N : Nat, ∀ n, N ≤ n → absRat (x n - y n) ≤ ε :=
  Iff.rfl

/-- The real numbers, as a quotient of pre-reals by `R`. -/
abbrev MyReal : Type := Quotient instSetoidMyPrereal

namespace MyReal

/-- Send a pre-real to its equivalence class. -/
def mk (x : MyPrereal) : MyReal := Quotient.mk instSetoidMyPrereal x

@[simp] theorem mk_eq (x : MyPrereal) : Quotient.mk instSetoidMyPrereal x = mk x := rfl

theorem mk_eq_iff {x y : MyPrereal} : mk x = mk y ↔ x ≈ y :=
  ⟨Quotient.exact, Quotient.sound⟩

theorem ind {motive : MyReal → Prop} (h : ∀ x : MyPrereal, motive (mk x)) :
    ∀ r : MyReal, motive r := Quotient.ind h

theorem inductionOn {motive : MyReal → Prop} (r : MyReal)
    (h : ∀ x : MyPrereal, motive (mk x)) : motive r := Quotient.inductionOn r h

theorem inductionOn₂ {motive : MyReal → MyReal → Prop} (r s : MyReal)
    (h : ∀ x y : MyPrereal, motive (mk x) (mk y)) : motive r s :=
  Quotient.inductionOn₂ r s h

theorem inductionOn₃ {motive : MyReal → MyReal → MyReal → Prop} (r s t : MyReal)
    (h : ∀ x y z : MyPrereal, motive (mk x) (mk y) (mk z)) : motive r s t :=
  Quotient.inductionOn₃ r s t h

end MyReal

end Quotient

/-! ## Section 4 — Field structure on `MyReal`.

We define addition, negation, subtraction, multiplication, and a partial
inverse on `MyPrereal`, prove each respects `IsCauchy` and the equivalence
`R`, then lift to `MyReal`. The eventual `mul_inv_cancel` requires showing
that a non-zero pre-real is eventually bounded away from zero. -/

section Field

namespace MyPrereal

/-! ### Constants. -/

/-- The zero pre-real (the constantly-zero sequence). -/
def zero : MyPrereal := ⟨fun _ => 0, isCauchy_const 0⟩

/-- The one pre-real (the constantly-one sequence). -/
def one : MyPrereal := ⟨fun _ => 1, isCauchy_const 1⟩

instance : Zero MyPrereal := ⟨zero⟩
instance : One MyPrereal := ⟨one⟩

@[simp] theorem zero_apply (n : Nat) : (0 : MyPrereal) n = 0 := rfl
@[simp] theorem one_apply (n : Nat) : (1 : MyPrereal) n = 1 := rfl

/-! ### Negation. -/

/-- The pointwise negation of a Cauchy sequence is Cauchy. -/
theorem isCauchy_neg {x : Nat → Rat} (hx : IsCauchy x) : IsCauchy (fun n => -(x n)) := by
  intro ε hε
  rcases hx ε hε with ⟨N, HN⟩
  refine ⟨N, fun p q hp hq => ?_⟩
  have heq : -(x p) - -(x q) = -(x p - x q) := by grind
  rw [heq, absRat_neg]
  exact HN p q hp hq

instance : Neg MyPrereal := ⟨fun x => ⟨fun n => -(x n), isCauchy_neg x.isCauchy⟩⟩

@[simp] theorem neg_apply (x : MyPrereal) (n : Nat) : (-x) n = -(x n) := rfl

/-! ### Addition. -/

/-- The pointwise sum of two Cauchy sequences is Cauchy. -/
theorem isCauchy_add {x y : Nat → Rat} (hx : IsCauchy x) (hy : IsCauchy y) :
    IsCauchy (fun n => x n + y n) := by
  intro ε hε
  rcases hx (ε / 2) (half_pos hε) with ⟨N, HN⟩
  rcases hy (ε / 2) (half_pos hε) with ⟨M, HM⟩
  refine ⟨max N M, fun p q hp hq => ?_⟩
  have hN : N ≤ p := Nat.le_trans (Nat.le_max_left _ _) hp
  have hM' : M ≤ p := Nat.le_trans (Nat.le_max_right _ _) hp
  have hN2 : N ≤ q := Nat.le_trans (Nat.le_max_left _ _) hq
  have hM2 : M ≤ q := Nat.le_trans (Nat.le_max_right _ _) hq
  -- (xp + yp) - (xq + yq) = (xp - xq) + (yp - yq)
  have heq : (x p + y p) - (x q + y q) = (x p - x q) + (y p - y q) := by grind
  rw [heq]
  have htri := absRat_add_le (x p - x q) (y p - y q)
  have h1 := HN p q hN hN2
  have h2 := HM p q hM' hM2
  have hsum : ε / 2 + ε / 2 = ε := half_add_half ε
  grind

instance : Add MyPrereal :=
  ⟨fun x y => ⟨fun n => x n + y n, isCauchy_add x.isCauchy y.isCauchy⟩⟩

instance : Sub MyPrereal := ⟨fun x y => x + (-y)⟩

@[simp] theorem add_apply (x y : MyPrereal) (n : Nat) : (x + y) n = x n + y n := rfl
@[simp] theorem sub_apply (x y : MyPrereal) (n : Nat) : (x - y) n = x n - y n := by
  show x n + -(y n) = x n - y n; grind

/-! ### Multiplication. -/

/-- Bound: for any positive `B`, `1/B > 0`. -/
private theorem inv_pos_of_pos {B : Rat} (hB : 0 < B) : 0 < B⁻¹ := Rat.inv_pos.mpr hB

/-- Division by a positive `B` preserves positivity. -/
private theorem div_pos {a B : Rat} (ha : 0 < a) (hB : 0 < B) : 0 < a / B := by
  rw [Rat.div_def]
  exact Rat.mul_pos ha (inv_pos_of_pos hB)

/-- `B * (ε / (2 * B)) = ε / 2` when `B ≠ 0`. -/
private theorem mul_div_two_mul {B ε : Rat} (hB : B ≠ 0) :
    B * (ε / (2 * B)) = ε / 2 := by
  rw [Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
  have hBi : B * B⁻¹ = 1 := Rat.mul_inv_cancel _ hB
  grind

/-- Pointwise product of two Cauchy sequences is Cauchy. -/
theorem isCauchy_mul {x y : Nat → Rat} (hx : IsCauchy x) (hy : IsCauchy y) :
    IsCauchy (fun n => x n * y n) := by
  rcases isCauchy_bounded hx with ⟨A, hApos, hA⟩
  rcases isCauchy_bounded hy with ⟨B, hBpos, hB⟩
  intro ε hε
  have h2A : 0 < 2 * A := Rat.mul_pos (by decide) hApos
  have h2B : 0 < 2 * B := Rat.mul_pos (by decide) hBpos
  -- Need |y p - y q| ≤ ε/(2A), |x p - x q| ≤ ε/(2B)
  rcases hy (ε / (2 * A)) (div_pos hε h2A) with ⟨M, HM⟩
  rcases hx (ε / (2 * B)) (div_pos hε h2B) with ⟨N, HN⟩
  refine ⟨max N M, fun p q hp hq => ?_⟩
  have hN : N ≤ p := Nat.le_trans (Nat.le_max_left _ _) hp
  have hM' : M ≤ p := Nat.le_trans (Nat.le_max_right _ _) hp
  have hN2 : N ≤ q := Nat.le_trans (Nat.le_max_left _ _) hq
  have hM2 : M ≤ q := Nat.le_trans (Nat.le_max_right _ _) hq
  -- xp*yp - xq*yq = xp*(yp - yq) + yq*(xp - xq)
  have heq : x p * y p - x q * y q = x p * (y p - y q) + y q * (x p - x q) := by grind
  rw [heq]
  have htri := absRat_add_le (x p * (y p - y q)) (y q * (x p - x q))
  have habs1 : absRat (x p * (y p - y q)) = absRat (x p) * absRat (y p - y q) :=
    absRat_mul _ _
  have habs2 : absRat (y q * (x p - x q)) = absRat (y q) * absRat (x p - x q) :=
    absRat_mul _ _
  rw [habs1, habs2] at htri
  -- bounds: |x p| ≤ A; |y q| ≤ B; |y p - y q| ≤ ε / (2A); |x p - x q| ≤ ε / (2B)
  have hab1 : absRat (x p) * absRat (y p - y q) ≤ A * (ε / (2 * A)) := by
    have hh1 : absRat (x p) * absRat (y p - y q) ≤ A * absRat (y p - y q) := by
      apply Rat.mul_le_mul_of_nonneg_right (hA p)
      exact absRat_nonneg _
    have hh2 : A * absRat (y p - y q) ≤ A * (ε / (2 * A)) := by
      apply Rat.mul_le_mul_of_nonneg_left (HM p q hM' hM2) (Rat.le_of_lt hApos)
    exact Rat.le_trans hh1 hh2
  have hab2 : absRat (y q) * absRat (x p - x q) ≤ B * (ε / (2 * B)) := by
    have hh1 : absRat (y q) * absRat (x p - x q) ≤ B * absRat (x p - x q) := by
      apply Rat.mul_le_mul_of_nonneg_right (hB q)
      exact absRat_nonneg _
    have hh2 : B * absRat (x p - x q) ≤ B * (ε / (2 * B)) := by
      apply Rat.mul_le_mul_of_nonneg_left (HN p q hN hN2) (Rat.le_of_lt hBpos)
    exact Rat.le_trans hh1 hh2
  -- Now A * (ε / (2A)) = ε/2 and B * (ε / (2B)) = ε/2
  have hAne : A ≠ 0 := fun h => by rw [h] at hApos; exact Rat.lt_irrefl hApos
  have hBne : B ≠ 0 := fun h => by rw [h] at hBpos; exact Rat.lt_irrefl hBpos
  have hAeq : A * (ε / (2 * A)) = ε / 2 := mul_div_two_mul hAne
  have hBeq : B * (ε / (2 * B)) = ε / 2 := mul_div_two_mul hBne
  rw [hAeq] at hab1
  rw [hBeq] at hab2
  have hε2 : ε / 2 + ε / 2 = ε := half_add_half ε
  grind

instance : Mul MyPrereal :=
  ⟨fun x y => ⟨fun n => x n * y n, isCauchy_mul x.isCauchy y.isCauchy⟩⟩

@[simp] theorem mul_apply (x y : MyPrereal) (n : Nat) : (x * y) n = x n * y n := rfl

/-! ### `R`-respecting versions of the operations. -/

/-- Negation respects the equivalence. -/
theorem neg_quotient {x x' : MyPrereal} (h : x ≈ x') : (-x) ≈ (-x') := by
  intro ε hε
  rcases h ε hε with ⟨N, HN⟩
  refine ⟨N, fun n hn => ?_⟩
  show absRat (-(x n) - -(x' n)) ≤ ε
  have heq : -(x n) - -(x' n) = -(x n - x' n) := by grind
  rw [heq, absRat_neg]; exact HN n hn

/-- Addition respects the equivalence. -/
theorem add_quotient {x x' y y' : MyPrereal} (h : x ≈ x') (h' : y ≈ y') :
    (x + y) ≈ (x' + y') := by
  intro ε hε
  rcases h (ε / 2) (half_pos hε) with ⟨N, HN⟩
  rcases h' (ε / 2) (half_pos hε) with ⟨M, HM⟩
  refine ⟨max N M, fun n hn => ?_⟩
  have hN : N ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hM' : M ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  show absRat ((x + y) n - (x' + y') n) ≤ ε
  have heq : (x + y) n - (x' + y') n = (x n - x' n) + (y n - y' n) := by
    show (x n + y n) - (x' n + y' n) = (x n - x' n) + (y n - y' n); grind
  rw [heq]
  have htri := absRat_add_le (x n - x' n) (y n - y' n)
  have h1 := HN n hN
  have h2 := HM n hM'
  have hsum := half_add_half ε
  grind

/-- Multiplication respects the equivalence. -/
theorem mul_quotient {x x' y y' : MyPrereal} (h : x ≈ x') (h' : y ≈ y') :
    (x * y) ≈ (x' * y') := by
  intro ε hε
  rcases x.bounded with ⟨A, hApos, hA⟩
  rcases y'.bounded with ⟨B, hBpos, hB⟩
  have h2A : 0 < 2 * A := Rat.mul_pos (by decide) hApos
  have h2B : 0 < 2 * B := Rat.mul_pos (by decide) hBpos
  rcases h' (ε / (2 * A)) (div_pos hε h2A) with ⟨N, HN⟩
  rcases h (ε / (2 * B)) (div_pos hε h2B) with ⟨M, HM⟩
  refine ⟨max N M, fun n hn => ?_⟩
  have hN : N ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hM' : M ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  show absRat ((x * y) n - (x' * y') n) ≤ ε
  -- xn*yn - x'n*y'n = xn*(yn - y'n) + y'n*(xn - x'n)
  have heq : (x * y) n - (x' * y') n = x n * (y n - y' n) + y' n * (x n - x' n) := by
    show x n * y n - x' n * y' n = x n * (y n - y' n) + y' n * (x n - x' n)
    grind
  rw [heq]
  have htri := absRat_add_le (x n * (y n - y' n)) (y' n * (x n - x' n))
  rw [absRat_mul, absRat_mul] at htri
  have hAne : A ≠ 0 := fun h => by rw [h] at hApos; exact Rat.lt_irrefl hApos
  have hBne : B ≠ 0 := fun h => by rw [h] at hBpos; exact Rat.lt_irrefl hBpos
  have hab1 : absRat (x n) * absRat (y n - y' n) ≤ A * (ε / (2 * A)) := by
    have hh1 : absRat (x n) * absRat (y n - y' n) ≤ A * absRat (y n - y' n) := by
      apply Rat.mul_le_mul_of_nonneg_right (hA n)
      exact absRat_nonneg _
    have hh2 : A * absRat (y n - y' n) ≤ A * (ε / (2 * A)) := by
      apply Rat.mul_le_mul_of_nonneg_left (HN n hN) (Rat.le_of_lt hApos)
    exact Rat.le_trans hh1 hh2
  have hab2 : absRat (y' n) * absRat (x n - x' n) ≤ B * (ε / (2 * B)) := by
    have hh1 : absRat (y' n) * absRat (x n - x' n) ≤ B * absRat (x n - x' n) := by
      apply Rat.mul_le_mul_of_nonneg_right (hB n)
      exact absRat_nonneg _
    have hh2 : B * absRat (x n - x' n) ≤ B * (ε / (2 * B)) := by
      apply Rat.mul_le_mul_of_nonneg_left (HM n hM') (Rat.le_of_lt hBpos)
    exact Rat.le_trans hh1 hh2
  rw [mul_div_two_mul hAne] at hab1
  rw [mul_div_two_mul hBne] at hab2
  have hε2 : ε / 2 + ε / 2 = ε := half_add_half ε
  grind

/-! ### Inverse — the eventually-non-zero analysis. -/

/-- For `Rat`: subtracting from both sides of `≤`. -/
private theorem Rat.sub_le_sub_of_le {a b c : Rat} (h : a ≤ b) : a - c ≤ b - c := by
  rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg]; exact Rat.add_le_add_right.mpr h

/-- For `Rat`: `a ≤ b + c → a - c ≤ b`. -/
private theorem Rat.sub_le_of_le_add {a b c : Rat} (h : a ≤ b + c) : a - c ≤ b := by
  have h1 : a - c ≤ b + c - c := Rat.sub_le_sub_of_le h
  have heq : b + c - c = b := by grind
  rw [heq] at h1; exact h1

/-- A non-zero pre-real is eventually bounded away from zero. -/
theorem pos_of_not_equiv_zero {x : MyPrereal} (H : ¬(x ≈ 0)) :
    ∃ δ : Rat, 0 < δ ∧ ∃ N, ∀ n, N ≤ n → δ < absRat (x n) := by
  -- Unfold ¬(x ≈ 0): there exists δ > 0 such that for some N, ∃ n ≥ N with δ < |x n - 0|
  -- We'll use Classical.byContradiction on "∀ ε > 0 ∃ N ∀ n ≥ N, |x n| ≤ ε".
  classical
  -- Step 1: extract δ > 0 with the property that ∀ N, ∃ n ≥ N, δ < |x n|.
  have Hdelta : ∃ δ : Rat, 0 < δ ∧ ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ δ < absRat (x n) := by
    by_contra hcontra
    apply H
    intro ε hε
    -- Suppose ¬∃ δ … then ∀ δ > 0 ∀ N ∃ n …, but actually we want to push neg.
    -- Manually: hcontra : ¬ ∃ δ, ... means: for all δ, ¬ (0 < δ ∧ ∀ N, ∃ ...)
    -- Take δ = ε. Then either ¬ 0 < ε (false) or ¬ ∀ N, ∃ n ≥ N, δ < |x n|, i.e. ∃ N, ∀ n ≥ N, ε ≥ |x n|.
    have hne : ¬ (0 < ε ∧ ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ ε < absRat (x n)) := by
      intro h
      apply hcontra
      exact ⟨ε, h⟩
    have hne' : ¬ ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ ε < absRat (x n) := fun h => hne ⟨hε, h⟩
    -- ∃ N, ¬ ∃ n ≥ N, ε < |x n|
    have hex : ∃ N : Nat, ¬ ∃ n : Nat, N ≤ n ∧ ε < absRat (x n) := by
      by_contra h2
      apply hne'
      intro N
      by_contra h3
      apply h2
      exact ⟨N, h3⟩
    rcases hex with ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    -- ¬ (N ≤ n ∧ ε < |x n|) gives N ≤ n → |x n| ≤ ε
    have : ¬ (N ≤ n ∧ ε < absRat (x n)) := fun h => hN ⟨n, h⟩
    have hnot : ¬ ε < absRat (x n) := fun he => this ⟨hn, he⟩
    have hle : absRat (x n) ≤ ε := Rat.not_lt.mp hnot
    show absRat (x n - (0 : MyPrereal) n) ≤ ε
    have h0 : (0 : MyPrereal) n = 0 := rfl
    rw [h0]
    have heq2 : x n - 0 = x n := by grind
    rw [heq2]; exact hle
  rcases Hdelta with ⟨δ, hδpos, hH⟩
  -- Cauchy: ∃ N₀, ∀ p q ≥ N₀, |x p - x q| ≤ δ/2.
  rcases x.prop (δ / 2) (half_pos hδpos) with ⟨N₀, HN₀⟩
  rcases hH N₀ with ⟨M, HMN, HM⟩
  refine ⟨δ / 2, half_pos hδpos, M, fun n hn => ?_⟩
  have hMn : N₀ ≤ n := Nat.le_trans HMN hn
  have hbnd : absRat (x M - x n) ≤ δ / 2 := HN₀ M n HMN hMn
  have heq : x n + (x M - x n) = x M := by grind
  have htri : absRat (x M) ≤ absRat (x n) + absRat (x M - x n) := by
    have := absRat_add_le (x n) (x M - x n)
    rw [heq] at this; exact this
  -- |x M| ≤ |x n| + |x M - x n| ≤ |x n| + δ/2
  have htri2 : absRat (x M) ≤ absRat (x n) + δ / 2 := by
    have hh : absRat (x n) + absRat (x M - x n) ≤ absRat (x n) + δ / 2 :=
      Rat.add_le_add_left.mpr hbnd
    exact Rat.le_trans htri hh
  -- So |x M| - δ/2 ≤ |x n|, and |x M| > δ, hence |x n| > δ/2.
  have h2 : absRat (x M) - δ / 2 ≤ absRat (x n) := Rat.sub_le_of_le_add htri2
  have hsum := half_add_half δ
  grind

/-- A non-zero pre-real has Cauchy reciprocal. -/
theorem isCauchy_inv {x : MyPrereal} (H : ¬(x ≈ 0)) :
    IsCauchy (fun n => (x n)⁻¹) := by
  intro ε hε
  rcases pos_of_not_equiv_zero H with ⟨A, hApos, N, HN⟩
  have hAA : 0 < A * A := Rat.mul_pos hApos hApos
  rcases x.prop (ε * (A * A)) (Rat.mul_pos hε hAA) with ⟨M, hM⟩
  refine ⟨max N M, fun p q hp hq => ?_⟩
  have hNp : N ≤ p := Nat.le_trans (Nat.le_max_left _ _) hp
  have hNq : N ≤ q := Nat.le_trans (Nat.le_max_left _ _) hq
  have hMp : M ≤ p := Nat.le_trans (Nat.le_max_right _ _) hp
  have hMq : M ≤ q := Nat.le_trans (Nat.le_max_right _ _) hq
  -- |x p|, |x q| > A so x p, x q nonzero
  have hxp_pos : 0 < absRat (x p) := Rat.lt_trans hApos (HN p hNp)
  have hxq_pos : 0 < absRat (x q) := Rat.lt_trans hApos (HN q hNq)
  have hxp : x p ≠ 0 := absRat_ne_zero_iff.mp (fun h => by rw [h] at hxp_pos; exact Rat.lt_irrefl hxp_pos)
  have hxq : x q ≠ 0 := absRat_ne_zero_iff.mp (fun h => by rw [h] at hxq_pos; exact Rat.lt_irrefl hxq_pos)
  -- (x p)⁻¹ - (x q)⁻¹ = (x q - x p) * ((x p) * (x q))⁻¹
  have hxpq : x p * x q ≠ 0 := fun h => by
    rcases Rat.mul_eq_zero.mp h with h | h
    · exact hxp h
    · exact hxq h
  have hinv : (x p)⁻¹ - (x q)⁻¹ = (x q - x p) * (x p * x q)⁻¹ := by
    have h1 : (x p)⁻¹ = x q * (x p * x q)⁻¹ := by
      rw [Rat.inv_mul_rev, ← Rat.mul_assoc, Rat.mul_inv_cancel _ hxq, Rat.one_mul]
    have h2 : (x q)⁻¹ = x p * (x p * x q)⁻¹ := by
      rw [Rat.inv_mul_rev, ← Rat.mul_assoc, Rat.mul_comm (x p) (x q)⁻¹,
          Rat.mul_assoc, Rat.mul_inv_cancel _ hxp, Rat.mul_one]
    rw [h1, h2]; grind
  rw [hinv, absRat_mul]
  -- |x q - x p| * |(x p * x q)⁻¹| = |x q - x p| / (|x p| * |x q|)
  -- Need this ≤ ε.
  -- |x q - x p| ≤ ε * A * A (from hM, applied to q p) -- but hM is for q ≥ M, p ≥ M
  have hbnd : absRat (x q - x p) ≤ ε * (A * A) := hM q p hMq hMp
  -- |(x p * x q)⁻¹| = 1 / (|x p| * |x q|), and |x p|, |x q| > A so |x p|*|x q| > A*A
  -- so |(x p * x q)⁻¹| ≤ 1/(A*A)
  have habsinv : absRat (x p * x q)⁻¹ = (absRat (x p * x q))⁻¹ := by
    -- |y⁻¹| = |y|⁻¹ when y ≠ 0
    have hy : (absRat (x p * x q)) ≠ 0 := by
      rw [absRat_mul]
      intro h
      rcases Rat.mul_eq_zero.mp h with h | h
      · exact (absRat_ne_zero_iff.mpr hxp) h
      · exact (absRat_ne_zero_iff.mpr hxq) h
    -- show absRat z⁻¹ = (absRat z)⁻¹ when z ≠ 0
    -- use that z * z⁻¹ = 1 → |z| * |z⁻¹| = 1, so |z⁻¹| = 1/|z|
    have hmul : x p * x q * (x p * x q)⁻¹ = 1 := Rat.mul_inv_cancel _ hxpq
    have habs_one : absRat (x p * x q) * absRat (x p * x q)⁻¹ = 1 := by
      rw [← absRat_mul, hmul, absRat_one]
    -- so absRat (x p * x q)⁻¹ = (absRat (x p * x q))⁻¹
    have hxpqabs := habs_one
    -- (absRat (xp*xq)) * absRat (xp*xq)⁻¹ = 1, multiply both sides by (absRat (xp*xq))⁻¹
    have hh : (absRat (x p * x q))⁻¹ * (absRat (x p * x q) * absRat (x p * x q)⁻¹)
              = (absRat (x p * x q))⁻¹ * 1 := by rw [habs_one]
    rw [Rat.mul_one, ← Rat.mul_assoc, Rat.inv_mul_cancel _ hy, Rat.one_mul] at hh
    exact hh
  rw [habsinv]
  -- Now goal: |x q - x p| * (absRat (x p * x q))⁻¹ ≤ ε
  rw [absRat_mul]
  -- |x p| * |x q| ≥ A * A
  have habs_xpxq : A * A ≤ absRat (x p) * absRat (x q) := by
    have h1 : A * A ≤ A * absRat (x q) := by
      apply Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt (HN q hNq)) (Rat.le_of_lt hApos)
    have h2 : A * absRat (x q) ≤ absRat (x p) * absRat (x q) := by
      apply Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt (HN p hNp))
      exact Rat.le_of_lt hxq_pos
    exact Rat.le_trans h1 h2
  -- (|x p|*|x q|)⁻¹ ≤ (A*A)⁻¹: inversion is monotone-decreasing on positives
  have hAAne : A * A ≠ 0 := fun h => by rw [h] at hAA; exact Rat.lt_irrefl hAA
  have hxpxq_pos : 0 < absRat (x p) * absRat (x q) := Rat.mul_pos hxp_pos hxq_pos
  have hxpxq_ne : absRat (x p) * absRat (x q) ≠ 0 :=
    fun h => by rw [h] at hxpxq_pos; exact Rat.lt_irrefl hxpxq_pos
  have hinv_le : (absRat (x p) * absRat (x q))⁻¹ ≤ (A * A)⁻¹ := by
    -- 1 = (A*A) * (A*A)⁻¹ = |x p|*|x q| * |x p|*|x q|⁻¹
    -- We want X⁻¹ ≤ Y⁻¹ from Y ≤ X. Use: Y * X⁻¹ ≤ X * X⁻¹ = 1, so X⁻¹ ≤ 1/Y = Y⁻¹.
    have h1 : (A * A) * (absRat (x p) * absRat (x q))⁻¹ ≤
              (absRat (x p) * absRat (x q)) * (absRat (x p) * absRat (x q))⁻¹ := by
      apply Rat.mul_le_mul_of_nonneg_right habs_xpxq
      exact Rat.le_of_lt (Rat.inv_pos.mpr hxpxq_pos)
    rw [Rat.mul_inv_cancel _ hxpxq_ne] at h1
    -- h1 : (A * A) * (...)⁻¹ ≤ 1
    -- multiply by (A*A)⁻¹: (...)⁻¹ ≤ (A*A)⁻¹
    have h2 := Rat.mul_le_mul_of_nonneg_left h1 (Rat.le_of_lt (Rat.inv_pos.mpr hAA))
    rw [← Rat.mul_assoc, Rat.inv_mul_cancel _ hAAne, Rat.one_mul, Rat.mul_one] at h2
    exact h2
  -- Combine: |x q - x p| * (|x p|*|x q|)⁻¹ ≤ |x q - x p| * (A*A)⁻¹ ≤ ε * (A*A) * (A*A)⁻¹ = ε
  have h1 : absRat (x q - x p) * (absRat (x p) * absRat (x q))⁻¹
            ≤ absRat (x q - x p) * (A * A)⁻¹ := by
    apply Rat.mul_le_mul_of_nonneg_left hinv_le (absRat_nonneg _)
  have h2 : absRat (x q - x p) * (A * A)⁻¹ ≤ ε * (A * A) * (A * A)⁻¹ := by
    apply Rat.mul_le_mul_of_nonneg_right hbnd
    exact Rat.le_of_lt (Rat.inv_pos.mpr hAA)
  have h3 : ε * (A * A) * (A * A)⁻¹ = ε := by
    rw [Rat.mul_assoc, Rat.mul_inv_cancel _ hAAne, Rat.mul_one]
  grind

/-- The classical inverse: send `0`-equivalent to `0`, otherwise to the
pointwise inverse Cauchy sequence. -/
noncomputable def inv (x : MyPrereal) : MyPrereal := by
  classical
  exact if H : ¬(x ≈ 0) then ⟨fun n => (x n)⁻¹, isCauchy_inv H⟩ else (0 : MyPrereal)

theorem inv_apply_of_nzero {x : MyPrereal} (H : ¬(x ≈ 0)) (n : Nat) :
    (inv x) n = (x n)⁻¹ := by
  unfold inv
  rw [dif_pos H]

theorem inv_of_zero {x : MyPrereal} (H : x ≈ 0) : inv x = 0 := by
  unfold inv
  rw [dif_neg (not_not_intro H)]

/-- The inverse respects `R`. -/
theorem inv_quotient {x x' : MyPrereal} (h : x ≈ x') : inv x ≈ inv x' := by
  classical
  by_cases H : x ≈ 0
  · -- Then x' ≈ 0 too, and both inverses are 0.
    have H' : x' ≈ 0 := MyPrereal.R_trans (MyPrereal.R_symm h) H
    rw [inv_of_zero H, inv_of_zero H']
    exact MyPrereal.R_refl _
  · have H' : ¬(x' ≈ 0) := fun h0 => H (MyPrereal.R_trans h h0)
    intro ε hε
    rcases pos_of_not_equiv_zero H with ⟨A, hApos, N, HN⟩
    rcases pos_of_not_equiv_zero H' with ⟨A', hA'pos, N', HN'⟩
    have hAA' : 0 < A * A' := Rat.mul_pos hApos hA'pos
    have hAA'ne : A * A' ≠ 0 := fun h => by rw [h] at hAA'; exact Rat.lt_irrefl hAA'
    rcases (MyPrereal.R_symm h) (ε * (A * A')) (Rat.mul_pos hε hAA') with ⟨M, hM⟩
    refine ⟨max M (max N N'), fun n hn => ?_⟩
    have hMn : M ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
    have hNN' : max N N' ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
    have hNn : N ≤ n := Nat.le_trans (Nat.le_max_left _ _) hNN'
    have hN'n : N' ≤ n := Nat.le_trans (Nat.le_max_right _ _) hNN'
    -- Now: inv x n = (x n)⁻¹, inv x' n = (x' n)⁻¹
    rw [inv_apply_of_nzero H, inv_apply_of_nzero H']
    -- Same calculation as in isCauchy_inv but with x and x' instead of x at p, q
    have hxn_pos : 0 < absRat (x n) := Rat.lt_trans hApos (HN n hNn)
    have hx'n_pos : 0 < absRat (x' n) := Rat.lt_trans hA'pos (HN' n hN'n)
    have hxn : x n ≠ 0 := absRat_ne_zero_iff.mp (fun h => by rw [h] at hxn_pos; exact Rat.lt_irrefl hxn_pos)
    have hx'n : x' n ≠ 0 := absRat_ne_zero_iff.mp (fun h => by rw [h] at hx'n_pos; exact Rat.lt_irrefl hx'n_pos)
    have hxx'n : x n * x' n ≠ 0 := fun h => by
      rcases Rat.mul_eq_zero.mp h with h | h
      · exact hxn h
      · exact hx'n h
    have hinv : (x n)⁻¹ - (x' n)⁻¹ = (x' n - x n) * (x n * x' n)⁻¹ := by
      have h1 : (x n)⁻¹ = x' n * (x n * x' n)⁻¹ := by
        rw [Rat.inv_mul_rev, ← Rat.mul_assoc, Rat.mul_inv_cancel _ hx'n, Rat.one_mul]
      have h2 : (x' n)⁻¹ = x n * (x n * x' n)⁻¹ := by
        rw [Rat.inv_mul_rev, ← Rat.mul_assoc, Rat.mul_comm (x n) (x' n)⁻¹,
            Rat.mul_assoc, Rat.mul_inv_cancel _ hxn, Rat.mul_one]
      rw [h1, h2]; grind
    rw [hinv, absRat_mul]
    -- |x' n - x n| ≤ ε * (A * A') from hM
    -- hM : ∀ n ≥ M, absRat ((x' - x) n) ≤ ε*(A*A')
    -- but (x' - x) n = x' n - x n
    have hbnd : absRat (x' n - x n) ≤ ε * (A * A') := by
      have := hM n hMn
      show absRat (x' n - x n) ≤ ε * (A * A')
      exact this
    -- Same trick as in isCauchy_inv:
    have habsinv : absRat (x n * x' n)⁻¹ = (absRat (x n * x' n))⁻¹ := by
      have habs_one : absRat (x n * x' n) * absRat (x n * x' n)⁻¹ = 1 := by
        rw [← absRat_mul, Rat.mul_inv_cancel _ hxx'n, absRat_one]
      have hy : (absRat (x n * x' n)) ≠ 0 := by
        rw [absRat_mul]
        intro h
        rcases Rat.mul_eq_zero.mp h with h | h
        · exact (absRat_ne_zero_iff.mpr hxn) h
        · exact (absRat_ne_zero_iff.mpr hx'n) h
      have hh : (absRat (x n * x' n))⁻¹ * (absRat (x n * x' n) * absRat (x n * x' n)⁻¹)
              = (absRat (x n * x' n))⁻¹ * 1 := by rw [habs_one]
      rw [Rat.mul_one, ← Rat.mul_assoc, Rat.inv_mul_cancel _ hy, Rat.one_mul] at hh
      exact hh
    rw [habsinv, absRat_mul]
    -- A * A' ≤ |x n| * |x' n|
    have habs_xx' : A * A' ≤ absRat (x n) * absRat (x' n) := by
      have h1 : A * A' ≤ A * absRat (x' n) :=
        Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt (HN' n hN'n)) (Rat.le_of_lt hApos)
      have h2 : A * absRat (x' n) ≤ absRat (x n) * absRat (x' n) :=
        Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt (HN n hNn))
          (Rat.le_of_lt hx'n_pos)
      exact Rat.le_trans h1 h2
    have hxx'_pos : 0 < absRat (x n) * absRat (x' n) := Rat.mul_pos hxn_pos hx'n_pos
    have hxx'_ne : absRat (x n) * absRat (x' n) ≠ 0 :=
      fun h => by rw [h] at hxx'_pos; exact Rat.lt_irrefl hxx'_pos
    have hinv_le : (absRat (x n) * absRat (x' n))⁻¹ ≤ (A * A')⁻¹ := by
      have h1 : (A * A') * (absRat (x n) * absRat (x' n))⁻¹ ≤
                (absRat (x n) * absRat (x' n)) * (absRat (x n) * absRat (x' n))⁻¹ := by
        apply Rat.mul_le_mul_of_nonneg_right habs_xx'
        exact Rat.le_of_lt (Rat.inv_pos.mpr hxx'_pos)
      rw [Rat.mul_inv_cancel _ hxx'_ne] at h1
      have h2 := Rat.mul_le_mul_of_nonneg_left h1 (Rat.le_of_lt (Rat.inv_pos.mpr hAA'))
      rw [← Rat.mul_assoc, Rat.inv_mul_cancel _ hAA'ne, Rat.one_mul, Rat.mul_one] at h2
      exact h2
    have h1 : absRat (x' n - x n) * (absRat (x n) * absRat (x' n))⁻¹
              ≤ absRat (x' n - x n) * (A * A')⁻¹ :=
      Rat.mul_le_mul_of_nonneg_left hinv_le (absRat_nonneg _)
    have h2 : absRat (x' n - x n) * (A * A')⁻¹ ≤ ε * (A * A') * (A * A')⁻¹ :=
      Rat.mul_le_mul_of_nonneg_right hbnd (Rat.le_of_lt (Rat.inv_pos.mpr hAA'))
    have h3 : ε * (A * A') * (A * A')⁻¹ = ε := by
      rw [Rat.mul_assoc, Rat.mul_inv_cancel _ hAA'ne, Rat.mul_one]
    grind

end MyPrereal

/-! ### Operations on `MyReal` via `Quotient.map`. -/

namespace MyReal

open MyPrereal

/-- Generic quotient `map₁`: lift a unary `MyPrereal → MyPrereal` to `MyReal`. -/
private def map₁ (f : MyPrereal → MyPrereal)
    (h : ∀ {x x' : MyPrereal}, x ≈ x' → f x ≈ f x') : MyReal → MyReal :=
  Quotient.lift (fun x => mk (f x)) (fun _ _ hxy => Quotient.sound (h hxy))

/-- Generic quotient `map₂`: lift a binary operation. -/
private def map₂ (f : MyPrereal → MyPrereal → MyPrereal)
    (h : ∀ {x x' y y' : MyPrereal}, x ≈ x' → y ≈ y' → f x y ≈ f x' y') :
    MyReal → MyReal → MyReal :=
  Quotient.lift (fun x => map₁ (f x) (fun {y y'} hyy => h (MyPrereal.R_refl x) hyy))
    (fun x x' hxx => by
      apply funext
      intro q
      refine Quotient.inductionOn q (fun y => ?_)
      show mk (f x y) = mk (f x' y)
      exact Quotient.sound (h hxx (MyPrereal.R_refl y)))

/-- Negation on `MyReal`. -/
def neg : MyReal → MyReal := map₁ (fun x => -x) (fun h => MyPrereal.neg_quotient h)

instance : Neg MyReal := ⟨neg⟩

theorem neg_def (x : MyPrereal) : -(mk x) = mk (-x) := rfl

/-- Addition on `MyReal`. -/
def add : MyReal → MyReal → MyReal :=
  map₂ (fun x y => x + y) (fun h h' => MyPrereal.add_quotient h h')

instance : Add MyReal := ⟨add⟩

theorem add_def (x y : MyPrereal) : (mk x) + (mk y) = mk (x + y) := rfl

instance : Sub MyReal := ⟨fun x y => x + (-y)⟩

theorem sub_def (x y : MyPrereal) : (mk x) - (mk y) = mk (x - y) := by
  show (mk x) + (-(mk y)) = mk (x - y)
  rw [neg_def, add_def]
  show mk (x + -y) = mk (x - y)
  rfl

/-- Multiplication on `MyReal`. -/
def mul : MyReal → MyReal → MyReal :=
  map₂ (fun x y => x * y) (fun h h' => MyPrereal.mul_quotient h h')

instance : Mul MyReal := ⟨mul⟩

theorem mul_def (x y : MyPrereal) : (mk x) * (mk y) = mk (x * y) := rfl

/-- Inverse on `MyReal`. -/
noncomputable def invFun : MyReal → MyReal :=
  map₁ MyPrereal.inv (fun h => MyPrereal.inv_quotient h)

noncomputable instance : Inv MyReal := ⟨invFun⟩

theorem inv_def (x : MyPrereal) : (mk x)⁻¹ = mk (MyPrereal.inv x) := rfl

instance : Zero MyReal := ⟨mk 0⟩
instance : One MyReal := ⟨mk 1⟩

theorem zero_def : (0 : MyReal) = mk 0 := rfl
theorem one_def : (1 : MyReal) = mk 1 := rfl

/-! ### Ring lemmas, proved as named theorems. -/

/-- Helper: turn a pointwise-equality of pre-reals into an `R`-relation. -/
private theorem R_of_funext {a b : MyPrereal} (h : ∀ n, a n = b n) : a ≈ b := by
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  rw [h n, Rat.sub_self, absRat_zero]; grind

theorem add_comm (x y : MyReal) : x + y = y + x := by
  refine Quotient.inductionOn₂ x y (motive := fun x y => x + y = y + x) (fun a b => ?_)
  show mk a + mk b = mk b + mk a
  rw [add_def, add_def]
  apply Quotient.sound
  apply R_of_funext; intro n
  show a n + b n = b n + a n; grind

theorem add_assoc (x y z : MyReal) : (x + y) + z = x + (y + z) := by
  refine Quotient.inductionOn₃ x y z
    (motive := fun x y z => (x + y) + z = x + (y + z)) (fun a b c => ?_)
  show (mk a + mk b) + mk c = mk a + (mk b + mk c)
  rw [add_def, add_def, add_def, add_def]
  apply Quotient.sound
  apply R_of_funext; intro n
  show (a n + b n) + c n = a n + (b n + c n); grind

theorem add_zero (x : MyReal) : x + 0 = x := by
  refine Quotient.inductionOn x (motive := fun x => x + 0 = x) (fun a => ?_)
  show mk a + mk 0 = mk a
  rw [add_def]
  apply Quotient.sound
  apply R_of_funext; intro n
  show a n + 0 = a n; grind

theorem zero_add (x : MyReal) : 0 + x = x := by
  rw [add_comm]; exact add_zero x

theorem neg_add_cancel (x : MyReal) : -x + x = 0 := by
  refine Quotient.inductionOn x (motive := fun x => -x + x = 0) (fun a => ?_)
  show -(mk a) + mk a = mk 0
  rw [neg_def, add_def]
  apply Quotient.sound
  apply R_of_funext; intro n
  show (-(a n)) + a n = 0; grind

theorem mul_comm (x y : MyReal) : x * y = y * x := by
  refine Quotient.inductionOn₂ x y (motive := fun x y => x * y = y * x) (fun a b => ?_)
  show mk a * mk b = mk b * mk a
  rw [mul_def, mul_def]
  apply Quotient.sound
  apply R_of_funext; intro n
  show a n * b n = b n * a n; grind

theorem mul_assoc (x y z : MyReal) : (x * y) * z = x * (y * z) := by
  refine Quotient.inductionOn₃ x y z
    (motive := fun x y z => (x * y) * z = x * (y * z)) (fun a b c => ?_)
  show (mk a * mk b) * mk c = mk a * (mk b * mk c)
  rw [mul_def, mul_def, mul_def, mul_def]
  apply Quotient.sound
  apply R_of_funext; intro n
  show (a n * b n) * c n = a n * (b n * c n); grind

theorem mul_one (x : MyReal) : x * 1 = x := by
  refine Quotient.inductionOn x (motive := fun x => x * 1 = x) (fun a => ?_)
  show mk a * mk 1 = mk a
  rw [mul_def]
  apply Quotient.sound
  apply R_of_funext; intro n
  show a n * 1 = a n; grind

theorem one_mul (x : MyReal) : 1 * x = x := by
  rw [mul_comm]; exact mul_one x

/-- `a * 0 = 0` over `Rat` (derived from distributivity). -/
private theorem Rat.mul_zero (a : Rat) : a * 0 = 0 := by grind

/-- `0 * a = 0` over `Rat`. -/
private theorem Rat.zero_mul (a : Rat) : 0 * a = 0 := by grind

theorem mul_zero (x : MyReal) : x * 0 = 0 := by
  refine Quotient.inductionOn x (motive := fun x => x * 0 = 0) (fun a => ?_)
  show mk a * mk 0 = mk 0
  rw [mul_def]
  apply Quotient.sound
  apply R_of_funext; intro n
  show a n * 0 = 0; grind

theorem zero_mul (x : MyReal) : 0 * x = 0 := by
  rw [mul_comm]; exact mul_zero x

theorem mul_add (x y z : MyReal) : x * (y + z) = x * y + x * z := by
  refine Quotient.inductionOn₃ x y z
    (motive := fun x y z => x * (y + z) = x * y + x * z) (fun a b c => ?_)
  show mk a * (mk b + mk c) = mk a * mk b + mk a * mk c
  rw [add_def, mul_def, mul_def, mul_def, add_def]
  apply Quotient.sound
  apply R_of_funext; intro n
  show a n * (b n + c n) = a n * b n + a n * c n; grind

theorem add_mul (x y z : MyReal) : (x + y) * z = x * z + y * z := by
  rw [mul_comm, mul_add, mul_comm z x, mul_comm z y]

/-- The reals are non-trivial: `0 ≠ 1`. -/
theorem zero_ne_one : (0 : MyReal) ≠ 1 := by
  intro h
  -- mk 0 = mk 1, i.e. (0 : MyPrereal) ≈ (1 : MyPrereal)
  have h' : (0 : MyPrereal) ≈ (1 : MyPrereal) := Quotient.exact h
  rcases h' (1/2) (by
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.inv_pos.mpr (by decide)) with ⟨N, HN⟩
  have := HN N (Nat.le_refl _)
  show False
  -- |0 - 1| = |-1| = 1, but we have ≤ 1/2
  have heq : (0 : MyPrereal) N - (1 : MyPrereal) N = -1 := by
    show 0 - 1 = -(1 : Rat); grind
  rw [heq, absRat_neg, absRat_one] at this
  -- this : 1 ≤ 1/2
  have hsum : (2 : Rat)⁻¹ + (2 : Rat)⁻¹ = 1 := MyPrereal.inv_two_add_inv_two
  have h2inv : (0 : Rat) < (2 : Rat)⁻¹ := Rat.inv_pos.mpr (by decide)
  grind

/-- `mul_inv_cancel` for non-zero reals. -/
theorem mul_inv_cancel (x : MyReal) (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  revert hx
  refine Quotient.inductionOn x (motive := fun x => x ≠ 0 → x * x⁻¹ = 1) ?_
  intro a ha
  show mk a * (mk a)⁻¹ = mk 1
  -- mk a ≠ 0, so a not equiv 0
  have hne : ¬ (a ≈ (0 : MyPrereal)) := fun h => ha (Quotient.sound h)
  rw [inv_def, mul_def]
  apply Quotient.sound
  rcases pos_of_not_equiv_zero hne with ⟨δ, hδpos, N, HN⟩
  intro ε hε
  refine ⟨N, fun n hn => ?_⟩
  -- a n is nonzero (|a n| > δ > 0)
  have hapos : 0 < absRat (a n) := Rat.lt_trans hδpos (HN n hn)
  have hane : a n ≠ 0 :=
    absRat_ne_zero_iff.mp (fun h => by rw [h] at hapos; exact Rat.lt_irrefl hapos)
  -- (a * inv a) n = a n * (inv a) n = a n * (a n)⁻¹ = 1 = (1 : MyPrereal) n
  have heq : (a * MyPrereal.inv a) n - (1 : MyPrereal) n = 0 := by
    show (a * MyPrereal.inv a) n - 1 = 0
    have h1 : (a * MyPrereal.inv a) n = a n * (a n)⁻¹ := by
      show a n * (MyPrereal.inv a) n = a n * (a n)⁻¹
      rw [inv_apply_of_nzero hne n]
    rw [h1, Rat.mul_inv_cancel _ hane, Rat.sub_self]
  rw [heq, absRat_zero]; exact Rat.le_of_lt hε

end MyReal

end Field

/-! ## Section 5 — Order on `MyReal`.

We define `IsPos` and `IsNonneg` on pre-reals, lift `IsNonneg` to `MyReal`,
derive `≤` and `<`, prove the linear-order properties, and establish the
Archimedean property. -/

section Order

namespace MyPrereal

/-- A pre-real is positive iff it is eventually bounded below by a positive
rational. -/
def IsPos (x : MyPrereal) : Prop :=
  ∃ δ : Rat, 0 < δ ∧ ∃ N : Nat, ∀ n, N ≤ n → δ ≤ x n

/-- A positive pre-real is eventually positive. -/
theorem pos_of_isPos {x : MyPrereal} (hx : IsPos x) :
    ∃ N, ∀ n, N ≤ n → 0 < x n := by
  rcases hx with ⟨δ, hδpos, N, HN⟩
  exact ⟨N, fun n hn => Rat.lt_of_lt_of_le hδpos (HN n hn)⟩

/-- A pre-real equivalent to zero is not positive. -/
theorem not_isPos_of_equiv_zero {x : MyPrereal} (hx : x ≈ 0) : ¬ IsPos x := by
  intro ⟨δ, hδpos, N, HN⟩
  rcases hx (δ / 2) (half_pos hδpos) with ⟨M, HM⟩
  have hmax := Nat.le_max_left N M
  have hmaxM := Nat.le_max_right N M
  have hbnd1 : δ ≤ x (max N M) := HN _ hmax
  have hbnd2 : absRat (x (max N M) - (0 : MyPrereal) (max N M)) ≤ δ / 2 := HM _ hmaxM
  -- x (max N M) - 0 = x (max N M)
  have heq : x (max N M) - (0 : MyPrereal) (max N M) = x (max N M) := by
    show x (max N M) - 0 = x (max N M); grind
  rw [heq] at hbnd2
  -- |x (max N M)| ≤ δ/2 and δ ≤ x (max N M)
  -- So x (max N M) ≤ δ/2 (from absRat ≤ δ/2)
  have hxle : x (max N M) ≤ δ / 2 := by
    have := absRat_le_iff.mp hbnd2
    exact this.2
  -- δ ≤ x (max N M) ≤ δ/2, so δ ≤ δ/2, so δ/2 ≤ 0, so δ ≤ 0, contradiction
  have hδ : δ ≤ δ / 2 := Rat.le_trans hbnd1 hxle
  have hsum := half_add_half δ
  have hpos := half_pos hδpos
  grind

/-- IsPos respects equivalence. -/
theorem isPos_quotient {x x' : MyPrereal} (h : x ≈ x') (hx : IsPos x) : IsPos x' := by
  rcases hx with ⟨δ, hδpos, N, HN⟩
  rcases h (δ / 2) (half_pos hδpos) with ⟨M, HM⟩
  refine ⟨δ / 2, half_pos hδpos, max N M, fun n hn => ?_⟩
  have hN : N ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hM : M ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  -- |x n - x' n| ≤ δ/2 and δ ≤ x n
  have habs := HM n hM
  have hxn := HN n hN
  have habs2 := absRat_le_iff.mp habs
  -- (x n - x' n) ≤ δ/2 and -(δ/2) ≤ (x n - x' n)
  -- so x' n ≥ x n - δ/2 ≥ δ - δ/2 = δ/2
  have h1 : x n - x' n ≤ δ / 2 := habs2.2
  have hsum := half_add_half δ
  grind

/-- A pre-real is non-negative if it is positive or equivalent to zero. -/
def IsNonneg (x : MyPrereal) : Prop := IsPos x ∨ x ≈ 0

theorem IsNonneg_of_equiv_zero {x : MyPrereal} (hx : x ≈ 0) : IsNonneg x := Or.inr hx

/-- A pre-real eventually bounded below by 0 is non-negative. -/
theorem IsNonneg_of_nonneg {x : MyPrereal} (N : Nat) (hx : ∀ n, N ≤ n → 0 ≤ x n) :
    IsNonneg x := by
  classical
  by_cases h : x ≈ 0
  · exact IsNonneg_of_equiv_zero h
  · rcases pos_of_not_equiv_zero h with ⟨δ, hδpos, M, HM⟩
    left
    refine ⟨δ, hδpos, max N M, fun n hn => ?_⟩
    have hN : N ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
    have hM' : M ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
    have hxn0 : 0 ≤ x n := hx n hN
    have hxnabs : absRat (x n) = x n := absRat_of_nonneg hxn0
    have hδlt : δ < x n := by
      have := HM n hM'
      rw [hxnabs] at this; exact this
    exact Rat.le_of_lt hδlt

@[simp] theorem zero_nonneg : IsNonneg 0 := Or.inr (R_refl _)

@[simp] theorem one_pos : IsPos (1 : MyPrereal) := by
  refine ⟨1, by decide, 0, fun _ _ => ?_⟩
  show (1 : Rat) ≤ 1; grind

@[simp] theorem one_nonneg : IsNonneg (1 : MyPrereal) := Or.inl one_pos

/-- IsNonneg respects equivalence. -/
theorem isNonneg_quotient {x x' : MyPrereal} (h : x ≈ x') (hx : IsNonneg x) :
    IsNonneg x' := by
  classical
  by_cases h0 : x ≈ 0
  · exact IsNonneg_of_equiv_zero (R_trans (R_symm h) h0)
  · -- x not equiv 0, so hx must be IsPos
    rcases hx with hpos | hzero
    · -- IsPos x → IsPos x' → IsNonneg x'
      by_cases h0' : x' ≈ 0
      · exact IsNonneg_of_equiv_zero h0'
      · exact Or.inl (isPos_quotient h hpos)
    · exact absurd hzero h0

/-- Sum of two positives is positive. -/
theorem IsPos.add {x y : MyPrereal} (hx : IsPos x) (hy : IsPos y) : IsPos (x + y) := by
  rcases hx with ⟨A, hApos, N, HN⟩
  rcases hy with ⟨B, hBpos, M, HM⟩
  have hAB : 0 < A + B := by grind
  refine ⟨A + B, hAB, max N M, fun n hn => ?_⟩
  have hN : N ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hM : M ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  show A + B ≤ x n + y n
  have h1 := HN n hN
  have h2 := HM n hM
  grind

/-- Product of two positives is positive. -/
theorem IsPos.mul {x y : MyPrereal} (hx : IsPos x) (hy : IsPos y) : IsPos (x * y) := by
  rcases hx with ⟨A, hApos, N, HN⟩
  rcases hy with ⟨B, hBpos, M, HM⟩
  refine ⟨A * B, Rat.mul_pos hApos hBpos, max N M, fun n hn => ?_⟩
  have hN : N ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hM : M ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  show A * B ≤ x n * y n
  have h1 : A * B ≤ A * y n := Rat.mul_le_mul_of_nonneg_left (HM n hM) (Rat.le_of_lt hApos)
  have h2 : A * y n ≤ x n * y n :=
    Rat.mul_le_mul_of_nonneg_right (HN n hN)
      (Rat.le_of_lt (Rat.lt_of_lt_of_le hBpos (HM n hM)))
  grind

/-- Equivalent-to-zero is closed under addition. -/
private theorem add_equiv_zero {x y : MyPrereal} (hx : x ≈ 0) (hy : y ≈ 0) :
    (x + y) ≈ (0 : MyPrereal) := by
  intro ε hε
  rcases hx (ε / 2) (half_pos hε) with ⟨N, HN⟩
  rcases hy (ε / 2) (half_pos hε) with ⟨M, HM⟩
  refine ⟨max N M, fun n hn => ?_⟩
  have hN : N ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hM : M ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  show absRat ((x + y) n - (0 : MyPrereal) n) ≤ ε
  have heq : (x + y) n - (0 : MyPrereal) n = x n + y n := by
    show (x n + y n) - 0 = x n + y n; grind
  rw [heq]
  have hxabs : absRat (x n - (0 : MyPrereal) n) ≤ ε / 2 := HN n hN
  have hyabs : absRat (y n - (0 : MyPrereal) n) ≤ ε / 2 := HM n hM
  have hzn : (0 : MyPrereal) n = (0 : Rat) := rfl
  rw [hzn] at hxabs hyabs
  have hsubx : x n - 0 = x n := by grind
  have hsuby : y n - 0 = y n := by grind
  rw [hsubx] at hxabs
  rw [hsuby] at hyabs
  have htri := absRat_add_le (x n) (y n)
  have hsum := half_add_half ε
  grind

/-- IsPos plus equivalent-to-zero is still IsPos. -/
private theorem isPos_add_equiv_zero {x y : MyPrereal} (hxp : IsPos x) (hy0 : y ≈ 0) :
    IsPos (x + y) := by
  rcases hxp with ⟨δ, hδpos, N, HN⟩
  rcases hy0 (δ / 2) (half_pos hδpos) with ⟨M, HM⟩
  refine ⟨δ / 2, half_pos hδpos, max N M, fun n hn => ?_⟩
  have hN : N ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hM : M ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  show δ / 2 ≤ (x + y) n
  have hxn : δ ≤ x n := HN n hN
  have hyn_abs : absRat (y n - (0 : MyPrereal) n) ≤ δ / 2 := HM n hM
  have hzn : (0 : MyPrereal) n = (0 : Rat) := rfl
  rw [hzn] at hyn_abs
  have hsuby : y n - 0 = y n := by grind
  rw [hsuby] at hyn_abs
  have hyn_lb : -(δ / 2) ≤ y n := (absRat_le_iff.mp hyn_abs).1
  show δ / 2 ≤ x n + y n
  have hsum := half_add_half δ
  grind

/-- Sum of two non-negatives is non-negative. -/
theorem IsNonneg.add {x y : MyPrereal} (hx : IsNonneg x) (hy : IsNonneg y) :
    IsNonneg (x + y) := by
  rcases hx with hxp | hx0
  · rcases hy with hyp | hy0
    · exact Or.inl (IsPos.add hxp hyp)
    · exact Or.inl (isPos_add_equiv_zero hxp hy0)
  · rcases hy with hyp | hy0
    · -- y positive, x ≈ 0; use commutativity
      have hcomm : (x + y) ≈ (y + x) := by
        intro ε hε
        refine ⟨0, fun n _ => ?_⟩
        show absRat ((x + y) n - (y + x) n) ≤ ε
        have : (x + y) n - (y + x) n = 0 := by
          show (x n + y n) - (y n + x n) = 0; grind
        rw [this, absRat_zero]; exact Rat.le_of_lt hε
      have hyx : IsPos (y + x) := isPos_add_equiv_zero hyp hx0
      exact Or.inl (isPos_quotient (R_symm hcomm) hyx)
    · exact Or.inr (add_equiv_zero hx0 hy0)

/-- Helper: if `y ≈ 0` then `x * y ≈ 0` for any `x`. -/
private theorem mul_equiv_zero_right {x y : MyPrereal} (hy : y ≈ 0) :
    (x * y) ≈ (0 : MyPrereal) := by
  rcases x.bounded with ⟨B, hBpos, hB⟩
  intro ε hε
  -- need |y n| ≤ ε/B (or some such)
  have hBne : B ≠ 0 := fun h => by rw [h] at hBpos; exact Rat.lt_irrefl hBpos
  have hε_div_B : 0 < ε / B := div_pos hε hBpos
  rcases hy (ε / B) hε_div_B with ⟨N, HN⟩
  refine ⟨N, fun n hn => ?_⟩
  show absRat ((x * y) n - (0 : MyPrereal) n) ≤ ε
  have h0 : (x * y) n - (0 : MyPrereal) n = x n * y n := by
    show x n * y n - 0 = x n * y n; grind
  rw [h0, absRat_mul]
  have hyn_abs : absRat (y n - (0 : MyPrereal) n) ≤ ε / B := HN n hn
  have heq : y n - (0 : MyPrereal) n = y n := by
    show y n - 0 = y n; grind
  rw [heq] at hyn_abs
  -- |x n| * |y n| ≤ B * (ε/B) = ε
  have h1 : absRat (x n) * absRat (y n) ≤ B * absRat (y n) :=
    Rat.mul_le_mul_of_nonneg_right (hB n) (absRat_nonneg _)
  have h2 : B * absRat (y n) ≤ B * (ε / B) :=
    Rat.mul_le_mul_of_nonneg_left hyn_abs (Rat.le_of_lt hBpos)
  have h3 : B * (ε / B) = ε := by
    have hBi : B * B⁻¹ = 1 := Rat.mul_inv_cancel _ hBne
    rw [Rat.div_def]; grind
  grind

/-- Product of two non-negatives is non-negative. -/
theorem IsNonneg.mul {x y : MyPrereal} (hx : IsNonneg x) (hy : IsNonneg y) :
    IsNonneg (x * y) := by
  rcases hx with hxp | hx0
  · rcases hy with hyp | hy0
    · exact Or.inl (IsPos.mul hxp hyp)
    · exact Or.inr (mul_equiv_zero_right hy0)
  · -- x ≈ 0; use commutativity
    have hcomm : (x * y) ≈ (y * x) := by
      intro ε hε
      refine ⟨0, fun n _ => ?_⟩
      show absRat ((x * y) n - (y * x) n) ≤ ε
      have : (x * y) n - (y * x) n = 0 := by
        show x n * y n - y n * x n = 0; grind
      rw [this, absRat_zero]; exact Rat.le_of_lt hε
    have hyx : (y * x) ≈ (0 : MyPrereal) := mul_equiv_zero_right hx0
    exact Or.inr (R_trans hcomm hyx)

/-- If both `x` and `-x` are non-negative, then `x ≈ 0`. -/
theorem eq_zero_of_isNonneg_of_isNonneg_neg {x : MyPrereal}
    (h : IsNonneg x) (h' : IsNonneg (-x)) : x ≈ 0 := by
  classical
  by_contra H
  -- Then x is positive (not ≈ 0, so the IsPos clause holds)
  have hpos : IsPos x := by
    rcases h with hp | h0
    · exact hp
    · exact absurd h0 H
  -- And -x is also positive (its negation): need to show -x not ≈ 0
  have Hneg : ¬ ((-x) ≈ 0) := fun h0 => by
    -- if -x ≈ 0 then x ≈ -(0) = 0
    apply H
    intro ε hε
    rcases h0 ε hε with ⟨N, HN⟩
    refine ⟨N, fun n hn => ?_⟩
    have := HN n hn
    show absRat (x n - (0 : MyPrereal) n) ≤ ε
    have hh : (-x) n - (0 : MyPrereal) n = -(x n) := by
      show (-(x n)) - 0 = -(x n); grind
    rw [hh] at this
    show absRat (x n - 0) ≤ ε
    have := absRat_neg (x n) ▸ this
    grind
  have hpos' : IsPos (-x) := by
    rcases h' with hp | h0
    · exact hp
    · exact absurd h0 Hneg
  -- IsPos x and IsPos (-x): so eventually x n ≥ A > 0 and -x n ≥ B > 0, contradiction
  rcases hpos with ⟨A, hApos, N, HN⟩
  rcases hpos' with ⟨B, hBpos, N', HN'⟩
  have hbig := Nat.le_max_left N N'
  have hbig' := Nat.le_max_right N N'
  have hxN : A ≤ x (max N N') := HN _ hbig
  have hxN' : B ≤ -(x (max N N')) := by
    have := HN' (max N N') hbig'
    show B ≤ -(x (max N N')); exact this
  -- x (max N N') ≥ A > 0 and -(x (max N N')) ≥ B > 0: contradiction
  grind

/-- A non-non-negative pre-real has non-negative negation. -/
theorem isNonneg_neg_of_not_isNonneg {x : MyPrereal} (hx : ¬ IsNonneg x) :
    IsNonneg (-x) := by
  classical
  -- ¬ IsNonneg x ⇒ ¬ IsPos x ∧ ¬ x ≈ 0
  have hxnp : ¬ IsPos x := fun hp => hx (Or.inl hp)
  have hxn0 : ¬ x ≈ 0 := fun hz => hx (Or.inr hz)
  -- So x is bounded away from 0 (by pos_of_not_equiv_zero) but not bounded below by any δ > 0.
  -- The argument: ¬ IsPos x means ∀ δ > 0, ∀ N, ∃ n ≥ N, x n < δ.
  -- Combined with bounded-away: ∃ δ > 0, ∀ n ≥ N₀, |x n| > δ.
  -- For some n ≥ max N₀ N, both |x n| > δ and x n < δ/2 (say). So x n is large in absolute value but
  -- negative ⇒ -x n > δ/2.
  -- Then we need: eventually -x n ≥ δ/2 (i.e. IsPos (-x)).
  rcases pos_of_not_equiv_zero hxn0 with ⟨δ, hδpos, N₀, HN₀⟩
  rcases x.prop (δ / 2) (half_pos hδpos) with ⟨M, HM⟩
  -- Find one n at which x n < δ (not IsPos x specialised to δ at index max N₀ M)
  -- ¬ IsPos x : ¬ ∃ δ, 0 < δ ∧ ∃ N, ∀ n ≥ N, δ ≤ x n
  -- so for δ : ∃ N, ∀ n ≥ N, δ ≤ x n is false, i.e. ∀ N, ∃ n ≥ N, ¬ δ ≤ x n, i.e. x n < δ.
  have hex : ∀ N : Nat, ∃ n, N ≤ n ∧ x n < δ := by
    intro N
    by_contra h
    apply hxnp
    refine ⟨δ, hδpos, N, fun n hn => ?_⟩
    by_contra hc
    apply h
    refine ⟨n, hn, ?_⟩
    exact Rat.not_le.mp hc
  rcases hex (max N₀ M) with ⟨R, hR_max, hRδ⟩
  have hR_N₀ : N₀ ≤ R := Nat.le_trans (Nat.le_max_left _ _) hR_max
  have hR_M : M ≤ R := Nat.le_trans (Nat.le_max_right _ _) hR_max
  -- |x R| > δ and x R < δ. So x R must be < -δ (since otherwise -δ ≤ x R < δ → |x R| < δ).
  -- Actually from |x R| > δ and x R < δ, need x R < -δ
  have habsR : δ < absRat (x R) := HN₀ R hR_N₀
  have hxR_neg : x R < -δ := by
    -- Suppose ¬ (x R < -δ), i.e. -δ ≤ x R. Then x R ∈ [-δ, δ), so |x R| ≤ δ, contradicting δ < |x R|.
    by_contra hc
    have hge : -δ ≤ x R := Rat.not_lt.mp hc
    have habs_le : absRat (x R) ≤ δ := absRat_le_iff.mpr ⟨hge, Rat.le_of_lt hRδ⟩
    exact Rat.lt_irrefl (Rat.lt_of_lt_of_le habsR habs_le)
  -- Now use Cauchy: for n ≥ M, |x R - x n| ≤ δ/2, so x n < x R + δ/2 < -δ + δ/2 = -δ/2.
  -- Thus -x n > δ/2, so -x is IsPos with witness δ/2 at threshold (max R M).
  left
  refine ⟨δ / 2, half_pos hδpos, max R M, fun n hn => ?_⟩
  have hRn : R ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hMn : M ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hbnd : absRat (x R - x n) ≤ δ / 2 := HM R n hR_M hMn
  have hbnd2 : x R - x n ≤ δ / 2 := (absRat_le_iff.mp hbnd).2
  -- x n ≥ x R - δ/2 (from hbnd2)
  -- But we want -x n ≥ δ/2, i.e., x n ≤ -(δ/2).
  -- We have x R < -δ and -(x R - x n) ≥ -(δ/2), i.e., x n - x R ≥ -(δ/2).
  -- and from absRat_le_iff: -(δ/2) ≤ x R - x n ≤ δ/2.
  -- Goal: δ/2 ≤ -x n, i.e., x n ≤ -(δ/2).
  -- From x R - x n ≤ δ/2: x R ≤ x n + δ/2, i.e., x n ≥ x R - δ/2.
  -- From -(δ/2) ≤ x R - x n: x n - x R ≤ δ/2, i.e., x n ≤ x R + δ/2.
  -- We have x R < -δ, so x R + δ/2 < -δ + δ/2 = -δ/2. So x n < -δ/2. Hence -x n > δ/2.
  have hbnd3 : -(δ / 2) ≤ x R - x n := (absRat_le_iff.mp hbnd).1
  have hsum := half_add_half δ
  show δ / 2 ≤ -(x n); grind

end MyPrereal

/-! ### Lifted order on `MyReal`. -/

namespace MyReal

open MyPrereal

/-- The non-negativity predicate on `MyReal`. -/
def IsNonneg : MyReal → Prop :=
  Quotient.lift MyPrereal.IsNonneg
    (fun _ _ h => propext ⟨isNonneg_quotient h, isNonneg_quotient (R_symm h)⟩)

theorem isNonneg_def {x : MyPrereal} : IsNonneg (mk x) ↔ x.IsNonneg := Iff.rfl

@[simp] theorem zero_nonneg' : IsNonneg 0 := by
  show MyPrereal.IsNonneg 0
  exact MyPrereal.zero_nonneg

theorem eq_zero_of_isNonneg_of_isNonneg_neg {x : MyReal}
    (h : IsNonneg x) (h' : IsNonneg (-x)) : x = 0 := by
  refine Quotient.inductionOn x
    (motive := fun x => IsNonneg x → IsNonneg (-x) → x = 0) ?_ h h'
  intro a ha ha'
  show mk a = mk 0
  apply Quotient.sound
  exact MyPrereal.eq_zero_of_isNonneg_of_isNonneg_neg ha ha'

/-- `IsNonneg.add` lifts to `MyReal`. -/
theorem IsNonneg.add {x y : MyReal} (hx : IsNonneg x) (hy : IsNonneg y) :
    IsNonneg (x + y) := by
  refine Quotient.inductionOn₂ x y
    (motive := fun x y => IsNonneg x → IsNonneg y → IsNonneg (x + y)) ?_ hx hy
  intro a b ha hb
  show MyPrereal.IsNonneg (a + b)
  exact MyPrereal.IsNonneg.add ha hb

/-- `IsNonneg.mul` lifts. -/
theorem IsNonneg.mul {x y : MyReal} (hx : IsNonneg x) (hy : IsNonneg y) :
    IsNonneg (x * y) := by
  refine Quotient.inductionOn₂ x y
    (motive := fun x y => IsNonneg x → IsNonneg y → IsNonneg (x * y)) ?_ hx hy
  intro a b ha hb
  show MyPrereal.IsNonneg (a * b)
  exact MyPrereal.IsNonneg.mul ha hb

/-- Helper: `(a + b) - (a + c) = b - c` over `Rat`. -/
private theorem rat_add_sub_add_left (a b c : Rat) : (a + b) - (a + c) = b - c := by grind

/-- The order on `MyReal`. -/
def le (x y : MyReal) : Prop := IsNonneg (y - x)

instance : LE MyReal := ⟨le⟩
instance : LT MyReal := ⟨fun x y => x ≤ y ∧ x ≠ y⟩

theorem le_def (x y : MyReal) : x ≤ y ↔ IsNonneg (y - x) := Iff.rfl
theorem lt_def (x y : MyReal) : x < y ↔ x ≤ y ∧ x ≠ y := Iff.rfl

/-- Helper for sub. -/
private theorem sub_self_eq_zero (x : MyReal) : x - x = 0 := by
  refine Quotient.inductionOn x (motive := fun x => x - x = 0) (fun a => ?_)
  show mk a - mk a = mk 0
  rw [sub_def]
  apply Quotient.sound
  apply R_of_funext; intro n
  rw [MyPrereal.sub_apply]; show a n - a n = 0; grind

theorem le_refl (x : MyReal) : x ≤ x := by
  rw [le_def, sub_self_eq_zero]; exact zero_nonneg'

theorem zero_le_iff_isNonneg (x : MyReal) : 0 ≤ x ↔ IsNonneg x := by
  rw [le_def]
  -- x - 0 = x
  have : x - 0 = x := by
    show x + -0 = x
    rw [show (-(0 : MyReal)) = (0 : MyReal) by
      show -(mk 0) = mk 0
      rw [neg_def]
      apply Quotient.sound
      apply R_of_funext; intro n
      show -(0 : Rat) = 0
      exact Rat.neg_zero,
      add_zero]
  rw [this]

theorem zero_le_one : (0 : MyReal) ≤ 1 := by
  rw [zero_le_iff_isNonneg]
  show MyPrereal.IsNonneg 1
  exact MyPrereal.one_nonneg

/-- `(x + y) - (x + z) = y - z` over `MyReal`. -/
private theorem add_sub_add_left_eq (x y z : MyReal) : (x + y) - (x + z) = y - z := by
  refine Quotient.inductionOn₃ x y z
    (motive := fun x y z => (x + y) - (x + z) = y - z) (fun a b c => ?_)
  show (mk a + mk b) - (mk a + mk c) = mk b - mk c
  rw [add_def, add_def, sub_def, sub_def]
  apply Quotient.sound
  apply R_of_funext; intro n
  rw [MyPrereal.sub_apply, MyPrereal.add_apply, MyPrereal.add_apply, MyPrereal.sub_apply]
  show (a n + b n) - (a n + c n) = b n - c n; grind

theorem le_trans (x y z : MyReal) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  rw [le_def] at *
  -- (z - x) = (z - y) + (y - x), use IsNonneg.add
  have hsum := IsNonneg.add h2 h1
  have heq : (z - y) + (y - x) = z - x := by
    refine Quotient.inductionOn₃ x y z
      (motive := fun x y z => (z - y) + (y - x) = z - x) (fun a b c => ?_)
    show (mk c - mk b) + (mk b - mk a) = mk c - mk a
    rw [sub_def, sub_def, sub_def, add_def]
    apply Quotient.sound
    apply R_of_funext; intro n
    rw [MyPrereal.add_apply, MyPrereal.sub_apply, MyPrereal.sub_apply, MyPrereal.sub_apply]
    show (c n - b n) + (b n - a n) = c n - a n; grind
  rw [← heq]; exact hsum

theorem le_antisymm (x y : MyReal) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  -- (y - x) ≥ 0 and (x - y) ≥ 0; (x - y) = -(y - x), so y - x = 0, so x = y.
  rw [le_def] at hxy hyx
  -- show y - x = 0 then x = y
  have hneg : x - y = -(y - x) := by
    refine Quotient.inductionOn₂ x y
      (motive := fun x y => x - y = -(y - x)) (fun a b => ?_)
    show mk a - mk b = -(mk b - mk a)
    rw [sub_def, sub_def, neg_def]
    apply Quotient.sound
    apply R_of_funext; intro n
    rw [MyPrereal.sub_apply, MyPrereal.neg_apply, MyPrereal.sub_apply]
    show a n - b n = -(b n - a n); grind
  rw [hneg] at hyx
  have hyx_zero : y - x = 0 := eq_zero_of_isNonneg_of_isNonneg_neg hxy hyx
  -- y - x = 0 → y = x
  have : y - x + x = 0 + x := by rw [hyx_zero]
  rw [zero_add] at this
  have heq : y - x + x = y := by
    refine Quotient.inductionOn₂ x y
      (motive := fun x y => y - x + x = y) (fun a b => ?_)
    show (mk b - mk a) + mk a = mk b
    rw [sub_def, add_def]
    apply Quotient.sound
    apply R_of_funext; intro n
    rw [MyPrereal.add_apply, MyPrereal.sub_apply]
    show (b n - a n) + a n = b n; grind
  rw [heq] at this; exact this.symm

theorem add_le_add_left (x y : MyReal) (h : x ≤ y) (t : MyReal) : t + x ≤ t + y := by
  rw [le_def] at *
  rw [add_sub_add_left_eq]; exact h

theorem mul_nonneg (x y : MyReal) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := by
  rw [zero_le_iff_isNonneg] at *
  exact IsNonneg.mul hx hy

/-- The total-order property. -/
theorem le_total (x y : MyReal) : x ≤ y ∨ y ≤ x := by
  classical
  by_cases h1 : IsNonneg (y - x)
  · exact Or.inl h1
  · -- ¬ IsNonneg (y - x), so IsNonneg (-(y - x)) = IsNonneg (x - y)
    refine Or.inr ?_
    rw [le_def]
    have h2 : IsNonneg (-(y - x)) := by
      refine Quotient.inductionOn (y - x) (motive := fun u => ¬ IsNonneg u → IsNonneg (-u)) ?_ h1
      intro a ha
      show MyPrereal.IsNonneg (-a)
      exact MyPrereal.isNonneg_neg_of_not_isNonneg ha
    -- -(y - x) = x - y
    have heq : -(y - x) = x - y := by
      refine Quotient.inductionOn₂ x y
        (motive := fun x y => -(y - x) = x - y) (fun a b => ?_)
      show -(mk b - mk a) = mk a - mk b
      rw [sub_def, sub_def, neg_def]
      apply Quotient.sound
      apply R_of_funext; intro n
      rw [MyPrereal.sub_apply, MyPrereal.neg_apply, MyPrereal.sub_apply]
      show -(b n - a n) = a n - b n; grind
    rw [heq] at h2; exact h2

theorem mul_pos (x y : MyReal) (hx : 0 < x) (hy : 0 < y) : 0 < x * y := by
  rcases hx with ⟨hxle, hxne⟩
  rcases hy with ⟨hyle, hyne⟩
  refine ⟨?_, ?_⟩
  · exact mul_nonneg _ _ hxle hyle
  · -- 0 ≠ x * y; suppose x * y = 0. Need to derive a contradiction.
    intro h
    -- We don't have a "mul_eq_zero" yet. Use mul_inv_cancel.
    -- If x * y = 0 then 1 = (x * y) * (x * y)⁻¹ = 0 * (x * y)⁻¹ = 0, contradiction.
    -- But that needs x * y ≠ 0. Easier: if x ≠ 0 (i.e., 0 ≠ x), then if x * y = 0, multiply by x⁻¹: y = 0.
    have hxnz : x ≠ 0 := fun h => hxne h.symm
    have hynz : y ≠ 0 := fun h => hyne h.symm
    have : x⁻¹ * (x * y) = x⁻¹ * 0 := by rw [h.symm]
    rw [mul_zero] at this
    rw [← mul_assoc, mul_comm x⁻¹ x, mul_inv_cancel x hxnz, one_mul] at this
    exact hynz this

/-! ### `Nat`-cast and Archimedean property. -/

/-- `Nat`-to-`MyReal` cast via the constant rational sequence. -/
def natCast (n : Nat) : MyReal := mk ⟨fun _ => (n : Rat), isCauchy_const _⟩

instance : NatCast MyReal := ⟨natCast⟩

theorem natCast_def (n : Nat) : ((n : MyReal)) = mk ⟨fun _ => (n : Rat), isCauchy_const _⟩ := rfl

/-- The Archimedean property: every real is bounded above by some natural. -/
theorem archimedean (x : MyReal) : ∃ n : Nat, x < (n : MyReal) := by
  refine Quotient.inductionOn x (motive := fun x => ∃ n : Nat, x < (n : MyReal)) ?_
  intro a
  rcases a.bounded with ⟨B, hBpos, hB⟩
  rcases Rat.archimedean B with ⟨n, hn⟩
  refine ⟨n + 1, ?_⟩
  -- mk a < (n+1 : MyReal), i.e., 0 ≤ (n+1) - a strictly
  show mk a < ((n + 1 : Nat) : MyReal)
  refine ⟨?_, ?_⟩
  · -- mk a ≤ ((n+1 : Nat) : MyReal): show IsNonneg (((n+1) : MyReal) - mk a)
    rw [le_def]
    show IsNonneg (((n + 1 : Nat) : MyReal) - mk a)
    show IsNonneg (mk ⟨fun _ => ((n + 1 : Nat) : Rat), isCauchy_const _⟩ - mk a)
    rw [sub_def]
    show MyPrereal.IsNonneg _
    refine MyPrereal.IsNonneg_of_nonneg 0 (fun m _ => ?_)
    rw [MyPrereal.sub_apply]
    show 0 ≤ ((n + 1 : Nat) : Rat) - a m
    -- a m ≤ |a m| ≤ B < n ≤ n + 1
    have h1 : a m ≤ absRat (a m) := le_absRat _
    have h2 : absRat (a m) ≤ B := hB m
    have h3 : a m ≤ B := Rat.le_trans h1 h2
    have h4 : B < (n : Rat) := hn
    have h5 : a m < (n : Rat) := Rat.lt_of_le_of_lt h3 h4
    have h6 : (n : Rat) ≤ ((n + 1 : Nat) : Rat) := by
      rw [Rat.natCast_add]; show (n : Rat) ≤ (n : Rat) + 1; grind
    have h7 : a m ≤ ((n + 1 : Nat) : Rat) := Rat.le_trans (Rat.le_of_lt h5) h6
    -- 0 ≤ (n+1 : Rat) - a m
    show 0 ≤ ((n + 1 : Nat) : Rat) - a m; grind
  · -- mk a ≠ ((n+1 : Nat) : MyReal)
    -- if mk a = ((n+1) : MyReal) then a ≈ const ↑(n+1), which means eventually |a m - (n+1)| ≤ ε
    -- but |a m| ≤ B < n < n+1, so a m < n+1 - ε for small ε. Take ε = 1.
    intro h
    -- mk a = ((n+1 : Nat) : MyReal) → a ≈ ⟨_, isCauchy_const ↑(n+1)⟩
    have ha_eq : a ≈ ⟨fun _ => ((n + 1 : Nat) : Rat), isCauchy_const _⟩ :=
      Quotient.exact h
    -- For ε = 1/2, get N such that |a m - (n+1)| ≤ 1/2 for m ≥ N
    have h12 : (0 : Rat) < 1 / 2 := by
      rw [Rat.div_def, Rat.one_mul]; exact Rat.inv_pos.mpr (by decide)
    rcases ha_eq (1/2) h12 with ⟨N, HN⟩
    have := HN N (Nat.le_refl _)
    -- this : |a N - (n+1)| ≤ 1/2
    have hrange := absRat_le_iff.mp this
    -- a N ≥ (n+1) - 1/2 = n + 1/2, but |a N| ≤ B < n, contradiction.
    have h1 : ((n + 1 : Nat) : Rat) - 1/2 ≤ a N := by
      have hh := hrange.1; grind
    -- But a N ≤ |a N| ≤ B < n < (n+1) - 1/2 (since 1/2 < 1)
    have h2 : a N ≤ absRat (a N) := le_absRat _
    have h3 : absRat (a N) ≤ B := hB N
    have h4 : a N ≤ B := Rat.le_trans h2 h3
    have h5 : B < (n : Rat) := hn
    have h6 : a N < (n : Rat) := Rat.lt_of_le_of_lt h4 h5
    -- Need (n : Rat) ≤ (n+1 : Rat) - 1/2
    have h7 : (n : Rat) ≤ ((n + 1 : Nat) : Rat) - 1/2 := by
      rw [Rat.natCast_add]
      show (n : Rat) ≤ ((n : Rat) + ((1 : Nat) : Rat)) - 1/2
      have hcast : ((1 : Nat) : Rat) = 1 := by simp
      rw [hcast]; grind
    -- Combine: a N < n ≤ (n+1) - 1/2 ≤ a N, contradiction
    have hlast : a N < a N := Rat.lt_of_lt_of_le (Rat.lt_of_lt_of_le h6 h7) h1
    exact Rat.lt_irrefl hlast

end MyReal

end Order

/-! ## Section 6 — Density and completeness.

The rational embedding `k : Rat → MyReal`, basic homomorphism lemmas,
density of rationals in the reals, the Cauchy property on `MyReal`-valued
sequences, and the completeness theorem. -/

section Completeness

namespace MyReal

open MyPrereal

/-- The embedding of `Rat` into `MyReal` via the constant Cauchy sequence. -/
def k (q : Rat) : MyReal := mk ⟨fun _ => q, isCauchy_const q⟩

@[simp] theorem k_zero : k 0 = 0 := rfl
@[simp] theorem k_one : k 1 = 1 := rfl

theorem k_add (a b : Rat) : k (a + b) = k a + k b := by
  show mk _ = mk _ + mk _
  rw [add_def]
  apply Quotient.sound
  apply R_of_funext
  intro n; rfl

theorem k_neg (a : Rat) : k (-a) = -(k a) := by
  show mk _ = -(mk _)
  rw [neg_def]
  apply Quotient.sound
  apply R_of_funext
  intro n; rfl

theorem k_sub (a b : Rat) : k (a - b) = k a - k b := by
  rw [Rat.sub_eq_add_neg, k_add, k_neg]
  rfl

theorem k_mul (a b : Rat) : k (a * b) = k a * k b := by
  show mk _ = mk _ * mk _
  rw [mul_def]
  apply Quotient.sound
  apply R_of_funext
  intro n; rfl

/-- Cauchy sequence on `MyReal`. -/
def IsCauchyMR (s : Nat → MyReal) : Prop :=
  ∀ ε : MyReal, 0 < ε → ∃ N : Nat, ∀ p q : Nat, N ≤ p → N ≤ q → s p - s q ≤ ε ∧ -(s p - s q) ≤ ε

/-- A sequence converges to a limit. -/
def Converges (s : Nat → MyReal) (L : MyReal) : Prop :=
  ∀ ε : MyReal, 0 < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n → s n - L ≤ ε ∧ -(s n - L) ≤ ε

/-- Stripped density: every real has a rational `ε`-approximation when `ε` is rational
and positive. We give a weaker form that suffices for the completeness proof:
the rational `a N` is "close" to `mk a` in the sense of the prereal Cauchy property. -/
theorem prereal_close (a : MyPrereal) {ε : Rat} (hε : 0 < ε) :
    ∃ N : Nat, ∀ n, N ≤ n → mk a - k (a n) ≤ k ε ∧ -(mk a - k (a n)) ≤ k ε := by
  rcases a.prop ε hε with ⟨N, HN⟩
  refine ⟨N, fun n hn => ?_⟩
  refine ⟨?_, ?_⟩
  · -- mk a - k (a n) ≤ k ε
    show IsNonneg (k ε - (mk a - k (a n)))
    -- k ε - (mk a - k (a n)) = k ε + k (a n) - mk a
    show MyPrereal.IsNonneg _
    -- Reduce via the quotient: equivalence-class of the difference
    refine MyPrereal.IsNonneg_of_nonneg N (fun m hm => ?_)
    show 0 ≤ _
    -- Manually expand: (k ε - (mk a - k (a n))).val m = ε - (a m - a n) = ε - a m + a n
    show 0 ≤ (((⟨_, isCauchy_const ε⟩ : MyPrereal)) - (a - ⟨_, isCauchy_const (a n)⟩)).val m
    rw [MyPrereal.sub_apply, MyPrereal.sub_apply]
    show 0 ≤ ε - (a m - a n)
    -- |a m - a n| ≤ ε for m, n ≥ N (use HN), so a m - a n ≤ ε
    have habs := HN m n hm hn
    have hbnd := absRat_le_iff.mp habs
    have h1 : a m - a n ≤ ε := hbnd.2
    grind
  · -- -(mk a - k (a n)) ≤ k ε
    show IsNonneg (k ε - -(mk a - k (a n)))
    show MyPrereal.IsNonneg _
    refine MyPrereal.IsNonneg_of_nonneg N (fun m hm => ?_)
    show 0 ≤ _
    show 0 ≤ (((⟨_, isCauchy_const ε⟩ : MyPrereal)) - -(a - ⟨_, isCauchy_const (a n)⟩)).val m
    rw [MyPrereal.sub_apply, MyPrereal.neg_apply, MyPrereal.sub_apply]
    show 0 ≤ ε - -(a m - a n)
    -- a m - a n ≥ -ε, so -(a m - a n) ≤ ε
    have habs := HN m n hm hn
    have hbnd := absRat_le_iff.mp habs
    have h1 : -ε ≤ a m - a n := hbnd.1
    grind

/-! ### `MyAbs` — absolute value on `MyReal`.

We define `MyAbs` as the quotient lift of pointwise `absRat`. Going via the
pointwise lift (rather than the equivalent `if 0 ≤ x then x else -x`)
lets every algebraic property of `MyAbs` be derived directly from the
corresponding `absRat` lemma applied at each index, with no `MyReal`-level
case-splitting on the order. -/

/-- Reverse triangle: `|absRat a - absRat b| ≤ absRat (a - b)`. -/
private theorem absRat_sub_absRat_le (a b : Rat) :
    absRat (absRat a - absRat b) ≤ absRat (a - b) := by
  rw [absRat_le_iff]
  have hba := absRat_nonneg b
  have hab := absRat_nonneg a
  have habab := absRat_nonneg (a - b)
  refine ⟨?_, ?_⟩
  · -- Goal: -(absRat (a - b)) ≤ absRat a - absRat b
    -- Use absRat ((b - a) + a) ≤ absRat (b - a) + absRat a, and absRat (b - a) = absRat (a - b).
    have htri := absRat_add_le (b - a) a
    have heq : (b - a) + a = b := by grind
    rw [heq] at htri
    have hsym : absRat (b - a) = absRat (a - b) := absRat_sub_comm _ _
    rw [hsym] at htri
    -- htri : absRat b ≤ absRat (a - b) + absRat a, want: -(absRat (a - b)) ≤ absRat a - absRat b
    grind
  · -- Goal: absRat a - absRat b ≤ absRat (a - b)
    have htri := absRat_add_le b (a - b)
    have heq : b + (a - b) = a := by grind
    rw [heq] at htri
    grind

/-- Pointwise `absRat` of a Cauchy sequence is Cauchy. -/
theorem MyPrereal.isCauchy_abs {x : Nat → Rat} (hx : IsCauchy x) :
    IsCauchy (fun n => absRat (x n)) := by
  intro ε hε
  rcases hx ε hε with ⟨N, HN⟩
  refine ⟨N, fun p q hp hq => ?_⟩
  -- |absRat (x p) - absRat (x q)| ≤ |x p - x q| ≤ ε
  exact Rat.le_trans (absRat_sub_absRat_le (x p) (x q)) (HN p q hp hq)

/-- Pointwise absolute value on `MyPrereal`. -/
def MyPrereal.abs (x : MyPrereal) : MyPrereal :=
  ⟨fun n => absRat (x n), MyPrereal.isCauchy_abs x.isCauchy⟩

@[simp] theorem MyPrereal.abs_apply (x : MyPrereal) (n : Nat) :
    (MyPrereal.abs x) n = absRat (x n) := rfl

/-- `MyPrereal.abs` respects the equivalence relation. -/
theorem MyPrereal.abs_quotient {x x' : MyPrereal} (h : x ≈ x') :
    MyPrereal.abs x ≈ MyPrereal.abs x' := by
  intro ε hε
  rcases h ε hε with ⟨N, HN⟩
  refine ⟨N, fun n hn => ?_⟩
  show absRat ((MyPrereal.abs x) n - (MyPrereal.abs x') n) ≤ ε
  rw [MyPrereal.abs_apply, MyPrereal.abs_apply]
  -- |absRat (x n) - absRat (x' n)| ≤ |x n - x' n| ≤ ε
  exact Rat.le_trans (absRat_sub_absRat_le (x n) (x' n)) (HN n hn)

/-- The absolute value on `MyReal`, defined as the quotient lift of
pointwise `absRat`. We use the pointwise lift rather than
`if 0 ≤ x then x else -x` because every property reduces directly to a
pointwise `absRat` lemma. -/
def MyAbs : MyReal → MyReal :=
  Quotient.lift (fun x => mk (MyPrereal.abs x))
    (fun _ _ h => Quotient.sound (MyPrereal.abs_quotient h))

@[simp] theorem MyAbs_mk (x : MyPrereal) : MyAbs (mk x) = mk (MyPrereal.abs x) := rfl

@[simp] theorem MyAbs_zero : MyAbs 0 = 0 := by
  show mk (MyPrereal.abs 0) = mk 0
  apply Quotient.sound
  apply R_of_funext; intro n
  show absRat ((0 : MyPrereal) n) = (0 : MyPrereal) n
  rw [MyPrereal.zero_apply]; exact absRat_zero

@[simp] theorem MyAbs_neg (x : MyReal) : MyAbs (-x) = MyAbs x := by
  refine Quotient.inductionOn x (motive := fun x => MyAbs (-x) = MyAbs x) (fun a => ?_)
  show MyAbs (mk (-a)) = MyAbs (mk a)
  show mk (MyPrereal.abs (-a)) = mk (MyPrereal.abs a)
  apply Quotient.sound
  apply R_of_funext; intro n
  show absRat ((-a) n) = absRat (a n)
  rw [MyPrereal.neg_apply]; exact absRat_neg _

/-- Absolute value is non-negative. -/
theorem MyAbs_nonneg (x : MyReal) : 0 ≤ MyAbs x := by
  refine Quotient.inductionOn x (motive := fun x => 0 ≤ MyAbs x) (fun a => ?_)
  show 0 ≤ mk (MyPrereal.abs a)
  rw [zero_le_iff_isNonneg]
  show MyPrereal.IsNonneg (MyPrereal.abs a)
  refine MyPrereal.IsNonneg_of_nonneg 0 (fun n _ => ?_)
  rw [MyPrereal.abs_apply]; exact absRat_nonneg _

/-- Absolute-value preservation of the rational embedding. -/
theorem k_abs (a : Rat) : MyAbs (k a) = k (absRat a) := by
  show mk (MyPrereal.abs ⟨_, isCauchy_const a⟩) = mk ⟨_, isCauchy_const (absRat a)⟩
  apply Quotient.sound
  apply R_of_funext; intro n
  rfl

/-- `MyAbs` of a difference is symmetric. -/
theorem MyAbs_sub_comm (a b : MyReal) : MyAbs (a - b) = MyAbs (b - a) := by
  refine Quotient.inductionOn₂ a b
    (motive := fun a b => MyAbs (a - b) = MyAbs (b - a)) (fun x y => ?_)
  show MyAbs (mk x - mk y) = MyAbs (mk y - mk x)
  rw [sub_def, sub_def]
  show mk (MyPrereal.abs (x - y)) = mk (MyPrereal.abs (y - x))
  apply Quotient.sound
  apply R_of_funext; intro n
  rw [MyPrereal.abs_apply, MyPrereal.abs_apply, MyPrereal.sub_apply, MyPrereal.sub_apply]
  exact absRat_sub_comm _ _

/-- Triangle inequality on `MyReal`. -/
theorem MyAbs_add (a b : MyReal) : MyAbs (a + b) ≤ MyAbs a + MyAbs b := by
  refine Quotient.inductionOn₂ a b
    (motive := fun a b => MyAbs (a + b) ≤ MyAbs a + MyAbs b) (fun x y => ?_)
  show MyAbs (mk x + mk y) ≤ MyAbs (mk x) + MyAbs (mk y)
  rw [add_def, MyAbs_mk, MyAbs_mk, MyAbs_mk, add_def, le_def, sub_def]
  show MyPrereal.IsNonneg _
  refine MyPrereal.IsNonneg_of_nonneg 0 (fun n _ => ?_)
  rw [MyPrereal.sub_apply, MyPrereal.add_apply,
      MyPrereal.abs_apply, MyPrereal.abs_apply, MyPrereal.abs_apply, MyPrereal.add_apply]
  -- 0 ≤ (absRat (x n) + absRat (y n)) - absRat (x n + y n)
  have h := absRat_add_le (x n) (y n)
  show 0 ≤ (absRat (x n) + absRat (y n)) - absRat (x n + y n); grind

/-- A `MyPrereal` is non-negative iff for every positive ε it is eventually
above `-ε`. This is the bridge between the order structure (which is
defined via `IsNonneg`) and pointwise estimates. -/
theorem MyPrereal.isNonneg_iff_eventually_neg_eps (x : MyPrereal) :
    MyPrereal.IsNonneg x ↔
      ∀ ε : Rat, 0 < ε → ∃ N : Nat, ∀ n, N ≤ n → -ε ≤ x n := by
  refine ⟨fun h ε hε => ?_, fun h => ?_⟩
  · rcases h with hpos | h0
    · rcases hpos with ⟨δ, _, N, HN⟩
      refine ⟨N, fun n hn => ?_⟩
      have hxn := HN n hn
      -- δ ≤ x n; want -ε ≤ x n. Since 0 < δ ≤ x n and -ε ≤ 0, done.
      have hnonneg : 0 ≤ x n := Rat.le_trans (Rat.le_of_lt ‹0 < δ›) hxn
      have hneg_le : -ε ≤ (0 : Rat) := by
        have := Rat.le_of_lt hε
        grind
      exact Rat.le_trans hneg_le hnonneg
    · rcases h0 ε hε with ⟨N, HN⟩
      refine ⟨N, fun n hn => ?_⟩
      have habs := HN n hn
      -- absRat (x n - 0) ≤ ε, so -ε ≤ x n
      have heq : x n - (0 : MyPrereal) n = x n := by
        show x n - 0 = x n; grind
      rw [heq] at habs
      exact (absRat_le_iff.mp habs).1
  · classical
    by_cases h0 : x ≈ 0
    · exact Or.inr h0
    · -- Use pos_of_not_equiv_zero to find δ > 0 with δ < |x n| eventually.
      -- Combine with hypothesis at ε = δ/2 to conclude δ/2 ≤ x n.
      rcases MyPrereal.pos_of_not_equiv_zero h0 with ⟨δ, hδpos, N₀, HN₀⟩
      rcases h (δ / 2) (MyPrereal.half_pos hδpos) with ⟨N₁, HN₁⟩
      left
      refine ⟨δ / 2, MyPrereal.half_pos hδpos, max N₀ N₁, fun n hn => ?_⟩
      have hN0 : N₀ ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
      have hN1 : N₁ ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
      have habs : δ < absRat (x n) := HN₀ n hN0
      have hneg : -(δ / 2) ≤ x n := HN₁ n hN1
      -- Want: δ/2 ≤ x n. From δ < |x n|: x n > δ or x n < -δ. Hypothesis rules out x n < -δ since
      -- -(δ/2) ≤ x n and -δ < -(δ/2) would mean x n ≥ -(δ/2) > -δ.
      -- So x n > δ, and δ > δ/2.
      have hsum := MyPrereal.half_add_half δ
      -- Now case split on sign of x n
      by_cases hxn_sign : 0 ≤ x n
      · -- x n ≥ 0, |x n| = x n, so δ < x n, so δ/2 ≤ x n
        have : absRat (x n) = x n := absRat_of_nonneg hxn_sign
        rw [this] at habs; grind
      · -- x n < 0, |x n| = -x n, so δ < -x n, so x n < -δ. But -(δ/2) ≤ x n, so -(δ/2) ≤ x n < -δ.
        -- That gives -(δ/2) < -δ, contradicting δ/2 < δ.
        have hxn_neg : x n ≤ 0 := Rat.le_of_lt (Rat.not_le.mp hxn_sign)
        have : absRat (x n) = -(x n) := absRat_of_nonpos hxn_neg
        rw [this] at habs
        -- δ < -x n ↔ x n < -δ
        -- combined with -(δ/2) ≤ x n: -(δ/2) ≤ x n < -δ
        -- so δ < δ/2; contradicts δ/2 + δ/2 = δ and δ/2 > 0
        exfalso
        have hδ2_pos := MyPrereal.half_pos hδpos
        grind

/-- The bridge: the existing `(a ≤ ε ∧ -a ≤ ε)` Cauchy formulation is
equivalent to `MyAbs a ≤ ε`. -/
theorem MyAbs_le_iff (a b : MyReal) : MyAbs a ≤ b ↔ -b ≤ a ∧ a ≤ b := by
  refine Quotient.inductionOn₂ a b
    (motive := fun a b => MyAbs a ≤ b ↔ -b ≤ a ∧ a ≤ b) (fun x y => ?_)
  show MyAbs (mk x) ≤ mk y ↔ -(mk y) ≤ mk x ∧ mk x ≤ mk y
  show mk (MyPrereal.abs x) ≤ mk y ↔ -(mk y) ≤ mk x ∧ mk x ≤ mk y
  rw [neg_def]
  rw [le_def, le_def, le_def]
  -- Goals: IsNonneg (mk y - mk (abs x)) ↔ IsNonneg (mk x - mk (-y)) ∧ IsNonneg (mk y - mk x)
  rw [sub_def, sub_def, sub_def]
  -- IsNonneg (mk (y - abs x)) ↔ IsNonneg (mk (x - (-y))) ∧ IsNonneg (mk (y - x))
  show MyPrereal.IsNonneg _ ↔ MyPrereal.IsNonneg _ ∧ MyPrereal.IsNonneg _
  rw [MyPrereal.isNonneg_iff_eventually_neg_eps,
      MyPrereal.isNonneg_iff_eventually_neg_eps,
      MyPrereal.isNonneg_iff_eventually_neg_eps]
  refine ⟨fun h => ⟨fun ε hε => ?_, fun ε hε => ?_⟩, fun ⟨h1, h2⟩ ε hε => ?_⟩
  · -- (x - (-y)) n ≥ -ε from (y - abs x) n ≥ -ε
    rcases h ε hε with ⟨N, HN⟩
    refine ⟨N, fun n hn => ?_⟩
    have := HN n hn
    -- (y - abs x) n = y n - absRat (x n); want (x - (-y)) n = x n - (-(y n)) = x n + y n ≥ -ε
    -- From y n - absRat (x n) ≥ -ε: y n ≥ absRat (x n) - ε ≥ -x n - ε (using -x n ≤ absRat (x n))
    -- so x n + y n ≥ -ε.
    rw [MyPrereal.sub_apply, MyPrereal.abs_apply] at this
    show -ε ≤ (x - -y) n
    rw [MyPrereal.sub_apply, MyPrereal.neg_apply]
    -- have : -ε ≤ y n - absRat (x n)
    -- want: -ε ≤ x n - -(y n) = x n + y n
    have hax := neg_le_absRat (x n)  -- -(x n) ≤ absRat (x n)
    grind
  · -- (y - x) n ≥ -ε from (y - abs x) n ≥ -ε
    rcases h ε hε with ⟨N, HN⟩
    refine ⟨N, fun n hn => ?_⟩
    have := HN n hn
    rw [MyPrereal.sub_apply, MyPrereal.abs_apply] at this
    show -ε ≤ (y - x) n
    rw [MyPrereal.sub_apply]
    -- have : -ε ≤ y n - absRat (x n)
    -- want: -ε ≤ y n - x n
    -- absRat (x n) ≥ x n
    have hax := le_absRat (x n)
    grind
  · -- (y - abs x) n ≥ -ε from (x - (-y)) n ≥ -ε ∧ (y - x) n ≥ -ε
    -- Use ε for h1 and h2.
    rcases h1 ε hε with ⟨N1, HN1⟩
    rcases h2 ε hε with ⟨N2, HN2⟩
    refine ⟨max N1 N2, fun n hn => ?_⟩
    have hN1 : N1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
    have hN2 : N2 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
    have h1n := HN1 n hN1
    have h2n := HN2 n hN2
    rw [MyPrereal.sub_apply, MyPrereal.neg_apply] at h1n
    rw [MyPrereal.sub_apply] at h2n
    show -ε ≤ (y - MyPrereal.abs x) n
    rw [MyPrereal.sub_apply, MyPrereal.abs_apply]
    -- h1n : -ε ≤ x n - -(y n) = x n + y n
    -- h2n : -ε ≤ y n - x n
    -- want: -ε ≤ y n - absRat (x n)
    -- absRat (x n) = if 0 ≤ x n then x n else -(x n)
    by_cases hx_sign : 0 ≤ x n
    · rw [absRat_of_nonneg hx_sign]
      -- want: -ε ≤ y n - x n; that's h2n.
      grind
    · have hx_le : x n ≤ 0 := Rat.le_of_lt (Rat.not_le.mp hx_sign)
      rw [absRat_of_nonpos hx_le]
      -- want: -ε ≤ y n - (-(x n)) = y n + x n; that's h1n.
      grind

/-- Absolute value is positive iff the argument is non-zero. -/
theorem MyAbs_pos_iff (x : MyReal) : 0 < MyAbs x ↔ x ≠ 0 := by
  refine ⟨fun h hx => ?_, fun hx => ?_⟩
  · rw [hx, MyAbs_zero] at h
    rcases h with ⟨_, hne⟩; exact hne rfl
  · -- 0 ≤ MyAbs x always; need 0 ≠ MyAbs x.
    refine ⟨MyAbs_nonneg x, fun heq => ?_⟩
    -- MyAbs x = 0 → x = 0. Use MyAbs_le_iff with b = 0.
    have hle : MyAbs x ≤ 0 := by rw [← heq]; exact le_refl _
    rw [MyAbs_le_iff] at hle
    -- -0 ≤ x ∧ x ≤ 0; -0 = 0 in MyReal
    have hneg0 : -(0 : MyReal) = 0 := by
      show -(mk 0) = mk 0
      rw [neg_def]; apply Quotient.sound
      apply R_of_funext; intro n
      show -(0 : Rat) = 0; grind
    rw [hneg0] at hle
    -- 0 ≤ x ∧ x ≤ 0 → x = 0
    exact hx (le_antisymm _ _ hle.2 hle.1)

/-- Negation flips inequalities: `-a ≤ b ↔ -b ≤ a`. -/
theorem neg_le_iff_neg_le (a b : MyReal) : -a ≤ b ↔ -b ≤ a := by
  refine Quotient.inductionOn₂ a b
    (motive := fun a b => -a ≤ b ↔ -b ≤ a) (fun x y => ?_)
  show -(mk x) ≤ mk y ↔ -(mk y) ≤ mk x
  rw [neg_def, neg_def, le_def, le_def, sub_def, sub_def]
  show MyPrereal.IsNonneg _ ↔ MyPrereal.IsNonneg _
  rw [MyPrereal.isNonneg_iff_eventually_neg_eps,
      MyPrereal.isNonneg_iff_eventually_neg_eps]
  refine ⟨fun h ε hε => ?_, fun h ε hε => ?_⟩
  · rcases h ε hε with ⟨N, HN⟩
    refine ⟨N, fun n hn => ?_⟩
    have := HN n hn
    rw [MyPrereal.sub_apply, MyPrereal.neg_apply] at this
    rw [MyPrereal.sub_apply, MyPrereal.neg_apply]
    -- this : -ε ≤ y n - -(x n); want: -ε ≤ x n - -(y n)
    grind
  · rcases h ε hε with ⟨N, HN⟩
    refine ⟨N, fun n hn => ?_⟩
    have := HN n hn
    rw [MyPrereal.sub_apply, MyPrereal.neg_apply] at this
    rw [MyPrereal.sub_apply, MyPrereal.neg_apply]
    grind

/-- Bridge: the existing `(a ≤ ε ∧ -a ≤ ε)` formulation in `IsCauchyMR` /
`Converges` is equivalent to `MyAbs a ≤ ε`. -/
theorem bound_iff_MyAbs_le (a ε : MyReal) :
    (a ≤ ε ∧ -a ≤ ε) ↔ MyAbs a ≤ ε := by
  rw [MyAbs_le_iff]
  rw [show (-a ≤ ε ↔ -ε ≤ a) from neg_le_iff_neg_le a ε]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩

/-! ### Approximation via the prereal `n`-th term. -/

/-- Helper: `1/(n+1) > 0` for `n : Nat`. -/
private theorem one_div_succ_pos (n : Nat) : (0 : Rat) < 1 / ((n : Rat) + 1) := by
  rw [Rat.div_def, Rat.one_mul]
  apply Rat.inv_pos.mpr
  have h0 : (0 : Rat) ≤ (n : Rat) := by
    induction n with
    | zero => exact Rat.le_refl
    | succ k ih =>
      have hcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by
        rw [Rat.natCast_add]; rfl
      rw [hcast]; grind
  grind

/-! ### `k`-monotonicity. -/

/-- The rational embedding is order-preserving. -/
theorem k_le_iff {a b : Rat} : k a ≤ k b ↔ a ≤ b := by
  show mk ⟨_, _⟩ ≤ mk ⟨_, _⟩ ↔ a ≤ b
  rw [le_def, sub_def]
  show MyPrereal.IsNonneg _ ↔ a ≤ b
  refine ⟨fun h => ?_, fun h => ?_⟩
  · -- IsNonneg ⟨fun _ => b - a, _⟩ → a ≤ b
    -- Use the eventually-≥-(-ε) characterisation with ε = (b - a) is hard if a > b.
    -- Instead, suppose a > b, derive contradiction.
    by_contra hba
    have hba' : b < a := Rat.not_le.mp hba
    -- Then b - a < 0. Pick ε = (a - b) / 2 > 0.
    have hε_pos : 0 < (a - b) / 2 := by
      have : 0 < a - b := by grind
      exact MyPrereal.half_pos this
    rw [MyPrereal.isNonneg_iff_eventually_neg_eps] at h
    rcases h ((a - b) / 2) hε_pos with ⟨N, HN⟩
    have hN := HN N (Nat.le_refl _)
    rw [MyPrereal.sub_apply] at hN
    -- hN : -((a - b) / 2) ≤ b - a (the constant value at index N)
    show False
    have hsum := MyPrereal.half_add_half (a - b)
    have : 0 < a - b := by grind
    grind
  · rw [MyPrereal.isNonneg_iff_eventually_neg_eps]
    intro ε hε
    refine ⟨0, fun n _ => ?_⟩
    rw [MyPrereal.sub_apply]
    show -ε ≤ b - a
    have : 0 ≤ b - a := by grind
    grind

theorem k_lt_iff {a b : Rat} : k a < k b ↔ a < b := by
  rw [lt_def, k_le_iff]
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun h => ⟨Rat.le_of_lt h, ?_⟩⟩
  · -- a ≤ b ∧ k a ≠ k b → a < b
    have : a ≠ b := fun heq => h2 (by rw [heq])
    grind
  · intro heq
    -- k a = k b → a = b (since k a ≤ k b and k b ≤ k a)
    -- but we already have a < b, so b ≤ a from heq → contradiction.
    have hba : b ≤ a := k_le_iff.mp (by rw [heq]; exact le_refl _)
    have : a < a := Rat.lt_of_lt_of_le h hba
    exact Rat.lt_irrefl this

/-- `0 < k a ↔ 0 < a`. -/
theorem k_pos_iff {a : Rat} : 0 < k a ↔ 0 < a := by
  rw [show (0 : MyReal) = k 0 from rfl, k_lt_iff]

/-- `k` of a natural cast equals the natural cast in `MyReal`. -/
theorem k_natCast (n : Nat) : k (n : Rat) = (n : MyReal) := rfl

/-! ### Real Archimedean-of-inverse.

For every positive real `x` there is a natural `n` with `k (1/(n+1)) ≤ x`.
Proved by combining the Archimedean property of `MyReal` (already in §5)
with `k`-monotonicity. -/

/-- Helper: `k (1/(n+1)) > 0`. -/
theorem k_one_div_succ_pos (n : Nat) : 0 < k (1 / ((n : Rat) + 1)) :=
  k_pos_iff.mpr (one_div_succ_pos n)

/-- Helper: for a positive `Rat` `q`, there is a natural `n` with `1/(n+1) ≤ q`.
This is essentially the contrapositive of the rational Archimedean property
applied to `1/q`. -/
private theorem one_div_succ_le_of_pos {q : Rat} (hq : 0 < q) :
    ∃ n : Nat, 1 / ((n : Rat) + 1) ≤ q := by
  -- Get N with 1/q < N (Archimedean on Rat).
  rcases Rat.archimedean (1 / q) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  -- Show 1/(N+1) ≤ q, i.e., 1 ≤ q * (N+1). Use 1/q < N ≤ N+1, so 1 < q*(N+1) using q > 0.
  -- 1/q < N+1 (since N ≤ N+1 < N+1 strict? Actually need N < N+1 true)
  have hcast : ((N + 1 : Nat) : Rat) = (N : Rat) + 1 := by rw [Rat.natCast_add]; rfl
  have hN' : 1 / q < (N : Rat) + 1 := by
    have : (N : Rat) < (N : Rat) + 1 := by
      have : (0 : Rat) < 1 := by decide
      grind
    exact Rat.lt_trans hN this
  -- So 1 < q * (N+1) (multiply by q > 0)
  have hqne : q ≠ 0 := fun h => by rw [h] at hq; exact Rat.lt_irrefl hq
  have hone_div_q : 1 / q = q⁻¹ := by rw [Rat.div_def, Rat.one_mul]
  rw [hone_div_q] at hN'
  -- q⁻¹ < N+1, multiply by q: 1 < q * (N+1)
  have h1 : q * q⁻¹ < q * ((N : Rat) + 1) :=
    Rat.mul_lt_mul_of_pos_left hN' hq
  rw [Rat.mul_inv_cancel _ hqne] at h1
  -- h1 : 1 < q * (N + 1)
  -- Need: 1 / (N+1) ≤ q.
  -- N+1 > 0 (N ≥ 0, so N+1 ≥ 1 > 0).
  have hNp1_pos : (0 : Rat) < (N : Rat) + 1 := by
    have h1q : 0 < q⁻¹ := Rat.inv_pos.mpr hq
    exact Rat.lt_trans h1q hN'
  have hNp1_ne : ((N : Rat) + 1) ≠ 0 :=
    fun h => by rw [h] at hNp1_pos; exact Rat.lt_irrefl hNp1_pos
  -- 1 < q * (N+1) and (N+1) > 0 → 1/(N+1) < q (divide by N+1)
  have h2 : 1 * ((N : Rat) + 1)⁻¹ < q * ((N : Rat) + 1) * ((N : Rat) + 1)⁻¹ :=
    Rat.mul_lt_mul_of_pos_right h1 (Rat.inv_pos.mpr hNp1_pos)
  rw [Rat.one_mul, Rat.mul_assoc, Rat.mul_inv_cancel _ hNp1_ne, Rat.mul_one] at h2
  -- h2 : (N+1)⁻¹ < q. Now (1 / (N+1)) = (N+1)⁻¹ via Rat.div_def with 1 * x = x.
  -- Convert.
  have hdivexp : 1 / (((N : Nat) : Rat) + 1) = ((N : Rat) + 1)⁻¹ := by
    rw [Rat.div_def, Rat.one_mul]
  rw [hdivexp]
  exact Rat.le_of_lt h2

/-- Real Archimedean-of-inverse: every positive real has a `1/(n+1)`-bound below. -/
theorem archimedean_inv (x : MyReal) (hx : 0 < x) :
    ∃ n : Nat, k (1 / ((n : Rat) + 1)) ≤ x := by
  rcases hx with ⟨h_le, h_ne⟩
  refine Quotient.inductionOn x
    (motive := fun x => 0 ≤ x → 0 ≠ x → ∃ n : Nat, k (1 / ((n : Rat) + 1)) ≤ x)
    ?_ h_le h_ne
  intro a hle hne
  have hnn : MyPrereal.IsNonneg a := (zero_le_iff_isNonneg (mk a)).mp hle
  have ha_nz : ¬ (a ≈ 0) := fun heq => hne (Quotient.sound heq).symm
  have hpos : MyPrereal.IsPos a := by
    rcases hnn with hp | hz
    · exact hp
    · exact absurd hz ha_nz
  rcases hpos with ⟨δ, hδpos, N, HN⟩
  rcases one_div_succ_le_of_pos hδpos with ⟨n₀, hn₀⟩
  refine ⟨n₀, ?_⟩
  show k (1 / ((n₀ : Rat) + 1)) ≤ mk a
  show mk ⟨_, isCauchy_const _⟩ ≤ mk a
  rw [le_def, sub_def]
  show MyPrereal.IsNonneg _
  refine MyPrereal.IsNonneg_of_nonneg N (fun n hn => ?_)
  rw [MyPrereal.sub_apply]
  show 0 ≤ a n - 1 / ((n₀ : Rat) + 1)
  have hδle : δ ≤ a n := HN n hn
  -- 1/(n₀+1) ≤ δ ≤ a n
  have h := Rat.le_trans hn₀ hδle
  grind

/-! ### Approximation. -/

/-- Given a Cauchy `MyReal`-sequence, choose a rational approximation per
index using `Classical.choose` on a representative's Cauchy property.
The witness is `q m`, where `q` is a chosen prereal representative of `s n`
and `m` is the Cauchy threshold for the rational tolerance `1/(n+1)`. -/
noncomputable def approx (s : Nat → MyReal) (n : Nat) : Rat :=
  let q : MyPrereal := Classical.choose (Quotient.exists_rep (s n))
  q (Classical.choose (q.prop (1 / ((n : Rat) + 1)) (one_div_succ_pos n)))

/-- The defining bound of `approx`: at every index, `s n` is within `1/(n+1)`
of `k (approx s n)` in `MyReal`. -/
theorem approx_spec (s : Nat → MyReal) (n : Nat) :
    s n - k (approx s n) ≤ k (1 / ((n : Rat) + 1)) ∧
    -(s n - k (approx s n)) ≤ k (1 / ((n : Rat) + 1)) := by
  -- Unfold approx: q is the chosen representative, m the chosen index.
  let q : MyPrereal := Classical.choose (Quotient.exists_rep (s n))
  have hq : mk q = s n := Classical.choose_spec (Quotient.exists_rep (s n))
  let m : Nat := Classical.choose (q.prop (1 / ((n : Rat) + 1)) (one_div_succ_pos n))
  have hm := Classical.choose_spec (q.prop (1 / ((n : Rat) + 1)) (one_div_succ_pos n))
  have happrox_eq : approx s n = q m := rfl
  rw [happrox_eq, ← hq]
  -- Now goal: mk q - k (q m) ≤ k (1/(n+1)) ∧ -(mk q - k (q m)) ≤ k (1/(n+1))
  -- Reduce to MyPrereal level. Note k a = mk ⟨const a, _⟩.
  have hsub_eq : mk q - k (q m) = mk (q - ⟨_, isCauchy_const (q m)⟩) := by
    show mk q - mk ⟨_, isCauchy_const (q m)⟩ = _
    rw [sub_def]
  refine ⟨?_, ?_⟩
  · rw [hsub_eq]
    show mk _ ≤ k _
    show mk _ ≤ mk ⟨_, isCauchy_const _⟩
    rw [le_def, sub_def]
    show MyPrereal.IsNonneg _
    refine MyPrereal.IsNonneg_of_nonneg m (fun j hj => ?_)
    rw [MyPrereal.sub_apply, MyPrereal.sub_apply]
    show 0 ≤ 1 / ((n : Rat) + 1) - (q j - q m)
    have habs := hm j m hj (Nat.le_refl _)
    have hbnd := absRat_le_iff.mp habs
    have h1 : q j - q m ≤ 1 / ((n : Rat) + 1) := hbnd.2
    grind
  · rw [hsub_eq]
    show -(mk _) ≤ k _
    rw [neg_def]
    show mk _ ≤ mk ⟨_, isCauchy_const _⟩
    rw [le_def, sub_def]
    show MyPrereal.IsNonneg _
    refine MyPrereal.IsNonneg_of_nonneg m (fun j hj => ?_)
    rw [MyPrereal.sub_apply, MyPrereal.neg_apply, MyPrereal.sub_apply]
    show 0 ≤ 1 / ((n : Rat) + 1) - -(q j - q m)
    have habs := hm j m hj (Nat.le_refl _)
    have hbnd := absRat_le_iff.mp habs
    have h1 : -(1 / ((n : Rat) + 1)) ≤ q j - q m := hbnd.1
    grind

/-- `MyAbs`-formulated bound: `|s n - k (approx s n)| ≤ k (1/(n+1))`. -/
theorem MyAbs_approx_spec (s : Nat → MyReal) (n : Nat) :
    MyAbs (s n - k (approx s n)) ≤ k (1 / ((n : Rat) + 1)) :=
  (bound_iff_MyAbs_le _ _).mp (approx_spec s n)

/-! ### Auxiliary `MyReal` order arithmetic for completeness. -/

/-- Right-monotonicity of addition. -/
theorem add_le_add_right (x y : MyReal) (h : x ≤ y) (t : MyReal) : x + t ≤ y + t := by
  rw [add_comm x t, add_comm y t]; exact add_le_add_left _ _ h _

/-- Two-sided monotonicity of addition. -/
theorem add_le_add {a b c d : MyReal} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  le_trans _ _ _ (add_le_add_right _ _ h1 c) (add_le_add_left _ _ h2 b)

/-- Triangle inequality for differences: `|a - c| ≤ |a - b| + |b - c|`. -/
theorem MyAbs_sub_triangle (a b c : MyReal) :
    MyAbs (a - c) ≤ MyAbs (a - b) + MyAbs (b - c) := by
  -- a - c = (a - b) + (b - c)
  have heq : a - c = (a - b) + (b - c) := by
    refine Quotient.inductionOn₃ a b c
      (motive := fun a b c => a - c = (a - b) + (b - c)) (fun x y z => ?_)
    show mk x - mk z = (mk x - mk y) + (mk y - mk z)
    rw [sub_def, sub_def, sub_def, add_def]
    apply Quotient.sound
    apply R_of_funext; intro n
    rw [MyPrereal.add_apply, MyPrereal.sub_apply, MyPrereal.sub_apply, MyPrereal.sub_apply]
    show x n - z n = (x n - y n) + (y n - z n); grind
  rw [heq]
  exact MyAbs_add (a - b) (b - c)

/-- `k` distributes over rational addition (already proved as `k_add`); we restate for `≤`. -/
theorem k_add_le_add (a b c : Rat) (h : a ≤ b + c) : k a ≤ k b + k c := by
  rw [← k_add]; exact k_le_iff.mpr h

/-! ### Step A: `approx s` is `Rat`-Cauchy. -/

/-- Helper: for any natural `n0` and `n ≥ n0`, `1/(n+1) ≤ 1/(n0+1)` rationally. -/
private theorem one_div_succ_mono {n0 n : Nat} (h : n0 ≤ n) :
    1 / ((n : Rat) + 1) ≤ 1 / ((n0 : Rat) + 1) := by
  -- (n+1) ≥ (n0+1), both positive, so reciprocals reverse.
  have hn0p1_pos : (0 : Rat) < (n0 : Rat) + 1 := by
    have h0 : (0 : Rat) ≤ (n0 : Rat) := by
      induction n0 with
      | zero => exact Rat.le_refl
      | succ k ih =>
        have hcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by
          rw [Rat.natCast_add]; rfl
        rw [hcast]; grind
    grind
  have hnp1_pos : (0 : Rat) < (n : Rat) + 1 := by
    have h0 : (0 : Rat) ≤ (n : Rat) := by
      induction n with
      | zero => exact Rat.le_refl
      | succ k ih =>
        have hcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by
          rw [Rat.natCast_add]; rfl
        rw [hcast]; grind
    grind
  have hcast_le : (n0 : Rat) ≤ (n : Rat) := by
    -- nat-cast monotone
    have hn0n : (0 : Int) ≤ (n : Int) - (n0 : Int) := by exact_mod_cast Nat.zero_le (n - n0)
    -- Hmm easier: induct on h.
    have : ∀ m, n0 ≤ m → (n0 : Rat) ≤ (m : Rat) := by
      intro m hm
      induction hm with
      | refl => exact Rat.le_refl
      | step _ ih =>
        rename_i j _
        have hcast : ((j + 1 : Nat) : Rat) = (j : Rat) + 1 := by
          rw [Rat.natCast_add]; rfl
        rw [hcast]
        have h01 : (0 : Rat) ≤ 1 := by decide
        have hj : (j : Rat) ≤ (j : Rat) + 1 := by grind
        exact Rat.le_trans ih hj
    exact this n h
  have hn0p1_le : (n0 : Rat) + 1 ≤ (n : Rat) + 1 := by
    have h01 : (1 : Rat) ≤ 1 := Rat.le_refl
    grind
  have hn0p1_ne : ((n0 : Rat) + 1) ≠ 0 := fun h => by rw [h] at hn0p1_pos; exact Rat.lt_irrefl hn0p1_pos
  have hnp1_ne : ((n : Rat) + 1) ≠ 0 := fun h => by rw [h] at hnp1_pos; exact Rat.lt_irrefl hnp1_pos
  -- Show (n+1)⁻¹ ≤ (n0+1)⁻¹.
  have hinv : ((n : Rat) + 1)⁻¹ ≤ ((n0 : Rat) + 1)⁻¹ := by
    -- (n0+1) * (n+1)⁻¹ ≤ (n+1) * (n+1)⁻¹ = 1, so (n+1)⁻¹ ≤ (n0+1)⁻¹
    have h1 : ((n0 : Rat) + 1) * ((n : Rat) + 1)⁻¹ ≤ ((n : Rat) + 1) * ((n : Rat) + 1)⁻¹ :=
      Rat.mul_le_mul_of_nonneg_right hn0p1_le (Rat.le_of_lt (Rat.inv_pos.mpr hnp1_pos))
    rw [Rat.mul_inv_cancel _ hnp1_ne] at h1
    -- h1 : (n0+1) * (n+1)⁻¹ ≤ 1
    -- Multiply by (n0+1)⁻¹ ≥ 0
    have h2 := Rat.mul_le_mul_of_nonneg_left h1 (Rat.le_of_lt (Rat.inv_pos.mpr hn0p1_pos))
    rw [← Rat.mul_assoc, Rat.inv_mul_cancel _ hn0p1_ne, Rat.one_mul, Rat.mul_one] at h2
    exact h2
  rw [show (1 / ((n : Rat) + 1)) = ((n : Rat) + 1)⁻¹ by rw [Rat.div_def, Rat.one_mul]]
  rw [show (1 / ((n0 : Rat) + 1)) = ((n0 : Rat) + 1)⁻¹ by rw [Rat.div_def, Rat.one_mul]]
  exact hinv

/-- Step A: the rational approximation sequence is Cauchy. -/
theorem isCauchy_approx (s : Nat → MyReal) (hs : IsCauchyMR s) :
    IsCauchy (approx s) := by
  intro ε hε
  -- Pick n0 with 1/(n0+1) ≤ ε/3.
  have hε3 : 0 < ε / 3 := by
    rw [Rat.div_def]
    have h3pos : (0 : Rat) < 3 := by decide
    exact Rat.mul_pos hε (Rat.inv_pos.mpr h3pos)
  rcases one_div_succ_le_of_pos hε3 with ⟨n0, hn0⟩
  -- Cauchy of s with k(ε/3): get N₁
  rcases hs (k (ε / 3)) (k_pos_iff.mpr hε3) with ⟨N₁, HN₁⟩
  refine ⟨max N₁ n0, fun p q hp hq => ?_⟩
  have hp1 : N₁ ≤ p := Nat.le_trans (Nat.le_max_left _ _) hp
  have hq1 : N₁ ≤ q := Nat.le_trans (Nat.le_max_left _ _) hq
  have hpn0 : n0 ≤ p := Nat.le_trans (Nat.le_max_right _ _) hp
  have hqn0 : n0 ≤ q := Nat.le_trans (Nat.le_max_right _ _) hq
  -- MyAbs (s p - s q) ≤ k (ε/3)
  have hsab : MyAbs (s p - s q) ≤ k (ε / 3) := (bound_iff_MyAbs_le _ _).mp (HN₁ p q hp1 hq1)
  -- MyAbs (s p - k (approx s p)) ≤ k (1/(p+1)) ≤ k (1/(n0+1)) ≤ k (ε/3)
  have hpapp_a : MyAbs (s p - k (approx s p)) ≤ k (1 / ((p : Rat) + 1)) :=
    MyAbs_approx_spec s p
  have hpapp_b : k (1 / ((p : Rat) + 1)) ≤ k (ε / 3) :=
    k_le_iff.mpr (Rat.le_trans (one_div_succ_mono hpn0) hn0)
  have hpapp : MyAbs (s p - k (approx s p)) ≤ k (ε / 3) :=
    le_trans _ _ _ hpapp_a hpapp_b
  -- Same for q:
  have hqapp_a : MyAbs (s q - k (approx s q)) ≤ k (1 / ((q : Rat) + 1)) :=
    MyAbs_approx_spec s q
  have hqapp_b : k (1 / ((q : Rat) + 1)) ≤ k (ε / 3) :=
    k_le_iff.mpr (Rat.le_trans (one_div_succ_mono hqn0) hn0)
  have hqapp : MyAbs (s q - k (approx s q)) ≤ k (ε / 3) :=
    le_trans _ _ _ hqapp_a hqapp_b
  -- We need: MyAbs (k (approx s p) - k (approx s q)) ≤ k ε.
  -- Triangle: MyAbs (k (app p) - k (app q)) ≤ MyAbs (k (app p) - s p) + MyAbs (s p - k (app q))
  --   And MyAbs (s p - k (app q)) ≤ MyAbs (s p - s q) + MyAbs (s q - k (app q)).
  have hsubcomm : MyAbs (k (approx s p) - s p) = MyAbs (s p - k (approx s p)) :=
    MyAbs_sub_comm _ _
  have hpapp' : MyAbs (k (approx s p) - s p) ≤ k (ε / 3) := by
    rw [hsubcomm]; exact hpapp
  have htri1 : MyAbs (k (approx s p) - k (approx s q))
              ≤ MyAbs (k (approx s p) - s p) + MyAbs (s p - k (approx s q)) :=
    MyAbs_sub_triangle _ _ _
  have htri2 : MyAbs (s p - k (approx s q))
              ≤ MyAbs (s p - s q) + MyAbs (s q - k (approx s q)) :=
    MyAbs_sub_triangle _ _ _
  -- Combine
  have hsum1 : MyAbs (s p - k (approx s q)) ≤ k (ε / 3) + k (ε / 3) :=
    le_trans _ _ _ htri2 (add_le_add hsab hqapp)
  have hsum2 : MyAbs (k (approx s p) - k (approx s q)) ≤ k (ε / 3) + (k (ε / 3) + k (ε / 3)) :=
    le_trans _ _ _ htri1 (add_le_add hpapp' hsum1)
  -- ε/3 + ε/3 + ε/3 = ε, so RHS = k ε.
  have hε_third : ε / 3 + (ε / 3 + ε / 3) = ε := by
    have h3ne : (3 : Rat) ≠ 0 := by decide
    have h3i : (3 : Rat) * (3 : Rat)⁻¹ = 1 := Rat.mul_inv_cancel _ h3ne
    rw [Rat.div_def]; grind
  have hsumk : k (ε / 3) + (k (ε / 3) + k (ε / 3)) = k ε := by
    rw [← k_add, ← k_add, hε_third]
  rw [hsumk] at hsum2
  -- Final: MyAbs (k(app p) - k(app q)) ≤ k ε. By k_abs and k_le_iff:
  -- MyAbs (k (app p) - k (app q)) = MyAbs (k (app p - app q)) = k (absRat (app p - app q)).
  have hk_diff : k (approx s p) - k (approx s q) = k (approx s p - approx s q) := by
    rw [k_sub]
  rw [hk_diff, k_abs] at hsum2
  -- hsum2 : k (absRat (...)) ≤ k ε
  exact k_le_iff.mp hsum2

/-! ### Step B & C: completeness theorem. -/

/-- The completeness theorem: every `MyReal`-valued Cauchy sequence converges. -/
theorem complete (s : Nat → MyReal) (hs : IsCauchyMR s) :
    ∃ L : MyReal, Converges s L := by
  -- L is the prereal approximation lifted to MyReal.
  let q : MyPrereal := ⟨approx s, isCauchy_approx s hs⟩
  refine ⟨mk q, ?_⟩
  intro ε hε
  -- Pick n0 with k (1/(n0+1)) ≤ ε.
  rcases archimedean_inv ε hε with ⟨n0, hn0⟩
  -- We aim to bound MyAbs (s n - L) ≤ k (1/(n0+1)) ≤ ε.
  -- Use ε/2 split: δ' = (1/(n0+1))/2 rationally.
  let δ : Rat := 1 / ((n0 : Rat) + 1)
  have hδpos : 0 < δ := one_div_succ_pos n0
  have hδ2pos : 0 < δ / 2 := MyPrereal.half_pos hδpos
  -- Cauchy of s with k(δ/2): get N₁
  rcases hs (k (δ / 2)) (k_pos_iff.mpr hδ2pos) with ⟨N₁, HN₁⟩
  -- Find n1 with 1/(n1+1) ≤ δ/2 (rationally Archimedean).
  rcases one_div_succ_le_of_pos hδ2pos with ⟨n1, hn1⟩
  -- prereal_close on q: for m ≥ N₂, mk q - k (q m) ≤ k (δ/2) and -(...) ≤ k(δ/2).
  rcases prereal_close q hδ2pos with ⟨N₂, HN₂⟩
  refine ⟨max N₁ (max n1 N₂), fun n hn => ?_⟩
  have hN1 : N₁ ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hrest : max n1 N₂ ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hn1n : n1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hrest
  have hN2n : N₂ ≤ n := Nat.le_trans (Nat.le_max_right _ _) hrest
  -- MyAbs (s n - k (approx s n)) ≤ k (1/(n+1)) ≤ k (1/(n1+1)) ≤ k (δ/2)
  have happ_a : MyAbs (s n - k (approx s n)) ≤ k (1 / ((n : Rat) + 1)) :=
    MyAbs_approx_spec s n
  have happ_b : k (1 / ((n : Rat) + 1)) ≤ k (δ / 2) :=
    k_le_iff.mpr (Rat.le_trans (one_div_succ_mono hn1n) hn1)
  have happ : MyAbs (s n - k (approx s n)) ≤ k (δ / 2) :=
    le_trans _ _ _ happ_a happ_b
  -- mk q - k (q n) bound:
  have hLapp : MyAbs (mk q - k (approx s n)) ≤ k (δ / 2) := by
    -- approx s n = q n by definition
    have : (q : MyPrereal) n = approx s n := rfl
    have hq_n : k ((q : MyPrereal) n) = k (approx s n) := rfl
    rw [← hq_n]
    exact (bound_iff_MyAbs_le _ _).mp (HN₂ n hN2n)
  -- Triangle: MyAbs (s n - mk q) ≤ MyAbs (s n - k (approx s n)) + MyAbs (k (approx s n) - mk q)
  have hLapp' : MyAbs (k (approx s n) - mk q) ≤ k (δ / 2) := by
    rw [MyAbs_sub_comm]; exact hLapp
  have htri : MyAbs (s n - mk q) ≤ MyAbs (s n - k (approx s n)) + MyAbs (k (approx s n) - mk q) :=
    MyAbs_sub_triangle _ _ _
  have htotal : MyAbs (s n - mk q) ≤ k (δ / 2) + k (δ / 2) :=
    le_trans _ _ _ htri (add_le_add happ hLapp')
  -- δ/2 + δ/2 = δ
  have hsum : (δ / 2) + (δ / 2) = δ := MyPrereal.half_add_half δ
  have hsumk : k (δ / 2) + k (δ / 2) = k δ := by rw [← k_add, hsum]
  rw [hsumk] at htotal
  -- htotal : MyAbs (s n - mk q) ≤ k δ.
  -- And k δ ≤ ε from hn0.
  have hε_bound : MyAbs (s n - mk q) ≤ ε := le_trans _ _ _ htotal hn0
  exact (bound_iff_MyAbs_le _ _).mpr hε_bound

end MyReal

end Completeness

/-! ### Sanity checks (kept as `example`s — not exported lemmas). -/
section SanityChecks

open MyReal MyPrereal

/-- Constants `0` and `1` are distinct in `MyReal`. -/
example : (1 : MyReal) + 1 ≠ 0 := by
  intro h
  have h' : ((1 : MyPrereal) + (1 : MyPrereal)) ≈ (0 : MyPrereal) := by
    have : (mk 1 + mk 1 : MyReal) = mk 0 := h
    rw [add_def] at this
    exact Quotient.exact this
  rcases h' (1/2) (by rw [Rat.div_def, Rat.one_mul]; exact Rat.inv_pos.mpr (by decide)) with ⟨N, HN⟩
  have := HN N (Nat.le_refl _)
  have heq : ((1 : MyPrereal) + 1) N - (0 : MyPrereal) N = 2 := by
    show ((1 : Rat) + 1) - 0 = 2; grind
  rw [heq] at this
  have h2 : absRat (2 : Rat) = 2 := absRat_of_nonneg (by decide)
  rw [h2] at this
  have hcontra : (2 : Rat) ≤ 1/2 := this
  have hsum : (2 : Rat)⁻¹ + (2 : Rat)⁻¹ = 1 := MyPrereal.inv_two_add_inv_two
  have h2inv_pos : (0 : Rat) < (2 : Rat)⁻¹ := Rat.inv_pos.mpr (by decide)
  grind

/-- Archimedean witness exists. -/
example (x : MyReal) : ∃ n : Nat, x < (n : MyReal) := MyReal.archimedean x

/-- The rational embedding preserves addition. -/
example (a b : Rat) : MyReal.k (a + b) = MyReal.k a + MyReal.k b := MyReal.k_add a b

/-- Cauchy completeness: every Cauchy sequence converges. -/
example (s : Nat → MyReal) (hs : MyReal.IsCauchyMR s) :
    ∃ L : MyReal, MyReal.Converges s L := MyReal.complete s hs

/-- Triangle inequality. -/
example (a b : MyReal) : MyReal.MyAbs (a + b) ≤ MyReal.MyAbs a + MyReal.MyAbs b :=
  MyReal.MyAbs_add a b

end SanityChecks

end Mgw.Reals
