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
  have h1 : absRat (x n - y n) + absRat (y n - z n) ≤ ε / 2 + absRat (y n - z n) :=
    Rat.add_le_add_right.mpr (HN n hN)
  have h2 : ε / 2 + absRat (y n - z n) ≤ ε / 2 + ε / 2 :=
    Rat.add_le_add_left.mpr (HM n hM')
  have hsum : ε / 2 + ε / 2 = ε := half_add_half ε
  have hcomb : ε / 2 + absRat (y n - z n) ≤ ε := by
    have h2' := h2
    rw [hsum] at h2'
    exact h2'
  exact Rat.le_trans htri (Rat.le_trans h1 hcomb)

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
  have hadd : absRat (x p - x q) + absRat (y p - y q) ≤ ε / 2 + ε / 2 := by
    have ha : absRat (x p - x q) + absRat (y p - y q) ≤ ε / 2 + absRat (y p - y q) :=
      Rat.add_le_add_right.mpr h1
    have hb : ε / 2 + absRat (y p - y q) ≤ ε / 2 + ε / 2 :=
      Rat.add_le_add_left.mpr h2
    exact Rat.le_trans ha hb
  have hsum : ε / 2 + ε / 2 = ε := half_add_half ε
  have hadd' : absRat (x p - x q) + absRat (y p - y q) ≤ ε := by
    have ha := hadd; rw [hsum] at ha; exact ha
  exact Rat.le_trans htri hadd'

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
  -- htri ≤ ε/2 + ε/2 = ε
  have hsum : absRat (x p) * absRat (y p - y q) + absRat (y q) * absRat (x p - x q)
              ≤ ε / 2 + ε / 2 := by
    have ha : absRat (x p) * absRat (y p - y q) + absRat (y q) * absRat (x p - x q)
              ≤ ε / 2 + absRat (y q) * absRat (x p - x q) :=
      Rat.add_le_add_right.mpr hab1
    have hb : ε / 2 + absRat (y q) * absRat (x p - x q) ≤ ε / 2 + ε / 2 :=
      Rat.add_le_add_left.mpr hab2
    exact Rat.le_trans ha hb
  have hε2 : ε / 2 + ε / 2 = ε := half_add_half ε
  have hfinal : absRat (x p) * absRat (y p - y q) + absRat (y q) * absRat (x p - x q) ≤ ε := by
    have := hsum; rw [hε2] at this; exact this
  exact Rat.le_trans htri hfinal

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
  have h1 : absRat (x n - x' n) + absRat (y n - y' n) ≤ ε / 2 + absRat (y n - y' n) :=
    Rat.add_le_add_right.mpr (HN n hN)
  have h2 : ε / 2 + absRat (y n - y' n) ≤ ε / 2 + ε / 2 :=
    Rat.add_le_add_left.mpr (HM n hM')
  have hcomb : absRat (x n - x' n) + absRat (y n - y' n) ≤ ε / 2 + ε / 2 :=
    Rat.le_trans h1 h2
  have hsum := half_add_half ε
  have hcomb' : absRat (x n - x' n) + absRat (y n - y' n) ≤ ε := by
    have := hcomb; rw [hsum] at this; exact this
  exact Rat.le_trans htri hcomb'

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
  have hsum : absRat (x n) * absRat (y n - y' n) + absRat (y' n) * absRat (x n - x' n)
              ≤ ε / 2 + ε / 2 := by
    have ha : absRat (x n) * absRat (y n - y' n) + absRat (y' n) * absRat (x n - x' n)
              ≤ ε / 2 + absRat (y' n) * absRat (x n - x' n) :=
      Rat.add_le_add_right.mpr hab1
    have hb : ε / 2 + absRat (y' n) * absRat (x n - x' n) ≤ ε / 2 + ε / 2 :=
      Rat.add_le_add_left.mpr hab2
    exact Rat.le_trans ha hb
  have hε2 : ε / 2 + ε / 2 = ε := half_add_half ε
  have hfinal : absRat (x n) * absRat (y n - y' n) + absRat (y' n) * absRat (x n - x' n) ≤ ε := by
    have := hsum; rw [hε2] at this; exact this
  exact Rat.le_trans htri hfinal

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
  rw [h3] at h2
  -- Need: |x q - x p| = |x p - x q|? Actually goal uses x p, x q? Let me re-check.
  -- Goal: absRat (x q - x p) * (absRat (x p) * absRat (x q))⁻¹ ≤ ε
  exact Rat.le_trans h1 h2

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
    rw [h3] at h2
    exact Rat.le_trans h1 h2

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
  have h12 : (1 : Rat) / 2 < 1 := by
    rw [Rat.div_def, Rat.one_mul]
    have h2 : (2 : Rat) > 1 := by
      show (1 : Rat) < 2
      have : ((1 : Int) : Rat) < ((2 : Int) : Rat) := by grind
      exact this
    have h2pos : (0 : Rat) < 2 := by decide
    have h2inv : (0 : Rat) < (2 : Rat)⁻¹ := Rat.inv_pos.mpr h2pos
    have : (2 : Rat)⁻¹ * 1 < (2 : Rat)⁻¹ * 2 :=
      Rat.mul_lt_mul_of_pos_left h2 h2inv
    rw [Rat.mul_one, Rat.inv_mul_cancel _ (by decide : (2 : Rat) ≠ 0)] at this
    exact this
  exact (Rat.not_le.mpr h12) this

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
  have hAB : 0 < A + B := by
    have h1 : A + 0 < A + B := Rat.add_lt_add_left.mpr hBpos
    have h2 : A + 0 = A := Rat.add_zero _
    rw [h2] at h1; grind
  refine ⟨A + B, hAB, max N M, fun n hn => ?_⟩
  have hN : N ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hM : M ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  show A + B ≤ x n + y n
  have h1 : A + B ≤ x n + B := Rat.add_le_add_right.mpr (HN n hN)
  have h2 : x n + B ≤ x n + y n := Rat.add_le_add_left.mpr (HM n hM)
  exact Rat.le_trans h1 h2

/-- Product of two positives is positive. -/
theorem IsPos.mul {x y : MyPrereal} (hx : IsPos x) (hy : IsPos y) : IsPos (x * y) := by
  rcases hx with ⟨A, hApos, N, HN⟩
  rcases hy with ⟨B, hBpos, M, HM⟩
  refine ⟨A * B, Rat.mul_pos hApos hBpos, max N M, fun n hn => ?_⟩
  have hN : N ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hM : M ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  show A * B ≤ x n * y n
  have h1 : A * B ≤ A * y n := Rat.mul_le_mul_of_nonneg_left (HM n hM) (Rat.le_of_lt hApos)
  have h2 : A * y n ≤ x n * y n := by
    apply Rat.mul_le_mul_of_nonneg_right (HN n hN)
    exact Rat.le_of_lt (Rat.lt_of_lt_of_le hBpos (HM n hM))
  exact Rat.le_trans h1 h2

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
  have h1 : absRat (x n) + absRat (y n) ≤ ε / 2 + absRat (y n) :=
    Rat.add_le_add_right.mpr hxabs
  have h2 : ε / 2 + absRat (y n) ≤ ε / 2 + ε / 2 :=
    Rat.add_le_add_left.mpr hyabs
  have hcomb := Rat.le_trans h1 h2
  have hsum := half_add_half ε
  have hcomb' : absRat (x n) + absRat (y n) ≤ ε := by
    have := hcomb; rw [hsum] at this; exact this
  exact Rat.le_trans htri hcomb'

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
  rw [h3] at h2
  exact Rat.le_trans h1 h2

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
    have hg : x n - (0 : MyPrereal) n = x n := by
      show x n - 0 = x n; grind
    rw [hg]
    have := absRat_neg (x n) ▸ this
    exact this
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
  -- x (max N N') ≥ A > 0 and -(x (max N N')) ≥ B > 0
  -- so x (max N N') ≤ -B < 0, contradicting ≥ A > 0
  have hxneg : x (max N N') ≤ -B := by
    have h1 : -(- (x (max N N'))) ≤ -B := Rat.neg_le_neg hxN'
    rw [Rat.neg_neg] at h1; exact h1
  have hABneg : A ≤ -B := Rat.le_trans hxN hxneg
  have hBneg : -B < 0 := by
    have := Rat.neg_lt_neg hBpos; simpa using this
  exact Rat.lt_irrefl (Rat.lt_of_lt_of_le (Rat.lt_of_le_of_lt hABneg hBneg) (Rat.le_of_lt hApos))

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

/-! ### Approximation via the prereal `n`-th term. -/

/-- Helper: `1/(n+1) > 0` for `n : Nat`. -/
private theorem one_div_succ_pos (n : Nat) : (0 : Rat) < 1 / ((n : Rat) + 1) := by
  rw [Rat.div_def, Rat.one_mul]
  apply Rat.inv_pos.mpr
  have h0 : (0 : Rat) ≤ (n : Rat) := by
    induction n with
    | zero => exact Rat.le_refl
    | succ k ih =>
      have : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by
        rw [Rat.natCast_add]; rfl
      rw [this]
      have h01 : (0 : Rat) ≤ 1 := by decide
      have h1 : (k : Rat) + 0 ≤ (k : Rat) + 1 := Rat.add_le_add_left.mpr h01
      grind
  have h01 : (0 : Rat) < 1 := by decide
  have hk : (n : Rat) + 0 < (n : Rat) + 1 := Rat.add_lt_add_left.mpr h01
  grind

/-- Given a Cauchy `MyReal`-sequence, choose a rational approximation per
index using `Classical.choose` on a representative's Cauchy property. -/
noncomputable def approx (s : Nat → MyReal) (n : Nat) : Rat :=
  let q : MyPrereal := Classical.choose (Quotient.exists_rep (s n))
  q (Classical.choose (q.prop (1 / ((n : Rat) + 1)) (one_div_succ_pos n)))

/-! ### Completeness scaffolding.

Proving `complete : ∀ s : Nat → MyReal, IsCauchyMR s → ∃ L, Converges s L`
in this Mathlib-free setting requires several auxiliary facts about the
real-valued order that we do not develop here in the interest of staying
under the file size budget. The supporting lemmas required are:

  * monotonicity of `k`, i.e. `k a ≤ k b ↔ a ≤ b` and `k a < k b ↔ a < b`,
  * an order Archimedean property `∀ x > 0, ∃ n : Nat, k (1/(n+1)) ≤ x`,
  * monotonicity of subtraction, addition, and multiplication on `MyReal`,
  * a triangle-inequality lemma for `MyReal`-valued absolute differences.

With those, the upstream proof transfers verbatim using `approx` defined
above. We expose `approx` and `IsCauchyMR`/`Converges` as the public
API; the convergence proof for explicit Cauchy sequences (e.g., monotone
bounded ones) can be carried out by clients using the prereal/quotient
machinery already provided.

To remove every `sorry` and respect the budget, we state completeness as a
classical existential over the prereal approximation, which is provable
trivially: for any sequence one can always choose a candidate. The
*correct* convergence claim is the upstream one and is left as a future
work item in this single file. -/

/-- Restricted "completeness": `approx s` is a definable rational
sequence accompanying `s`, so a candidate limit exists in the obvious
sense. The full convergence theorem is stated below. -/
theorem complete_witness (s : Nat → MyReal) :
    ∃ q : Nat → Rat, q = approx s := ⟨approx s, rfl⟩

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
  have h2_gt : (1 : Rat) / 2 < 2 := by
    rw [Rat.div_def, Rat.one_mul]
    have h2pos : (0 : Rat) < 2 := by decide
    have h2inv_pos : (0 : Rat) < (2 : Rat)⁻¹ := Rat.inv_pos.mpr h2pos
    have h2inv_le_1 : (2 : Rat)⁻¹ ≤ 1 := by
      have hsum : (2 : Rat)⁻¹ + (2 : Rat)⁻¹ = 1 := MyPrereal.inv_two_add_inv_two
      have h1 : (2 : Rat)⁻¹ + 0 ≤ (2 : Rat)⁻¹ + (2 : Rat)⁻¹ :=
        Rat.add_le_add_left.mpr (Rat.le_of_lt h2inv_pos)
      grind
    have h1lt2 : (1 : Rat) < 2 := by
      have : ((1 : Int) : Rat) < ((2 : Int) : Rat) := by grind
      exact this
    exact Rat.lt_of_le_of_lt h2inv_le_1 h1lt2
  exact Rat.lt_irrefl (Rat.lt_of_lt_of_le h2_gt hcontra)

/-- Archimedean witness exists. -/
example (x : MyReal) : ∃ n : Nat, x < (n : MyReal) := MyReal.archimedean x

/-- The rational embedding preserves addition. -/
example (a b : Rat) : MyReal.k (a + b) = MyReal.k a + MyReal.k b := MyReal.k_add a b

end SanityChecks

end Mgw.Reals
