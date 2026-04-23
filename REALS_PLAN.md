# Reals Experiment — Plan

Branch: `experiment/reals-import`

## Goal

Add a minimal theory of the real numbers to MgwTopology — analogous in
spirit to `SetLib.lean` — so the currently-omitted ℝ-valued statements
from `topology.mg` (§14-ℝ, §20, §27, §33–35, §43, ℝ-fragments of
§46–50) become portable.

Reference construction:
`riccardobrasca/Numbers` — `Numbers/Solutions/reals_no_sorry.lean`
(Cauchy sequences over ℚ, quotient, field + order + completeness).

## What we keep from upstream, what we drop

Upstream is a 4-file chain totalling ~2,260 lines with
`import Mathlib.Tactic` at the bottom (`integers_no_sorry.lean`,
`rationals_no_sorry.lean`, `rationals_order_no_sorry.lean`,
`reals_no_sorry.lean`). MgwTopology's Phase-0 rule forbids Mathlib
(`PORTING_PLAN.md` §1), so we cannot vendor the chain as-is.

**Key realisation:** **Lean core already ships `Rat`**, and Batteries
brings in the ring/order lemma bundle we need. Confirmed present:

| Kind | Lemmas (Lean core / Batteries) |
|---|---|
| Ring | `Rat.add_zero`, `zero_add`, `add_comm`, `add_assoc`, `neg_add_cancel`, `mul_comm`, `mul_assoc`, `mul_one`, `one_mul`, `add_mul`, `mul_add`, `mul_inv_cancel` |
| Order | `Rat.le_refl`, `le_trans`, `le_total`, `lt_irrefl`, `add_le_add_left` (↔), `add_lt_add_left` (↔), `mul_pos`, `mul_nonneg` |
| Casts | `Int.cast : Int → Rat`, `Nat.cast : Nat → Rat`, `Rat.den_pos` |

So the upstream files `integers_no_sorry.lean` (~497 lines) and
`rationals_no_sorry.lean` + `rationals_order_no_sorry.lean` (~847
lines) are **entirely redundant** — their job is to build exactly what
Lean core's `Rat` already provides. We skip all of R0/R1 from the
previous plan draft and start directly from the 916-line upstream
`reals_no_sorry.lean`, re-grounded on core `Rat`.

What still needs manual work:

1. A handful of `Rat` conveniences not in the core API — most
   importantly `|x|` (absolute value) and its triangle inequality.
   Upstream pulls these from Mathlib; we define them ourselves.
2. Tactic replacement. Upstream proofs use `linarith`, `grind`, `ring`,
   `Finset`, `max'`, `abs_nonneg`. All must be rewritten to
   Lean-core-only tactics (`omega` on ℤ/ℕ, `decide` where literal,
   explicit term-mode rewrites for the rest) plus tiny private helpers
   in our own namespace.

## File layout

**One file, like `SetLib.lean`**: `MgwTopology/Reals.lean`. No
sub-directory, no aggregator. Wired into the default build by adding
one line to root `MgwTopology.lean`.

Internal section ordering (within the single file):

1. `Rat` extras — `Rat.abs`, triangle inequality, sign helpers,
   bounded-Cauchy lemma. (~150 lines)
2. `IsCauchy` predicate, `MyPrereal := {f // IsCauchy f}`, equivalence
   `R`, `MyReal` as a `Quotient`. (~200 lines)
3. Pointwise `+`, `-`, `*`, conditional `⁻¹` on `MyPrereal`; lift to
   `MyReal`; commutative-ring + field lemmas. (~400 lines)
4. `IsPos`/`IsNonneg`; `≤`/`<` on `MyReal`; partial + linear order;
   order/ring compatibility; Archimedean property. (~300 lines)
5. Rational embedding `k : Rat → MyReal`; density; `IsCauchy` on
   `MyReal`; `approx`; completeness theorem. (~350 lines)

Total rough estimate: **~1,400 lines in one file**, about 40% smaller
than the upstream chain because ~45% of upstream bulk was its own
`MyInt` / `MyRat` reconstruction that we skip.

## Tactic replacement reference

Every upstream proof uses one or more of these; we replace them as
follows.

| Upstream | MgwTopology replacement |
|---|---|
| `linarith` over `Rat` | Manual chain: use `Rat.add_le_add_left`, `Rat.add_lt_add_left`, `Rat.mul_nonneg`, `Rat.mul_pos`, transitivity. Package frequently-used chains as named lemmas in `RatExtras.lean`. |
| `linarith` over `Int`/`Nat` | `omega` (ships in Lean core). |
| `ring`, `ring_nf` | Explicit `rw`/term-mode using the ring lemmas already in the `Rat` API above. |
| `Finset.max'` over `range (A+1)` | Replace with a small `List.foldr max` helper in `RatExtras.lean` (pure Lean core). |
| `abs_nonneg`, `abs_sub_abs_le_abs_sub` etc. | Hand-proved in `RatExtras.lean`. |
| `grind` | Rewrite by hand; often a single `exact`/`omega`. |
| `Quot.induction_on` (multi-arg macros in upstream) | Use Lean's `Quotient.inductionOn₂` / `inductionOn₃` directly. |

## Work order (commits)

Single file grown section by section, `lake build` green at each step.

1. `feat(reals): create MgwTopology/Reals.lean with Rat extras (R0)`.
2. `feat(reals): IsCauchy and MyReal quotient (R1)`.
3. `feat(reals): field structure on MyReal (R2)`.
4. `feat(reals): linear order + Archimedean (R3)`.
5. `feat(reals): density + Cauchy completeness (R4)`.
6. `feat(reals): wire Reals into root MgwTopology.lean + sanity tests`.

## Acceptance criteria

A downstream module can write

```lean
import MgwTopology.Reals
open Mgw.Reals

example : (1 : MyReal) + 1 ≠ 0 := …          -- ring + order
example (x : MyReal) : ∃ n : ℕ, x < Nat.cast n := … -- Archimedean
example (f : ℕ → MyReal) (h : IsCauchy f)
    : ∃ L, Converges f L := …                 -- completeness
```

and re-enable the §14-ℝ / §27 section of the main port on top of it.

## Deliberately not doing

- **No Mathlib dependency.** Same constraint as `PORTING_PLAN.md` §1.
- **No `MyInt`/`MyRat` rebuild.** Lean core's `Rat` is enough. If a
  gap appears mid-port, fill it in `RatExtras.lean`, don't fork the
  rationals.
- **No decimal / binary representations, no √, no π, no sin/cos, no
  limits beyond sequential.** Purely the Cauchy-sequence construction
  and its order/field/completeness.
- **No `Real` typeclass instance (`Field ℝ` in the Mathlib sense).**
  We expose named lemmas, not instances — same style as
  `Mgw.Topology` records.

## Resolved

- Strategy C confirmed.
- Single file: `MgwTopology/Reals.lean`, mirroring `SetLib.lean`'s
  organisation.
- Wired into the default build target from the start.
- Namespace: `Mgw.Reals` (matches `Mgw` / `Mgw.Set` precedent).
