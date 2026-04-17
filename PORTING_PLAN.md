# MgwTopology — Porting Plan

Target: a **Mathlib-free** Lean 4 port of the real-free topological content of
`mgw_test/mglib/topology.mg`, built on Lean core + Batteries only.

## Scope decision

`topology.mg` contains **3,452 theorems**. After tightened filtering for
`real`, `rational`, surreal (`SNo`/`PNo`/`CSNo`/`HSNo`/`OSNo`), `metric`,
`Euclidean`, `norm`, `sqrt`, `exp`, `Pi`, `int`, `nat_p`, `abs_SNo`, and the
surreal arithmetic operators, **1,217 theorems** (≈ 35% of the file) have
statements that use only topological concepts (`topology_on`, continuity,
compactness, connectedness, separation, countability, closure, interior,
basis, …). These are the port target. Full list: `PORT_MANIFEST.md` and
`port_manifest.csv`.

### What's in scope

Pure set-theoretic topology over a type `α` with a user-provided
`Mgw.Topology α` record: open/closed, basis, subbasis, subspace, product
(finite — infinite products need a small amount of indexing machinery that
is still Mathlib-free), continuous maps, compactness, connectedness, T1 /
Hausdorff / regular / normal, countability axioms, Lindelöf, dense sets,
closure, interior, boundary, quotient topology.

### What's explicitly out of scope

- Anything mentioning `ℝ` or the surreal-number stack. That rules out §20
  Metric Topology, §34 Urysohn Metrization's ℝ-valued conclusion, §35
  Tietze Extension, §43 Complete Metric Spaces.
- The admitted 850 surreal/ordinal axioms in `topology.mg`.
- Urysohn's Lemma and Tietze as stated (both conclude with an
  `ℝ`-valued continuous map). The supporting normal-space infrastructure
  (§31–§32) is in scope.

## Design decisions

1. **No Mathlib.** Dependencies: Lean core + Batteries only. Pinned to
   Lean `v4.29.1` / Batteries `v4.29.0`.
2. **Roll our own `Set α`.** `Set` is not in Lean core or Batteries. We
   provide `MgwTopology/SetLib.lean` with `Set α := α → Prop` as an
   `abbrev`, plus `∈`, `⊆`, `∅`, `univ`, `∪`, `∩`, `ᶜ`, `\`, singleton,
   insert, `⋃₀`, `⋂₀`, `setOf`, `image`, `preimage`, `Finite`, `Countable`.
   Keep the API minimal; add lemmas only as ports need them.
3. **Record, not typeclass.** `Topology α` is a `structure` with four
   axioms, mirroring `topology.mg`'s `topology_on` predicate literally.
   Every theorem takes `T : Topology α` as an explicit argument. This
   trades Mathlib-style ergonomics (`[TopologicalSpace α]`) for a direct
   transliteration of the source.
4. **`Set α`, not untyped sets.** Points live in `α`; subsets live in
   `Set α`; topologies live in `Set (Set α)` (indirectly, as
   `IsOpen : Set α → Prop`). Subspaces are topologies on subtypes
   `{x : α // Y x}`.
5. **Finite / countable from scratch.** Defined as existence of a
   surjection from `Fin n` / `Nat`. No `Finset` machinery.

## Phase plan

Each phase produces a `.lean` file (or files) under `MgwTopology/` that
compiles standalone on top of earlier phases. Theorem counts are taken from
the manifest.

### Phase 0 — Foundation (done)

| File | Contents |
|---|---|
| `SetLib.lean` | `Set α`, membership, ops, `⋃₀`, `⋂₀`, `Finite`, `Countable`, basic lemmas |
| `Core.lean` | `Topology α` record, `IsClosed` |

### Phase 1 — Topological spaces (≈ 243 theorems)

| Section | Count | File |
|---|---:|---|
| §12 Topological Spaces | 98 | `Core.lean` (extend) |
| §13 Basis for a Topology | 136 | `Basis.lean` |
| §14 Order Topology (non-ℝ parts) | 85 | `OrderTopology.lean` |
| §16 Subspace Topology | 112 | `Subspace.lean` |

Infrastructure lemmas to build first: `IsOpen_union` (binary), `IsOpen_iUnion`
from indexed family, closure / interior / boundary operators, basic
calculational lemmas about complement and difference. Much of this is "shape"
manipulation and will use the `ext` tactic on `Set`.

### Phase 2 — Closed sets, continuity, product (≈ 234 theorems)

| Section | Count | File |
|---|---:|---|
| §17 Closed Sets and Limit Points | 105 | `ClosedAndLimit.lean` |
| §18 Continuous Functions | 107 | `Continuous.lean` (extend) |
| §15 Product (X × Y) | 20 | `BinaryProduct.lean` |
| §19 Product Topology (general, finite index parts) | 65 | `Product.lean` |

### Phase 3 — Connectedness, Compactness (≈ 126 theorems)

| Section | Count | File |
|---|---:|---|
| §23 Connected Spaces | 49 | `Connected.lean` (extend) |
| §25 Components and Local Connectedness | 34 | `Components.lean` |
| §26 Compact Spaces | 43 | `Compact.lean` (extend) |

### Phase 4 — Separation, Countability, Local Compactness (≈ 467 theorems)

| Section | Count | File |
|---|---:|---|
| §29 Local Compactness | 153 | `LocalCompact.lean` |
| §30 Countability Axioms | 117 | `Countability.lean` (extend) |
| §31 Separation Axioms | 71 | `Separation.lean` (extend) |
| §32 Normal Spaces | 126 | `Normal.lean` |

This is the largest phase and contains the non-ℝ half of the Urysohn/Tietze
infrastructure (normal-space separation, shrinking-cover machinery).

### Phase 5 — Advanced topology (≈ 147 theorems, selective)

| Section | Count | File |
|---|---:|---|
| §36 Imbeddings of Manifolds (set-theoretic parts) | 57 | `Imbeddings.lean` |
| §37 Tychonoff (real-free parts) | 19 | `Tychonoff.lean` |
| §39 Local Finiteness | 14 | `LocalFinite.lean` |
| §41 Paracompactness | 59 | `Paracompact.lean` |

Note: the Tychonoff theorem itself is typically proved with Zorn / ultrafilters.
Our `Classical` access covers Zorn via `Classical.choice` + a small Zorn
lemma proof (≈ 50 lines, Mathlib-free).

### Phase 6 — Function spaces and Baire (≈ 143 theorems)

| Section | Count | File |
|---|---:|---|
| §46 Pointwise/Compact Convergence (topology-only) | 18 | `PtwiseCompact.lean` |
| §47 Ascoli (topology-only) | 19 | `Ascoli.lean` |
| §48 Baire Spaces | 46 | `Baire.lean` |
| §50 Function-space topology (non-metric parts) | 275 (large) | `FunctionSpaces.lean` |

§50 is the largest single section. Many of its 275 "real-free" statements
are probably helper lemmas of metric-heavy material and may need closer
inspection. Treat this phase as optional stretch.

## Work budget estimate

- **Phases 1–4 are the backbone:** ~1,070 theorems. These form a coherent,
  idiomatic Lean topology library standing entirely on Batteries.
- **Phase 5–6 are optional stretch:** ~290 additional theorems, uneven
  depth.

## Per-theorem cost drivers

- `ext` and membership chasing in `Set α` is ergonomic because `Set` is an
  `abbrev` for `α → Prop`. Expect 5–20 lines per theorem for direct ports.
- Proofs of `topology.mg` theorems that use classical principles translate
  via `Classical.choice` / `byContradiction` / `em`. No tactic in scope
  relies on Mathlib.
- Proofs that use the Megalodon `apply H; …` style map to Lean `apply`
  fine. Term-mode proofs transliterate directly.

## Validation

- `lake build` must stay green after each file is added.
- Each ported theorem carries a `/- source: topology.mg:<line> -/`
  comment pointing back to the original.
- A lightweight test file asserts the type signatures of a few
  load-bearing theorems (`IsCompact` of closed subset of compact,
  continuous image of compact is compact, Hausdorff separation, …) to
  catch API drift.

## Not doing (deliberately)

- **No `TopologicalSpace` typeclass wrapper.** Would mean providing
  instances and defeat the 1-to-1-with-source property.
- **No bridge to Mathlib.** A user who wants Mathlib-style theorems can
  adapter-wrap `Mgw.Topology` → Mathlib later; not part of this port.
- **No automation beyond core.** No `simp` sets, no custom tactics.
- **No attempt on the 850 admitted surreal axioms.** They do not enter
  the real-free fragment.
