/-
Countability axioms.

Corresponds to topology.mg §30 (Countability Axioms).
First- and second-countability, separability, Lindelöf.
-/
import MgwTopology.Core
import MgwTopology.Basis
import MgwTopology.ClosureInterior
import MgwTopology.ClosedAndLimit
import MgwTopology.Subspace
import MgwTopology.Compact

namespace Mgw
namespace Topology

universe u
variable {α : Type u} (T : Topology α)

/-- A local basis at `x` is a family `ℬ₀` of open sets each containing `x`
    such that every open neighborhood of `x` contains some member of `ℬ₀`. -/
def IsLocalBasisAt (x : α) (ℬ₀ : Set (Set α)) : Prop :=
  (∀ B ∈ ℬ₀, T.IsOpen B ∧ x ∈ B) ∧
  ∀ U, T.IsOpen U → x ∈ U → ∃ B, B ∈ ℬ₀ ∧ B ⊆ U

/-- First countable: every point has a countable local basis. -/
def FirstCountable : Prop :=
  ∀ x : α, ∃ ℬ₀ : Set (Set α), ℬ₀.Countable ∧ T.IsLocalBasisAt x ℬ₀

/-- Second countable: there is a countable basis. -/
def SecondCountable : Prop :=
  ∃ ℬ : Set (Set α), ℬ.Countable ∧ IsBasis ℬ ∧
    ∀ U, T.IsOpen U ↔ Topology.generatedBy ℬ U

/-- A set `D` is dense iff every nonempty open set meets `D`. -/
def Dense (D : Set α) : Prop :=
  ∀ U : Set α, T.IsOpen U → U ≠ ∅ → ∃ x ∈ D, x ∈ U

/-- Separable: there is a countable dense subset. -/
def Separable : Prop := ∃ D : Set α, D.Countable ∧ Dense T D

/-- Lindelöf: every open cover of `univ` has a countable subcover. -/
def Lindelof : Prop :=
  ∀ 𝒰 : Set (Set α), (∀ U ∈ 𝒰, T.IsOpen U) → Set.univ ⊆ ⋃₀ 𝒰 →
    ∃ 𝒰₀ ⊆ 𝒰, 𝒰₀.Countable ∧ Set.univ ⊆ ⋃₀ 𝒰₀

/-! ### Countable-set utility. -/

/- source: topology.mg:128175 name: countable_image -/
/-- The image of a countable set under a function is countable. -/
theorem Set.Countable.image {β : Type u} {s : Set α} (hs : s.Countable)
    (f : α → β) : (Set.image f s).Countable := by
  classical
  rcases hs with hempty | ⟨e, he⟩
  · left
    rintro y ⟨x, hx, _⟩
    exact hempty x hx
  · right
    refine ⟨fun n => f (e n), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨n, hn⟩ := he x hx
    refine ⟨n, ?_⟩
    show f (e n) = f x
    rw [hn]

/-- Finite sets are countable. -/
theorem Set.Finite.countable {s : Set α} (hs : s.Finite) : s.Countable := by
  classical
  obtain ⟨n, f, hf⟩ := hs
  by_cases hn : n = 0
  · left
    intro x hx
    obtain ⟨i, _⟩ := hf x hx
    subst hn
    exact i.elim0
  · right
    -- Replace index type via a Nat-indexed function using `Nat.toFin`.
    refine ⟨fun k => if h : k < n then f ⟨k, h⟩ else f ⟨0, Nat.pos_of_ne_zero hn⟩, ?_⟩
    intro x hx
    obtain ⟨i, hi⟩ := hf x hx
    refine ⟨i.val, ?_⟩
    have : i.val < n := i.isLt
    simp only [this, ↓reduceDIte]
    have heq : (⟨i.val, this⟩ : Fin n) = i := Fin.ext rfl
    rw [heq]; exact hi

/-! ### Second countable → First countable. -/

/- source: topology.mg:128606 name: second_countable_implies_first_countable -/
/-- Every second countable space is first countable. -/
theorem FirstCountable.of_secondCountable (h : T.SecondCountable) :
    T.FirstCountable := by
  classical
  obtain ⟨ℬ, hℬc, hℬb, hℬgen⟩ := h
  intro x
  -- Take ℬ₀ = {B ∈ ℬ | x ∈ B}.
  refine ⟨fun B => B ∈ ℬ ∧ x ∈ B, ?_, ?_, ?_⟩
  · -- Subcollection of a countable set is countable.
    rcases hℬc with hempty | ⟨e, he⟩
    · left
      rintro B ⟨hB, _⟩
      exact hempty B hB
    · right
      refine ⟨e, ?_⟩
      rintro B ⟨hB, _⟩
      exact he B hB
  · rintro B ⟨hB, hxB⟩
    refine ⟨?_, hxB⟩
    -- B is open in T (T's opens = generatedBy ℬ; ℬ ⊆ open).
    rw [hℬgen]
    intro y hyB
    exact ⟨B, hB, hyB, fun _ h => h⟩
  · intro U hU hxU
    rw [hℬgen] at hU
    obtain ⟨B, hB, hxB, hBU⟩ := hU x hxU
    exact ⟨B, ⟨hB, hxB⟩, hBU⟩

/-! ### Dense in a superset. -/

/- source: topology.mg:131174 name: dense_in_superset -/
/-- If `A ⊆ B` and `A` is dense, then `B` is dense. -/
theorem Dense.mono {A B : Set α} (hAB : A ⊆ B) (hA : T.Dense A) : T.Dense B := by
  intro U hU hne
  obtain ⟨x, hxA, hxU⟩ := hA U hU hne
  exact ⟨x, hAB hxA, hxU⟩

/- source: topology.mg:131204 name: meets_nonempty_open_implies_dense_in -/
/-- If `A` meets every nonempty open set, then `A` is dense. (This is just
    unfolding the definition.) -/
theorem Dense.of_meets {A : Set α}
    (h : ∀ U, T.IsOpen U → U ≠ ∅ → ∃ x ∈ A, x ∈ U) : T.Dense A := h

/-! ### Characterizations of density via closure. -/

/-- `A` is dense iff its closure is `univ`. -/
theorem dense_iff_closure_univ {A : Set α} :
    T.Dense A ↔ T.closure A = Set.univ := by
  classical
  refine ⟨?_, ?_⟩
  · intro hA
    apply Set.subset_antisymm (Set.subset_univ _)
    intro x _
    show x ∈ T.closure A
    rw [T.mem_closure_iff]
    intro U hU hxU
    have hne : U ≠ ∅ := by
      intro heq
      rw [heq] at hxU; exact hxU
    obtain ⟨y, hyA, hyU⟩ := hA U hU hne
    exact ⟨y, hyU, hyA⟩
  · intro hcl U hU hne
    -- U nonempty: pick x ∈ U. x ∈ closure A means every open nbhd of x meets A.
    have hxex : ∃ x, x ∈ U := by
      classical
      by_contra hnex
      apply hne
      ext x
      exact ⟨fun hx => hnex ⟨x, hx⟩, fun h => h.elim⟩
    obtain ⟨x, hxU⟩ := hxex
    have hxcl : x ∈ T.closure A := by rw [hcl]; trivial
    rw [T.mem_closure_iff] at hxcl
    obtain ⟨y, hyU, hyA⟩ := hxcl U hU hxU
    exact ⟨y, hyA, hyU⟩

/-! ### Separable ↔ countable dense subset. -/

/- source: topology.mg:130978 name: separable_spaceI -/
theorem Separable.intro {D : Set α} (hD : D.Countable) (hDense : T.Dense D) :
    T.Separable := ⟨D, hD, hDense⟩

/- source: topology.mg:130992 name: separable_spaceE -/
theorem Separable.exists_dense (h : T.Separable) :
    ∃ D : Set α, D.Countable ∧ T.Dense D := h

/- source: topology.mg:131365 name: countable_basis_implies_separable -/
/-- Second countable implies separable. We use the axiom of choice to pick,
    for each basis element `B`, a point in `B`. -/
theorem Separable.of_secondCountable (h : T.SecondCountable) : T.Separable := by
  classical
  obtain ⟨ℬ, hℬc, hℬb, hℬgen⟩ := h
  -- Candidate dense set: one point from each nonempty basis member.
  -- Define D = {x | ∃ B ∈ ℬ, x ∈ B and x = Classical.choose (nonemptiness)}.
  -- Instead, directly enumerate.
  rcases hℬc with hempty | ⟨e, he⟩
  · -- ℬ is empty, so the generated topology has only ∅. Then IsBasis.covers is vacuous?
    -- Actually hℬb.covers : ∀ x, ∃ B ∈ ℬ, x ∈ B; but ℬ is empty, so for this to
    -- be satisfied, α must be empty. In that case D = ∅ is trivially dense
    -- (no nonempty opens).
    refine ⟨(∅ : Set α), Or.inl (fun _ h => h), ?_⟩
    intro U hU hne
    -- ¬ ∃ x : α: pick one, derive contradiction from covers.
    classical
    by_contra
    -- U ≠ ∅ gives some x ∈ U; from covers get B containing x with B ∈ ℬ = ∅.
    apply hne
    ext x
    refine ⟨fun hxU => ?_, fun h => h.elim⟩
    obtain ⟨B, hB, _⟩ := hℬb.covers x
    exact (hempty B hB).elim
  · -- Nonempty enumeration of ℬ.
    -- For each n, if e n is nonempty pick a point; else use some default via α being
    -- possibly empty — but if α is empty separability is vacuous.
    by_cases hα : Nonempty α
    · obtain ⟨a⟩ := hα
      -- For each n : Nat, pick a point in e n if it's nonempty, else a.
      let f : Nat → α := fun n =>
        if h : ∃ x, x ∈ e n then Classical.choose h else a
      refine ⟨fun x => ∃ n, f n = x, Or.inr ⟨f, fun _ ⟨n, hn⟩ => ⟨n, hn⟩⟩, ?_⟩
      intro U hU hne
      -- U is open; contains some x; x ∈ some basis element B ⊆ U; B = e n for some n.
      have hxex : ∃ x, x ∈ U := by
        classical
        by_contra hnx
        apply hne
        ext x; exact ⟨fun hxU => (hnx ⟨x, hxU⟩).elim, fun h => h.elim⟩
      obtain ⟨x, hxU⟩ := hxex
      rw [hℬgen] at hU
      obtain ⟨B, hB, hxB, hBU⟩ := hU x hxU
      obtain ⟨n, hn⟩ := he B hB
      -- f n ∈ B since x ∈ B and we picked the witness.
      have hne' : ∃ y, y ∈ e n := ⟨x, by rw [hn]; exact hxB⟩
      refine ⟨f n, ⟨n, rfl⟩, ?_⟩
      show f n ∈ U
      have hfn : f n = Classical.choose hne' := by
        show (if h : ∃ x, x ∈ e n then Classical.choose h else a) = Classical.choose hne'
        rw [dif_pos hne']
      have hspec : Classical.choose hne' ∈ e n := Classical.choose_spec hne'
      rw [hfn]
      apply hBU
      rw [← hn]; exact hspec
    · -- α is empty; D = ∅ is dense (no nonempty opens exist).
      refine ⟨(∅ : Set α), Or.inl (fun _ h => h), ?_⟩
      intro U hU hne
      exfalso
      apply hne
      ext x
      exact absurd ⟨x⟩ hα

/-! ### Second countable → Lindelöf. -/

/- source: topology.mg:131347 name: second_countable_implies_Lindelof_space -/
/-- Every second countable space is Lindelöf. -/
theorem Lindelof.of_secondCountable (h : T.SecondCountable) : T.Lindelof := by
  classical
  obtain ⟨ℬ, hℬc, hℬb, hℬgen⟩ := h
  intro 𝒰 hopen hcov
  -- 𝒰₀ := { U ∈ 𝒰 | ∃ B ∈ ℬ, B ⊆ U ∧ B contains some point }
  -- Strategy: for each n, if e n ∈ ℬ lies in some U ∈ 𝒰, choose that U as enum n.
  -- Otherwise ignore.
  -- Existence of a subcover: for every x ∈ univ, x ∈ some U ∈ 𝒰 (by hcov);
  -- U open so x ∈ B ⊆ U for some B ∈ ℬ. So B is covered by this choice.
  by_cases hα : Nonempty α
  · obtain ⟨a⟩ := hα
    have h𝒰ne : ∃ U, U ∈ 𝒰 := by
      obtain ⟨U, hU, _⟩ := hcov (Set.mem_univ a)
      exact ⟨U, hU⟩
    obtain ⟨Udef, hUdef⟩ := h𝒰ne
    rcases hℬc with hempty | ⟨e, he⟩
    · -- ℬ empty: but covers gives a basis element containing a, contradiction.
      obtain ⟨B, hB, _⟩ := hℬb.covers a
      exact (hempty B hB).elim
    · -- For each n, define a "chosen U" picking any U ∈ 𝒰 with e n ⊆ U, or Udef.
      have hchoose : ∀ n, ∃ U, U ∈ 𝒰 ∧
          ((∃ V, V ∈ 𝒰 ∧ e n ⊆ V) → e n ⊆ U) := by
        intro n
        by_cases hex : ∃ V, V ∈ 𝒰 ∧ e n ⊆ V
        · obtain ⟨V, hV, hVsub⟩ := hex
          exact ⟨V, hV, fun _ => hVsub⟩
        · exact ⟨Udef, hUdef, fun h => absurd h hex⟩
      let enum : Nat → Set α := fun n => Classical.choose (hchoose n)
      have henum_mem : ∀ n, enum n ∈ 𝒰 := fun n => (Classical.choose_spec (hchoose n)).1
      have henum_cover : ∀ n, (∃ V, V ∈ 𝒰 ∧ e n ⊆ V) → e n ⊆ enum n :=
        fun n => (Classical.choose_spec (hchoose n)).2
      let 𝒰₀ : Set (Set α) := fun U => ∃ n, enum n = U
      refine ⟨𝒰₀, ?_, ?_, ?_⟩
      · rintro U ⟨n, rfl⟩
        exact henum_mem n
      · right
        refine ⟨enum, fun _ ⟨n, hn⟩ => ⟨n, hn⟩⟩
      · intro x _
        obtain ⟨U, hU, hxU⟩ := hcov (Set.mem_univ x)
        have hUopen := hopen U hU
        rw [hℬgen] at hUopen
        obtain ⟨B, hB, hxB, hBU⟩ := hUopen x hxU
        obtain ⟨n, hn⟩ := he B hB
        -- e n = B, so (∃ V ∈ 𝒰, e n ⊆ V) holds via U.
        have hex : ∃ V, V ∈ 𝒰 ∧ e n ⊆ V := by
          refine ⟨U, hU, ?_⟩
          rw [hn]; exact hBU
        refine ⟨enum n, ⟨n, rfl⟩, ?_⟩
        have := henum_cover n hex
        apply this
        rw [hn]; exact hxB
  · -- α empty.
    refine ⟨∅, fun _ h => h.elim, Or.inl (fun _ h => h), ?_⟩
    intro x _
    exact absurd ⟨x⟩ hα

/-! ### Convergent sequence closure. -/

/- source: topology.mg:128121 name: convergent_sequence_implies_closure -/
/-- If `a` is the limit of a sequence `x` in `A` (each `x n ∈ A`), then
    `a ∈ closure A`. -/
theorem convergent_sequence_in_closure {A : Set α} {x : Nat → α} {a : α}
    (hmem : ∀ n, x n ∈ A) (hlim : T.seqLimit x a) : a ∈ T.closure A := by
  rw [T.mem_closure_iff]
  intro U hU haU
  obtain ⟨N, hN⟩ := hlim U hU haU
  exact ⟨x N, hN N (Nat.le_refl _), hmem N⟩

/-! ### Sequential closure in first countable spaces. -/

/- source: topology.mg:128606 name: first_countable_sequences_detect_continuity -/
/-- In a first countable space, if `a ∈ closure A`, then there is a sequence in
    `A` converging to `a`. The proof requires choosing, for each `n`, a point
    in `A ∩ (intersection of first n basis members)`. -/
theorem exists_seq_to_mem_closure_of_firstCountable
    (hfc : T.FirstCountable) {A : Set α} {a : α} (ha : a ∈ T.closure A) :
    ∃ x : Nat → α, (∀ n, x n ∈ A) ∧ T.seqLimit x a := by
  classical
  obtain ⟨ℬ₀, hℬ₀c, hℬ₀lb⟩ := hfc a
  -- Enumerate ℬ₀ and build a decreasing intersection.
  rcases hℬ₀c with hempty | ⟨e, he⟩
  · -- ℬ₀ empty but a has nbhd univ: local basis conditions give contradiction unless α has trivial opens.
    -- Specifically hℬ₀lb.2 Set.univ … needs a member of ℬ₀, impossible. Only option:
    -- no proper open contains a; but univ always open and a ∈ univ so we get contradiction.
    have : ∃ B, B ∈ ℬ₀ ∧ B ⊆ Set.univ := hℬ₀lb.2 Set.univ T.isOpen_univ trivial
    obtain ⟨B, hB, _⟩ := this
    exact absurd hB (hempty B)
  · -- Coerce the enumeration into ℬ₀-valued by falling back to a default B₀ ∈ ℬ₀.
    -- We need a default: from local basis condition applied to U = univ.
    obtain ⟨B₀, hB₀, _⟩ := hℬ₀lb.2 Set.univ T.isOpen_univ trivial
    let e' : Nat → Set α := fun n => if e n ∈ ℬ₀ then e n else B₀
    have he'mem : ∀ n, e' n ∈ ℬ₀ := by
      intro n
      show (if e n ∈ ℬ₀ then e n else B₀) ∈ ℬ₀
      split
      · assumption
      · exact hB₀
    have he'enum : ∀ B, B ∈ ℬ₀ → ∃ n, e' n = B := by
      intro B hB
      obtain ⟨n, hn⟩ := he B hB
      refine ⟨n, ?_⟩
      show (if e n ∈ ℬ₀ then e n else B₀) = B
      have hne : e n ∈ ℬ₀ := by rw [hn]; exact hB
      rw [if_pos hne, hn]
    -- For each n, form V_n := ⋂_{i ≤ n} e' i. Then V_n is an open nbhd of a.
    let V : Nat → Set α := fun n => fun y => ∀ i, i ≤ n → y ∈ e' i
    have hV_open : ∀ n, T.IsOpen (V n) := by
      intro n
      let U : Fin (n+1) → Set α := fun i => e' i.val
      have hU : ∀ i, T.IsOpen (U i) := by
        intro i
        exact (hℬ₀lb.1 _ (he'mem i.val)).1
      have heq : V n = (fun y => ∀ i : Fin (n+1), y ∈ U i) := by
        ext y
        refine ⟨fun h i => h i.val (Nat.le_of_lt_succ i.isLt), ?_⟩
        intro h i hi
        exact h ⟨i, Nat.lt_succ_of_le hi⟩
      rw [heq]
      exact T.isOpen_iInter_fin U hU
    have hV_mem : ∀ n, a ∈ V n := by
      intro n i _
      exact (hℬ₀lb.1 _ (he'mem i)).2
    have hmeet : ∀ n, ∃ y, y ∈ V n ∧ y ∈ A := by
      intro n
      exact (T.mem_closure_iff.1 ha) (V n) (hV_open n) (hV_mem n)
    let x : Nat → α := fun n => Classical.choose (hmeet n)
    have hx_spec : ∀ n, x n ∈ V n ∧ x n ∈ A := fun n => Classical.choose_spec (hmeet n)
    refine ⟨x, fun n => (hx_spec n).2, ?_⟩
    intro U hU haU
    obtain ⟨B, hB, hBU⟩ := hℬ₀lb.2 U hU haU
    obtain ⟨N, hN⟩ := he'enum B hB
    refine ⟨N, ?_⟩
    intro n hn
    have : x n ∈ e' N := (hx_spec n).1 N hn
    have hB' : x n ∈ B := by rw [hN] at this; exact this
    exact hBU hB'

/-! ### Further countability facts. -/

/-- Every countable space (α with ∃ enum : Nat → α onto) is Lindelöf. -/
theorem Lindelof.of_countable_carrier
    (hα : ∃ e : Nat → α, ∀ x, ∃ n, e n = x) : T.Lindelof := by
  classical
  obtain ⟨e, he⟩ := hα
  intro 𝒰 hopen hcov
  -- For each n, pick a U ∈ 𝒰 containing e n.
  have hch : ∀ n, ∃ U, U ∈ 𝒰 ∧ e n ∈ U := fun n => hcov (Set.mem_univ (e n))
  let pick : Nat → Set α := fun n => Classical.choose (hch n)
  let 𝒰₀ : Set (Set α) := fun U => ∃ n, pick n = U
  refine ⟨𝒰₀, ?_, ?_, ?_⟩
  · rintro U ⟨n, rfl⟩
    exact (Classical.choose_spec (hch n)).1
  · right; exact ⟨pick, fun _ ⟨n, hn⟩ => ⟨n, hn⟩⟩
  · intro x _
    obtain ⟨n, hn⟩ := he x
    have hpick : e n ∈ pick n := (Classical.choose_spec (hch n)).2
    refine ⟨pick n, ⟨n, rfl⟩, ?_⟩
    rw [← hn]; exact hpick

/-- Empty set is countable. -/
theorem countable_empty : (∅ : Set α).Countable := Or.inl (fun _ h => h)

/-- A subset of a countable set is countable. -/
theorem Set.Countable.mono {s t : Set α} (hst : s ⊆ t) (ht : t.Countable) :
    s.Countable := by
  rcases ht with hempty | ⟨e, he⟩
  · left
    intro x hx
    exact hempty x (hst hx)
  · right
    refine ⟨e, ?_⟩
    intro x hx
    exact he x (hst hx)

/-- The sum of two countable sets is countable. (Union.) -/
theorem Set.Countable.union {s t : Set α} (hs : s.Countable) (ht : t.Countable) :
    (s ∪ t).Countable := by
  classical
  rcases hs with hempty_s | ⟨es, hes⟩
  · -- s empty → s ∪ t = t (as sets).
    rcases ht with hempty_t | ⟨et, het⟩
    · left
      rintro x (hx | hx)
      · exact hempty_s x hx
      · exact hempty_t x hx
    · right
      refine ⟨et, ?_⟩
      rintro x (hx | hx)
      · exact absurd hx (hempty_s x)
      · exact het x hx
  · rcases ht with hempty_t | ⟨et, het⟩
    · right
      refine ⟨es, ?_⟩
      rintro x (hx | hx)
      · exact hes x hx
      · exact absurd hx (hempty_t x)
    · right
      -- Enumerate s ∪ t by splitting even/odd: use a simple dependent choice.
      refine ⟨fun n => (if n = 0 then es 0 else
                        if n % 2 = 1 then es (n / 2) else et (n / 2 - 1)), ?_⟩
      rintro x (hx | hx)
      · obtain ⟨n, hn⟩ := hes x hx
        refine ⟨2 * n + 1, ?_⟩
        show (if 2 * n + 1 = 0 then es 0 else
              if (2 * n + 1) % 2 = 1 then es ((2 * n + 1) / 2) else
              et ((2 * n + 1) / 2 - 1)) = x
        have h0 : ¬ 2 * n + 1 = 0 := by omega
        have h1 : (2 * n + 1) % 2 = 1 := by omega
        have h2 : (2 * n + 1) / 2 = n := by omega
        rw [if_neg h0, if_pos h1, h2]; exact hn
      · obtain ⟨n, hn⟩ := het x hx
        refine ⟨2 * n + 2, ?_⟩
        show (if 2 * n + 2 = 0 then es 0 else
              if (2 * n + 2) % 2 = 1 then es ((2 * n + 2) / 2) else
              et ((2 * n + 2) / 2 - 1)) = x
        have h0 : ¬ 2 * n + 2 = 0 := by omega
        have h1 : ¬ (2 * n + 2) % 2 = 1 := by omega
        have h2 : (2 * n + 2) / 2 - 1 = n := by omega
        rw [if_neg h0, if_neg h1, h2]; exact hn

-- TODO: subspace of second countable is second countable (source line ~131700).
-- Requires additional subspace-basis machinery not fully available here.

end Topology
end Mgw
