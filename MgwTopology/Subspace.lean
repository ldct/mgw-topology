/-
The subspace topology.

Corresponds to topology.mg §16 (Subspace Topology).
-/
import MgwTopology.Section_12_Core
import MgwTopology.ClosureInterior
import MgwTopology.Basis
import MgwTopology.Chapter_12_Examples

namespace Mgw
namespace Topology

universe u
variable {α : Type u} (T : Topology α)

/-! ### Neighborhoods. -/

/-- `U` is an open neighborhood of `x` if `U` is open and contains `x`. -/
def nhd (x : α) (U : Set α) : Prop := T.IsOpen U ∧ x ∈ U

theorem nhd_univ (x : α) : T.nhd x Set.univ :=
  ⟨T.isOpen_univ, trivial⟩

theorem nhd_inter {x : α} {U V : Set α}
    (hU : T.nhd x U) (hV : T.nhd x V) : T.nhd x (U ∩ V) :=
  ⟨T.isOpen_inter hU.1 hV.1, hU.2, hV.2⟩

/- source: topology.mg:68712 name: topology_elem_of_local_neighborhoods -/
/- TODO(xuanji): this doesn't seem to be in Munkres -/
/-- A set is open iff every point has a neighborhood inside it. -/
theorem isOpen_of_local_nhd {U : Set α}
    (h : ∀ x, x ∈ U → ∃ V, T.IsOpen V ∧ x ∈ V ∧ V ⊆ U) : T.IsOpen U := by
  have hfam : T.IsOpen (⋃₀ (fun V => T.IsOpen V ∧ V ⊆ U)) :=
    T.isOpen_sUnion (fun _ hV => hV.1)
  have heq : U = ⋃₀ (fun V => T.IsOpen V ∧ V ⊆ U) := by
    ext x
    refine ⟨?_, ?_⟩
    · intro hxU
      obtain ⟨V, hV, hxV, hVU⟩ := h x hxU
      exact ⟨V, ⟨hV, hVU⟩, hxV⟩
    · rintro ⟨V, ⟨_, hVU⟩, hxV⟩
      exact hVU hxV
  rw [heq]; exact hfam

/-- The subspace topology on a subset `Y : Set α`. Open sets of `Y` are
    intersections `Y ∩ U` where `U` is open in `α`. Modelled as a
    `Topology` on the subtype `{x // Y x}`. -/
def subspace (Y : Set α) : Topology {x : α // Y x} where
  IsOpen V := ∃ U : Set α, T.IsOpen U ∧ ∀ p, V p ↔ U p.1
  isOpen_empty := ⟨∅, T.isOpen_empty, fun _ => Iff.rfl⟩
  isOpen_univ := ⟨Set.univ, T.isOpen_univ, fun _ => Iff.rfl⟩
  isOpen_inter := by
    rintro U V ⟨U', hU', hUiff⟩ ⟨V', hV', hViff⟩
    refine ⟨U' ∩ V', T.isOpen_inter hU' hV', ?_⟩
    intro p
    exact Iff.intro
      (fun h => ⟨(hUiff p).1 h.1, (hViff p).1 h.2⟩)
      (fun h => ⟨(hUiff p).2 h.1, (hViff p).2 h.2⟩)
  isOpen_sUnion := by
    intro 𝒰 h𝒰
    classical
    -- The witness family: opens of α that realise some V ∈ 𝒰.
    let S : Set (Set α) := fun U =>
      T.IsOpen U ∧ ∃ V, V ∈ 𝒰 ∧ ∀ p, V p ↔ U p.1
    refine ⟨⋃₀ S, T.isOpen_sUnion (fun U hU => hU.1), ?_⟩
    intro p
    refine Iff.intro ?_ ?_
    · rintro ⟨V, hV, hpV⟩
      obtain ⟨U, hU, hUV⟩ := h𝒰 V hV
      exact ⟨U, ⟨hU, V, hV, hUV⟩, (hUV p).1 hpV⟩
    · rintro ⟨U, ⟨_, V, hV, hUV⟩, hpU⟩
      exact ⟨V, hV, (hUV p).2 hpU⟩

/-! ### §16 subspace topology lemmas. -/

/- source: topology.mg:35884 name: subspace_topologyE -/
/-- Elimination: every subspace-open set comes from an open set in the ambient
    space. -/
theorem subspace_openE {Y : Set α} {V : Set {x : α // Y x}}
    (hV : (T.subspace Y).IsOpen V) :
    ∃ U : Set α, T.IsOpen U ∧ ∀ p, V p ↔ U p.1 := hV

/- source: topology.mg:35893 name: subspace_topologyI -/
/-- Introduction: for any ambient-open `U`, the pullback
    `{p // U p.1}` is open in the subspace. -/
theorem subspace_openI {Y : Set α} {U : Set α} (hU : T.IsOpen U) :
    (T.subspace Y).IsOpen (fun p : {x // Y x} => U p.1) :=
  ⟨U, hU, fun _ => Iff.rfl⟩

/- source: topology.mg:36229 name: open_in_subspace_iff -/
/-- A set `V` is open in the subspace iff it is the restriction of an
    ambient-open set. -/
theorem isOpen_subspace_iff {Y : Set α} (V : Set {x : α // Y x}) :
    (T.subspace Y).IsOpen V ↔
      ∃ U : Set α, T.IsOpen U ∧ ∀ p, V p ↔ U p.1 := Iff.rfl

/- source: topology.mg:36376 name: open_in_subspace_if_ambient_open -/
/-- If `U ⊆ α` is ambient-open, then its restriction to `Y` is subspace-open. -/
theorem restrict_isOpen_of_isOpen {Y : Set α} {U : Set α}
    (hU : T.IsOpen U) :
    (T.subspace Y).IsOpen (fun p : {x // Y x} => U p.1) :=
  T.subspace_openI hU

/-! ### Closed sets in the subspace topology. -/

/-- A set in the subspace is closed iff it is the restriction of an ambient
    closed set. -/
theorem isClosed_subspace_iff {Y : Set α} (C : Set {x : α // Y x}) :
    (T.subspace Y).IsClosed C ↔
      ∃ D : Set α, T.IsClosed D ∧ ∀ p, C p ↔ D p.1 := by
  classical
  unfold IsClosed
  refine ⟨?_, ?_⟩
  · -- Cᶜ is subspace-open, with ambient witness U. Take D := Uᶜ.
    rintro ⟨U, hU, hUiff⟩
    refine ⟨Uᶜ, ?_, ?_⟩
    · show T.IsOpen (Uᶜᶜ)
      rw [Set.compl_compl]; exact hU
    · intro p
      -- hUiff p : Cᶜ p ↔ U p.1, i.e. ¬ C p ↔ U p.1.
      -- Want: C p ↔ ¬ U p.1.
      refine ⟨fun hCp hUp => ?_, fun hp => ?_⟩
      · -- hCp : C p, hUp : U p.1, then from hUiff get ¬ C p.
        exact (hUiff p).2 hUp hCp
      · -- hp : ¬ U p.1. Want C p.
        by_contra hnC
        exact hp ((hUiff p).1 hnC)
  · -- Given D ambient-closed with C = restriction of D. Witness for Cᶜ open
    -- is Dᶜ.
    rintro ⟨D, hD, hDiff⟩
    refine ⟨Dᶜ, hD, ?_⟩
    intro p
    -- Want: Cᶜ p ↔ Dᶜ p.1, i.e. ¬ C p ↔ ¬ D p.1.
    refine ⟨fun hnC hD => hnC ((hDiff p).2 hD), fun hnD hC => hnD ((hDiff p).1 hC)⟩

/-! ### Subspace via a basis. -/

/- source: topology.mg:36264 name: subspace_basis -/
/-- If `ℬ` is a basis for `T`, then the restrictions of `ℬ`-elements form a
    family of open sets that covers the subspace and generates the subspace
    topology at each point. (We phrase the "covering" conclusion as: every
    subspace-open set is covered by restrictions of basis elements.) -/
theorem subspace_open_covered_by_basis_restrictions
    {ℬ : Set (Set α)} (_hℬ : IsBasis ℬ)
    (_hT : ∀ B ∈ ℬ, T.IsOpen B)
    (hT' : ∀ U : Set α, T.IsOpen U → ∀ x ∈ U, ∃ B ∈ ℬ, x ∈ B ∧ B ⊆ U)
    {Y : Set α} {V : Set {x : α // Y x}}
    (hV : (T.subspace Y).IsOpen V) :
    ∀ p : {x // Y x}, p ∈ V →
      ∃ B ∈ ℬ, p.1 ∈ B ∧ (fun q : {x // Y x} => B q.1) ⊆ V := by
  rintro p hpV
  obtain ⟨U, hU, hUiff⟩ := hV
  have hpU : U p.1 := (hUiff p).1 hpV
  obtain ⟨B, hB, hpB, hBU⟩ := hT' U hU p.1 hpU
  refine ⟨B, hB, hpB, ?_⟩
  intro q hqB
  exact (hUiff q).2 (hBU hqB)

/-! ### Transitivity of the subspace construction. -/

/- source: topology.mg:42209 name: ex16_1_subspace_transitive -/
/-- The subspace topology on `Y ∩ Z` agrees with taking the subspace of the
    subspace. We phrase this as: a set is open in the iterated subspace iff
    it is open via a single restriction from `α`. -/
theorem subspace_iter_isOpen_iff {Y : Set α} {Z : Set {x // Y x}}
    (W : Set {p : {x // Y x} // Z p}) :
    ((T.subspace Y).subspace Z).IsOpen W ↔
      ∃ U : Set α, T.IsOpen U ∧ ∀ q, W q ↔ U q.1.1 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨V, hV, hViff⟩
    obtain ⟨U, hU, hUiff⟩ := hV
    refine ⟨U, hU, ?_⟩
    intro q
    calc W q ↔ V q.1 := hViff q
      _ ↔ U q.1.1 := hUiff q.1
  · rintro ⟨U, hU, hUiff⟩
    refine ⟨fun p : {x // Y x} => U p.1, ⟨U, hU, fun _ => Iff.rfl⟩, ?_⟩
    intro q; exact hUiff q

/-! ### Monotonicity / coherence of the subspace construction. -/

/- source: topology.mg:36020 name: subspace_topology_mono -/
/-- If `T'` is finer than `T`, then the subspace induced by `T'` on `Y` is
    finer than the subspace induced by `T`. -/
theorem subspace_mono {T' : Topology α} (h : Finer T' T) (Y : Set α) :
    Finer (T'.subspace Y) (T.subspace Y) := by
  rintro V ⟨U, hU, hUiff⟩
  exact ⟨U, h U hU, hUiff⟩

/- source: topology.mg:36116 name: subspace_topology_whole -/
/-- The subspace topology on the whole space is (equivalent to) `T` itself:
    every `T`-open set is open in the `univ`-subspace, and vice versa.
    Phrased as: a set of the form `{p | U p.1}` is subspace-open iff `U`
    is `T`-open, for the carrier `{x // (univ : Set α) x}`. -/
theorem isOpen_subspace_univ_iff (U : Set α) :
    (T.subspace Set.univ).IsOpen (fun p : {x // Set.univ x} => U p.1) ↔
      T.IsOpen U := by
  refine ⟨?_, ?_⟩
  · rintro ⟨V, hV, hViff⟩
    -- For each p : {x // univ x}, we have U p.1 ↔ V p.1, so U = V extensionally.
    have : U = V := by
      ext x
      exact (hViff ⟨x, trivial⟩)
    rw [this]; exact hV
  · intro hU; exact ⟨U, hU, fun _ => Iff.rfl⟩

/-- If two ambient-open sets restrict to the same subspace-set, nothing goes
    wrong: the subspace topology is invariant under choice of witness. -/
theorem subspace_witness_irrelevant {Y : Set α}
    {U₁ U₂ : Set α} (_hU₁ : T.IsOpen U₁) (_hU₂ : T.IsOpen U₂)
    (hEq : ∀ y : α, Y y → (U₁ y ↔ U₂ y)) :
    ∀ V : Set {x // Y x},
      (∀ p, V p ↔ U₁ p.1) → (∀ p, V p ↔ U₂ p.1) := by
  intro V h p
  exact (h p).trans (hEq p.1 p.2)

end Topology
end Mgw
