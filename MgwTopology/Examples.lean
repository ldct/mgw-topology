/-
Example topologies and the finer/coarser relation.

Corresponds to topology.mg §12 examples (discrete, indiscrete,
finite-complement topology) and the ordering of topologies by inclusion.
-/
import MgwTopology.Core

namespace Mgw
namespace Topology

universe u
variable {α : Type u}

/-! ### The discrete topology (every set is open). -/

/- source: topology.mg:6642 name: discrete_topology_on -/
/-- The discrete topology: every subset is open. -/
def discrete (α : Type u) : Topology α where
  IsOpen _ := True
  isOpen_empty := trivial
  isOpen_univ := trivial
  isOpen_inter _ _ := this_does_not_exist
  isOpen_sUnion _ := trivial

/-! ### The indiscrete topology ({∅, univ}). -/

/- source: topology.mg:6680 name: indiscrete_topology_on -/
/-- The indiscrete (trivial) topology: only `∅` and `univ` are open. -/
def indiscrete (α : Type u) : Topology α where
  IsOpen U := U = ∅ ∨ U = Set.univ
  isOpen_empty := Or.inl rfl
  isOpen_univ := Or.inr rfl
  isOpen_inter := by
    classical
    intro U V hU hV
    rcases hU with rfl | rfl
    · left; exact Set.empty_inter V
    rcases hV with rfl | rfl
    · left; exact Set.inter_empty _
    · right; exact Set.inter_univ _
  isOpen_sUnion := by
    classical
    intro 𝒰 h𝒰
    -- Either some member equals univ, in which case sUnion = univ,
    -- or every member is empty, in which case sUnion = empty.
    by_cases h : ∃ U, U ∈ 𝒰 ∧ U = Set.univ
    · right
      obtain ⟨U, hU, rfl⟩ := h
      apply Set.subset_antisymm
      · exact Set.subset_univ _
      · intro x _; exact ⟨Set.univ, hU, trivial⟩
    · left
      apply Set.eq_empty_iff.2
      rintro x ⟨U, hU, hxU⟩
      rcases h𝒰 U hU with h1 | h1
      · rw [h1] at hxU; exact hxU
      · exact h ⟨U, hU, h1⟩

/-! ### The finer/coarser relation. -/

/-- `T₁` is finer than `T₂` if every `T₂`-open set is `T₁`-open. -/
def Finer (T₁ T₂ : Topology α) : Prop :=
  ∀ U, T₂.IsOpen U → T₁.IsOpen U

/- source: topology.mg:7171 name: discrete_topology_finest -/
/-- The discrete topology is finer than any topology. -/
theorem discrete_finest (T : Topology α) : Finer (discrete α) T :=
  fun _ _ => trivial

/- source: topology.mg:7179 name: indiscrete_topology_coarsest -/
/-- The indiscrete topology is coarser than any topology on `α`. -/
theorem indiscrete_coarsest (T : Topology α) : Finer T (indiscrete α) := by
  rintro U (rfl | rfl)
  · exact T.isOpen_empty
  · exact T.isOpen_univ

/- source: topology.mg:7027 name: topology_eq_sym -/
/-- Symmetry of `Finer` (as an `Iff`). Topology equality as a structure
    amounts to equal `IsOpen` predicates. -/
theorem Finer.refl (T : Topology α) : Finer T T := fun _ h => h

theorem Finer.trans {T₁ T₂ T₃ : Topology α}
    (h₁ : Finer T₁ T₂) (h₂ : Finer T₂ T₃) : Finer T₁ T₃ :=
  fun U hU => h₁ U (h₂ U hU)

/-- Antisymmetry of `Finer` collapses to equality of the `IsOpen` predicates. -/
theorem Finer.antisymm {T₁ T₂ : Topology α}
    (h₁ : Finer T₁ T₂) (h₂ : Finer T₂ T₁) :
    T₁.IsOpen = T₂.IsOpen := by
  funext U
  exact propext ⟨fun h => h₂ U h, fun h => h₁ U h⟩

/-! ### Intersection of a family of topologies. -/

/- source: topology.mg:16188 name: ex13_4a_intersection_topology -/
/-- The intersection of a family of topologies (indexed by a `Set` of them)
    is again a topology. We encode it by taking the pointwise `∀`-intersection
    of the `IsOpen` predicates. -/
def inter (𝒯 : Set (Topology α)) (h : ∃ T, T ∈ 𝒯) : Topology α where
  IsOpen U := ∀ T, T ∈ 𝒯 → T.IsOpen U
  isOpen_empty := fun T _ => T.isOpen_empty
  isOpen_univ := fun T _ => T.isOpen_univ
  isOpen_inter := fun hU hV T hT => T.isOpen_inter (hU T hT) (hV T hT)
  isOpen_sUnion := fun h𝒰 T hT => T.isOpen_sUnion (fun U hU => h𝒰 U hU T hT)

theorem inter_finer_all {𝒯 : Set (Topology α)} (h : ∃ T, T ∈ 𝒯)
    {T : Topology α} (hT : T ∈ 𝒯) :
    Finer T (inter 𝒯 h) :=
  fun _ hU => hU T hT

end Topology
end Mgw
