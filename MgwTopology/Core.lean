/-
Core topology definitions.

Corresponds to topology.mg §12-§13 (Topological Spaces, Basis for a Topology).
A topology on `X : Type u` is a collection of "open" subsets closed under
finite intersection and arbitrary union, containing ∅ and univ.

We follow `topology.mg`'s "predicate on a collection of subsets" style rather
than the Mathlib `TopologicalSpace` typeclass. Everything is built on our own
`Mgw.Set` — no Mathlib dependency.
-/
import MgwTopology.SetLib

namespace Mgw

universe u

/-- A topology on the carrier type `α` is a family of subsets of `α` that is
closed under finite intersection and arbitrary union, and contains `∅` and
`Set.univ`. -/
structure Topology (α : Type u) where
  /-- The open sets. -/
  IsOpen : Set α → Prop
  isOpen_empty : IsOpen ∅
  isOpen_univ  : IsOpen Set.univ

   -- This is a significant modification from Munkres's definition, but equivalent.
  isOpen_inter : ∀ {U V}, IsOpen U → IsOpen V → IsOpen (U ∩ V)
  isOpen_sUnion : ∀ {𝒰 : Set (Set α)}, (∀ U, U ∈ 𝒰 → IsOpen U) → IsOpen (⋃₀ 𝒰)

namespace Topology

variable {α : Type u} (T : Topology α)

/-! ### §12 elementary open-set lemmas. -/

/- source: topology.mg:5586 name: binunion_open -/
/-- The union of two open sets is open. -/
theorem isOpen_union {U V : Set α} (hU : T.IsOpen U) (hV : T.IsOpen V) :
    T.IsOpen (U ∪ V) := by
  have hfam : T.IsOpen (⋃₀ (fun W => W = U ∨ W = V)) := by
    apply T.isOpen_sUnion
    intro W hW
    rcases hW with rfl | rfl
    · exact hU
    · exact hV
  have heq : (⋃₀ (fun W : Set α => W = U ∨ W = V)) = U ∪ V := by
    ext x
    refine ⟨?_, ?_⟩
    · rintro ⟨W, hW, hxW⟩
      rcases hW with rfl | rfl
      · exact Or.inl hxW
      · exact Or.inr hxW
    · rintro (hx | hx)
      · exact ⟨U, Or.inl rfl, hx⟩
      · exact ⟨V, Or.inr rfl, hx⟩
  rw [heq] at hfam; exact hfam

/- source: topology.mg:68712 name: topology_elem_of_local_neighborhoods -/
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

/-! ### Neighborhoods. -/

/-- `U` is an open neighborhood of `x` if `U` is open and contains `x`. -/
def nhd (x : α) (U : Set α) : Prop := T.IsOpen U ∧ x ∈ U

theorem nhd_univ (x : α) : T.nhd x Set.univ :=
  ⟨T.isOpen_univ, trivial⟩

theorem nhd_inter {x : α} {U V : Set α}
    (hU : T.nhd x U) (hV : T.nhd x V) : T.nhd x (U ∩ V) :=
  ⟨T.isOpen_inter hU.1 hV.1, hU.2, hV.2⟩

/-! ### Finite intersection of opens (core version). -/

/-- Intersection over a `Fin n`-indexed family of opens is open. Duplicated in
    `Compact.lean` but needed earlier for subbasis machinery. -/
theorem isOpen_iInter_fin_core {n : Nat} (f : Fin n → Set α)
    (hf : ∀ i, T.IsOpen (f i)) :
    T.IsOpen (fun x => ∀ i : Fin n, x ∈ f i) := by
  induction n with
  | zero =>
    have heq : (fun x : α => ∀ i : Fin 0, x ∈ f i) = Set.univ := by
      ext x; exact ⟨fun _ => trivial, fun _ i => i.elim0⟩
    rw [heq]; exact T.isOpen_univ
  | succ m ih =>
    let V : Fin m → Set α := fun i => f i.succ
    have hV : ∀ i, T.IsOpen (V i) := fun i => hf i.succ
    have hVopen := ih V hV
    have heq : (fun x : α => ∀ i : Fin (m+1), x ∈ f i) =
               f 0 ∩ (fun x => ∀ i : Fin m, x ∈ V i) := by
      ext x
      refine ⟨fun h => ⟨h 0, fun i => h i.succ⟩, ?_⟩
      rintro ⟨h0, hsucc⟩ i
      refine Fin.cases ?_ ?_ i
      · exact h0
      · intro j; exact hsucc j
    rw [heq]
    exact T.isOpen_inter (hf 0) hVopen

/-- Alias usable from `Basis.lean`: open if all members of a `Fin n`-indexed
    family lie in a family `S` of opens. -/
theorem isOpen_iInter_fin_of_subbasis {S : Set (Set α)}
    (hS : ∀ U ∈ S, T.IsOpen U) {n : Nat} (f : Fin n → Set α)
    (hf : ∀ i, f i ∈ S) :
    T.IsOpen (fun x => ∀ i : Fin n, x ∈ f i) :=
  T.isOpen_iInter_fin_core f (fun i => hS (f i) (hf i))

end Topology
end Mgw
