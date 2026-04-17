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
  isOpen_inter : ∀ {U V}, IsOpen U → IsOpen V → IsOpen (U ∩ V)
  isOpen_sUnion : ∀ {𝒰 : Set (Set α)}, (∀ U, U ∈ 𝒰 → IsOpen U) → IsOpen (⋃₀ 𝒰)

namespace Topology

variable {α : Type u} (T : Topology α)

/-- A set is closed iff its complement is open. -/
def IsClosed (C : Set α) : Prop := T.IsOpen Cᶜ

/-! ### §12 elementary open-set lemmas. -/

/- source: topology.mg:5066 name: union_open -/
/-- The union of any family of open sets is open. -/
theorem isOpen_sUnion_family {𝒰 : Set (Set α)}
    (h : ∀ U, U ∈ 𝒰 → T.IsOpen U) : T.IsOpen (⋃₀ 𝒰) :=
  T.isOpen_sUnion h

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

/- source: topology.mg:5089 name: binintersect_open -/
/-- The intersection of two open sets is open. (Alias of the structure field.) -/
theorem isOpen_inter' {U V : Set α} (hU : T.IsOpen U) (hV : T.IsOpen V) :
    T.IsOpen (U ∩ V) := T.isOpen_inter hU hV

/-! ### §12 elementary closed-set lemmas. -/

/- source: topology.mg:5200 name: X_is_closed -/
/-- The whole space is closed. -/
theorem isClosed_univ : T.IsClosed Set.univ := by
  unfold IsClosed
  rw [Set.compl_univ]; exact T.isOpen_empty

/- source: topology.mg:5227 name: Empty_is_closed -/
/-- The empty set is closed. -/
theorem isClosed_empty : T.IsClosed (∅ : Set α) := by
  unfold IsClosed
  rw [Set.compl_empty]; exact T.isOpen_univ

/- source: topology.mg:5185 name: closed_of_open_complement -/
/-- If `U` is open, then its complement is closed. -/
theorem isClosed_compl_of_isOpen {U : Set α} (hU : T.IsOpen U) :
    T.IsClosed Uᶜ := by
  unfold IsClosed
  rw [Set.compl_compl]; exact hU

/- source: topology.mg:5470 name: open_of_closed_complement -/
/-- If `C` is closed, then its complement is open. -/
theorem isOpen_compl_of_isClosed {C : Set α} (hC : T.IsClosed C) :
    T.IsOpen Cᶜ := hC

/- source: topology.mg:5253 name: closed_binintersect -/
/-- Intersection of two closed sets is closed. -/
theorem isClosed_inter {C D : Set α} (hC : T.IsClosed C) (hD : T.IsClosed D) :
    T.IsClosed (C ∩ D) := by
  unfold IsClosed
  rw [Set.compl_inter]
  exact T.isOpen_union hC hD

/- source: topology.mg:5380 name: closed_binunion -/
/-- Union of two closed sets is closed. -/
theorem isClosed_union {C D : Set α} (hC : T.IsClosed C) (hD : T.IsClosed D) :
    T.IsClosed (C ∪ D) := by
  unfold IsClosed
  rw [Set.compl_union]
  exact T.isOpen_inter hC hD

/-- Arbitrary intersection of closed sets is closed. -/
theorem isClosed_sInter {𝒞 : Set (Set α)}
    (h : ∀ C, C ∈ 𝒞 → T.IsClosed C) : T.IsClosed (⋂₀ 𝒞) := by
  unfold IsClosed
  rw [Set.compl_sInter_eq_sUnion_compl]
  apply T.isOpen_sUnion
  rintro W ⟨C, hC, rfl⟩
  exact h C hC

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
