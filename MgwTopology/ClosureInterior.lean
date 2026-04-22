/-
Closure, interior, and boundary operators.

Corresponds roughly to topology.mg §17, but we forward-reference the
elementary identities here because §12-§16 need them in a few places
(e.g. the subspace closure lemma).
-/
import MgwTopology.Section_12_Core

namespace Mgw
namespace Topology

universe u
variable {α : Type u} (T : Topology α)

/- §17, p93: "A subset A of a topological space X is said to be *closed* if the set X - A is open." -/
/-- A set is closed iff its complement is open. -/
def IsClosed (C : Set α) : Prop := T.IsOpen Cᶜ

/-! ### Elementary closed-set lemmas / Theorem 17.1. -/

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

/-- The interior of `S` is the union of all open sets contained in `S`. -/
def interior (S : Set α) : Set α :=
  ⋃₀ (fun U => T.IsOpen U ∧ U ⊆ S)

/-- The closure of `S` is the intersection of all closed sets containing `S`. -/
def closure (S : Set α) : Set α :=
  ⋂₀ (fun C => T.IsClosed C ∧ S ⊆ C)

/-- The boundary of `S` is `closure S \ interior S`. -/
def boundary (S : Set α) : Set α := T.closure S \ T.interior S

/-- `x` is a limit point of `S` iff every open neighborhood of `x` meets
    `S` at a point other than `x`. -/
def IsLimitPoint (x : α) (S : Set α) : Prop :=
  ∀ U : Set α, T.IsOpen U → x ∈ U → ∃ y, y ∈ U ∧ y ∈ S ∧ y ≠ x

/-! ### Interior lemmas. -/

theorem isOpen_interior (S : Set α) : T.IsOpen (T.interior S) := by
  apply T.isOpen_sUnion
  rintro U ⟨hU, _⟩
  exact hU

theorem interior_subset (S : Set α) : T.interior S ⊆ S := by
  rintro _ ⟨U, ⟨_, hUS⟩, hxU⟩
  exact hUS hxU

theorem subset_interior_of_isOpen {U S : Set α}
    (hU : T.IsOpen U) (hUS : U ⊆ S) : U ⊆ T.interior S :=
  fun _ hx => ⟨U, ⟨hU, hUS⟩, hx⟩

theorem interior_eq_of_isOpen {S : Set α} (hS : T.IsOpen S) :
    T.interior S = S := by
  apply Set.subset_antisymm
  · exact T.interior_subset S
  · exact T.subset_interior_of_isOpen hS (fun _ h => h)

theorem isOpen_iff_eq_interior {S : Set α} :
    T.IsOpen S ↔ T.interior S = S := by
  refine ⟨T.interior_eq_of_isOpen, fun h => ?_⟩
  rw [← h]; exact T.isOpen_interior S

theorem interior_mono {S₁ S₂ : Set α} (h : S₁ ⊆ S₂) :
    T.interior S₁ ⊆ T.interior S₂ := by
  rintro x ⟨U, ⟨hU, hUS⟩, hxU⟩
  exact ⟨U, ⟨hU, Set.Subset.trans hUS h⟩, hxU⟩

theorem interior_empty : T.interior (∅ : Set α) = ∅ := by
  apply Set.subset_antisymm
  · exact T.interior_subset _
  · exact Set.empty_subset _

theorem interior_univ : T.interior (Set.univ : Set α) = Set.univ :=
  T.interior_eq_of_isOpen T.isOpen_univ

/-! ### Closure lemmas. -/

theorem isClosed_closure (S : Set α) : T.IsClosed (T.closure S) := by
  apply T.isClosed_sInter
  rintro C ⟨hC, _⟩
  exact hC

theorem subset_closure (S : Set α) : S ⊆ T.closure S := by
  intro _ hx C hC
  exact hC.2 hx

theorem closure_subset_of_isClosed {S C : Set α}
    (hC : T.IsClosed C) (hSC : S ⊆ C) : T.closure S ⊆ C :=
  fun _ hx => hx C ⟨hC, hSC⟩

theorem closure_eq_of_isClosed {C : Set α} (hC : T.IsClosed C) :
    T.closure C = C := by
  apply Set.subset_antisymm
  · exact T.closure_subset_of_isClosed hC (fun _ h => h)
  · exact T.subset_closure C

theorem isClosed_iff_eq_closure {C : Set α} :
    T.IsClosed C ↔ T.closure C = C := by
  refine ⟨T.closure_eq_of_isClosed, fun h => ?_⟩
  rw [← h]; exact T.isClosed_closure C

theorem closure_mono {S₁ S₂ : Set α} (h : S₁ ⊆ S₂) :
    T.closure S₁ ⊆ T.closure S₂ := by
  intro x hx C hC
  exact hx C ⟨hC.1, Set.Subset.trans h hC.2⟩

theorem closure_empty : T.closure (∅ : Set α) = ∅ := by
  apply Set.subset_antisymm
  · intro x hx
    exact hx ∅ ⟨T.isClosed_empty, fun _ h => h.elim⟩
  · exact Set.empty_subset _

theorem closure_univ : T.closure (Set.univ : Set α) = Set.univ := by
  apply Set.subset_antisymm
  · exact Set.subset_univ _
  · exact T.subset_closure _

theorem closure_closure (S : Set α) : T.closure (T.closure S) = T.closure S :=
  T.closure_eq_of_isClosed (T.isClosed_closure S)

theorem interior_interior (S : Set α) : T.interior (T.interior S) = T.interior S :=
  T.interior_eq_of_isOpen (T.isOpen_interior S)

/-! ### Relations between closure, interior and complement. -/

/-- Interior of `S` equals the complement of the closure of the complement. -/
theorem interior_eq_compl_closure_compl (S : Set α) :
    T.interior S = (T.closure Sᶜ)ᶜ := by
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨U, ⟨hU, hUS⟩, hxU⟩ hxcl
    -- hxcl : x ∈ closure Sᶜ, i.e. ∀ C closed with Sᶜ ⊆ C, x ∈ C
    -- Take C := Uᶜ, which is closed, and Sᶜ ⊆ Uᶜ since U ⊆ S.
    have hUC : T.IsClosed Uᶜ := T.isClosed_compl_of_isOpen hU
    have hSsubUc : Sᶜ ⊆ Uᶜ := by
      intro y hy hyU
      exact hy (hUS hyU)
    have := hxcl Uᶜ ⟨hUC, hSsubUc⟩
    exact this hxU
  · intro hx
    -- hx : x ∉ closure Sᶜ. So there is some closed C with Sᶜ ⊆ C and x ∉ C.
    -- We need an open U with x ∈ U ⊆ S. Take U := Cᶜ.
    classical
    by_contra hxint
    apply hx
    intro C ⟨hC, hSC⟩
    by_contra hxC
    apply hxint
    refine ⟨Cᶜ, ⟨hC, ?_⟩, hxC⟩
    intro y hy
    by_contra hyS
    exact hy (hSC hyS)

/-- Closure of `S` equals the complement of the interior of the complement. -/
theorem closure_eq_compl_interior_compl (S : Set α) :
    T.closure S = (T.interior Sᶜ)ᶜ := by
  have h := T.interior_eq_compl_closure_compl Sᶜ
  rw [Set.compl_compl] at h
  have : (T.interior Sᶜ)ᶜ = ((T.closure S)ᶜ)ᶜ := by rw [h]
  rw [Set.compl_compl] at this
  exact this.symm

/-- A point is in the closure of `S` iff every open neighborhood meets `S`. -/
theorem mem_closure_iff {S : Set α} {x : α} :
    x ∈ T.closure S ↔ ∀ U, T.IsOpen U → x ∈ U → ∃ y, y ∈ U ∧ y ∈ S := by
  classical
  refine ⟨?_, ?_⟩
  · intro hx U hU hxU
    by_contra hne
    -- Uᶜ is closed, S ⊆ Uᶜ, so closure S ⊆ Uᶜ, contradicting hxU.
    have hS_sub : S ⊆ Uᶜ := by
      intro y hy hyU
      exact hne ⟨y, hyU, hy⟩
    have : x ∈ Uᶜ :=
      hx Uᶜ ⟨T.isClosed_compl_of_isOpen hU, hS_sub⟩
    exact this hxU
  · intro h C ⟨hC, hSC⟩
    -- If x ∉ C, then Cᶜ is an open neighborhood avoiding S. Contradiction.
    by_contra hxC
    obtain ⟨y, hyCc, hyS⟩ := h Cᶜ hC hxC
    exact hyCc (hSC hyS)

/-! ### Monotonicity and basic closure identities. -/

theorem closure_union_subset (S₁ S₂ : Set α) :
    T.closure S₁ ∪ T.closure S₂ ⊆ T.closure (S₁ ∪ S₂) := by
  apply Set.union_subset
  · exact T.closure_mono (Set.subset_union_left _ _)
  · exact T.closure_mono (Set.subset_union_right _ _)

theorem closure_union (S₁ S₂ : Set α) :
    T.closure (S₁ ∪ S₂) = T.closure S₁ ∪ T.closure S₂ := by
  apply Set.subset_antisymm
  · exact T.closure_subset_of_isClosed
      (T.isClosed_union (T.isClosed_closure S₁) (T.isClosed_closure S₂))
      (Set.union_subset_union (T.subset_closure _) (T.subset_closure _))
  · exact T.closure_union_subset S₁ S₂

theorem interior_inter (S₁ S₂ : Set α) :
    T.interior (S₁ ∩ S₂) = T.interior S₁ ∩ T.interior S₂ := by
  apply Set.subset_antisymm
  · apply Set.subset_inter
    · exact T.interior_mono (Set.inter_subset_left _ _)
    · exact T.interior_mono (Set.inter_subset_right _ _)
  · rintro x ⟨⟨U, ⟨hU, hUS₁⟩, hxU⟩, ⟨V, ⟨hV, hVS₂⟩, hxV⟩⟩
    refine ⟨U ∩ V, ⟨T.isOpen_inter hU hV, ?_⟩, hxU, hxV⟩
    exact Set.inter_subset_inter hUS₁ hVS₂

/-! ### Boundary. -/

theorem boundary_def (S : Set α) :
    T.boundary S = T.closure S \ T.interior S := rfl

theorem isClosed_boundary (S : Set α) : T.IsClosed (T.boundary S) := by
  unfold boundary
  rw [Set.diff_eq]
  exact T.isClosed_inter (T.isClosed_closure S)
    (by
      unfold IsClosed
      rw [Set.compl_compl]
      exact T.isOpen_interior S)

end Topology
end Mgw
