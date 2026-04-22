/-
Continuous maps.

Corresponds to topology.mg §18 (Continuous Functions).
-/
import MgwTopology.Section_12_Core
import MgwTopology.Basis
import MgwTopology.ClosureInterior
import MgwTopology.Chapter_12_Examples
import MgwTopology.Subspace

namespace Mgw

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- A map `f : α → β` is continuous with respect to topologies `TX`, `TY`
    iff preimages of open sets are open. -/
def Continuous (TX : Topology α) (TY : Topology β) (f : α → β) : Prop :=
  ∀ V : Set β, TY.IsOpen V → TX.IsOpen (f ⁻¹' V)

namespace Continuous

variable {TX : Topology α} {TY : Topology β}

/- source: topology.mg:68852 name: identity_continuous -/
theorem id : Continuous TX TX (fun x => x) := by
  intro V hV; exact hV

/- source: topology.mg:69144 name: composition_continuous -/
theorem comp
    {TZ : Topology γ}
    {f : α → β} {g : β → γ}
    (hg : Continuous TY TZ g) (hf : Continuous TX TY f) :
    Continuous TX TZ (fun x => g (f x)) := by
  intro W hW
  exact hf _ (hg _ hW)

/- source: topology.mg:67491 name: continuous_map_preimage -/
/-- Extract the preimage condition (definitional). -/
theorem preimage_isOpen
    {f : α → β} (hf : Continuous TX TY f)
    {V : Set β} (hV : TY.IsOpen V) : TX.IsOpen (f ⁻¹' V) :=
  hf V hV

/- source: topology.mg:68503 name: const_fun_continuous -/
/-- Any constant map is continuous. -/
theorem const (b : β) : Continuous TX TY (fun _ : α => b) := by
  classical
  intro V hV
  by_cases hb : b ∈ V
  · have h : ((fun _ : α => b) ⁻¹' V) = Set.univ := Set.preimage_const_of_mem b hb
    rw [h]; exact TX.isOpen_univ
  · have h : ((fun _ : α => b) ⁻¹' V) = ∅ := Set.preimage_const_of_not_mem b hb
    rw [h]; exact TX.isOpen_empty

/- source: topology.mg:68600 name: continuous_preserves_closed -/
/-- Continuity preserves closed sets under preimage. -/
theorem preimage_isClosed
    {f : α → β} (hf : Continuous TX TY f)
    {C : Set β} (hC : TY.IsClosed C) : TX.IsClosed (f ⁻¹' C) := by
  unfold Topology.IsClosed
  rw [← Set.preimage_compl]
  exact hf _ hC

/-- Converse: if preimages of closed sets are closed, then `f` is continuous. -/
theorem of_preimage_isClosed
    {f : α → β}
    (h : ∀ C : Set β, TY.IsClosed C → TX.IsClosed (f ⁻¹' C)) :
    Continuous TX TY f := by
  intro V hV
  have hV' : TY.IsClosed Vᶜ := by
    unfold Topology.IsClosed
    rw [Set.compl_compl]; exact hV
  have := h Vᶜ hV'
  unfold Topology.IsClosed at this
  rw [← Set.preimage_compl, Set.compl_compl] at this
  exact this

/- source: topology.mg:68769 name: continuity_equiv_forms -/
/-- Equivalence: continuity via open preimages vs. closed preimages. -/
theorem iff_preimage_isClosed {f : α → β} :
    Continuous TX TY f ↔ ∀ C, TY.IsClosed C → TX.IsClosed (f ⁻¹' C) :=
  ⟨fun hf _ hC => preimage_isClosed hf hC, of_preimage_isClosed⟩

/- source: topology.mg:67667 name: closure_preimage_contained -/
/-- For continuous `f`: the image of the closure is contained in the closure of
    the image — equivalently, `closure S ⊆ f⁻¹'(closure (f '' S))`. We state the
    preimage-closure form, which is more convenient in this set-theoretic
    setting. -/
theorem closure_subset_preimage_closure_image
    {f : α → β} (hf : Continuous TX TY f) (S : Set α) :
    TX.closure S ⊆ f ⁻¹' (TY.closure (Set.image f S)) := by
  -- f ⁻¹' (closure (f '' S)) is closed and contains S.
  have hClosed : TX.IsClosed (f ⁻¹' (TY.closure (Set.image f S))) :=
    preimage_isClosed hf (TY.isClosed_closure _)
  have hSub : S ⊆ f ⁻¹' (TY.closure (Set.image f S)) := by
    intro x hx
    have : f x ∈ Set.image f S := ⟨x, hx, rfl⟩
    exact TY.subset_closure _ this
  exact TX.closure_subset_of_isClosed hClosed hSub

/- source: topology.mg:68684 name: continuous_local_neighborhood -/
/-- Continuity implies the local neighborhood property: for every open
    neighborhood `V` of `f x`, there is an open neighborhood `U` of `x`
    mapped into `V`. -/
theorem local_nhd {f : α → β} (hf : Continuous TX TY f)
    (x : α) {V : Set β} (hV : TY.IsOpen V) (hfx : f x ∈ V) :
    ∃ U : Set α, TX.IsOpen U ∧ x ∈ U ∧ ∀ u, u ∈ U → f u ∈ V :=
  ⟨f ⁻¹' V, hf V hV, hfx, fun _ h => h⟩


/-- Converse of `local_nhd`: if for every `x` and every open `V` containing
    `f x` there is an open `U` containing `x` with `f '' U ⊆ V`, then `f` is
    continuous. -/
theorem of_local_nhd {f : α → β}
    (h : ∀ x : α, ∀ V : Set β, TY.IsOpen V → f x ∈ V →
         ∃ U : Set α, TX.IsOpen U ∧ x ∈ U ∧ ∀ u, u ∈ U → f u ∈ V) :
    Continuous TX TY f := by
  intro V hV
  apply TX.isOpen_of_local_nhd
  intro x hxV
  obtain ⟨U, hU, hxU, hUV⟩ := h x V hV hxV
  exact ⟨U, hU, hxU, fun y hy => hUV y hy⟩

/- source: topology.mg:67726 name: continuous_map_domain_finer -/
/-- Continuity is preserved when the domain topology is made finer. -/
theorem mono_dom {TX' : Topology α} (hTX' : Topology.Finer TX' TX)
    {f : α → β} (hf : Continuous TX TY f) :
    Continuous TX' TY f :=
  fun V hV => hTX' _ (hf V hV)

/- source: topology.mg:67756 name: continuous_map_codomain_coarser -/
/-- Continuity is preserved when the codomain topology is made coarser:
    if `TY` is finer than `TY'` and `f` is continuous into `TY`, then `f` is
    continuous into `TY'`. -/
theorem mono_cod {TY' : Topology β} (hTY' : Topology.Finer TY TY')
    {f : α → β} (hf : Continuous TX TY f) :
    Continuous TX TY' f :=
  fun V hV => hf V (hTY' _ hV)

/- source: topology.mg:67934 name: continuous_map_from_subbasis -/
/-- A map is continuous iff preimages of basis elements are open. -/
theorem of_basis
    {ℬ : Set (Set β)} (hℬ : IsBasis ℬ)
    {f : α → β}
    (h : ∀ B, B ∈ ℬ → TX.IsOpen (f ⁻¹' B)) :
    Continuous TX (Topology.ofBasis ℬ hℬ) f := by
  intro V hV
  -- V is a union of basis elements.
  obtain ⟨𝒰, h𝒰, rfl⟩ := (Topology.isOpen_iff_sUnion_of_basis hℬ V).1 hV
  -- f⁻¹'(⋃ 𝒰) = ⋃ (preimages).
  rw [Set.preimage_sUnion]
  apply TX.isOpen_sUnion
  rintro W ⟨U, hU, rfl⟩
  exact h U (h𝒰 U hU)

/- source: topology.mg:68575 name: const_fun_continuous_total -/
/-- Constant map: alternative name. -/
theorem const' {f : α → β} {b : β} (hb : ∀ x, f x = b) :
    Continuous TX TY f := by
  have heq : f = (fun _ : α => b) := funext hb
  rw [heq]
  exact const b

/-! ### Continuity under composition with inclusions and restrictions. -/

/- source: topology.mg:67786 name: continuous_map_range_restrict -/
/-- Range-restrict: if `f : α → β` is continuous and factors through `Y ⊆ β`,
    then the corestricted map `α → {y // Y y}` is continuous into the subspace. -/
theorem range_restrict
    {Y : Set β} {f : α → β} (hf : Continuous TX TY f)
    (hrange : ∀ x, Y (f x)) :
    Continuous TX (TY.subspace Y) (fun x => (⟨f x, hrange x⟩ : {y // Y y})) := by
  intro V hV
  obtain ⟨U, hU, hUiff⟩ := hV
  have : ((fun x => (⟨f x, hrange x⟩ : {y // Y y})) ⁻¹' V) = f ⁻¹' U := by
    ext x
    exact hUiff ⟨f x, hrange x⟩
  rw [this]
  exact hf U hU

/- source: topology.mg:67855 name: continuous_map_range_expand -/
/-- Range-expand: if the corestricted map is continuous then the original
    map into the ambient space is continuous. -/
theorem range_expand
    {Y : Set β} {f : α → β} (hrange : ∀ x, Y (f x))
    (hf : Continuous TX (TY.subspace Y)
              (fun x => (⟨f x, hrange x⟩ : {y // Y y}))) :
    Continuous TX TY f := by
  intro U hU
  -- the preimage under the subspace-valued map of the restriction {p | U p.1}
  -- equals the preimage of U under f.
  have h : (TY.subspace Y).IsOpen (fun p : {y // Y y} => U p.1) :=
    ⟨U, hU, fun _ => Iff.rfl⟩
  exact hf _ h

/-- The subspace inclusion `{y // Y y} → β` is continuous. -/
theorem subtype_inclusion (T : Topology β) (Y : Set β) :
    Continuous (T.subspace Y) T (fun p : {y // Y y} => p.1) := by
  intro U hU
  exact ⟨U, hU, fun _ => Iff.rfl⟩

/-- Restriction of a continuous map to a subspace of the domain is continuous.
    (§18 "restriction of the domain".) -/
theorem restrict_dom
    {f : α → β} (hf : Continuous TX TY f) (X₀ : Set α) :
    Continuous (TX.subspace X₀) TY (fun p : {x // X₀ x} => f p.1) := by
  exact comp hf (subtype_inclusion TX X₀)

/-! ### Homeomorphisms. -/

/- source: topology.mg:70631 name: homeomorphism_continuous -/
/-- Predicate: `f` is a homeomorphism between `(α,TX)` and `(β,TY)`.
    We encode it as: `f` and some inverse `g` are continuous and mutual
    inverses. -/
structure Homeomorphism (TX : Topology α) (TY : Topology β)
    (f : α → β) (g : β → α) : Prop where
  cont_f : Continuous TX TY f
  cont_g : Continuous TY TX g
  left_inv : ∀ x, g (f x) = x
  right_inv : ∀ y, f (g y) = y

/- source: topology.mg:75116 name: homeomorphism_inverse_continuous -/
theorem Homeomorphism.inverse_continuous
    {f : α → β} {g : β → α}
    (h : Homeomorphism TX TY f g) : Continuous TY TX g := h.cont_g

/- source: topology.mg:75136 name: homeomorphism_inverse_is_homeomorphism -/
theorem Homeomorphism.symm
    {f : α → β} {g : β → α}
    (h : Homeomorphism TX TY f g) : Homeomorphism TY TX g f where
  cont_f := h.cont_g
  cont_g := h.cont_f
  left_inv := h.right_inv
  right_inv := h.left_inv

/- source: topology.mg:75195 name: homeomorphism_compose -/
theorem Homeomorphism.trans
    {TZ : Topology γ}
    {f₁ : α → β} {g₁ : β → α} {f₂ : β → γ} {g₂ : γ → β}
    (h₁ : Homeomorphism TX TY f₁ g₁)
    (h₂ : Homeomorphism TY TZ f₂ g₂) :
    Homeomorphism TX TZ (fun x => f₂ (f₁ x)) (fun z => g₁ (g₂ z)) where
  cont_f := comp h₂.cont_f h₁.cont_f
  cont_g := comp h₁.cont_g h₂.cont_g
  left_inv := by
    intro x
    show g₁ (g₂ (f₂ (f₁ x))) = x
    rw [h₂.left_inv, h₁.left_inv]
  right_inv := by
    intro z
    show f₂ (f₁ (g₁ (g₂ z))) = z
    rw [h₁.right_inv, h₂.right_inv]

theorem Homeomorphism.id (T : Topology α) :
    Homeomorphism T T (fun x => x) (fun x => x) where
  cont_f := Continuous.id
  cont_g := Continuous.id
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### Pasting lemma (two closed sets). -/

/- source: topology.mg:75800 name: pasting_lemma -/
/-- Pasting lemma: if `A ∪ B = univ`, both are closed, and `f` is continuous on
    each (as restricted maps into `β`), with the two restrictions agreeing on
    `A ∩ B`, then `f` is continuous on all of `α`.

    We state this in the "set" formulation: given `f : α → β` such that the
    restriction to `A` and to `B` are each continuous (viewed on the subspace)
    and `A ∪ B = Set.univ`, `A`,`B` closed, then `f` is continuous. -/
theorem pasting_closed
    {A B : Set α}
    (hA : TX.IsClosed A) (hB : TX.IsClosed B)
    (hcover : A ∪ B = Set.univ)
    {f : α → β}
    (hfA : Continuous (TX.subspace A) TY (fun p : {x // A x} => f p.1))
    (hfB : Continuous (TX.subspace B) TY (fun p : {x // B x} => f p.1)) :
    Continuous TX TY f := by
  apply of_preimage_isClosed
  intro C hC
  -- f⁻¹'C = (A ∩ f⁻¹'C) ∪ (B ∩ f⁻¹'C); both parts closed in α.
  have hpreA : TX.IsClosed (A ∩ f ⁻¹' C) := by
    -- On subspace A, (fun p => f p.1)⁻¹' C is closed, coming from some ambient-closed D.
    have hsub : (TX.subspace A).IsClosed
        ((fun p : {x // A x} => f p.1) ⁻¹' C) := preimage_isClosed hfA hC
    obtain ⟨D, hD, hDiff⟩ := (TX.isClosed_subspace_iff _).1 hsub
    -- We claim A ∩ f⁻¹'C = A ∩ D.
    have heq : A ∩ f ⁻¹' C = A ∩ D := by
      ext x
      refine ⟨?_, ?_⟩
      · rintro ⟨hxA, hxpre⟩
        exact ⟨hxA, (hDiff ⟨x, hxA⟩).1 hxpre⟩
      · rintro ⟨hxA, hxD⟩
        exact ⟨hxA, (hDiff ⟨x, hxA⟩).2 hxD⟩
    rw [heq]
    exact TX.isClosed_inter hA hD
  have hpreB : TX.IsClosed (B ∩ f ⁻¹' C) := by
    have hsub : (TX.subspace B).IsClosed
        ((fun p : {x // B x} => f p.1) ⁻¹' C) := preimage_isClosed hfB hC
    obtain ⟨D, hD, hDiff⟩ := (TX.isClosed_subspace_iff _).1 hsub
    have heq : B ∩ f ⁻¹' C = B ∩ D := by
      ext x
      refine ⟨?_, ?_⟩
      · rintro ⟨hxB, hxpre⟩
        exact ⟨hxB, (hDiff ⟨x, hxB⟩).1 hxpre⟩
      · rintro ⟨hxB, hxD⟩
        exact ⟨hxB, (hDiff ⟨x, hxB⟩).2 hxD⟩
    rw [heq]
    exact TX.isClosed_inter hB hD
  have hunion : f ⁻¹' C = (A ∩ f ⁻¹' C) ∪ (B ∩ f ⁻¹' C) := by
    ext x
    refine ⟨?_, ?_⟩
    · intro hx
      have hxAB : (A ∪ B) x := by rw [hcover]; trivial
      rcases hxAB with hA | hB
      · exact Or.inl ⟨hA, hx⟩
      · exact Or.inr ⟨hB, hx⟩
    · rintro (⟨_, hx⟩ | ⟨_, hx⟩) <;> exact hx
  rw [hunion]
  exact TX.isClosed_union hpreA hpreB

/-! ### Subspace continuity criterion. -/

/- source: topology.mg:75018 name: continuous_on_subspace -/
/-- The inclusion `{x // Y x} → α` is continuous. -/
theorem inclusion_continuous (T : Topology α) (Y : Set α) :
    Continuous (T.subspace Y) T (fun p : {x // Y x} => p.1) :=
  subtype_inclusion T Y

/- source: topology.mg:70001 name: product_space_component_sub -/
/-- A constructive corollary: the restriction of identity along a subtype
    inclusion yields a continuous map. -/
theorem subtype_id_continuous (T : Topology α) (Y : Set α) :
    Continuous (T.subspace Y) T (fun p : {x // Y x} => p.1) :=
  inclusion_continuous T Y

/- source: topology.mg:70091 name: continuous_map_congr_on -/
/-- If `f = g` pointwise, continuity of one implies continuity of the other. -/
theorem congr {f g : α → β} (hfg : ∀ x, f x = g x) (hf : Continuous TX TY f) :
    Continuous TX TY g := by
  have heq : f = g := funext hfg
  rw [heq] at hf
  exact hf

/- source: topology.mg:69819 name: continuous_map_local_cover -/
/-- Local-cover continuity: if `α` is covered by open sets `{U_i}` and the
    restriction of `f` to each `U_i` is continuous (viewed as a map from the
    subspace), then `f` is continuous. Stated for a two-cover here. -/
theorem local_open_cover
    {A B : Set α} (hA : TX.IsOpen A) (hB : TX.IsOpen B)
    (hcover : A ∪ B = Set.univ)
    {f : α → β}
    (hfA : Continuous (TX.subspace A) TY (fun p : {x // A x} => f p.1))
    (hfB : Continuous (TX.subspace B) TY (fun p : {x // B x} => f p.1)) :
    Continuous TX TY f := by
  intro V hV
  -- f⁻¹'V = (A ∩ f⁻¹'V) ∪ (B ∩ f⁻¹'V); each is ambient-open via witness from subspace.
  have hpreA : TX.IsOpen (A ∩ f ⁻¹' V) := by
    have hsub : (TX.subspace A).IsOpen
        ((fun p : {x // A x} => f p.1) ⁻¹' V) := hfA V hV
    obtain ⟨U, hU, hUiff⟩ := hsub
    have heq : A ∩ f ⁻¹' V = A ∩ U := by
      ext x
      refine ⟨?_, ?_⟩
      · rintro ⟨hxA, hxpre⟩
        exact ⟨hxA, (hUiff ⟨x, hxA⟩).1 hxpre⟩
      · rintro ⟨hxA, hxU⟩
        exact ⟨hxA, (hUiff ⟨x, hxA⟩).2 hxU⟩
    rw [heq]
    exact TX.isOpen_inter hA hU
  have hpreB : TX.IsOpen (B ∩ f ⁻¹' V) := by
    have hsub : (TX.subspace B).IsOpen
        ((fun p : {x // B x} => f p.1) ⁻¹' V) := hfB V hV
    obtain ⟨U, hU, hUiff⟩ := hsub
    have heq : B ∩ f ⁻¹' V = B ∩ U := by
      ext x
      refine ⟨?_, ?_⟩
      · rintro ⟨hxB, hxpre⟩
        exact ⟨hxB, (hUiff ⟨x, hxB⟩).1 hxpre⟩
      · rintro ⟨hxB, hxU⟩
        exact ⟨hxB, (hUiff ⟨x, hxB⟩).2 hxU⟩
    rw [heq]
    exact TX.isOpen_inter hB hU
  have hunion : f ⁻¹' V = (A ∩ f ⁻¹' V) ∪ (B ∩ f ⁻¹' V) := by
    ext x
    refine ⟨?_, ?_⟩
    · intro hx
      have hxAB : (A ∪ B) x := by rw [hcover]; trivial
      rcases hxAB with hA | hB
      · exact Or.inl ⟨hA, hx⟩
      · exact Or.inr ⟨hB, hx⟩
    · rintro (⟨_, hx⟩ | ⟨_, hx⟩) <;> exact hx
  rw [hunion]
  exact TX.isOpen_union hpreA hpreB

/- source: topology.mg:75586 name: subspace_union_of_opens -/
/-- A convenience: a map is continuous iff its restriction to every open of a
    finite cover is continuous. (Two-cover version — same as `local_open_cover`
    but stated as an iff in one direction.) -/
theorem iff_local_open_cover_two
    {A B : Set α} (hA : TX.IsOpen A) (hB : TX.IsOpen B)
    (hcover : A ∪ B = Set.univ) {f : α → β} :
    Continuous TX TY f ↔
      (Continuous (TX.subspace A) TY (fun p : {x // A x} => f p.1) ∧
       Continuous (TX.subspace B) TY (fun p : {x // B x} => f p.1)) := by
  refine ⟨fun hf => ⟨?_, ?_⟩, fun ⟨hfA, hfB⟩ => local_open_cover hA hB hcover hfA hfB⟩
  · exact restrict_dom hf A
  · exact restrict_dom hf B

/- source: topology.mg:69344 name: continuous_construction_rules -/
/-- Continuity of identity and composition bundled as a "rules" lemma. -/
theorem rules :
    Continuous TX TX (fun x => x) ∧
    (∀ {TZ : Topology γ} {f : α → β} {g : β → γ},
        Continuous TY TZ g → Continuous TX TY f →
        Continuous TX TZ (fun x => g (f x))) :=
  ⟨Continuous.id, @Continuous.comp _ _ _ _ _⟩

end Continuous
end Mgw
