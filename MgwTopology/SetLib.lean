/-
A minimal `Set α` library for the MgwTopology port.

Lean core and Batteries do not ship a `Set α` type — that lives in Mathlib.
Rather than depend on Mathlib, we roll our own in the `Mgw` namespace.

Encoding: `Set α = α → Prop` as an `abbrev`, so membership unfolds
definitionally and elementary proofs close by `rfl`/`Iff.rfl`.
-/
import Batteries

namespace Mgw

universe u v

/-- A set of elements of `α`, encoded as a predicate. -/
abbrev Set (α : Type u) : Type u := α → Prop

namespace Set

variable {α : Type u} {β : Type v}

instance : Membership α (Set α) := ⟨fun s a => s a⟩
instance : EmptyCollection (Set α) := ⟨fun _ => False⟩
instance : HasSubset (Set α) := ⟨fun s t => ∀ ⦃x⦄, s x → t x⟩
instance : Union (Set α) := ⟨fun s t x => s x ∨ t x⟩
instance : Inter (Set α) := ⟨fun s t x => s x ∧ t x⟩
instance : SDiff (Set α) := ⟨fun s t x => s x ∧ ¬ t x⟩
instance : Singleton α (Set α) := ⟨fun a x => x = a⟩
instance : Insert α (Set α) := ⟨fun a s x => x = a ∨ s x⟩

/-- The whole space. -/
def univ : Set α := fun _ => True

/-- Set complement. -/
def compl (s : Set α) : Set α := fun x => ¬ s x

@[inherit_doc] postfix:max "ᶜ" => compl

/-- Set-builder predicate. `setOf p x ↔ p x` by definition. -/
def setOf (p : α → Prop) : Set α := p

/-- Set-builder notation: `{ x | p x }` and `{ x : τ | p x }`. -/
syntax "{ " ident " | " term " }" : term
syntax "{ " ident " : " term " | " term " }" : term
macro_rules
  | `({ $x:ident | $p }) => `(Mgw.Set.setOf (fun $x => $p))
  | `({ $x:ident : $t | $p }) => `(Mgw.Set.setOf (fun ($x : $t) => $p))

/-- Union of a family of sets. -/
def sUnion (𝒰 : Set (Set α)) : Set α := fun x => ∃ U, U ∈ 𝒰 ∧ U x

@[inherit_doc] prefix:110 "⋃₀" => sUnion

/-- Intersection of a family of sets. -/
def sInter (𝒰 : Set (Set α)) : Set α := fun x => ∀ U, U ∈ 𝒰 → U x

@[inherit_doc] prefix:110 "⋂₀" => sInter

/-- Preimage of a set under a function. -/
def preimage (f : α → β) (s : Set β) : Set α := fun x => s (f x)

@[inherit_doc] infixl:80 " ⁻¹' " => preimage

/-- Image of a set under a function. -/
def image (f : α → β) (s : Set α) : Set β := fun y => ∃ x, x ∈ s ∧ f x = y

/-- Cartesian product of two sets: `s ×ˢ t = {(a,b) | a ∈ s ∧ b ∈ t}`. -/
def prod (s : Set α) (t : Set β) : Set (α × β) :=
  fun p => s p.1 ∧ t p.2

@[inherit_doc] infixr:82 " ×ˢ " => prod

/-- Extensionality: two sets are equal iff they have the same members. -/
@[ext]
theorem ext {s t : Set α} (h : ∀ x, s x ↔ t x) : s = t :=
  funext fun x => propext (h x)

theorem mem_univ (x : α) : x ∈ (univ : Set α) := trivial
theorem not_mem_empty (x : α) : x ∉ (∅ : Set α) := id

theorem subset_def {s t : Set α} : s ⊆ t ↔ ∀ x, s x → t x := Iff.rfl

theorem Subset.refl (s : Set α) : s ⊆ s := fun _ h => h
theorem Subset.trans {s t u : Set α} (h₁ : s ⊆ t) (h₂ : t ⊆ u) : s ⊆ u :=
  fun _ h => h₂ (h₁ h)

/-- `s` is finite iff some `Fin n` maps onto every element of `s`. -/
def Finite (s : Set α) : Prop :=
  ∃ n : Nat, ∃ f : Fin n → α, ∀ x, s x → ∃ i, f i = x

/-- `s` is countable iff empty or covered by a `Nat`-indexed enumeration. -/
def Countable (s : Set α) : Prop :=
  (∀ x, ¬ s x) ∨ ∃ f : Nat → α, ∀ x, s x → ∃ n, f n = x

theorem eq_empty_iff {s : Set α} : s = ∅ ↔ ∀ x, ¬ s x := by
  refine Iff.intro (fun h x hx => ?_) (fun h => ?_)
  · rw [h] at hx; exact hx
  · ext x; exact ⟨fun hx => (h x hx).elim, fun hx => hx.elim⟩

/-! ### Basic Boolean-algebra lemmas (no Mathlib). -/

theorem mem_union {s t : Set α} {x : α} : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t := Iff.rfl
theorem mem_inter {s t : Set α} {x : α} : x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t := Iff.rfl
theorem mem_compl {s : Set α} {x : α} : x ∈ sᶜ ↔ ¬ x ∈ s := Iff.rfl
theorem mem_diff {s t : Set α} {x : α} : x ∈ s \ t ↔ x ∈ s ∧ ¬ x ∈ t := Iff.rfl
theorem mem_setOf {p : α → Prop} {x : α} : x ∈ setOf p ↔ p x := Iff.rfl
theorem mem_sUnion {𝒰 : Set (Set α)} {x : α} :
    x ∈ ⋃₀ 𝒰 ↔ ∃ U, U ∈ 𝒰 ∧ x ∈ U := Iff.rfl
theorem mem_sInter {𝒰 : Set (Set α)} {x : α} :
    x ∈ ⋂₀ 𝒰 ↔ ∀ U, U ∈ 𝒰 → x ∈ U := Iff.rfl

theorem inter_comm (s t : Set α) : s ∩ t = t ∩ s := by
  ext x; exact And.comm
theorem union_comm (s t : Set α) : s ∪ t = t ∪ s := by
  ext x; exact Or.comm
theorem inter_assoc (s t u : Set α) : (s ∩ t) ∩ u = s ∩ (t ∩ u) := by
  ext x; exact and_assoc
theorem union_assoc (s t u : Set α) : (s ∪ t) ∪ u = s ∪ (t ∪ u) := by
  ext x; exact or_assoc

theorem inter_self (s : Set α) : s ∩ s = s := by
  ext x; exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩
theorem union_self (s : Set α) : s ∪ s = s := by
  ext x; exact ⟨fun h => h.elim id id, fun h => Or.inl h⟩

theorem inter_empty (s : Set α) : s ∩ ∅ = ∅ := by
  ext x; exact ⟨fun h => h.2, fun h => h.elim⟩
theorem empty_inter (s : Set α) : ∅ ∩ s = ∅ := by
  ext x; exact ⟨fun h => h.1, fun h => h.elim⟩
theorem union_empty (s : Set α) : s ∪ ∅ = s := by
  ext x; exact ⟨fun h => h.elim id (fun e => e.elim), Or.inl⟩
theorem empty_union (s : Set α) : ∅ ∪ s = s := by
  ext x; exact ⟨fun h => h.elim (fun e => e.elim) id, Or.inr⟩

theorem inter_univ (s : Set α) : s ∩ univ = s := by
  ext x; exact ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩
theorem univ_inter (s : Set α) : univ ∩ s = s := by
  ext x; exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
theorem union_univ (s : Set α) : s ∪ univ = univ := by
  ext x; exact ⟨fun _ => trivial, fun _ => Or.inr trivial⟩
theorem univ_union (s : Set α) : univ ∪ s = univ := by
  ext x; exact ⟨fun _ => trivial, fun _ => Or.inl trivial⟩

theorem subset_univ (s : Set α) : s ⊆ univ := fun _ _ => trivial
theorem empty_subset (s : Set α) : (∅ : Set α) ⊆ s := fun _ h => h.elim
theorem inter_subset_left (s t : Set α) : s ∩ t ⊆ s := fun _ h => h.1
theorem inter_subset_right (s t : Set α) : s ∩ t ⊆ t := fun _ h => h.2
theorem subset_union_left (s t : Set α) : s ⊆ s ∪ t := fun _ h => Or.inl h
theorem subset_union_right (s t : Set α) : t ⊆ s ∪ t := fun _ h => Or.inr h

theorem compl_compl (s : Set α) : sᶜᶜ = s := by
  ext x
  refine ⟨fun h => ?_, fun h hc => hc h⟩
  classical
  by_contra hx
  exact h hx

theorem compl_empty : (∅ : Set α)ᶜ = univ := by
  ext x; exact ⟨fun _ => trivial, fun _ h => h.elim⟩

theorem compl_univ : (univ : Set α)ᶜ = ∅ := by
  ext x; exact ⟨fun h => h trivial, fun h => h.elim⟩

theorem compl_union (s t : Set α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ := by
  ext x
  refine ⟨fun h => ⟨fun hs => h (Or.inl hs), fun ht => h (Or.inr ht)⟩, ?_⟩
  rintro ⟨hs, ht⟩ (h | h)
  · exact hs h
  · exact ht h

theorem compl_inter (s t : Set α) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ := by
  ext x
  classical
  refine ⟨fun h => ?_, ?_⟩
  · by_cases hs : s x
    · exact Or.inr (fun ht => h ⟨hs, ht⟩)
    · exact Or.inl hs
  · rintro (h | h) ⟨hs, ht⟩
    · exact h hs
    · exact h ht

theorem diff_eq (s t : Set α) : s \ t = s ∩ tᶜ := rfl

theorem sUnion_empty : ⋃₀ (∅ : Set (Set α)) = (∅ : Set α) := by
  ext x
  refine ⟨fun ⟨_, hU, _⟩ => hU.elim, fun h => h.elim⟩

theorem sInter_empty : ⋂₀ (∅ : Set (Set α)) = (univ : Set α) := by
  ext x
  refine ⟨fun _ => trivial, fun _ U hU => hU.elim⟩

theorem subset_antisymm {s t : Set α} (h₁ : s ⊆ t) (h₂ : t ⊆ s) : s = t := by
  ext x; exact ⟨fun h => h₁ h, fun h => h₂ h⟩

theorem compl_subset_compl {s t : Set α} : sᶜ ⊆ tᶜ ↔ t ⊆ s := by
  classical
  refine ⟨fun h x hx => ?_, fun h x hx hy => hx (h hy)⟩
  by_contra hx'
  exact h hx' hx

theorem subset_compl_iff {s t : Set α} : s ⊆ tᶜ ↔ ∀ x, x ∈ s → x ∉ t := Iff.rfl

theorem inter_subset_inter {s₁ s₂ t₁ t₂ : Set α}
    (h₁ : s₁ ⊆ s₂) (h₂ : t₁ ⊆ t₂) : s₁ ∩ t₁ ⊆ s₂ ∩ t₂ :=
  fun _ h => ⟨h₁ h.1, h₂ h.2⟩

theorem union_subset_union {s₁ s₂ t₁ t₂ : Set α}
    (h₁ : s₁ ⊆ s₂) (h₂ : t₁ ⊆ t₂) : s₁ ∪ t₁ ⊆ s₂ ∪ t₂ :=
  fun _ h => h.elim (fun h => Or.inl (h₁ h)) (fun h => Or.inr (h₂ h))

theorem union_subset {s t u : Set α} (h₁ : s ⊆ u) (h₂ : t ⊆ u) : s ∪ t ⊆ u :=
  fun _ h => h.elim (fun h => h₁ h) (fun h => h₂ h)

theorem subset_inter {s t u : Set α} (h₁ : u ⊆ s) (h₂ : u ⊆ t) : u ⊆ s ∩ t :=
  fun _ h => ⟨h₁ h, h₂ h⟩

theorem subset_sUnion_of_mem {𝒰 : Set (Set α)} {U : Set α}
    (hU : U ∈ 𝒰) : U ⊆ ⋃₀ 𝒰 :=
  fun _ hx => ⟨U, hU, hx⟩

theorem sUnion_subset {𝒰 : Set (Set α)} {t : Set α}
    (h : ∀ U ∈ 𝒰, U ⊆ t) : ⋃₀ 𝒰 ⊆ t := by
  rintro x ⟨U, hU, hxU⟩
  exact h U hU hxU

theorem sInter_subset_of_mem {𝒰 : Set (Set α)} {U : Set α}
    (hU : U ∈ 𝒰) : ⋂₀ 𝒰 ⊆ U :=
  fun _ hx => hx U hU

theorem subset_sInter {𝒰 : Set (Set α)} {t : Set α}
    (h : ∀ U ∈ 𝒰, t ⊆ U) : t ⊆ ⋂₀ 𝒰 :=
  fun _ hx U hU => h U hU hx

/-! ### Preimage and image basics. -/

theorem mem_preimage {f : α → β} {s : Set β} {x : α} :
    x ∈ f ⁻¹' s ↔ f x ∈ s := Iff.rfl

theorem preimage_univ (f : α → β) : f ⁻¹' (univ : Set β) = univ := rfl

theorem preimage_empty (f : α → β) : f ⁻¹' (∅ : Set β) = ∅ := rfl

theorem preimage_inter (f : α → β) (s t : Set β) :
    f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t := rfl

theorem preimage_union (f : α → β) (s t : Set β) :
    f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t := rfl

theorem preimage_compl (f : α → β) (s : Set β) :
    f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ := rfl

theorem preimage_sUnion (f : α → β) (𝒰 : Set (Set β)) :
    f ⁻¹' (⋃₀ 𝒰) = ⋃₀ (image (preimage f) 𝒰) := by
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨U, hU, hxU⟩
    exact ⟨f ⁻¹' U, ⟨U, hU, rfl⟩, hxU⟩
  · rintro ⟨V, ⟨U, hU, rfl⟩, hxV⟩
    exact ⟨U, hU, hxV⟩

theorem preimage_id (s : Set α) : (fun x => x) ⁻¹' s = s := rfl

theorem preimage_comp {γ : Type _} (g : β → γ) (f : α → β) (s : Set γ) :
    (fun x => g (f x)) ⁻¹' s = f ⁻¹' (g ⁻¹' s) := rfl

theorem preimage_mono {f : α → β} {s t : Set β} (h : s ⊆ t) :
    f ⁻¹' s ⊆ f ⁻¹' t :=
  fun _ hx => h hx

theorem preimage_const_of_mem (b : β) {s : Set β} (h : b ∈ s) :
    (fun _ : α => b) ⁻¹' s = univ := by
  ext x; exact ⟨fun _ => trivial, fun _ => h⟩

theorem preimage_const_of_not_mem (b : β) {s : Set β} (h : b ∉ s) :
    (fun _ : α => b) ⁻¹' s = ∅ := by
  ext x; exact ⟨fun hx => h hx, fun hx => hx.elim⟩

theorem mem_image {f : α → β} {s : Set α} {y : β} :
    y ∈ image f s ↔ ∃ x, x ∈ s ∧ f x = y := Iff.rfl

theorem image_subset_iff {f : α → β} {s : Set α} {t : Set β} :
    image f s ⊆ t ↔ s ⊆ f ⁻¹' t := by
  refine ⟨fun h x hx => h ⟨x, hx, rfl⟩, ?_⟩
  rintro h _ ⟨x, hx, rfl⟩
  exact h hx

theorem subset_preimage_image (f : α → β) (s : Set α) :
    s ⊆ f ⁻¹' image f s :=
  fun x hx => ⟨x, hx, rfl⟩

/-! ### Product-set basics. -/

theorem mem_prod {s : Set α} {t : Set β} {p : α × β} :
    p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t := Iff.rfl

theorem mk_mem_prod {s : Set α} {t : Set β} {a : α} {b : β}
    (ha : a ∈ s) (hb : b ∈ t) : (a, b) ∈ s ×ˢ t := ⟨ha, hb⟩

theorem prod_subset_prod {s₁ s₂ : Set α} {t₁ t₂ : Set β}
    (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁ ×ˢ t₁ ⊆ s₂ ×ˢ t₂ :=
  fun _ h => ⟨hs h.1, ht h.2⟩

theorem prod_inter_prod (s₁ s₂ : Set α) (t₁ t₂ : Set β) :
    (s₁ ×ˢ t₁) ∩ (s₂ ×ˢ t₂) = (s₁ ∩ s₂) ×ˢ (t₁ ∩ t₂) := by
  ext p
  exact ⟨fun ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ => ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩,
         fun ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩ => ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩⟩

theorem prod_univ_univ : (univ : Set α) ×ˢ (univ : Set β) = univ := by
  ext p; exact ⟨fun _ => trivial, fun _ => ⟨trivial, trivial⟩⟩

theorem fst_preimage_eq_prod_univ (s : Set α) :
    (Prod.fst : α × β → α) ⁻¹' s = s ×ˢ univ := by
  ext p; exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩

theorem snd_preimage_eq_univ_prod (t : Set β) :
    (Prod.snd : α × β → β) ⁻¹' t = univ ×ˢ t := by
  ext p; exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩

theorem prod_eq_inter_fst_snd (s : Set α) (t : Set β) :
    s ×ˢ t = ((Prod.fst : α × β → α) ⁻¹' s) ∩ ((Prod.snd : α × β → β) ⁻¹' t) := rfl

/-- De Morgan for `sUnion`. -/
theorem compl_sUnion_eq_sInter_compl (𝒰 : Set (Set α)) :
    (⋃₀ 𝒰)ᶜ = ⋂₀ (image compl 𝒰) := by
  ext x
  refine ⟨fun h U hU => ?_, ?_⟩
  · rcases hU with ⟨V, hV, rfl⟩
    intro hxV
    exact h ⟨V, hV, hxV⟩
  · rintro h ⟨U, hU, hxU⟩
    exact h Uᶜ ⟨U, hU, rfl⟩ hxU

/-- De Morgan for `sInter`. -/
theorem compl_sInter_eq_sUnion_compl (𝒰 : Set (Set α)) :
    (⋂₀ 𝒰)ᶜ = ⋃₀ (image compl 𝒰) := by
  classical
  ext x
  refine ⟨fun h => ?_, ?_⟩
  · by_contra hc
    apply h
    intro U hU
    by_contra hxU
    exact hc ⟨Uᶜ, ⟨U, hU, rfl⟩, hxU⟩
  · rintro ⟨V, ⟨U, hU, rfl⟩, hxV⟩ h'
    exact hxV (h' U hU)

end Set
end Mgw
