/-
Baire spaces and G_δ / F_σ sets.

Corresponds to topology.mg §48 (Baire Spaces).
-/
import MgwTopology.Section_12_Core
import MgwTopology.ClosureInterior
import MgwTopology.Subspace
import MgwTopology.Countability

namespace Mgw
namespace Topology

universe u
variable {α : Type u} (T : Topology α)

/-! ### G_δ and F_σ sets. -/

/-- A set is a G_δ if it is a countable intersection of open sets. -/
def IsGdelta (U : Set α) : Prop :=
  ∃ 𝒰 : Set (Set α), 𝒰.Countable ∧ (∀ V ∈ 𝒰, T.IsOpen V) ∧ U = ⋂₀ 𝒰

/-- A set is an F_σ if it is a countable union of closed sets. -/
def IsFsigma (C : Set α) : Prop :=
  ∃ 𝒞 : Set (Set α), 𝒞.Countable ∧ (∀ V ∈ 𝒞, T.IsClosed V) ∧ C = ⋃₀ 𝒞

/-- Countable image: if `f : α → β` preserves countability of an indexing,
    then `{f a | a ∈ s}` is countable when `s` is. -/
theorem countable_image_set {β : Type u} {s : Set α} (hs : s.Countable)
    (f : α → β) : (Set.image f s).Countable := Set.Countable.image hs f

/-- De Morgan: `U` is G_δ iff `Uᶜ` is F_σ. -/
theorem IsGdelta.compl_isFsigma {U : Set α} (h : T.IsGdelta U) :
    T.IsFsigma Uᶜ := by
  classical
  obtain ⟨𝒰, h𝒰c, h𝒰o, rfl⟩ := h
  refine ⟨Set.image Set.compl 𝒰, Set.Countable.image h𝒰c _, ?_, ?_⟩
  · rintro V ⟨W, hW, rfl⟩
    -- Wᶜ is closed since W is open.
    exact T.isClosed_compl_of_isOpen (h𝒰o W hW)
  · exact Set.compl_sInter_eq_sUnion_compl 𝒰

/-- De Morgan: `C` is F_σ iff `Cᶜ` is G_δ. -/
theorem IsFsigma.compl_isGdelta {C : Set α} (h : T.IsFsigma C) :
    T.IsGdelta Cᶜ := by
  classical
  obtain ⟨𝒞, h𝒞c, h𝒞cl, rfl⟩ := h
  refine ⟨Set.image Set.compl 𝒞, Set.Countable.image h𝒞c _, ?_, ?_⟩
  · rintro V ⟨W, hW, rfl⟩
    exact h𝒞cl W hW
  · exact Set.compl_sUnion_eq_sInter_compl 𝒞

/-! ### Baire space definitions. -/

/-- A topology is a **Baire space** (open-set form) if every countable
    intersection of dense open sets is dense. -/
def BaireSpace : Prop :=
  ∀ 𝒰 : Set (Set α), 𝒰.Countable →
    (∀ U ∈ 𝒰, T.IsOpen U) →
    (∀ U ∈ 𝒰, T.Dense U) →
    T.Dense (⋂₀ 𝒰)

/-- A topology is a **Baire space** (closed-set form) if every countable
    union of closed sets with empty interior has empty interior. -/
def BaireSpaceClosed : Prop :=
  ∀ 𝒞 : Set (Set α), 𝒞.Countable →
    (∀ C ∈ 𝒞, T.IsClosed C ∧ T.interior C = ∅) →
    T.interior (⋃₀ 𝒞) = ∅

/-! ### Helpers: dense iff complement has empty interior. -/

/-- A set is dense iff the interior of its complement is empty. -/
theorem dense_iff_compl_interior_empty {A : Set α} :
    T.Dense A ↔ T.interior Aᶜ = ∅ := by
  classical
  rw [T.dense_iff_closure_univ]
  constructor
  · intro hcl
    -- interior (Aᶜ) = (closure A)ᶜ, and closure A = univ means interior Aᶜ = ∅.
    rw [T.interior_eq_compl_closure_compl]
    have hcc : T.closure Aᶜᶜ = T.closure A := by rw [Set.compl_compl]
    rw [hcc, hcl, Set.compl_univ]
  · intro hint
    -- closure A = (interior Aᶜ)ᶜ? Yes by the identity `closure A = (interior Aᶜ)ᶜ`.
    rw [T.closure_eq_compl_interior_compl]
    rw [hint, Set.compl_empty]

/-! ### Equivalence of the two Baire formulations. -/

/- source: topology.mg:257317 name: Baire_space_closed_imp -/
/-- Closed-set Baire implies open-set Baire. -/
theorem BaireSpace.of_closed (h : T.BaireSpaceClosed) : T.BaireSpace := by
  classical
  intro 𝒰 h𝒰c h𝒰o h𝒰d
  -- Consider the family of complements.
  let 𝒞 : Set (Set α) := Set.image Set.compl 𝒰
  have h𝒞c : 𝒞.Countable := Set.Countable.image h𝒰c _
  have h𝒞prop : ∀ C ∈ 𝒞, T.IsClosed C ∧ T.interior C = ∅ := by
    rintro C ⟨U, hU, rfl⟩
    refine ⟨T.isClosed_compl_of_isOpen (h𝒰o U hU), ?_⟩
    -- U dense ↔ interior Uᶜ = ∅.
    exact (T.dense_iff_compl_interior_empty).1 (h𝒰d U hU)
  have hint : T.interior (⋃₀ 𝒞) = ∅ := h 𝒞 h𝒞c h𝒞prop
  -- Now ⋃₀ 𝒞 = (⋂₀ 𝒰)ᶜ; so interior ((⋂₀ 𝒰)ᶜ) = ∅, i.e., ⋂₀ 𝒰 is dense.
  have heq : ⋃₀ 𝒞 = (⋂₀ 𝒰)ᶜ := by
    show ⋃₀ (Set.image Set.compl 𝒰) = (⋂₀ 𝒰)ᶜ
    exact (Set.compl_sInter_eq_sUnion_compl 𝒰).symm
  rw [heq] at hint
  exact (T.dense_iff_compl_interior_empty).2 hint

/- source: topology.mg:257441 name: Baire_space_imp_closed -/
/-- Open-set Baire implies closed-set Baire. -/
theorem BaireSpace.to_closed (h : T.BaireSpace) : T.BaireSpaceClosed := by
  classical
  intro 𝒞 h𝒞c h𝒞prop
  -- Complement family of opens with empty interior complements.
  let 𝒰 : Set (Set α) := Set.image Set.compl 𝒞
  have h𝒰c : 𝒰.Countable := Set.Countable.image h𝒞c _
  have h𝒰o : ∀ U ∈ 𝒰, T.IsOpen U := by
    rintro U ⟨C, hC, rfl⟩
    exact (h𝒞prop C hC).1
  have h𝒰d : ∀ U ∈ 𝒰, T.Dense U := by
    rintro U ⟨C, hC, rfl⟩
    -- C closed, interior C = ∅, so Cᶜ is dense (since closure Cᶜ = univ).
    apply (T.dense_iff_compl_interior_empty).2
    have hcc : Cᶜᶜ = C := Set.compl_compl C
    rw [hcc]; exact (h𝒞prop C hC).2
  have hdens : T.Dense (⋂₀ 𝒰) := h 𝒰 h𝒰c h𝒰o h𝒰d
  have heq : ⋂₀ 𝒰 = (⋃₀ 𝒞)ᶜ := by
    show ⋂₀ (Set.image Set.compl 𝒞) = (⋃₀ 𝒞)ᶜ
    -- compl_sUnion = sInter (image compl).
    rw [Set.compl_sUnion_eq_sInter_compl]
  rw [heq] at hdens
  -- Dense complement means interior of the set is empty.
  have := (T.dense_iff_compl_interior_empty).1 hdens
  have hdd : (⋃₀ 𝒞)ᶜᶜ = ⋃₀ 𝒞 := Set.compl_compl _
  rw [hdd] at this
  exact this

/- source: topology.mg:257633 name: Baire_space_closed_iff -/
/-- Equivalence of the two formulations. -/
theorem BaireSpace.iff_closed : T.BaireSpaceClosed ↔ T.BaireSpace :=
  ⟨BaireSpace.of_closed T, BaireSpace.to_closed T⟩

/-! ### Dense G_δ is dense. -/

/- source: topology.mg:257643 name: Baire_space_dense_Gdelta -/
/-- In a Baire space, a countable intersection of dense open sets is dense. -/
theorem BaireSpace.dense_sInter_open_dense (hB : T.BaireSpace)
    {𝒰 : Set (Set α)} (h𝒰c : 𝒰.Countable)
    (h𝒰o : ∀ U ∈ 𝒰, T.IsOpen U) (h𝒰d : ∀ U ∈ 𝒰, T.Dense U) :
    T.Dense (⋂₀ 𝒰) := hB 𝒰 h𝒰c h𝒰o h𝒰d

/-! ### G_δ basics. -/

/-- The whole space is a G_δ. -/
theorem isGdelta_univ : T.IsGdelta (Set.univ : Set α) := by
  refine ⟨∅, ?_, ?_, ?_⟩
  · exact Or.inl (fun _ h => h)
  · intro V hV; exact hV.elim
  · ext x; refine ⟨fun _ _ h => h.elim, fun _ => trivial⟩

/-- The empty set is an F_σ. -/
theorem isFsigma_empty : T.IsFsigma (∅ : Set α) := by
  refine ⟨∅, ?_, ?_, ?_⟩
  · exact Or.inl (fun _ h => h)
  · intro V hV; exact hV.elim
  · ext x
    refine ⟨fun h => h.elim, ?_⟩
    rintro ⟨V, hV, _⟩; exact hV.elim

/-- Any open set is G_δ (singleton family). -/
theorem IsGdelta.of_isOpen {U : Set α} (hU : T.IsOpen U) : T.IsGdelta U := by
  refine ⟨{U}, ?_, ?_, ?_⟩
  · -- Singleton is countable: enumerate as constant.
    right
    refine ⟨fun _ => U, ?_⟩
    intro x hx
    have : x = U := hx
    exact ⟨0, this.symm⟩
  · intro V hV
    have : V = U := hV
    rw [this]; exact hU
  · ext x
    refine ⟨fun hxU V hV => ?_, fun h => h U rfl⟩
    have : V = U := hV
    rw [this]; exact hxU

/-- Any closed set is F_σ. -/
theorem IsFsigma.of_isClosed {C : Set α} (hC : T.IsClosed C) : T.IsFsigma C := by
  refine ⟨{C}, ?_, ?_, ?_⟩
  · right
    refine ⟨fun _ => C, ?_⟩
    intro x hx
    have : x = C := hx
    exact ⟨0, this.symm⟩
  · intro V hV
    have : V = C := hV
    rw [this]; exact hC
  · ext x
    refine ⟨fun hxC => ⟨C, rfl, hxC⟩, ?_⟩
    rintro ⟨V, hV, hxV⟩
    have : V = C := hV
    rw [this] at hxV; exact hxV

/-! ### Baire, subspaces via dense G_δ. -/

/-! ### Further set-theoretic helpers. -/

/-- Two G_δ sets intersect in a G_δ (pairwise). -/
theorem IsGdelta.inter {U V : Set α}
    (hU : T.IsGdelta U) (hV : T.IsGdelta V) : T.IsGdelta (U ∩ V) := by
  classical
  obtain ⟨𝒰, h𝒰c, h𝒰o, hUeq⟩ := hU
  obtain ⟨𝒱, h𝒱c, h𝒱o, hVeq⟩ := hV
  refine ⟨𝒰 ∪ 𝒱, Set.Countable.union h𝒰c h𝒱c, ?_, ?_⟩
  · rintro W (hW | hW)
    · exact h𝒰o W hW
    · exact h𝒱o W hW
  · rw [hUeq, hVeq]
    ext x
    refine ⟨?_, ?_⟩
    · rintro ⟨h1, h2⟩ W hW
      rcases hW with hW | hW
      · exact h1 W hW
      · exact h2 W hW
    · intro h
      refine ⟨fun W hW => h W (Or.inl hW), fun W hW => h W (Or.inr hW)⟩

/-- Two F_σ sets union to an F_σ. -/
theorem IsFsigma.union {A B : Set α}
    (hA : T.IsFsigma A) (hB : T.IsFsigma B) : T.IsFsigma (A ∪ B) := by
  classical
  obtain ⟨𝒜, h𝒜c, h𝒜cl, hAeq⟩ := hA
  obtain ⟨ℬ, hℬc, hℬcl, hBeq⟩ := hB
  refine ⟨𝒜 ∪ ℬ, Set.Countable.union h𝒜c hℬc, ?_, ?_⟩
  · rintro C (hC | hC)
    · exact h𝒜cl C hC
    · exact hℬcl C hC
  · rw [hAeq, hBeq]
    ext x
    refine ⟨?_, ?_⟩
    · rintro (⟨C, hC, hxC⟩ | ⟨C, hC, hxC⟩)
      · exact ⟨C, Or.inl hC, hxC⟩
      · exact ⟨C, Or.inr hC, hxC⟩
    · rintro ⟨C, (hC | hC), hxC⟩
      · exact Or.inl ⟨C, hC, hxC⟩
      · exact Or.inr ⟨C, hC, hxC⟩

/- source: topology.mg:257671 name: Baire_dense_Gdelta_subspace -/
/-- If `Y` is a dense G_δ subset of a Baire space `X`, then the subspace
    topology on `Y` is also a Baire space.

    **Stub**: the Megalodon proof uses the closed-set reformulation and that
    countable intersections of dense opens stay dense after adjoining the
    family defining `Y` as a G_δ. The full transliteration is long; we record
    the statement and defer the proof. -/
theorem BaireSpace.subspace_of_dense_gdelta
    (_hB : T.BaireSpace) {Y : Set α}
    (_hYd : T.Dense Y) (_hYgd : T.IsGdelta Y) :
    (T.subspace Y).BaireSpace := by
  sorry

end Topology
end Mgw
