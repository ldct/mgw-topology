/-
Binary product topology (X × Y).

Corresponds to topology.mg §15 (The Product Topology on X × Y).
-/
import MgwTopology.Core
import MgwTopology.Basis
import MgwTopology.Continuous
import MgwTopology.ClosedAndLimit

namespace Mgw
namespace Topology

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- The product basis: sets of the form `U ×ˢ V` where `U` is open in `α`
    and `V` is open in `β`. -/
def prodBasis (TX : Topology α) (TY : Topology β) : Set (Set (α × β)) :=
  fun W => ∃ U V, TX.IsOpen U ∧ TY.IsOpen V ∧ W = U ×ˢ V

/- source: topology.mg:32750 name: product_subbasis_is_basis -/
/-- The product basis is indeed a basis. -/
theorem isBasis_prodBasis (TX : Topology α) (TY : Topology β) :
    IsBasis (prodBasis TX TY) where
  covers := by
    intro p
    refine ⟨Set.univ, ⟨Set.univ, Set.univ,
      TX.isOpen_univ, TY.isOpen_univ, Set.prod_univ_univ.symm⟩, ?_⟩
    trivial
  inter := by
    rintro B₁ ⟨U₁, V₁, hU₁, hV₁, rfl⟩ B₂ ⟨U₂, V₂, hU₂, hV₂, rfl⟩ p hp
    refine ⟨(U₁ ∩ U₂) ×ˢ (V₁ ∩ V₂), ⟨U₁ ∩ U₂, V₁ ∩ V₂,
      TX.isOpen_inter hU₁ hU₂, TY.isOpen_inter hV₁ hV₂, rfl⟩, ?_, ?_⟩
    · exact ⟨⟨hp.1.1, hp.2.1⟩, ⟨hp.1.2, hp.2.2⟩⟩
    · rw [Set.prod_inter_prod]; exact fun _ h => h

/- source: topology.mg:32889 name: product_topology_is_topology -/
/-- The product topology on `α × β`. -/
def prod (TX : Topology α) (TY : Topology β) : Topology (α × β) :=
  Topology.ofBasis (prodBasis TX TY) (isBasis_prodBasis TX TY)

/- source: topology.mg:32909 name: product_basis_generates_product_topology -/
/-- Every rectangle `U ×ˢ V` with `U,V` open is open in the product topology. -/
theorem prod_isOpen_rect {TX : Topology α} {TY : Topology β}
    {U : Set α} {V : Set β} (hU : TX.IsOpen U) (hV : TY.IsOpen V) :
    (TX.prod TY).IsOpen (U ×ˢ V) :=
  basis_mem_isOpen (isBasis_prodBasis TX TY) ⟨U, V, hU, hV, rfl⟩

/-- A set is open in the product topology iff it is a union of open rectangles. -/
theorem isOpen_prod_iff (TX : Topology α) (TY : Topology β) (W : Set (α × β)) :
    (TX.prod TY).IsOpen W ↔
      ∀ p ∈ W, ∃ U V, TX.IsOpen U ∧ TY.IsOpen V ∧ p ∈ U ×ˢ V ∧ U ×ˢ V ⊆ W := by
  refine ⟨?_, ?_⟩
  · intro hW p hp
    obtain ⟨B, ⟨U, V, hU, hV, rfl⟩, hpB, hBW⟩ := hW p hp
    exact ⟨U, V, hU, hV, hpB, hBW⟩
  · intro h p hp
    obtain ⟨U, V, hU, hV, hpUV, hUVW⟩ := h p hp
    exact ⟨U ×ˢ V, ⟨U, V, hU, hV, rfl⟩, hpUV, hUVW⟩

/-! ### Projection continuity. -/

/-- First projection is continuous. -/
theorem prod_fst_continuous (TX : Topology α) (TY : Topology β) :
    Continuous (TX.prod TY) TX (Prod.fst : α × β → α) := by
  intro U hU
  -- fst⁻¹'U = U ×ˢ univ is open.
  rw [Set.fst_preimage_eq_prod_univ]
  exact prod_isOpen_rect hU TY.isOpen_univ

/-- Second projection is continuous. -/
theorem prod_snd_continuous (TX : Topology α) (TY : Topology β) :
    Continuous (TX.prod TY) TY (Prod.snd : α × β → β) := by
  intro V hV
  rw [Set.snd_preimage_eq_univ_prod]
  exact prod_isOpen_rect TX.isOpen_univ hV

/-! ### Universal property of the product. -/

/- source: topology.mg:76370 name: maps_into_products -/
/-- Universal property: `(f,g) : γ → α × β` is continuous iff both components
    are continuous. -/
theorem continuous_prod_iff
    {TZ : Topology γ} {TX : Topology α} {TY : Topology β}
    (f : γ → α) (g : γ → β) :
    Continuous TZ (TX.prod TY) (fun z => (f z, g z)) ↔
      Continuous TZ TX f ∧ Continuous TZ TY g := by
  refine ⟨?_, ?_⟩
  · intro h
    refine ⟨?_, ?_⟩
    · have := Continuous.comp (prod_fst_continuous TX TY) h
      exact this
    · have := Continuous.comp (prod_snd_continuous TX TY) h
      exact this
  · rintro ⟨hf, hg⟩
    -- Use `of_basis` against the product basis.
    apply Continuous.of_basis (isBasis_prodBasis TX TY)
    rintro B ⟨U, V, hU, hV, rfl⟩
    -- preimage of U ×ˢ V under (f,g) is f⁻¹U ∩ g⁻¹V.
    have : ((fun z => (f z, g z)) ⁻¹' (U ×ˢ V)) = f ⁻¹' U ∩ g ⁻¹' V := by
      ext z; exact Iff.rfl
    rw [this]
    exact TZ.isOpen_inter (hf U hU) (hg V hV)

/-! ### Rectangle closure; simple corollaries. -/

/-- A rectangle `A ×ˢ B` is a subset of its "outer" rectangle after closure:
    `closure (A ×ˢ B) ⊆ closure A ×ˢ closure B`. -/
theorem closure_prod_subset (TX : Topology α) (TY : Topology β)
    (A : Set α) (B : Set β) :
    (TX.prod TY).closure (A ×ˢ B) ⊆ (TX.closure A) ×ˢ (TY.closure B) := by
  -- `closure A ×ˢ closure B` is closed in the product.
  have hCl : (TX.prod TY).IsClosed ((TX.closure A) ×ˢ (TY.closure B)) := by
    -- Complement is an open set: union of two open rectangles.
    unfold IsClosed
    apply (TX.prod TY).isOpen_of_local_nhd
    intro p hp
    -- hp : p ∉ closure A ×ˢ closure B, i.e. p.1 ∉ closure A ∨ p.2 ∉ closure B.
    classical
    by_cases h1 : p.1 ∈ TX.closure A
    · have h2 : p.2 ∉ TY.closure B := fun h => hp ⟨h1, h⟩
      -- closure B is closed; complement is open.
      have hOpen : TY.IsOpen (TY.closure B)ᶜ := TY.isClosed_closure B
      refine ⟨Set.univ ×ˢ (TY.closure B)ᶜ,
        prod_isOpen_rect TX.isOpen_univ hOpen, ⟨trivial, h2⟩, ?_⟩
      intro q hq hq2
      -- q ∈ univ ×ˢ (closure B)ᶜ means q.2 ∉ closure B. But hq2 says q.2 ∈ closure B.
      exact hq.2 hq2.2
    · have hOpen : TX.IsOpen (TX.closure A)ᶜ := TX.isClosed_closure A
      refine ⟨(TX.closure A)ᶜ ×ˢ Set.univ,
        prod_isOpen_rect hOpen TY.isOpen_univ, ⟨h1, trivial⟩, ?_⟩
      intro q hq hq2
      exact hq.1 hq2.1
  -- A ×ˢ B ⊆ closure A ×ˢ closure B.
  apply (TX.prod TY).closure_subset_of_isClosed hCl
  exact Set.prod_subset_prod (TX.subset_closure A) (TY.subset_closure B)

/-! ### Hausdorff product. -/

/- source: topology.mg:51881 name: ex17_11_product_Hausdorff -/
/-- The product of two Hausdorff spaces is Hausdorff. -/
theorem prod_IsHausdorff {TX : Topology α} {TY : Topology β}
    (hX : TX.IsHausdorff) (hY : TY.IsHausdorff) :
    (TX.prod TY).IsHausdorff := by
  intro p q hne
  classical
  -- Either first coordinates differ, or second coordinates differ.
  by_cases h1 : p.1 = q.1
  · -- then p.2 ≠ q.2.
    have h2 : p.2 ≠ q.2 := by
      intro h2eq
      apply hne
      ext <;> assumption
    obtain ⟨U, V, hU, hV, hpU, hqV, hUV⟩ := hY p.2 q.2 h2
    refine ⟨Set.univ ×ˢ U, Set.univ ×ˢ V,
      prod_isOpen_rect TX.isOpen_univ hU,
      prod_isOpen_rect TX.isOpen_univ hV,
      ⟨trivial, hpU⟩, ⟨trivial, hqV⟩, ?_⟩
    intro z hzU hzV
    exact hUV z.2 hzU.2 hzV.2
  · obtain ⟨U, V, hU, hV, hpU, hqV, hUV⟩ := hX p.1 q.1 h1
    refine ⟨U ×ˢ Set.univ, V ×ˢ Set.univ,
      prod_isOpen_rect hU TY.isOpen_univ,
      prod_isOpen_rect hV TY.isOpen_univ,
      ⟨hpU, trivial⟩, ⟨hqV, trivial⟩, ?_⟩
    intro z hzU hzV
    exact hUV z.1 hzU.1 hzV.1

/- source: topology.mg:33547 name: product_subbasis_from_projections -/
/-- Preimages of open sets under the two projections generate the product
    topology (they are open in the product). -/
theorem prod_isOpen_fst_preimage {TX : Topology α} {TY : Topology β}
    {U : Set α} (hU : TX.IsOpen U) :
    (TX.prod TY).IsOpen ((Prod.fst : α × β → α) ⁻¹' U) := by
  rw [Set.fst_preimage_eq_prod_univ]
  exact prod_isOpen_rect hU TY.isOpen_univ

theorem prod_isOpen_snd_preimage {TX : Topology α} {TY : Topology β}
    {V : Set β} (hV : TY.IsOpen V) :
    (TX.prod TY).IsOpen ((Prod.snd : α × β → β) ⁻¹' V) := by
  rw [Set.snd_preimage_eq_univ_prod]
  exact prod_isOpen_rect TX.isOpen_univ hV

/- source: topology.mg:33063 name: product_basis_from_is_basis_on -/
/-- If `ℬ_α` and `ℬ_β` are bases for `TX`, `TY`, then `{B_α ×ˢ B_β}` is a
    basis that generates the same product topology. We only prove the
    rectangles-from-bases direction: any rectangle of basis elements is open
    in the product. -/
theorem prod_isOpen_basis_rect
    {TX : Topology α} {TY : Topology β}
    {ℬα : Set (Set α)} (_hℬα : IsBasis ℬα) (hαT : ∀ B ∈ ℬα, TX.IsOpen B)
    {ℬβ : Set (Set β)} (_hℬβ : IsBasis ℬβ) (hβT : ∀ B ∈ ℬβ, TY.IsOpen B)
    {Bα : Set α} {Bβ : Set β} (hBα : Bα ∈ ℬα) (hBβ : Bβ ∈ ℬβ) :
    (TX.prod TY).IsOpen (Bα ×ˢ Bβ) :=
  prod_isOpen_rect (hαT Bα hBα) (hβT Bβ hBβ)

/-- Product of subspace and product commute in a weak sense:
    `univ × Y` restricts the product topology to `Y` in the second factor. -/
theorem prod_univ_subspace_open
    (TX : Topology α) (TY : Topology β) (V : Set β) (hV : TY.IsOpen V) :
    (TX.prod TY).IsOpen (Set.univ ×ˢ V) :=
  prod_isOpen_rect TX.isOpen_univ hV

/-- A rectangle of closed sets is closed in the product topology. -/
/- source: topology.mg:49688 name: ex17_3_product_of_closed_sets_closed -/
theorem prod_isClosed_rect
    (TX : Topology α) (TY : Topology β)
    {A : Set α} {B : Set β} (hA : TX.IsClosed A) (hB : TY.IsClosed B) :
    (TX.prod TY).IsClosed (A ×ˢ B) := by
  -- Complement = (Aᶜ × univ) ∪ (univ × Bᶜ).
  unfold IsClosed
  have hopen₁ : (TX.prod TY).IsOpen (Aᶜ ×ˢ (Set.univ : Set β)) :=
    prod_isOpen_rect hA TY.isOpen_univ
  have hopen₂ : (TX.prod TY).IsOpen ((Set.univ : Set α) ×ˢ Bᶜ) :=
    prod_isOpen_rect TX.isOpen_univ hB
  have hunion := (TX.prod TY).isOpen_union hopen₁ hopen₂
  have heq : (A ×ˢ B)ᶜ = (Aᶜ ×ˢ (Set.univ : Set β)) ∪ ((Set.univ : Set α) ×ˢ Bᶜ) := by
    classical
    ext p
    refine ⟨?_, ?_⟩
    · intro hp
      by_cases ha : p.1 ∈ A
      · right
        refine ⟨trivial, ?_⟩
        intro hb
        exact hp ⟨ha, hb⟩
      · left
        exact ⟨ha, trivial⟩
    · rintro (⟨ha, _⟩ | ⟨_, hb⟩) hp
      · exact ha hp.1
      · exact hb hp.2
  rw [heq]; exact hunion

end Topology
end Mgw
