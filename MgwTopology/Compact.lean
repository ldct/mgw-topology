/-
Compact spaces.

Corresponds to topology.mg §26 (Compact Spaces). Only the core compactness
lemmas needed by §29 Local Compactness are proved here — this is not a
complete port of §26.
-/
import MgwTopology.Core
import MgwTopology.ClosureInterior
import MgwTopology.ClosedAndLimit
import MgwTopology.Subspace
import MgwTopology.Continuous

namespace Mgw
namespace Topology

universe u v
variable {α : Type u} {β : Type v} (T : Topology α)

/-- An open cover of a set `K ⊆ α` is a family of open sets whose union
    contains `K`. -/
def OpenCover (K : Set α) (𝒰 : Set (Set α)) : Prop :=
  (∀ U ∈ 𝒰, T.IsOpen U) ∧ K ⊆ ⋃₀ 𝒰

/-- A set `K ⊆ α` is compact iff every open cover has a finite subcover. -/
def IsCompact (K : Set α) : Prop :=
  ∀ 𝒰 : Set (Set α), OpenCover T K 𝒰 →
    ∃ 𝒰₀ ⊆ 𝒰, 𝒰₀.Finite ∧ K ⊆ ⋃₀ 𝒰₀

/-- The whole space is compact. -/
def Compact : Prop := IsCompact T Set.univ

/-! ### Finite intersections of opens are open. -/

/-- Intersection over a finite `Fin n`-indexed family is open. -/
theorem isOpen_iInter_fin {n : Nat} (U : Fin n → Set α)
    (hU : ∀ i, T.IsOpen (U i)) :
    T.IsOpen (fun x => ∀ i : Fin n, x ∈ U i) := by
  induction n with
  | zero =>
    have heq : (fun x : α => ∀ i : Fin 0, x ∈ U i) = Set.univ := by
      ext x; exact ⟨fun _ => trivial, fun _ i => i.elim0⟩
    rw [heq]; exact T.isOpen_univ
  | succ m ih =>
    -- Split off i = 0 vs shift.
    let V : Fin m → Set α := fun i => U i.succ
    have hV : ∀ i, T.IsOpen (V i) := fun i => hU i.succ
    have hVopen := ih V hV
    have heq : (fun x : α => ∀ i : Fin (m+1), x ∈ U i) =
               U 0 ∩ (fun x => ∀ i : Fin m, x ∈ V i) := by
      ext x
      refine ⟨fun h => ⟨h 0, fun i => h i.succ⟩, ?_⟩
      rintro ⟨h0, hsucc⟩ i
      refine Fin.cases ?_ ?_ i
      · exact h0
      · intro j; exact hsucc j
    rw [heq]
    exact T.isOpen_inter (hU 0) hVopen

/-! ### Basic compactness facts. -/

/-- The empty set is compact. -/
theorem isCompact_empty : T.IsCompact (∅ : Set α) := by
  intro 𝒰 _
  refine ⟨(∅ : Set (Set α)), fun _ h => h.elim, ⟨0, Fin.elim0, fun _ h => h.elim⟩, ?_⟩
  intro _ h; exact h.elim

/-- Any subset of `∅` is compact. -/
theorem isCompact_of_subset_empty {K : Set α} (hK : K ⊆ (∅ : Set α)) :
    T.IsCompact K := by
  intro 𝒰 _
  refine ⟨(∅ : Set (Set α)), fun _ h => h.elim,
    ⟨0, Fin.elim0, fun _ h => h.elim⟩, ?_⟩
  intro x hx; exact (hK hx).elim

/-! ### Closed subsets of compact spaces are compact. -/

/- source: topology.mg:103340 name: closed_subset_compact_is_compact -/
/-- A closed subset of a compact space is compact. -/
theorem IsCompact.of_isClosed_of_compact {K : Set α}
    (hT : T.Compact) (hK : T.IsClosed K) : T.IsCompact K := by
  intro 𝒰 h𝒰
  classical
  let 𝒰' : Set (Set α) := fun U => U ∈ 𝒰 ∨ U = Kᶜ
  have hopen' : ∀ U ∈ 𝒰', T.IsOpen U := by
    intro U hU
    rcases hU with hU | rfl
    · exact h𝒰.1 U hU
    · exact hK
  have hcover' : Set.univ ⊆ ⋃₀ 𝒰' := by
    intro x _
    classical
    by_cases hxK : x ∈ K
    · obtain ⟨U, hU, hxU⟩ := h𝒰.2 hxK
      exact ⟨U, Or.inl hU, hxU⟩
    · exact ⟨Kᶜ, Or.inr rfl, hxK⟩
  obtain ⟨𝒰₀', h𝒰₀'sub, h𝒰₀'fin, h𝒰₀'cov⟩ := hT 𝒰' ⟨hopen', hcover'⟩
  refine ⟨(fun U => U ∈ 𝒰₀' ∧ U ≠ Kᶜ), ?_, ?_, ?_⟩
  · intro U hU
    rcases h𝒰₀'sub hU.1 with hU' | hU'
    · exact hU'
    · exact (hU.2 hU').elim
  · obtain ⟨n, f, hf⟩ := h𝒰₀'fin
    refine ⟨n, f, ?_⟩
    intro U hU
    exact hf U hU.1
  · intro x hxK
    obtain ⟨U, hU₀, hxU⟩ := h𝒰₀'cov (Set.mem_univ x)
    by_cases h : U = Kᶜ
    · rw [h] at hxU; exact (hxU hxK).elim
    · exact ⟨U, ⟨hU₀, h⟩, hxU⟩

/-! ### Image of a compact set under a continuous map is compact. -/

/- source: topology.mg:103575 name: compact_image_continuous -/
/-- The image of a compact set under a continuous map is compact. -/
theorem IsCompact.image_continuous {TY : Topology β}
    {K : Set α} (hK : T.IsCompact K)
    {f : α → β} (hf : Continuous T TY f) :
    TY.IsCompact (Set.image f K) := by
  intro 𝒱 h𝒱
  classical
  let 𝒰 : Set (Set α) := Set.image (fun V => f ⁻¹' V) 𝒱
  have hopenU : ∀ U ∈ 𝒰, T.IsOpen U := by
    rintro _ ⟨V, hV, rfl⟩
    exact hf V (h𝒱.1 V hV)
  have hcoverU : K ⊆ ⋃₀ 𝒰 := by
    intro x hxK
    have hfxK : f x ∈ Set.image f K := ⟨x, hxK, rfl⟩
    obtain ⟨V, hV, hfxV⟩ := h𝒱.2 hfxK
    exact ⟨f ⁻¹' V, ⟨V, hV, rfl⟩, hfxV⟩
  obtain ⟨𝒰₀, h𝒰₀sub, h𝒰₀fin, h𝒰₀cov⟩ := hK 𝒰 ⟨hopenU, hcoverU⟩
  have hchoice : ∀ U, U ∈ 𝒰₀ → ∃ V, V ∈ 𝒱 ∧ f ⁻¹' V = U := by
    intro U hU
    rcases h𝒰₀sub hU with ⟨V, hV, heq⟩
    exact ⟨V, hV, heq⟩
  let g : ∀ U, U ∈ 𝒰₀ → Set β :=
    fun U hU => Classical.choose (hchoice U hU)
  let 𝒱₀ : Set (Set β) := fun V => ∃ U, ∃ hU : U ∈ 𝒰₀, g U hU = V
  refine ⟨𝒱₀, ?_, ?_, ?_⟩
  · rintro V ⟨U, hU, rfl⟩
    exact (Classical.choose_spec (hchoice U hU)).1
  · obtain ⟨n, f₀, hf₀⟩ := h𝒰₀fin
    refine ⟨n, fun i =>
      if h : f₀ i ∈ 𝒰₀ then g (f₀ i) h else (∅ : Set β), ?_⟩
    rintro V ⟨U, hU, rfl⟩
    obtain ⟨i, hi⟩ := hf₀ U hU
    refine ⟨i, ?_⟩
    subst hi
    simp [hU]
  · rintro _ ⟨x, hxK, rfl⟩
    obtain ⟨U, hU, hxU⟩ := h𝒰₀cov hxK
    have hspec := (Classical.choose_spec (hchoice U hU)).2
    refine ⟨g U hU, ⟨U, hU, rfl⟩, ?_⟩
    -- `g U hU : Set β`, and by hspec f ⁻¹' (g U hU) = U. Since x ∈ U, f x ∈ g U hU.
    have hxin : x ∈ f ⁻¹' (g U hU) := by rw [hspec]; exact hxU
    exact hxin

/-! ### Union of two compacts is compact. -/

/- source: topology.mg:103820 name: finite_union_compact -/
/-- The union of two compact sets is compact. -/
theorem IsCompact.union {K₁ K₂ : Set α}
    (h₁ : T.IsCompact K₁) (h₂ : T.IsCompact K₂) :
    T.IsCompact (K₁ ∪ K₂) := by
  intro 𝒰 h𝒰
  classical
  have h1cov : K₁ ⊆ ⋃₀ 𝒰 := fun x hx => h𝒰.2 (Or.inl hx)
  have h2cov : K₂ ⊆ ⋃₀ 𝒰 := fun x hx => h𝒰.2 (Or.inr hx)
  obtain ⟨𝒰₁, h𝒰₁sub, h𝒰₁fin, h𝒰₁cov⟩ := h₁ 𝒰 ⟨h𝒰.1, h1cov⟩
  obtain ⟨𝒰₂, h𝒰₂sub, h𝒰₂fin, h𝒰₂cov⟩ := h₂ 𝒰 ⟨h𝒰.1, h2cov⟩
  refine ⟨𝒰₁ ∪ 𝒰₂, ?_, ?_, ?_⟩
  · intro U hU
    rcases hU with hU | hU
    · exact h𝒰₁sub hU
    · exact h𝒰₂sub hU
  · obtain ⟨n₁, f₁, hf₁⟩ := h𝒰₁fin
    obtain ⟨n₂, f₂, hf₂⟩ := h𝒰₂fin
    refine ⟨n₁ + n₂, fun i =>
      if h : i.val < n₁ then f₁ ⟨i.val, h⟩
      else f₂ ⟨i.val - n₁, by
        have hi := i.isLt
        have hge : n₁ ≤ i.val := Nat.le_of_not_lt h
        omega⟩, ?_⟩
    rintro U (hU | hU)
    · obtain ⟨i, hi⟩ := hf₁ U hU
      refine ⟨⟨i.val, by have := i.isLt; omega⟩, ?_⟩
      have hlt : i.val < n₁ := i.isLt
      simp only [hlt, ↓reduceDIte]
      have heq : (⟨i.val, hlt⟩ : Fin n₁) = i := Fin.ext rfl
      rw [heq]; exact hi
    · obtain ⟨i, hi⟩ := hf₂ U hU
      refine ⟨⟨n₁ + i.val, by have := i.isLt; omega⟩, ?_⟩
      have hlt : ¬ (n₁ + i.val) < n₁ := by have := i.isLt; omega
      simp only [hlt, ↓reduceDIte]
      have heq : (⟨n₁ + i.val - n₁, by have := i.isLt; omega⟩ : Fin n₂) = i := by
        apply Fin.ext
        show n₁ + i.val - n₁ = i.val
        omega
      rw [heq]; exact hi
  · intro x hx
    rcases hx with hx | hx
    · obtain ⟨U, hU, hxU⟩ := h𝒰₁cov hx
      exact ⟨U, Or.inl hU, hxU⟩
    · obtain ⟨U, hU, hxU⟩ := h𝒰₂cov hx
      exact ⟨U, Or.inr hU, hxU⟩

/-! ### Finite families and finite unions of compacts. -/

/-- A singleton is compact. -/
theorem isCompact_singleton (a : α) : T.IsCompact ({a} : Set α) := by
  intro 𝒰 h𝒰
  classical
  obtain ⟨U, hU, haU⟩ := h𝒰.2 (show a ∈ ({a} : Set α) from rfl)
  refine ⟨fun V => V = U, ?_, ⟨1, fun _ => U, ?_⟩, ?_⟩
  · rintro V rfl; exact hU
  · rintro V rfl; exact ⟨0, rfl⟩
  · rintro x rfl
    exact ⟨U, rfl, haU⟩

/-! ### Compactness via the Hausdorff separation of a point and a compact set. -/

/- source: topology.mg:107917 name: Hausdorff_compact_sets_closed -/
/-- Separation lemma: in a Hausdorff space, given a point `x` and a compact
    set `K` not containing `x`, there exist disjoint open sets `U` (containing
    `x`) and `V` (containing `K`). This is the key step behind
    "compact subsets of Hausdorff are closed". -/
theorem IsCompact.separate_point (hH : T.IsHausdorff)
    {K : Set α} (hK : T.IsCompact K)
    {x : α} (hx : x ∉ K) :
    ∃ U V : Set α, T.IsOpen U ∧ T.IsOpen V ∧
      x ∈ U ∧ K ⊆ V ∧ ∀ z, z ∈ U → z ∈ V → False := by
  classical
  -- 𝒱 = family of opens W together with a witness open U ∋ x disjoint from W,
  -- where W contains some point of K. We encode this as a plain ∃ statement.
  let 𝒱 : Set (Set α) := fun W =>
    T.IsOpen W ∧ ∃ k, k ∈ K ∧ k ∈ W ∧
      ∃ U : Set α, T.IsOpen U ∧ x ∈ U ∧ ∀ z, z ∈ U → z ∈ W → False
  have hVopen : ∀ W ∈ 𝒱, T.IsOpen W := fun W h => h.1
  have hVcov : K ⊆ ⋃₀ 𝒱 := by
    intro k hkK
    have hne : k ≠ x := by
      intro heq; rw [heq] at hkK; exact hx hkK
    obtain ⟨W, U, hW, hU, hkW, hxU, hUW⟩ := hH k x hne
    refine ⟨W, ⟨hW, k, hkK, hkW, U, hU, hxU, ?_⟩, hkW⟩
    intro z hzU hzW
    exact hUW z hzW hzU
  obtain ⟨𝒱₀, h𝒱₀sub, h𝒱₀fin, h𝒱₀cov⟩ := hK 𝒱 ⟨hVopen, hVcov⟩
  obtain ⟨n, g, hg⟩ := h𝒱₀fin
  -- For each W ∈ 𝒱₀, pick a corresponding U_W.
  have hdata : ∀ W, W ∈ 𝒱₀ → ∃ U : Set α, T.IsOpen U ∧ x ∈ U ∧
      (∀ z, z ∈ U → z ∈ W → False) := by
    intro W hW
    rcases h𝒱₀sub hW with ⟨_, _, _, _, U, hU, hxU, hdisj⟩
    exact ⟨U, hU, hxU, hdisj⟩
  let Ui : Fin n → Set α := fun i =>
    if h : g i ∈ 𝒱₀ then Classical.choose (hdata (g i) h) else Set.univ
  have Uopen : ∀ i, T.IsOpen (Ui i) := by
    intro i
    show T.IsOpen (if h : g i ∈ 𝒱₀ then Classical.choose (hdata (g i) h) else Set.univ)
    split
    · next h => exact (Classical.choose_spec (hdata (g i) h)).1
    · exact T.isOpen_univ
  have Ux : ∀ i, x ∈ Ui i := by
    intro i
    show x ∈ (if h : g i ∈ 𝒱₀ then Classical.choose (hdata (g i) h) else Set.univ)
    split
    · next h => exact (Classical.choose_spec (hdata (g i) h)).2.1
    · trivial
  let U : Set α := fun z => ∀ i : Fin n, z ∈ Ui i
  let V : Set α := ⋃₀ 𝒱₀
  have hUopen : T.IsOpen U := T.isOpen_iInter_fin Ui Uopen
  have hVopen' : T.IsOpen V :=
    T.isOpen_sUnion (fun W hW => hVopen W (h𝒱₀sub hW))
  have hxU : x ∈ U := Ux
  have hKV : K ⊆ V := h𝒱₀cov
  have hdisj : ∀ z, z ∈ U → z ∈ V → False := by
    intro z hzU hzV
    rcases hzV with ⟨W, hW, hzW⟩
    obtain ⟨i, hi⟩ := hg W hW
    have hgi_mem : g i ∈ 𝒱₀ := by rw [hi]; exact hW
    have hzUi : z ∈ Ui i := hzU i
    have heq : Ui i = Classical.choose (hdata (g i) hgi_mem) := by
      show (if h : g i ∈ 𝒱₀ then Classical.choose (hdata (g i) h) else Set.univ) =
             Classical.choose (hdata (g i) hgi_mem)
      split
      · rfl
      · next h => exact absurd hgi_mem h
    rw [heq] at hzUi
    have hdj := (Classical.choose_spec (hdata (g i) hgi_mem)).2.2
    apply hdj z hzUi
    rw [hi]; exact hzW
  exact ⟨U, V, hUopen, hVopen', hxU, hKV, hdisj⟩

/-- In a Hausdorff space, every compact subset is closed. -/
theorem IsCompact.isClosed_of_isHausdorff (hH : T.IsHausdorff)
    {K : Set α} (hK : T.IsCompact K) : T.IsClosed K := by
  apply T.isOpen_of_local_nhd
  intro x hxKc
  obtain ⟨U, V, hU, _, hxU, hKV, hdisj⟩ :=
    hK.separate_point T hH hxKc
  refine ⟨U, hU, hxU, ?_⟩
  intro y hyU hyK
  exact hdisj y hyU (hKV hyK)

/-! ### §26 named forms. -/

/-- `Compact` is shorthand for `IsCompact Set.univ`. -/
theorem compact_iff_univ : T.Compact ↔ T.IsCompact (Set.univ : Set α) := Iff.rfl

/-- A compact space is closed (as a subset of itself: univ). -/
theorem isClosed_univ_of_compact (_h : T.Compact) : T.IsClosed (Set.univ : Set α) :=
  T.isClosed_univ

/-- Finite union of compact sets is compact (two-set version). -/
theorem IsCompact.union_two {K₁ K₂ : Set α}
    (h₁ : T.IsCompact K₁) (h₂ : T.IsCompact K₂) :
    T.IsCompact (K₁ ∪ K₂) := h₁.union T h₂

/-- Closed subsets of a compact subspace are compact (the form used by §32). -/
theorem IsCompact.of_isClosed_subset
    {K L : Set α} (hK : T.IsCompact K) (hL : T.IsClosed L)
    (hLK : L ⊆ K) : T.IsCompact L := by
  -- Any cover of L gives a cover of K by adjoining Lᶜ, and finitely many
  -- members can be found; drop Lᶜ.
  intro 𝒰 h𝒰
  classical
  let 𝒰' : Set (Set α) := fun U => U ∈ 𝒰 ∨ U = Lᶜ
  have hopen' : ∀ U ∈ 𝒰', T.IsOpen U := by
    intro U hU
    rcases hU with hU | rfl
    · exact h𝒰.1 U hU
    · exact hL
  have hcov' : K ⊆ ⋃₀ 𝒰' := by
    intro x hxK
    classical
    by_cases hxL : x ∈ L
    · obtain ⟨U, hU, hxU⟩ := h𝒰.2 hxL
      exact ⟨U, Or.inl hU, hxU⟩
    · exact ⟨Lᶜ, Or.inr rfl, hxL⟩
  obtain ⟨𝒰₀', h𝒰₀'sub, h𝒰₀'fin, h𝒰₀'cov⟩ := hK 𝒰' ⟨hopen', hcov'⟩
  refine ⟨(fun U => U ∈ 𝒰₀' ∧ U ≠ Lᶜ), ?_, ?_, ?_⟩
  · intro U hU
    rcases h𝒰₀'sub hU.1 with hU' | hU'
    · exact hU'
    · exact (hU.2 hU').elim
  · obtain ⟨n, f, hf⟩ := h𝒰₀'fin
    exact ⟨n, f, fun U hU => hf U hU.1⟩
  · intro x hxL
    obtain ⟨U, hU₀, hxU⟩ := h𝒰₀'cov (hLK hxL)
    classical
    by_cases h : U = Lᶜ
    · rw [h] at hxU; exact (hxU hxL).elim
    · exact ⟨U, ⟨hU₀, h⟩, hxU⟩

end Topology
end Mgw
