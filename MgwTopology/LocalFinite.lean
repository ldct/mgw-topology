/-
Local finiteness.

Corresponds to topology.mg §39 (Local Finiteness and the Nagata-Smirnov
metrization theorem, set-theoretic core). We port the parts that do not
mention real numbers or the full Nagata-Smirnov theorem.

A family of subsets `F : Set (Set α)` is locally finite if every point has
an open neighborhood meeting only finitely many members of `F`.
-/
import MgwTopology.Section_12_Core
import MgwTopology.ClosureInterior
import MgwTopology.ClosedAndLimit
import MgwTopology.Basis
import MgwTopology.Countability

namespace Mgw
namespace Topology

universe u
variable {α : Type u} (T : Topology α)

/-- A family `F : Set (Set α)` is *locally finite* in `T` iff every point has
an open neighborhood meeting only finitely many members of `F`. -/
def LocallyFiniteFamily (F : Set (Set α)) : Prop :=
  ∀ x : α, ∃ N : Set α, T.IsOpen N ∧ x ∈ N ∧
    ∃ S : Set (Set α), S.Finite ∧ S ⊆ F ∧
      ∀ A, A ∈ F → (∃ y, y ∈ A ∧ y ∈ N) → A ∈ S

/-- σ-locally finite: a countable union of locally finite families. -/
def SigmaLocallyFiniteFamily (F : Set (Set α)) : Prop :=
  ∃ 𝓕 : Set (Set (Set α)), 𝓕.Countable ∧
    (∀ G, G ∈ 𝓕 → T.LocallyFiniteFamily G) ∧
    F = ⋃₀ 𝓕

/-! ### §39 elementary lemmas. -/

/- source: topology.mg:220611 name: lemma39_1a_subcollection_locally_finite -/
/-- A sub-family of a locally-finite family is locally finite. -/
theorem LocallyFiniteFamily.mono {F G : Set (Set α)}
    (hF : T.LocallyFiniteFamily F) (hGF : G ⊆ F) :
    T.LocallyFiniteFamily G := by
  intro x
  obtain ⟨N, hN, hxN, S, hSfin, hSF, hSprop⟩ := hF x
  -- SG := {A ∈ S | A ∈ G}
  refine ⟨N, hN, hxN, (fun A => A ∈ S ∧ A ∈ G), ?_, ?_, ?_⟩
  · -- Finite as subset of finite S.
    obtain ⟨n, f, hf⟩ := hSfin
    refine ⟨n, f, ?_⟩
    intro A hA
    exact hf A hA.1
  · intro A hA; exact hA.2
  · intro A hAG hmeet
    have hAF : A ∈ F := hGF hAG
    exact ⟨hSprop A hAF hmeet, hAG⟩

/-- Singleton family is locally finite. -/
/- source: topology.mg:228743 name: locally_finite_family_singleton -/
theorem LocallyFiniteFamily.singleton (A : Set α) :
    T.LocallyFiniteFamily ({A} : Set (Set α)) := by
  intro x
  refine ⟨Set.univ, T.isOpen_univ, trivial, ({A} : Set (Set α)),
    ⟨1, fun _ => A, ?_⟩, fun B h => h, ?_⟩
  · intro B hB
    have hBA : B = A := hB
    exact ⟨⟨0, Nat.one_pos⟩, hBA.symm⟩
  · intro B hB _; exact hB

/-- Empty family is locally finite. -/
theorem LocallyFiniteFamily.empty : T.LocallyFiniteFamily (∅ : Set (Set α)) := by
  intro x
  refine ⟨Set.univ, T.isOpen_univ, trivial, (∅ : Set (Set α)),
    ⟨0, Fin.elim0, fun _ h => h.elim⟩, fun _ h => h, ?_⟩
  intro A hA _; exact hA

/-- Locally finite families are point-finite: only finitely many members
contain a given point. -/
/- source: topology.mg:210686 name: locally_finite_family_point_finite_ex -/
theorem LocallyFiniteFamily.point_finite {F : Set (Set α)}
    (hF : T.LocallyFiniteFamily F) (x : α) :
    ∃ S : Set (Set α), S.Finite ∧ S ⊆ F ∧
      ∀ A, A ∈ F → x ∈ A → A ∈ S := by
  obtain ⟨N, hN, hxN, S, hSfin, hSF, hSprop⟩ := hF x
  refine ⟨S, hSfin, hSF, ?_⟩
  intro A hAF hxA
  exact hSprop A hAF ⟨x, hxA, hxN⟩

/-! ### §39 Lemma 39.1(b): closures of a locally-finite family are locally finite. -/

/- source: topology.mg:220623 name: lemma39_1b_closures_locally_finite -/
/-- If `F` is locally finite, so is the family of closures of members of `F`. -/
theorem LocallyFiniteFamily.closures {F : Set (Set α)}
    (hF : T.LocallyFiniteFamily F) :
    T.LocallyFiniteFamily (Set.image (T.closure) F) := by
  classical
  intro x
  obtain ⟨N, hN, hxN, S, hSfin, hSF, hSprop⟩ := hF x
  -- SCl := image closure S
  refine ⟨N, hN, hxN, Set.image (T.closure) S, ?_, ?_, ?_⟩
  · -- Finite image.
    obtain ⟨n, f, hf⟩ := hSfin
    refine ⟨n, fun i => T.closure (f i), ?_⟩
    rintro C ⟨A, hA, rfl⟩
    obtain ⟨i, hi⟩ := hf A hA
    refine ⟨i, ?_⟩
    show T.closure (f i) = T.closure A
    rw [hi]
  · rintro C ⟨A, hA, rfl⟩
    exact ⟨A, hSF hA, rfl⟩
  · rintro C ⟨A, hA, rfl⟩ ⟨y, hyC, hyN⟩
    -- y ∈ closure A and y ∈ N (open). So N ∩ A ≠ ∅ by the closure characterization.
    have hmeetN : ∃ z, z ∈ N ∧ z ∈ A := by
      rw [T.mem_closure_iff] at hyC
      exact hyC N hN hyN
    obtain ⟨z, hzN, hzA⟩ := hmeetN
    have hASmem : A ∈ S := hSprop A hA ⟨z, hzA, hzN⟩
    exact ⟨A, hASmem, rfl⟩

/-! ### §39 Lemma 39.1(c): closure of the union equals union of closures. -/

/- Auxiliary: closure of a union contains each member's closure (no LF needed). -/
theorem closure_sUnion_contains_sUnion_closures (F : Set (Set α)) :
    ⋃₀ (Set.image T.closure F) ⊆ T.closure (⋃₀ F) := by
  rintro x ⟨C, ⟨A, hAF, rfl⟩, hxC⟩
  have : A ⊆ ⋃₀ F := Set.subset_sUnion_of_mem hAF
  exact T.closure_mono this hxC

/- source: topology.mg:220635 name: lemma39_1c_closure_Union_eq_Union_closures -/
/-- Closure of the union of a locally-finite family equals the union of closures. -/
theorem LocallyFiniteFamily.closure_sUnion {F : Set (Set α)}
    (hF : T.LocallyFiniteFamily F) :
    T.closure (⋃₀ F) = ⋃₀ (Set.image T.closure F) := by
  classical
  apply Set.subset_antisymm
  · -- Forward: the hard direction using local finiteness.
    intro x hxcl
    by_contra hnot
    -- Goal: find an open N around x avoiding Union-of-closures; then show x ∉ closure(Union F).
    obtain ⟨N, hN, hxN, S, hSfin, hSF, hSprop⟩ := hF x
    -- For each A ∈ S we have A ∈ F, so closure A ∈ image closure F.
    -- Since x ∉ ⋃₀ (image closure F), for every A ∈ F: x ∉ closure A.
    have hxCl_not : ∀ A, A ∈ F → x ∉ T.closure A := by
      intro A hAF hxClA
      apply hnot
      exact ⟨T.closure A, ⟨A, hAF, rfl⟩, hxClA⟩
    -- For each A ∈ S, pick an open V_A with x ∈ V_A and V_A ∩ A = ∅.
    have hchoice : ∀ A, A ∈ S → ∃ V : Set α, T.IsOpen V ∧ x ∈ V ∧
        ∀ z, z ∈ V → z ∉ A := by
      intro A hA
      have hAF : A ∈ F := hSF hA
      have hx_notClA : x ∉ T.closure A := hxCl_not A hAF
      -- x ∉ closure A gives an open V with x ∈ V and V ∩ A = ∅.
      classical
      by_contra hno
      apply hx_notClA
      rw [T.mem_closure_iff]
      intro U hU hxU
      by_contra hmeet
      apply hno
      refine ⟨U, hU, hxU, ?_⟩
      intro z hzU hzA
      exact hmeet ⟨z, hzU, hzA⟩
    -- Build a finite intersection V = N ∩ (⋂ V_A for A ∈ S).
    obtain ⟨n, f, hf⟩ := hSfin
    -- For each i : Fin n, produce W i: open nbhd of x disjoint from f i.
    let W : Fin n → Set α := fun i =>
      if h : f i ∈ S then Classical.choose (hchoice (f i) h) else Set.univ
    have hW_open : ∀ i, T.IsOpen (W i) := by
      intro i
      show T.IsOpen (if h : f i ∈ S then Classical.choose (hchoice (f i) h) else Set.univ)
      split
      · next h => exact (Classical.choose_spec (hchoice (f i) h)).1
      · exact T.isOpen_univ
    have hW_mem : ∀ i, x ∈ W i := by
      intro i
      show x ∈ (if h : f i ∈ S then Classical.choose (hchoice (f i) h) else Set.univ)
      split
      · next h => exact (Classical.choose_spec (hchoice (f i) h)).2.1
      · trivial
    have hW_disj : ∀ i, f i ∈ S → ∀ z, z ∈ W i → z ∉ f i := by
      intro i hi z hzW hzA
      have heq : W i = Classical.choose (hchoice (f i) hi) := by
        show (if h : f i ∈ S then Classical.choose (hchoice (f i) h) else Set.univ) =
             Classical.choose (hchoice (f i) hi)
        rw [dif_pos hi]
      rw [heq] at hzW
      exact (Classical.choose_spec (hchoice (f i) hi)).2.2 z hzW hzA
    -- V := N ∩ (⋂ i, W i). Open, contains x.
    let V : Set α := N ∩ (fun y => ∀ i : Fin n, y ∈ W i)
    have hV_open : T.IsOpen V := by
      apply T.isOpen_inter hN
      exact T.isOpen_iInter_fin W hW_open
    have hxV : x ∈ V := ⟨hxN, fun i => hW_mem i⟩
    -- V is disjoint from every A ∈ F: V ⊆ N rules out the "A ∩ N ≠ ∅ ⇒ A ∈ S" case,
    -- and the inner intersection rules out `A ∈ S`.
    have hV_disj_F : ∀ A, A ∈ F → ∀ z, z ∈ V → z ∉ A := by
      intro A hAF z hzV hzA
      have hzN : z ∈ N := hzV.1
      -- A meets N at z, so by hSprop, A ∈ S.
      have hAS : A ∈ S := hSprop A hAF ⟨z, hzA, hzN⟩
      obtain ⟨i, hi⟩ := hf A hAS
      have hziW : z ∈ W i := hzV.2 i
      -- f i = A, so f i ∈ S and we can conclude z ∉ f i = A.
      have hi_mem : f i ∈ S := by rw [hi]; exact hAS
      have : z ∉ f i := hW_disj i hi_mem z hziW
      exact this (by rw [hi]; exact hzA)
    -- Now x ∈ closure (⋃₀ F), so V must meet ⋃₀ F: contradiction.
    have hxcl' : x ∈ T.closure (⋃₀ F) := hxcl
    rw [T.mem_closure_iff] at hxcl'
    obtain ⟨w, hwV, U, hUF, hwU⟩ := hxcl' V hV_open hxV
    exact hV_disj_F U hUF w hwV hwU
  · exact T.closure_sUnion_contains_sUnion_closures F

/-! ### §39 closure-family point finiteness. -/

/- source: topology.mg:220651 name: locally_finite_family_closure_point_finite_ex -/
/-- For each point, only finitely many members of a locally-finite family have
a closure containing that point. -/
theorem LocallyFiniteFamily.closure_point_finite {F : Set (Set α)}
    (hF : T.LocallyFiniteFamily F) (x : α) :
    ∃ S : Set (Set α), S.Finite ∧ S ⊆ Set.image T.closure F ∧
      ∀ A, A ∈ F → x ∈ T.closure A → T.closure A ∈ S := by
  have hCl : T.LocallyFiniteFamily (Set.image T.closure F) := hF.closures T
  obtain ⟨S, hSfin, hSsub, hSprop⟩ := hCl.point_finite T x
  refine ⟨S, hSfin, hSsub, ?_⟩
  intro A hAF hxClA
  exact hSprop (T.closure A) ⟨A, hAF, rfl⟩ hxClA

/-! ### Trivial wrapping: locally finite is σ-locally finite. -/

/- source: topology.mg:228778 name: locally_finite_family_imp_sigma_locally_finite_family -/
theorem LocallyFiniteFamily.sigma {F : Set (Set α)}
    (hF : T.LocallyFiniteFamily F) : T.SigmaLocallyFiniteFamily F := by
  -- Take 𝓕 := {F} (the singleton family of families).
  refine ⟨({F} : Set (Set (Set α))),
    Or.inr ⟨fun _ => F, fun G (hG : G = F) => ⟨0, hG.symm⟩⟩, ?_, ?_⟩
  · intro G hG
    have : G = F := hG
    rw [this]; exact hF
  · ext x
    refine ⟨fun hx => ⟨F, rfl, hx⟩, ?_⟩
    rintro ⟨G, (hG : G = F), hxG⟩
    rw [hG] at hxG; exact hxG

/-! ### §39 singleton decomposition for second-countable spaces. -/

/-- A σ-locally-finite basis: a basis that is a countable union of
locally-finite families. Encoded by the data directly. -/
def SigmaLocallyFiniteBasis (ℬ : Set (Set α)) : Prop :=
  IsBasis ℬ ∧ (∀ B, B ∈ ℬ → T.IsOpen B) ∧
  (∀ U, T.IsOpen U ↔ Topology.generatedBy ℬ U) ∧
  T.SigmaLocallyFiniteFamily ℬ

/- source: topology.mg:220769 name: second_countable_implies_sigma_locally_finite_basis -/
/-- Every second-countable space has a σ-locally-finite basis (namely the
basis itself, decomposed into singletons). -/
theorem SigmaLocallyFiniteBasis.of_secondCountable (h : T.SecondCountable) :
    ∃ ℬ : Set (Set α), T.SigmaLocallyFiniteBasis ℬ := by
  classical
  obtain ⟨ℬ, hℬc, hℬbasis, hℬgen⟩ := h
  refine ⟨ℬ, hℬbasis, ?_, hℬgen, ?_⟩
  · -- Every basis member is open in T.
    intro B hB
    rw [hℬgen]
    intro y hyB
    exact ⟨B, hB, hyB, fun _ h => h⟩
  · -- σ-locally-finite: take 𝓕 = {{B} | B ∈ ℬ}, each singleton is LF, countable.
    refine ⟨Set.image (fun B => ({B} : Set (Set α))) ℬ, ?_, ?_, ?_⟩
    · -- Countable image.
      exact Set.Countable.image hℬc _
    · -- Each family is locally finite (singleton).
      rintro G ⟨B, hB, rfl⟩
      exact LocallyFiniteFamily.singleton T B
    · -- ℬ = ⋃₀ {{B} | B ∈ ℬ}.
      ext U
      refine ⟨fun hU => ⟨({U} : Set (Set α)), ⟨U, hU, rfl⟩, rfl⟩, ?_⟩
      rintro ⟨G, ⟨B, hB, rfl⟩, (hU : U = B)⟩
      rw [hU]; exact hB

/-! ### §39 basis → basis-refines. -/

/- source: topology.mg:220732 name: basis_generates_imp_basis_refines -/
/-- If `ℬ` is a basis generating the topology `T`, then every open set `U`
contains a basis element around each of its points. -/
theorem basis_refines_of_generates {ℬ : Set (Set α)}
    (_hℬ : IsBasis ℬ) (hgen : ∀ U, T.IsOpen U ↔ Topology.generatedBy ℬ U)
    {U : Set α} (hU : T.IsOpen U) {x : α} (hxU : x ∈ U) :
    ∃ B, B ∈ ℬ ∧ x ∈ B ∧ B ⊆ U := by
  rw [hgen] at hU
  exact hU x hxU

end Topology
end Mgw
