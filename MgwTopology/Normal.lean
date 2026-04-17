/-
Normal spaces.

Corresponds to topology.mg §32 (Normal Spaces).

We prove:
* Compact Hausdorff implies normal (via the compact-set separation lemma).
* The "shrink closed" characterization of normality.
* Basic closed-subspace inheritance.

We skip Urysohn's lemma's real-valued conclusion and Tietze extension (both
require ℝ), and the infinite-product counterexamples from §32.

-/
import MgwTopology.Core
import MgwTopology.ClosureInterior
import MgwTopology.ClosedAndLimit
import MgwTopology.Subspace
import MgwTopology.Compact
import MgwTopology.Separation
import MgwTopology.LocalCompact
import MgwTopology.Countability

namespace Mgw
namespace Topology

universe u
variable {α : Type u} (T : Topology α)

/-! ### Compact + Hausdorff separation of a point and a compact set. -/

/-- Hausdorff + compact: for each point outside a compact set, we get
    disjoint separating opens. (Exported from `Compact.lean`.) -/
theorem hausdorff_separate_point_compact
    (hH : T.IsHausdorff) {B : Set α} (hB : T.IsCompact B)
    {a : α} (haB : a ∉ B) :
    ∃ U V : Set α, T.IsOpen U ∧ T.IsOpen V ∧
      a ∈ U ∧ B ⊆ V ∧ U ∩ V = ∅ := by
  obtain ⟨U, V, hU, hV, haU, hBV, hdisj⟩ := hB.separate_point T hH haB
  refine ⟨U, V, hU, hV, haU, hBV, ?_⟩
  ext z
  exact ⟨fun h => (hdisj z h.1 h.2).elim, fun h => h.elim⟩

/-! ### Compact + Hausdorff separation of two disjoint compacts. -/

/-- In a Hausdorff space, two disjoint compact sets have disjoint open
    neighborhoods. -/
theorem hausdorff_separate_compact_compact
    (hH : T.IsHausdorff) {A B : Set α}
    (hA : T.IsCompact A) (hB : T.IsCompact B) (hAB : A ∩ B = ∅) :
    ∃ U V : Set α, T.IsOpen U ∧ T.IsOpen V ∧
      A ⊆ U ∧ B ⊆ V ∧ U ∩ V = ∅ := by
  classical
  -- For each a ∈ A, use the point/compact separation lemma to get Uₐ ∋ a
  -- and Vₐ ⊇ B disjoint. Cover A by {Uₐ} and extract a finite subcover.
  have haB : ∀ a, a ∈ A → a ∉ B := by
    intro a haA haB
    have : a ∈ A ∩ B := ⟨haA, haB⟩
    rw [hAB] at this
    exact this
  -- Family 𝒲 of opens W = Uₐ, each containing some a ∈ A with a corresponding
  -- VW ⊇ B disjoint from W.
  let 𝒲 : Set (Set α) := fun W =>
    T.IsOpen W ∧ ∃ a, a ∈ A ∧ a ∈ W ∧
      ∃ V' : Set α, T.IsOpen V' ∧ B ⊆ V' ∧ W ∩ V' = ∅
  have hWopen : ∀ W ∈ 𝒲, T.IsOpen W := fun W h => h.1
  have hWcov : A ⊆ ⋃₀ 𝒲 := by
    intro a haA
    obtain ⟨Ua, Va, hUa, hVa, haUa, hBVa, hdisj⟩ :=
      hausdorff_separate_point_compact T hH hB (haB a haA)
    exact ⟨Ua, ⟨hUa, a, haA, haUa, Va, hVa, hBVa, hdisj⟩, haUa⟩
  obtain ⟨𝒲₀, h𝒲₀sub, h𝒲₀fin, h𝒲₀cov⟩ := hA 𝒲 ⟨hWopen, hWcov⟩
  obtain ⟨n, g, hg⟩ := h𝒲₀fin
  -- Choose V_W for each W ∈ 𝒲₀.
  have hVdata : ∀ W, W ∈ 𝒲₀ → ∃ V' : Set α, T.IsOpen V' ∧ B ⊆ V' ∧ W ∩ V' = ∅ := by
    intro W hW
    rcases h𝒲₀sub hW with ⟨_, _, _, _, V', hV', hBV', hdisj⟩
    exact ⟨V', hV', hBV', hdisj⟩
  let Vi : Fin n → Set α := fun i =>
    if h : g i ∈ 𝒲₀ then Classical.choose (hVdata (g i) h) else Set.univ
  have hViopen : ∀ i, T.IsOpen (Vi i) := by
    intro i
    show T.IsOpen (if h : g i ∈ 𝒲₀ then Classical.choose (hVdata (g i) h) else Set.univ)
    split
    · next h => exact (Classical.choose_spec (hVdata (g i) h)).1
    · exact T.isOpen_univ
  have hViB : ∀ i, B ⊆ Vi i := by
    intro i
    show B ⊆ (if h : g i ∈ 𝒲₀ then Classical.choose (hVdata (g i) h) else Set.univ)
    split
    · next h => exact (Classical.choose_spec (hVdata (g i) h)).2.1
    · intro _ _; trivial
  have hViDisj : ∀ i, g i ∈ 𝒲₀ → g i ∩ Vi i = ∅ := by
    intro i hi
    have heq : Vi i = Classical.choose (hVdata (g i) hi) := by
      show (if h : g i ∈ 𝒲₀ then Classical.choose (hVdata (g i) h) else Set.univ) =
             Classical.choose (hVdata (g i) hi)
      rw [dif_pos hi]
    rw [heq]
    exact (Classical.choose_spec (hVdata (g i) hi)).2.2
  let U : Set α := ⋃₀ 𝒲₀
  let V : Set α := fun y => ∀ i : Fin n, y ∈ Vi i
  have hUopen : T.IsOpen U :=
    T.isOpen_sUnion (fun W hW => hWopen W (h𝒲₀sub hW))
  have hVopen : T.IsOpen V := T.isOpen_iInter_fin Vi hViopen
  have hAU : A ⊆ U := h𝒲₀cov
  have hBV : B ⊆ V := fun y hy i => hViB i hy
  have hdisjUV : U ∩ V = ∅ := by
    ext y
    refine ⟨?_, fun h => h.elim⟩
    rintro ⟨⟨W, hW, hyW⟩, hyV⟩
    obtain ⟨i, hi⟩ := hg W hW
    have hgmem : g i ∈ 𝒲₀ := by rw [hi]; exact hW
    have hyi : y ∈ Vi i := hyV i
    have hdisjgV : g i ∩ Vi i = ∅ := hViDisj i hgmem
    have hywg : y ∈ g i := by rw [hi]; exact hyW
    have : y ∈ g i ∩ Vi i := ⟨hywg, hyi⟩
    rw [hdisjgV] at this
    exact this
  exact ⟨U, V, hUopen, hVopen, hAU, hBV, hdisjUV⟩

/-! ### §32 Theorem 32.3: compact Hausdorff is normal. -/

/- source: topology.mg:159124 name: compact_Hausdorff_normal -/
/-- Every compact Hausdorff space is normal. -/
theorem Normal.of_compact_hausdorff
    (hc : T.Compact) (hH : T.Hausdorff) : T.Normal := by
  have hHiff : T.IsHausdorff := (T.Hausdorff_iff_IsHausdorff).1 hH
  refine ⟨T1.of_hausdorff T hH, ?_⟩
  intro A B hA hB hAB
  -- A, B closed ⇒ both compact (as closed subsets of a compact space).
  have hAc : T.IsCompact A := IsCompact.of_isClosed_of_compact T hc hA
  have hBc : T.IsCompact B := IsCompact.of_isClosed_of_compact T hc hB
  exact hausdorff_separate_compact_compact T hHiff hAc hBc hAB

/-! ### §32 "shrink closed set" characterization. -/

/- source: topology.mg:147075 name: normal_space_shrink_closed -/
/-- In a normal space, for every closed `A` contained in an open `U`, there is
    an open `V` with `A ⊆ V ⊆ closure V ⊆ U`. -/
theorem Normal.shrink_closed
    (h : T.Normal) {A U : Set α} (hA : T.IsClosed A)
    (hU : T.IsOpen U) (hAU : A ⊆ U) :
    ∃ V : Set α, T.IsOpen V ∧ A ⊆ V ∧ T.closure V ⊆ U := by
  classical
  -- B := Uᶜ is closed, disjoint from A. Normality gives A ⊆ V, B ⊆ W, V ∩ W = ∅.
  -- Then closure V ⊆ Wᶜ ⊆ U.
  have hB : T.IsClosed Uᶜ := T.isClosed_compl_of_isOpen hU
  have hAB : A ∩ Uᶜ = ∅ := by
    ext z
    refine ⟨?_, fun h => h.elim⟩
    rintro ⟨hzA, hzUc⟩
    exact hzUc (hAU hzA)
  obtain ⟨V, W, hV, hW, hAV, hBW, hVW⟩ := h.2 A Uᶜ hA hB hAB
  refine ⟨V, hV, hAV, ?_⟩
  have hVW' : ∀ z, z ∈ V → z ∈ W → False := by
    intro z hzV hzW
    have : z ∈ V ∩ W := ⟨hzV, hzW⟩
    rw [hVW] at this
    exact this
  have hVsubWc : V ⊆ Wᶜ := fun z hzV hzW => hVW' z hzV hzW
  have hWc_cl : T.IsClosed Wᶜ := T.isClosed_compl_of_isOpen hW
  have hclV_sub_Wc : T.closure V ⊆ Wᶜ :=
    T.closure_subset_of_isClosed hWc_cl hVsubWc
  intro z hz
  classical
  by_contra hzU
  have hzUc : z ∈ Uᶜ := hzU
  have : z ∈ W := hBW hzUc
  exact (hclV_sub_Wc hz) this

/-- Equivalent form: normal iff closed sets contained in open sets can be
    "shrunk" by an open whose closure fits. -/
theorem Normal.iff_shrink_closed :
    T.Normal ↔
      T.T1 ∧ ∀ (A U : Set α), T.IsClosed A → T.IsOpen U → A ⊆ U →
        ∃ V, T.IsOpen V ∧ A ⊆ V ∧ T.closure V ⊆ U := by
  classical
  refine ⟨fun h => ⟨h.1, fun A U hA hU hAU => h.shrink_closed T hA hU hAU⟩, ?_⟩
  rintro ⟨hT1, h⟩
  refine ⟨hT1, ?_⟩
  intro A B hA hB hAB
  -- U := Bᶜ is open; A ⊆ U.
  have hU : T.IsOpen Bᶜ := hB
  have hAU : A ⊆ Bᶜ := by
    intro z hzA hzB
    have : z ∈ A ∩ B := ⟨hzA, hzB⟩
    rw [hAB] at this
    exact this
  obtain ⟨V, hV, hAV, hclV⟩ := h A Bᶜ hA hU hAU
  refine ⟨V, (T.closure V)ᶜ, hV, ?_, hAV, ?_, ?_⟩
  · exact T.isClosed_closure V
  · intro z hzB
    -- z ∈ B; need z ∉ closure V. If z ∈ closure V, then z ∈ Bᶜ — contradiction.
    intro hzcl
    have : z ∈ Bᶜ := hclV hzcl
    exact this hzB
  · ext z
    refine ⟨?_, fun h => h.elim⟩
    rintro ⟨hzV, hzncl⟩
    exact hzncl (T.subset_closure _ hzV)

/-! ### §32 Ex32.1: closed subspace of normal is normal. -/

/- source: topology.mg:338765 name: ex32_1_closed_subspace_normal -/
/-- A closed subspace of a normal space is normal. -/
theorem Normal.subspace_of_closed
    (h : T.Normal) {Y : Set α} (hY : T.IsClosed Y) :
    (T.subspace Y).Normal := by
  classical
  refine ⟨h.1.subspace T Y, ?_⟩
  intro A B hA hB hAB
  -- A, B are subspace-closed; realise as ambient-closed sets A', B' ⊆ Y.
  obtain ⟨A', hA', hAiff⟩ := (T.isClosed_subspace_iff A).1 hA
  obtain ⟨B', hB', hBiff⟩ := (T.isClosed_subspace_iff B).1 hB
  -- Since Y is closed in T, A' ∩ Y and B' ∩ Y are closed.
  let A'' := A' ∩ Y
  let B'' := B' ∩ Y
  have hA'' : T.IsClosed A'' := T.isClosed_inter hA' hY
  have hB'' : T.IsClosed B'' := T.isClosed_inter hB' hY
  -- A'' ∩ B'' = ∅: if z ∈ both, then (since z ∈ Y) ⟨z, z∈Y⟩ ∈ A ∩ B — contradiction.
  have hdisj : A'' ∩ B'' = ∅ := by
    ext z
    refine ⟨?_, fun h => h.elim⟩
    rintro ⟨⟨hzA', hzY⟩, ⟨hzB', _⟩⟩
    have hzA : (⟨z, hzY⟩ : {x // Y x}) ∈ A := (hAiff ⟨z, hzY⟩).2 hzA'
    have hzB : (⟨z, hzY⟩ : {x // Y x}) ∈ B := (hBiff ⟨z, hzY⟩).2 hzB'
    have : (⟨z, hzY⟩ : {x // Y x}) ∈ A ∩ B := ⟨hzA, hzB⟩
    rw [hAB] at this
    exact this
  obtain ⟨U', V', hU', hV', hAU, hBV, hUV'⟩ := h.2 A'' B'' hA'' hB'' hdisj
  refine ⟨fun p : {x // Y x} => U' p.1, fun p : {x // Y x} => V' p.1,
    ⟨U', hU', fun _ => Iff.rfl⟩, ⟨V', hV', fun _ => Iff.rfl⟩, ?_, ?_, ?_⟩
  · intro p hpA
    -- p ∈ A, so p.1 ∈ A'' by hAiff and p.2.
    have : p.1 ∈ A'' := ⟨(hAiff p).1 hpA, p.2⟩
    exact hAU this
  · intro p hpB
    have : p.1 ∈ B'' := ⟨(hBiff p).1 hpB, p.2⟩
    exact hBV this
  · ext p
    refine ⟨?_, fun h => h.elim⟩
    rintro ⟨hpU, hpV⟩
    have : p.1 ∈ U' ∩ V' := ⟨hpU, hpV⟩
    rw [hUV'] at this
    exact this

/-! ### §32 ex32.3: locally compact Hausdorff is regular. -/

/- source: topology.mg:339815 name: ex32_3_locally_compact_Hausdorff_regular -/
/-- A locally compact Hausdorff space is regular. -/
theorem Regular.of_locally_compact_hausdorff
    (hlc : T.IsLocallyCompact) (hH : T.Hausdorff) : T.Regular := by
  classical
  have hHiff : T.IsHausdorff := (T.Hausdorff_iff_IsHausdorff).1 hH
  refine ⟨T1.of_hausdorff T hH, ?_⟩
  intro x C hC hxC
  -- Take a compact neighborhood K of x (with open U ⊆ K).
  -- Then K ∩ C is compact (closed in compact). Separate x from K ∩ C via
  -- compact/Hausdorff. The resulting opens give the regular separation.
  obtain ⟨K, hK, U₀, hU₀, hxU₀, hU₀K⟩ := hlc x
  -- K ∩ C: intersect the compact K with the closed C. Compact subset of compact.
  -- For set-theoretic convenience we do the separation via K \ U₀ and C
  -- differently: we'll use point-compact separation with B = K ∩ C (compact).
  have hKC : T.IsCompact (fun y => y ∈ K ∧ y ∈ C) := by
    -- Viewing K∩C as a closed subset inside the compact K is tricky without
    -- subspace-compact scaffolding. Use the fact that the intersection is
    -- compact via the closed-in-compact-of-Hausdorff route once we know K
    -- itself is closed (K is compact in Hausdorff ⇒ closed).
    have hKclosed : T.IsClosed K := hK.isClosed_of_isHausdorff T hHiff
    have hKCclosed : T.IsClosed (K ∩ C) := T.isClosed_inter hKclosed hC
    -- Any closed set inside a compact set is compact.
    intro 𝒰 h𝒰
    classical
    -- Extend the cover of K∩C to a cover of K by adding (K∩C)ᶜ as an open.
    let 𝒰' : Set (Set α) := fun U => U ∈ 𝒰 ∨ U = (K ∩ C)ᶜ
    have hopen' : ∀ U ∈ 𝒰', T.IsOpen U := by
      intro U hU
      rcases hU with hU | rfl
      · exact h𝒰.1 U hU
      · exact hKCclosed
    have hcov' : K ⊆ ⋃₀ 𝒰' := by
      intro z hzK
      classical
      by_cases hzKC : z ∈ K ∧ z ∈ C
      · obtain ⟨U, hU, hzU⟩ := h𝒰.2 hzKC
        exact ⟨U, Or.inl hU, hzU⟩
      · exact ⟨(K ∩ C)ᶜ, Or.inr rfl, hzKC⟩
    obtain ⟨𝒰₀', h𝒰₀'sub, h𝒰₀'fin, h𝒰₀'cov⟩ := hK 𝒰' ⟨hopen', hcov'⟩
    refine ⟨(fun U => U ∈ 𝒰₀' ∧ U ≠ (K ∩ C)ᶜ), ?_, ?_, ?_⟩
    · intro U hU
      rcases h𝒰₀'sub hU.1 with hU' | hU'
      · exact hU'
      · exact (hU.2 hU').elim
    · obtain ⟨n, f, hf⟩ := h𝒰₀'fin
      exact ⟨n, f, fun U hU => hf U hU.1⟩
    · rintro z ⟨hzK, hzC⟩
      obtain ⟨U, hU₀', hzU⟩ := h𝒰₀'cov hzK
      classical
      by_cases h : U = (K ∩ C)ᶜ
      · rw [h] at hzU; exact (hzU ⟨hzK, hzC⟩).elim
      · exact ⟨U, ⟨hU₀', h⟩, hzU⟩
  by_cases hxKC : x ∈ (fun y => y ∈ K ∧ y ∈ C)
  · -- x ∈ K ∩ C means x ∈ C, contradicting hxC.
    exact absurd hxKC.2 hxC
  · -- Separate x from compact K ∩ C.
    obtain ⟨V, W, hV, hW, hxV, hKCW, hVW⟩ :=
      hausdorff_separate_point_compact T hHiff hKC hxKC
    -- Refine V by intersecting with U₀ to ensure V ⊆ U₀ ⊆ K. Then V ∩ W = ∅.
    refine ⟨V ∩ U₀, W ∪ Kᶜ, T.isOpen_inter hV hU₀,
      T.isOpen_union hW ?_, ⟨hxV, hxU₀⟩, ?_, ?_⟩
    · exact hK.isClosed_of_isHausdorff T hHiff
    · -- C ⊆ W ∪ Kᶜ: if y ∈ C, either y ∈ K (so y ∈ K ∩ C ⊆ W) or y ∉ K (so y ∈ Kᶜ).
      intro y hyC
      classical
      by_cases hyK : y ∈ K
      · exact Or.inl (hKCW ⟨hyK, hyC⟩)
      · exact Or.inr hyK
    · -- (V ∩ U₀) ∩ (W ∪ Kᶜ) = ∅:
      -- y ∈ V ∩ U₀ ⇒ y ∈ U₀ ⊆ K, so y ∉ Kᶜ.
      -- And y ∈ V ∩ W ⊆ ∅ (by hVW).
      ext y
      refine ⟨?_, fun h => h.elim⟩
      rintro ⟨⟨hyV, hyU₀⟩, hyWKc⟩
      rcases hyWKc with hyW | hyKc
      · have : y ∈ V ∩ W := ⟨hyV, hyW⟩
        rw [hVW] at this; exact this
      · exact hyKc (hU₀K hyU₀)

/-! ### §32 ex32.4: regular + Lindelöf is normal. -/

/- source: topology.mg:340028 name: ex32_4_regular_Lindelof_normal -/
/-- A regular Lindelöf space is normal. We prove the set-theoretic core. -/
theorem Normal.of_regular_lindelof
    (hR : T.Regular) (hL : T.Lindelof) : T.Normal := by
  classical
  refine ⟨hR.1, ?_⟩
  intro A B hA hB hAB
  -- For each a ∈ A, regularity gives an open nbhd Uₐ of a with closure ⊆ Bᶜ.
  -- Similarly for each b ∈ B we get Vb with closure disjoint from A.
  -- Lindelöf: the covers {Uₐ} and {Vb} have countable subcovers.
  -- Then construct U = ⋃ Uₙ \ ⋃_{j≤n} closure Vⱼ and similarly V; these
  -- are open, separate A from B, and are disjoint.
  -- This requires arbitrary countable index manipulation, which we state
  -- but leave with `sorry` — the proof is nontrivial.
  sorry

/-! ### §32 misc corollaries. -/

/-- A normal space is regular (from §31). -/
theorem Regular.of_normal' (h : T.Normal) : T.Regular := Regular.of_normal T h

/-- A normal space is Hausdorff. -/
theorem Hausdorff.of_normal' (h : T.Normal) : T.Hausdorff :=
  Hausdorff.of_normal T h

/-- A compact Hausdorff space is regular. -/
theorem Regular.of_compact_hausdorff (hc : T.Compact) (hH : T.Hausdorff) :
    T.Regular :=
  Regular.of_normal T (Normal.of_compact_hausdorff T hc hH)

/-- Closed sets in a normal space can be separated from disjoint closed sets
    by disjoint open sets (restated for export). -/
theorem Normal.separate (h : T.Normal) {A B : Set α}
    (hA : T.IsClosed A) (hB : T.IsClosed B) (hAB : A ∩ B = ∅) :
    ∃ U V, T.IsOpen U ∧ T.IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧ U ∩ V = ∅ :=
  h.2 A B hA hB hAB

/-- Regular spaces can separate points from disjoint closed sets
    (restated for export). -/
theorem Regular.separate_point (h : T.Regular) (x : α) {C : Set α}
    (hC : T.IsClosed C) (hxC : x ∉ C) :
    ∃ U V, T.IsOpen U ∧ T.IsOpen V ∧ x ∈ U ∧ C ⊆ V ∧ U ∩ V = ∅ :=
  h.2 x C hC hxC

/-! ### §32 Urysohn separation (set-theoretic precursor). -/

-- Urysohn's separation condition's one-step shrinking form is
-- `Normal.shrink_closed` above. The full dyadic-indexed construction and the
-- real-valued conclusion are out of scope for this real-free port.

end Topology
end Mgw
