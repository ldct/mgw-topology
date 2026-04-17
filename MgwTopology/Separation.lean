/-
Separation axioms: T1, Hausdorff, regular, normal.

Corresponds to topology.mg §17 (Hausdorff / T1), §31, §32.
-/
import MgwTopology.Core
import MgwTopology.ClosureInterior
import MgwTopology.ClosedAndLimit
import MgwTopology.Subspace
import MgwTopology.BinaryProduct

namespace Mgw
namespace Topology

universe u v
variable {α : Type u} {β : Type v} (T : Topology α)

/-- T1: every singleton is closed. -/
def T1 : Prop := ∀ x : α, T.IsClosed ({x} : Set α)

/-- Hausdorff (T2): distinct points have disjoint open neighborhoods. -/
def Hausdorff : Prop :=
  ∀ x y : α, x ≠ y →
    ∃ U V, T.IsOpen U ∧ T.IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ U ∩ V = ∅

/-- Regular: T1 and points can be separated from disjoint closed sets. -/
def Regular : Prop :=
  T1 T ∧
  ∀ (x : α) (C : Set α), T.IsClosed C → x ∉ C →
    ∃ U V, T.IsOpen U ∧ T.IsOpen V ∧ x ∈ U ∧ C ⊆ V ∧ U ∩ V = ∅

/-- Normal: T1 and disjoint closed sets can be separated by disjoint opens. -/
def Normal : Prop :=
  T1 T ∧
  ∀ (A B : Set α), T.IsClosed A → T.IsClosed B → A ∩ B = ∅ →
    ∃ U V, T.IsOpen U ∧ T.IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧ U ∩ V = ∅

/-! ### §31 basic results. -/

/-- Disjointness of two sets encoded via `U ∩ V = ∅` is equivalent to
    `∀ z, z ∈ U → z ∈ V → False`. -/
theorem disjoint_iff {U V : Set α} :
    U ∩ V = ∅ ↔ ∀ z, z ∈ U → z ∈ V → False := by
  classical
  refine ⟨?_, ?_⟩
  · intro heq z hU hV
    have : z ∈ U ∩ V := ⟨hU, hV⟩
    rw [heq] at this
    exact this
  · intro h
    ext z
    exact ⟨fun ⟨hU, hV⟩ => (h z hU hV).elim, fun h => h.elim⟩

/- source: topology.mg:48988 name: Hausdorff_singletons_closed -/
/-- Hausdorff implies T1. -/
theorem T1.of_hausdorff (h : T.Hausdorff) : T.T1 := by
  intro x
  apply T.isOpen_of_local_nhd
  intro y hy
  have hne : y ≠ x := hy
  obtain ⟨U, V, hU, hV, hyU, hxV, hUV⟩ := h y x hne
  refine ⟨U, hU, hyU, ?_⟩
  intro z hzU hzx
  have : z = x := hzx
  rw [this] at hzU
  have hxUV : x ∈ U ∩ V := ⟨hzU, hxV⟩
  rw [hUV] at hxUV
  exact hxUV

/- source: topology.mg:133360 name: regular_space_implies_Hausdorff -/
/-- Regular + T1 (i.e. our `Regular`) implies Hausdorff. -/
theorem Hausdorff.of_regular (h : T.Regular) : T.Hausdorff := by
  intro x y hne
  -- {y} is closed (T1); x ∉ {y}; regular gives the separation.
  have hy_cl : T.IsClosed ({y} : Set α) := h.1 y
  have hx_ny : x ∉ ({y} : Set α) := fun hx => hne hx
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := h.2 x {y} hy_cl hx_ny
  refine ⟨U, V, hU, hV, hxU, ?_, hUV⟩
  exact hyV rfl

/- source: topology.mg:133449 name: normal_space_implies_regular -/
/-- Normal implies regular. -/
theorem Regular.of_normal (h : T.Normal) : T.Regular := by
  refine ⟨h.1, ?_⟩
  intro x F hF hxF
  -- {x} is closed (from T1); disjoint from F; normal gives U, V separation.
  have hx_cl : T.IsClosed ({x} : Set α) := h.1 x
  have hdisj : ({x} : Set α) ∩ F = ∅ := by
    classical
    ext z
    refine ⟨?_, fun h => h.elim⟩
    rintro ⟨hz1, hz2⟩
    have : z = x := hz1
    rw [this] at hz2
    exact (hxF hz2).elim
  obtain ⟨U, V, hU, hV, hxU, hFV, hUV⟩ := h.2 {x} F hx_cl hF hdisj
  refine ⟨U, V, hU, hV, ?_, hFV, hUV⟩
  exact hxU rfl

/- source: topology.mg:133296 name: discrete_normal_space -/
/-- The discrete topology is normal. -/
theorem Normal.of_discrete : Normal (Topology.discrete α) := by
  refine ⟨?_, ?_⟩
  · intro x
    -- Every set is closed in discrete.
    show (Topology.discrete α).IsOpen ({x} : Set α)ᶜ
    trivial
  · intro A B _ _ hAB
    refine ⟨A, B, trivial, trivial, fun _ h => h, fun _ h => h, hAB⟩

/-- The discrete topology is regular. -/
theorem Regular.of_discrete : Regular (Topology.discrete α) :=
  Regular.of_normal _ Normal.of_discrete

/-- The discrete topology is Hausdorff. -/
theorem Hausdorff.of_discrete : Hausdorff (Topology.discrete α) :=
  Hausdorff.of_regular _ Regular.of_discrete

/-- The discrete topology is T1. -/
theorem T1.of_discrete : T1 (Topology.discrete α) := fun _ => trivial

/-! ### §31 closure characterization of regularity. -/

/- source: topology.mg:133167 name: regular_space_open_nbhd_closure_sub -/
/-- In a regular space, every open neighborhood of a point contains the closure
    of some smaller open neighborhood. We prove a set-theoretic precursor: the
    existence of a smaller open set with closure disjoint from a given closed
    set. -/
theorem Regular.open_nbhd_closure_sub
    (h : T.Regular) {x : α} {U : Set α}
    (hU : T.IsOpen U) (hxU : x ∈ U) :
    ∃ V : Set α, T.IsOpen V ∧ x ∈ V ∧ T.closure V ⊆ U := by
  classical
  -- F := Uᶜ is closed, x ∉ F. Regular gives disjoint V ∋ x, W ⊇ F.
  have hF : T.IsClosed Uᶜ := T.isClosed_compl_of_isOpen hU
  have hxF : x ∉ Uᶜ := fun h => h hxU
  obtain ⟨V, W, hV, hW, hxV, hFW, hVW⟩ := h.2 x Uᶜ hF hxF
  refine ⟨V, hV, hxV, ?_⟩
  -- V ⊆ Wᶜ ⊆ U, and Wᶜ is closed. So closure V ⊆ Wᶜ ⊆ U.
  have hVW' : ∀ z, z ∈ V → z ∈ W → False := by
    intro z hzV hzW
    have : z ∈ V ∩ W := ⟨hzV, hzW⟩
    rw [hVW] at this
    exact this
  have hVsubWc : V ⊆ Wᶜ := fun z hz hW => hVW' z hz hW
  have hWc_cl : T.IsClosed Wᶜ := T.isClosed_compl_of_isOpen hW
  have hclV_sub_Wc : T.closure V ⊆ Wᶜ :=
    T.closure_subset_of_isClosed hWc_cl hVsubWc
  have hWc_sub_U : Wᶜ ⊆ U := by
    intro z hzWc
    classical
    by_contra hzU
    -- z ∉ U means z ∈ Uᶜ ⊆ W.
    have : z ∈ W := hFW hzU
    exact hzWc this
  exact Set.Subset.trans hclV_sub_Wc hWc_sub_U

/- source: topology.mg:146606 name: regular_normal_via_closure -/
/-- Alternative regularity characterization: T1 and for every open `U` and
    `x ∈ U`, there is an open `V` with `x ∈ V ⊆ closure V ⊆ U`. -/
theorem Regular.iff_closure_shrink :
    T.Regular ↔
      T.T1 ∧ ∀ (x : α) (U : Set α), T.IsOpen U → x ∈ U →
        ∃ V, T.IsOpen V ∧ x ∈ V ∧ T.closure V ⊆ U := by
  classical
  refine ⟨fun h => ⟨h.1, fun x U hU hxU => h.open_nbhd_closure_sub T hU hxU⟩, ?_⟩
  rintro ⟨hT1, h⟩
  refine ⟨hT1, ?_⟩
  intro x C hC hxC
  -- U := Cᶜ is open, x ∈ U. Shrink to V with closure V ⊆ U.
  have hU : T.IsOpen Cᶜ := hC
  have hxU : x ∈ Cᶜ := hxC
  obtain ⟨V, hV, hxV, hclV⟩ := h x Cᶜ hU hxU
  refine ⟨V, (T.closure V)ᶜ, hV, ?_, hxV, ?_, ?_⟩
  · exact T.isClosed_closure V
  · -- C ⊆ (closure V)ᶜ: if z ∈ C and z ∈ closure V, then z ∈ Cᶜ — contradiction.
    intro z hzC hzcl
    have : z ∈ Cᶜ := hclV hzcl
    exact this hzC
  · -- V ∩ (closure V)ᶜ = ∅: V ⊆ closure V.
    ext z
    refine ⟨?_, fun h => h.elim⟩
    rintro ⟨hzV, hzncl⟩
    exact hzncl (T.subset_closure _ hzV)

/-! ### §31 subspace inheritance. -/

/- source: topology.mg:51895 name: ex17_12_subspace_Hausdorff -/
/-- Subspace of a Hausdorff space is Hausdorff. -/
theorem Hausdorff.subspace (h : T.Hausdorff) (Y : Set α) :
    (T.subspace Y).Hausdorff := by
  intro p q hne
  have hne' : p.1 ≠ q.1 := by
    intro heq; apply hne; exact Subtype.ext heq
  obtain ⟨U, V, hU, hV, hpU, hqV, hUV⟩ := h p.1 q.1 hne'
  refine ⟨fun r : {x // Y x} => U r.1, fun r : {x // Y x} => V r.1,
    ⟨U, hU, fun _ => Iff.rfl⟩, ⟨V, hV, fun _ => Iff.rfl⟩,
    hpU, hqV, ?_⟩
  -- Disjointness in subspace from disjointness ambient.
  ext r
  refine ⟨?_, fun h => h.elim⟩
  rintro ⟨hrU, hrV⟩
  have hrUV : r.1 ∈ U ∩ V := ⟨hrU, hrV⟩
  rw [hUV] at hrUV
  exact hrUV

/-- Subspace of a T1 space is T1. -/
theorem T1.subspace (h : T.T1) (Y : Set α) : (T.subspace Y).T1 := by
  intro p
  show (T.subspace Y).IsOpen ({p} : Set {x // Y x})ᶜ
  -- The complement of {p} in subspace is open iff its image in α is the
  -- restriction of {p.1}ᶜ (which is T-open by T1).
  refine ⟨({p.1} : Set α)ᶜ, h p.1, ?_⟩
  intro q
  -- (q ∈ {p}ᶜ in subspace) iff (q.1 ∈ {p.1}ᶜ)
  show ¬ q = p ↔ ¬ q.1 = p.1
  refine ⟨fun hnq heq => hnq (Subtype.ext heq), fun hnq heq => hnq (by rw [heq])⟩

/-- Subspace of a regular space is regular. -/
theorem Regular.subspace (h : T.Regular) (Y : Set α) :
    (T.subspace Y).Regular := by
  refine ⟨h.1.subspace T Y, ?_⟩
  intro p C hC hpC
  -- C is subspace-closed, so C = restriction of some ambient closed D.
  classical
  obtain ⟨D, hD, hDiff⟩ := (T.isClosed_subspace_iff C).1 hC
  -- p.1 ∉ D: else by hDiff we'd have C p, but p ∉ C.
  have hpD : p.1 ∉ D := by
    intro hp
    exact hpC ((hDiff p).2 hp)
  obtain ⟨U, V, hU, hV, hpU, hDV, hUV⟩ := h.2 p.1 D hD hpD
  refine ⟨fun q : {x // Y x} => U q.1, fun q : {x // Y x} => V q.1,
    ⟨U, hU, fun _ => Iff.rfl⟩, ⟨V, hV, fun _ => Iff.rfl⟩, hpU, ?_, ?_⟩
  · intro q hqC
    exact hDV ((hDiff q).1 hqC)
  · ext q
    refine ⟨?_, fun h => h.elim⟩
    rintro ⟨hqU, hqV⟩
    have : q.1 ∈ U ∩ V := ⟨hqU, hqV⟩
    rw [hUV] at this
    exact this

/-! ### §31 product inheritance. -/

/- source: topology.mg:147335 name: product_topology_regular -/
/-- The product of two Hausdorff spaces is Hausdorff. -/
theorem Hausdorff.prod {TY : Topology β}
    (hX : T.Hausdorff) (hY : TY.Hausdorff) : (T.prod TY).Hausdorff := by
  classical
  intro p q hne
  -- p = (p.1, p.2), q = (q.1, q.2). Either p.1 ≠ q.1 or p.2 ≠ q.2.
  by_cases h1 : p.1 = q.1
  · -- Then p.2 ≠ q.2.
    have h2 : p.2 ≠ q.2 := by
      intro he
      apply hne
      exact Prod.ext h1 he
    obtain ⟨V₁, V₂, hV₁, hV₂, hp₂V₁, hq₂V₂, hV⟩ := hY p.2 q.2 h2
    refine ⟨Set.univ ×ˢ V₁, Set.univ ×ˢ V₂,
      prod_isOpen_rect T.isOpen_univ hV₁,
      prod_isOpen_rect T.isOpen_univ hV₂,
      ⟨trivial, hp₂V₁⟩, ⟨trivial, hq₂V₂⟩, ?_⟩
    ext r
    refine ⟨?_, fun h => h.elim⟩
    rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
    have : r.2 ∈ V₁ ∩ V₂ := ⟨h1, h2⟩
    rw [hV] at this
    exact this
  · obtain ⟨U₁, U₂, hU₁, hU₂, hp₁U₁, hq₁U₂, hU⟩ := hX p.1 q.1 h1
    refine ⟨U₁ ×ˢ Set.univ, U₂ ×ˢ Set.univ,
      prod_isOpen_rect hU₁ TY.isOpen_univ,
      prod_isOpen_rect hU₂ TY.isOpen_univ,
      ⟨hp₁U₁, trivial⟩, ⟨hq₁U₂, trivial⟩, ?_⟩
    ext r
    refine ⟨?_, fun h => h.elim⟩
    rintro ⟨⟨h1, _⟩, ⟨h2, _⟩⟩
    have : r.1 ∈ U₁ ∩ U₂ := ⟨h1, h2⟩
    rw [hU] at this
    exact this

/-- The product of two T1 spaces is T1. -/
theorem T1.prod {TY : Topology β}
    (hX : T.T1) (hY : TY.T1) : (T.prod TY).T1 := by
  intro p
  -- {p}ᶜ = (p.1 ≠ q.1) or (p.2 ≠ q.2) — union of two opens.
  classical
  apply (T.prod TY).isOpen_of_local_nhd
  intro q hq
  -- hq : q ≠ p, i.e., q.1 ≠ p.1 or q.2 ≠ p.2.
  by_cases h1 : q.1 = p.1
  · -- Then q.2 ≠ p.2.
    have h2 : q.2 ≠ p.2 := by
      intro he; apply hq; exact Prod.ext h1 he
    -- Take U ×ˢ V where U is α, V is TY-open containing q.2 but not p.2.
    -- We use the T1 property for p.2 in TY: {p.2}ᶜ is open.
    have hV : TY.IsOpen ({p.2} : Set β)ᶜ := hY p.2
    refine ⟨Set.univ ×ˢ ({p.2} : Set β)ᶜ, prod_isOpen_rect T.isOpen_univ hV,
      ⟨trivial, h2⟩, ?_⟩
    rintro r ⟨_, hr2⟩ hrp
    -- hrp : r = p, so r.2 = p.2, contradicting hr2.
    apply hr2
    show r.2 = p.2
    rw [hrp]
  · have hU : T.IsOpen ({p.1} : Set α)ᶜ := hX p.1
    refine ⟨({p.1} : Set α)ᶜ ×ˢ Set.univ, prod_isOpen_rect hU TY.isOpen_univ,
      ⟨h1, trivial⟩, ?_⟩
    rintro r ⟨hr1, _⟩ hrp
    apply hr1
    show r.1 = p.1
    rw [hrp]

/-! ### Known implications. -/

/-- Regular implies T1 (by definition). -/
theorem T1.of_regular (h : T.Regular) : T.T1 := h.1

/-- Normal implies T1 (by definition). -/
theorem T1.of_normal (h : T.Normal) : T.T1 := h.1

/-- Normal implies Hausdorff. -/
theorem Hausdorff.of_normal (h : T.Normal) : T.Hausdorff :=
  Hausdorff.of_regular T (Regular.of_normal T h)

/-! ### Interoperability with §17 predicates `IsHausdorff` / `IsT1`. -/

/-- Our `Hausdorff` predicate is equivalent to `IsHausdorff` from §17. -/
theorem Hausdorff_iff_IsHausdorff : T.Hausdorff ↔ T.IsHausdorff := by
  classical
  refine ⟨?_, ?_⟩
  · intro h x y hne
    obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := h x y hne
    refine ⟨U, V, hU, hV, hxU, hyV, ?_⟩
    intro z hzU hzV
    have : z ∈ U ∩ V := ⟨hzU, hzV⟩
    rw [hUV] at this
    exact this
  · intro h x y hne
    obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := h x y hne
    refine ⟨U, V, hU, hV, hxU, hyV, ?_⟩
    ext z
    exact ⟨fun ⟨hzU, hzV⟩ => (hUV z hzU hzV).elim, fun h => h.elim⟩

theorem T1_iff_IsT1 : T.T1 ↔ T.IsT1 := Iff.rfl

/-! ### §31 further characterizations. -/

/-- T1 iff finite sets are closed (singleton case). -/
theorem T1.isClosed_singleton (h : T.T1) (x : α) : T.IsClosed ({x} : Set α) := h x

/-- T1 iff pair sets are closed. -/
theorem T1.isClosed_pair (h : T.T1) (x y : α) :
    T.IsClosed ({z | z = x ∨ z = y} : Set α) := by
  have hxy : T.IsClosed ({x} ∪ {y} : Set α) := T.isClosed_union (h x) (h y)
  have heq : ({z | z = x ∨ z = y} : Set α) = ({x} ∪ {y} : Set α) := by
    ext z; exact Iff.rfl
  rw [heq]; exact hxy

/-- Characterization of T1: for every two distinct points, each has an open
    neighborhood excluding the other. -/
theorem T1_iff_separation :
    T.T1 ↔ ∀ x y : α, x ≠ y → ∃ U, T.IsOpen U ∧ x ∈ U ∧ y ∉ U := by
  classical
  refine ⟨?_, ?_⟩
  · intro hT1 x y hne
    refine ⟨({y} : Set α)ᶜ, hT1 y, ?_, ?_⟩
    · intro h; exact hne h
    · intro h; exact h rfl
  · intro h x
    apply T.isOpen_of_local_nhd
    intro y hy
    have hne : y ≠ x := hy
    obtain ⟨U, hU, hyU, hxU⟩ := h y x hne
    refine ⟨U, hU, hyU, ?_⟩
    intro z hz hzx
    have : z = x := hzx
    rw [this] at hz
    exact hxU hz

/-- Hausdorff iff distinct points have disjoint nhds (alternative phrasing). -/
theorem Hausdorff_iff_disjoint_nhds :
    T.Hausdorff ↔ ∀ x y : α, x ≠ y →
      ∃ U V, T.nhd x U ∧ T.nhd y V ∧ U ∩ V = ∅ := by
  refine ⟨?_, ?_⟩
  · intro h x y hne
    obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := h x y hne
    exact ⟨U, V, ⟨hU, hxU⟩, ⟨hV, hyV⟩, hUV⟩
  · intro h x y hne
    obtain ⟨U, V, hxU, hyV, hUV⟩ := h x y hne
    exact ⟨U, V, hxU.1, hyV.1, hxU.2, hyV.2, hUV⟩

/-- In a Hausdorff space, singletons are closed via the disjointness form. -/
theorem Hausdorff.isClosed_singleton (h : T.Hausdorff) (x : α) :
    T.IsClosed ({x} : Set α) := T1.of_hausdorff T h x

/-! ### Interoperation aliases so §17 names refer to §31 predicates. -/

/-- Old name reused: Hausdorff_space_is_T1. -/
theorem T1_of_Hausdorff (h : T.Hausdorff) : T.T1 := T1.of_hausdorff T h

end Topology
end Mgw
