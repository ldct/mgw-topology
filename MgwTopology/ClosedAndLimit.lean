/-
Closed sets and limit points.

Corresponds to topology.mg §17. Builds on `ClosureInterior.lean` with
material about limit points, Hausdorff, T1, and the closure =
set ∪ limit-points characterization.
-/
import MgwTopology.Section_12_Core
import MgwTopology.ClosureInterior
import MgwTopology.Subspace

namespace Mgw
namespace Topology

universe u
variable {α : Type u} (T : Topology α)

/-! ### Separation axioms (real-free §17 material). -/

/- source: topology.mg:48789 name: Hausdorff_space_topology -/
/-- `T` is Hausdorff (T₂): distinct points have disjoint neighborhoods. -/
def IsHausdorff : Prop :=
  ∀ x y : α, x ≠ y →
    ∃ U V : Set α, T.IsOpen U ∧ T.IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ ∀ z, z ∈ U → z ∈ V → False

/- source: topology.mg:48826 name: T1_space_topology -/
/-- `T` is T₁: every singleton is closed. -/
def IsT1 : Prop := ∀ x : α, T.IsClosed ({x} : Set α)

/- source: topology.mg:48988 name: Hausdorff_singletons_closed -/
/-- Hausdorff implies T₁. -/
theorem IsT1_of_IsHausdorff (h : T.IsHausdorff) : T.IsT1 := by
  intro x
  -- {x}ᶜ is open: for each y ≠ x, pick separating neighborhood of y away from x.
  apply T.isOpen_of_local_nhd
  intro y hy
  -- hy : y ∈ {x}ᶜ, i.e. y ≠ x.
  have hne : y ≠ x := hy
  obtain ⟨U, V, hU, hV, hyU, hxV, hUV⟩ := h y x hne
  refine ⟨U, hU, hyU, ?_⟩
  intro z hz hzx
  -- hzx : z ∈ {x}, i.e. z = x.
  apply hUV z hz
  have : z = x := hzx
  rw [this]; exact hxV

/-- In a T₁ space, finite subsets are closed. (We prove the singleton case and
    a two-point version; arbitrary finite takes induction over our `Finite`
    definition which is not essential here.) -/
/- source: topology.mg:49013 name: finite_sets_closed_in_Hausdorff -/
theorem isClosed_singleton_of_IsT1 (h : T.IsT1) (x : α) : T.IsClosed ({x} : Set α) := h x

theorem isClosed_pair_of_IsT1 (h : T.IsT1) (x y : α) :
    T.IsClosed ({z | z = x ∨ z = y} : Set α) := by
  have hxy : T.IsClosed ({x} ∪ {y} : Set α) := T.isClosed_union (h x) (h y)
  have heq : ({z | z = x ∨ z = y} : Set α) = ({x} ∪ {y} : Set α) := by
    ext z; exact Iff.rfl
  rw [heq]; exact hxy

/-! ### Limit points and the closure characterization. -/

/- source: topology.mg:48589 name: closure_equals_set_plus_limit_points -/
/-- Closure of `S` equals `S` together with its limit points. -/
theorem closure_eq_union_limit_points (S : Set α) :
    T.closure S = fun x => x ∈ S ∨ T.IsLimitPoint x S := by
  classical
  ext x
  refine ⟨?_, ?_⟩
  · intro hx
    by_cases hxS : x ∈ S
    · exact Or.inl hxS
    right
    -- x is in closure S \ S, so every neighborhood meets S; since x ∉ S the
    -- witness is ≠ x.
    intro U hU hxU
    have hmeet : ∀ U, T.IsOpen U → x ∈ U → ∃ y, y ∈ U ∧ y ∈ S :=
      (T.mem_closure_iff).1 hx
    obtain ⟨y, hyU, hyS⟩ := hmeet U hU hxU
    refine ⟨y, hyU, hyS, ?_⟩
    intro heq
    rw [heq] at hyS
    exact hxS hyS
  · rintro (hxS | hlim)
    · exact T.subset_closure S hxS
    apply (T.mem_closure_iff).2
    intro U hU hxU
    obtain ⟨y, hyU, hyS, _⟩ := hlim U hU hxU
    exact ⟨y, hyU, hyS⟩

/- source: topology.mg:48722 name: closed_iff_contains_limit_points -/
/-- A set is closed iff it contains all its limit points. -/
theorem isClosed_iff_contains_limit_points {S : Set α} :
    T.IsClosed S ↔ ∀ x, T.IsLimitPoint x S → x ∈ S := by
  classical
  refine ⟨?_, ?_⟩
  · intro hS x hlim
    -- closure S = S since S is closed; x ∈ closure S by limit-point characterization.
    have : x ∈ T.closure S := by
      rw [T.closure_eq_union_limit_points]; exact Or.inr hlim
    rw [T.closure_eq_of_isClosed hS] at this
    exact this
  · intro h
    -- Show closure S ⊆ S, then closure = S so S is closed.
    rw [T.isClosed_iff_eq_closure]
    apply Set.subset_antisymm
    · intro x hx
      rw [T.closure_eq_union_limit_points] at hx
      rcases hx with hxS | hlim
      · exact hxS
      · exact h x hlim
    · exact T.subset_closure S

/- source: topology.mg:48560 name: closure_characterization -/
/-- Characterization: `x ∈ closure S` iff every open neighborhood of `x` meets
    `S`. (This is a repackaged `mem_closure_iff`, kept here under the §17
    name.) -/
theorem mem_closure_iff_meets (S : Set α) (x : α) :
    x ∈ T.closure S ↔ ∀ U, T.IsOpen U → x ∈ U → ∃ y, y ∈ U ∧ y ∈ S :=
  T.mem_closure_iff

/-! ### Limit points in Hausdorff spaces. -/

/- source: topology.mg:49042 name: limit_points_infinite_neighborhoods -/
/-- In a Hausdorff space, if `x` is a limit point of `S`, then every open
    neighborhood of `x` contains some point of `S` distinct from `x`. (This is
    actually the definition, but repackaged to emphasize the Hausdorff
    conclusion: the point from `S` can be chosen different from `x`.) -/
theorem IsLimitPoint.exists_ne_of_IsHausdorff
    (_hH : T.IsHausdorff) {x : α} {S : Set α}
    (hx : T.IsLimitPoint x S) (U : Set α) (hU : T.IsOpen U) (hxU : x ∈ U) :
    ∃ y, y ∈ U ∧ y ∈ S ∧ y ≠ x :=
  hx U hU hxU

/-- In a Hausdorff space, limits (in the filter sense at a single point) are
    unique: if every open neighborhood of both `a` and `b` meets a common
    point set that shrinks to each, then `a = b`. We state the set-theoretic
    form: if `{a}` and `{b}` have identical neighborhood filters in a
    Hausdorff space, then `a = b`. -/
theorem eq_of_nhd_eq_of_IsHausdorff (hH : T.IsHausdorff) {a b : α}
    (h : ∀ U, T.IsOpen U → (a ∈ U ↔ b ∈ U)) : a = b := by
  classical
  by_contra hne
  obtain ⟨U, V, hU, hV, haU, hbV, hUV⟩ := hH a b hne
  have haV : a ∈ V := (h V hV).2 hbV
  exact hUV a haU haV

/-! ### Subspace restrictions of closed sets and closures. -/

/- source: topology.mg:48115 name: closed_in_subspace_iff_intersection -/
/-- A set in a subspace is closed iff it is the restriction of an ambient
    closed set. (Re-export from `Subspace.lean`.) -/
theorem isClosed_subspace_iff' {Y : Set α} (C : Set {x // Y x}) :
    (T.subspace Y).IsClosed C ↔
      ∃ D : Set α, T.IsClosed D ∧ ∀ p, C p ↔ D p.1 :=
  T.isClosed_subspace_iff C

/- source: topology.mg:48279 name: closed_in_closed_subspace -/
/-- If `Y` is closed in `α` and `C` is closed in the subspace on `Y`, then
    the realisation of `C` as a subset of `α` (via existence of the underlying
    membership `Y`) is closed in `α`. -/
theorem isClosed_subspace_realize
    {Y : Set α} (hY : T.IsClosed Y) {C : Set {x // Y x}}
    (hC : (T.subspace Y).IsClosed C) :
    T.IsClosed (fun x => ∃ h : Y x, C ⟨x, h⟩) := by
  obtain ⟨D, hD, hDiff⟩ := (T.isClosed_subspace_iff C).1 hC
  -- Realisation = Y ∩ D.
  have heq : (fun x => ∃ h : Y x, C ⟨x, h⟩) = Y ∩ D := by
    ext x
    refine ⟨?_, ?_⟩
    · rintro ⟨hYx, hCx⟩
      exact ⟨hYx, (hDiff ⟨x, hYx⟩).1 hCx⟩
    · rintro ⟨hYx, hDx⟩
      exact ⟨hYx, (hDiff ⟨x, hYx⟩).2 hDx⟩
  rw [heq]
  exact T.isClosed_inter hY hD

/-! ### §17 basic closed-set lemmas that were not yet present. -/

/- source: topology.mg:50693 name: closure_idempotent_and_closed -/
theorem closure_idempotent_and_isClosed (S : Set α) :
    T.closure (T.closure S) = T.closure S ∧ T.IsClosed (T.closure S) :=
  ⟨T.closure_closure S, T.isClosed_closure S⟩

/- source: topology.mg:50877 name: ex17_6a_closure_monotone -/
theorem closure_monotone {S₁ S₂ : Set α} (h : S₁ ⊆ S₂) :
    T.closure S₁ ⊆ T.closure S₂ := T.closure_mono h

/- source: topology.mg:50889 name: ex17_6b_closure_binunion -/
theorem closure_binunion (S₁ S₂ : Set α) :
    T.closure (S₁ ∪ S₂) = T.closure S₁ ∪ T.closure S₂ := T.closure_union S₁ S₂

/- source: topology.mg:51169 name: ex17_8a_closure_intersection_Subq_intersection_closures -/
theorem closure_inter_subset (S₁ S₂ : Set α) :
    T.closure (S₁ ∩ S₂) ⊆ T.closure S₁ ∩ T.closure S₂ := by
  apply Set.subset_inter
  · exact T.closure_mono (Set.inter_subset_left _ _)
  · exact T.closure_mono (Set.inter_subset_right _ _)

/- source: topology.mg:51282 name: ex17_8c_closure_setminus_Subq_closure_left -/
theorem closure_diff_subset (S₁ S₂ : Set α) :
    T.closure (S₁ \ S₂) ⊆ T.closure S₁ :=
  T.closure_mono (fun _ h => h.1)

/- source: topology.mg:47644 name: lemma_union_two_open -/
/-- Lemma 17.1 (Munkres): a set with the "union of open subsets" property is
    open. Already supplied as `isOpen_of_local_nhd`; we restate the
    two-set case. -/
theorem isOpen_union_of_isOpen {U V : Set α}
    (hU : T.IsOpen U) (hV : T.IsOpen V) : T.IsOpen (U ∪ V) :=
  T.isOpen_union hU hV

/- source: topology.mg:47884 name: closed_sets_axioms -/
/-- The family of closed sets is closed under arbitrary intersection and
    finite union, and contains ∅ and univ. -/
theorem isClosed_axioms :
    T.IsClosed (∅ : Set α) ∧
    T.IsClosed (Set.univ : Set α) ∧
    (∀ {C D}, T.IsClosed C → T.IsClosed D → T.IsClosed (C ∩ D)) ∧
    (∀ {C D}, T.IsClosed C → T.IsClosed D → T.IsClosed (C ∪ D)) ∧
    (∀ {𝒞 : Set (Set α)}, (∀ C, C ∈ 𝒞 → T.IsClosed C) → T.IsClosed (⋂₀ 𝒞)) := by
  refine ⟨T.isClosed_empty, T.isClosed_univ, ?_, ?_, ?_⟩
  · intro _ _ hC hD; exact T.isClosed_inter hC hD
  · intro _ _ hC hD; exact T.isClosed_union hC hD
  · intro _ h; exact T.isClosed_sInter h

/- source: topology.mg:48400 name: closure_in_subspace -/
/-- Closure in the subspace equals the restriction of the ambient closure to
    the subspace: a point `p : {x // Y x}` is in the subspace-closure of `C`
    iff `p.1` is in the ambient closure of the realisation of `C`. -/
theorem mem_subspace_closure_iff
    {Y : Set α} (C : Set {x // Y x}) (p : {x // Y x}) :
    p ∈ (T.subspace Y).closure C ↔
      p.1 ∈ T.closure (fun x => ∃ h : Y x, C ⟨x, h⟩) := by
  classical
  -- Both sides: every open nbhd of the point meets C (resp. the realisation).
  rw [(T.subspace Y).mem_closure_iff, T.mem_closure_iff]
  refine ⟨?_, ?_⟩
  · intro h U hU hpU
    -- Restrict U to subspace: subspace-open, contains p.
    have hsubU : (T.subspace Y).IsOpen (fun q : {x // Y x} => U q.1) :=
      ⟨U, hU, fun _ => Iff.rfl⟩
    have hpsubU : p ∈ (fun q : {x // Y x} => U q.1) := hpU
    obtain ⟨q, hqU, hqC⟩ := h _ hsubU hpsubU
    exact ⟨q.1, hqU, q.2, hqC⟩
  · intro h V hV hpV
    obtain ⟨U, hU, hUiff⟩ := hV
    have hpU : U p.1 := (hUiff p).1 hpV
    obtain ⟨y, hyU, hyY, hyC⟩ := h U hU hpU
    refine ⟨⟨y, hyY⟩, ?_, hyC⟩
    exact (hUiff ⟨y, hyY⟩).2 hyU

/-! ### Sequential convergence (optional, real-free). -/

/-- A sequence `x : Nat → α` converges to `a` if every open neighborhood of
    `a` eventually contains every `x n`. -/
def seqLimit (x : Nat → α) (a : α) : Prop :=
  ∀ U : Set α, T.IsOpen U → a ∈ U → ∃ N : Nat, ∀ n, N ≤ n → x n ∈ U

theorem seqLimit_const (a : α) : T.seqLimit (fun _ => a) a := by
  intro U _ hU; exact ⟨0, fun _ _ => hU⟩

/- source: topology.mg:49663 name: ex17_1_topology_from_closed_sets -/
/-- A family of "closed" sets with the right axioms induces a topology.
    We construct the topology and prove its closed sets are exactly the
    original family. -/
def ofClosed (𝒞 : Set (Set α))
    (h_empty : (∅ : Set α) ∈ 𝒞) (h_univ : (Set.univ : Set α) ∈ 𝒞)
    (h_inter : ∀ {C D}, C ∈ 𝒞 → D ∈ 𝒞 → (C ∪ D) ∈ 𝒞)
    (h_sInter : ∀ {𝒟 : Set (Set α)}, (∀ D, D ∈ 𝒟 → D ∈ 𝒞) →
                (⋂₀ 𝒟) ∈ 𝒞) : Topology α where
  IsOpen U := Uᶜ ∈ 𝒞
  isOpen_empty := by
    show (∅ : Set α)ᶜ ∈ 𝒞
    rw [Set.compl_empty]; exact h_univ
  isOpen_univ := by
    show (Set.univ : Set α)ᶜ ∈ 𝒞
    rw [Set.compl_univ]; exact h_empty
  isOpen_inter := by
    intro U V hU hV
    show (U ∩ V)ᶜ ∈ 𝒞
    rw [Set.compl_inter]; exact h_inter hU hV
  isOpen_sUnion := by
    intro 𝒰 h𝒰
    show (⋃₀ 𝒰)ᶜ ∈ 𝒞
    rw [Set.compl_sUnion_eq_sInter_compl]
    apply h_sInter
    rintro D ⟨U, hU, rfl⟩
    exact h𝒰 U hU

/- source: topology.mg:51895 name: ex17_12_subspace_Hausdorff -/
/-- Subspace of a Hausdorff space is Hausdorff. -/
theorem subspace_IsHausdorff (hH : T.IsHausdorff) (Y : Set α) :
    (T.subspace Y).IsHausdorff := by
  intro p q hne
  have hne' : p.1 ≠ q.1 := by
    intro h
    apply hne
    -- Subtype values with equal underlying data are equal.
    exact Subtype.ext h
  obtain ⟨U, V, hU, hV, hpU, hqV, hUV⟩ := hH p.1 q.1 hne'
  refine ⟨fun r : {x // Y x} => U r.1, fun r : {x // Y x} => V r.1,
    ⟨U, hU, fun _ => Iff.rfl⟩, ⟨V, hV, fun _ => Iff.rfl⟩,
    hpU, hqV, ?_⟩
  intro r hrU hrV
  exact hUV r.1 hrU hrV

/- source: topology.mg:47218 name: interior_closure_complement_duality -/
/-- Duality: `(interior S)ᶜ = closure Sᶜ` (equivalent to the duality in
    `ClosureInterior`, phrased in complement-explicit form). -/
theorem compl_interior (S : Set α) :
    (T.interior S)ᶜ = T.closure Sᶜ := by
  have h := T.interior_eq_compl_closure_compl S
  -- interior S = (closure Sᶜ)ᶜ, so (interior S)ᶜ = (closure Sᶜ)ᶜᶜ = closure Sᶜ.
  rw [h, Set.compl_compl]

theorem compl_closure (S : Set α) :
    (T.closure S)ᶜ = T.interior Sᶜ := by
  have h := T.closure_eq_compl_interior_compl S
  rw [h, Set.compl_compl]

/- source: topology.mg:47078 name: not_in_closure_has_disjoint_open -/
/-- If `x ∉ closure S`, then there is an open neighborhood of `x` disjoint
    from `S`. -/
theorem exists_disjoint_open_of_not_mem_closure
    {S : Set α} {x : α} (hx : x ∉ T.closure S) :
    ∃ U, T.IsOpen U ∧ x ∈ U ∧ ∀ y, y ∈ U → y ∉ S := by
  classical
  -- x ∉ closure S means x ∈ (closure S)ᶜ = interior Sᶜ.
  have hxI : x ∈ T.interior Sᶜ := by
    rw [← T.compl_closure]; exact hx
  obtain ⟨U, ⟨hU, hUsub⟩, hxU⟩ := hxI
  refine ⟨U, hU, hxU, ?_⟩
  intro y hyU hyS
  exact hUsub hyU hyS

/-- In a Hausdorff space, sequence limits are unique. -/
theorem seqLimit_unique_of_IsHausdorff
    (hH : T.IsHausdorff) {x : Nat → α} {a b : α}
    (ha : T.seqLimit x a) (hb : T.seqLimit x b) : a = b := by
  classical
  by_contra hne
  obtain ⟨U, V, hU, hV, haU, hbV, hUV⟩ := hH a b hne
  obtain ⟨Na, hNa⟩ := ha U hU haU
  obtain ⟨Nb, hNb⟩ := hb V hV hbV
  have hle : Na ≤ Na + Nb := Nat.le_add_right _ _
  have hle' : Nb ≤ Na + Nb := Nat.le_add_left _ _
  exact hUV (x (Na + Nb)) (hNa _ hle) (hNb _ hle')

end Topology
end Mgw
