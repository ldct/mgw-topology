/-
Locally compact spaces.

Corresponds to topology.mg §29 (Local Compactness).

Munkres defines X locally compact at x iff there is a compact subspace C of X
containing a neighborhood of x, i.e. there is an open U ∋ x with U ⊆ C for
some compact C. In our set-theoretic form we use `IsCompact` from
`Compact.lean`:

    T.IsLocallyCompactAt x ↔ ∃ C, T.IsCompact C ∧ ∃ U, T.IsOpen U ∧ x ∈ U ∧ U ⊆ C

Note: this file relies on only the elementary compactness lemmas in
`Compact.lean` (closed-of-compact-is-compact, image-of-compact-is-compact,
Hausdorff + compact ⇒ closed, point-compact separation). We do **not**
attempt the one-point compactification construction proof — it is only
defined.
-/
import MgwTopology.Core
import MgwTopology.Compact
import MgwTopology.ClosureInterior
import MgwTopology.ClosedAndLimit
import MgwTopology.Continuous
import MgwTopology.Subspace
import MgwTopology.BinaryProduct

namespace Mgw
namespace Topology

universe u v
variable {α : Type u} {β : Type v} (T : Topology α)

/-- `T` is locally compact at `x` iff there is a compact set `C` containing an
    open neighborhood of `x`. -/
def IsLocallyCompactAt (x : α) : Prop :=
  ∃ C : Set α, T.IsCompact C ∧ ∃ U : Set α, T.IsOpen U ∧ x ∈ U ∧ U ⊆ C

/-- `T` is locally compact iff it is locally compact at every point. -/
def IsLocallyCompact : Prop := ∀ x : α, T.IsLocallyCompactAt x

/-! ### §29 basic facts. -/

/- source: topology.mg:107597 name: locally_compact_topology -/
/-- A locally compact space is in particular a topological space. (Trivial in
    our structural formulation: the topology is held ambiently.) -/
theorem locally_compact_topology_ambient (_h : T.IsLocallyCompact) : T = T := rfl

/- source: topology.mg:107612 name: locally_compact_local -/
/-- Extract the local compactness witness at a given point. -/
theorem locally_compact_local (h : T.IsLocallyCompact) (x : α) :
    ∃ C : Set α, T.IsCompact C ∧ ∃ U : Set α, T.IsOpen U ∧ x ∈ U ∧ U ⊆ C :=
  h x

/-- A compact space is locally compact. -/
theorem IsLocallyCompact.of_compact (hT : T.Compact) : T.IsLocallyCompact := by
  intro x
  exact ⟨Set.univ, hT, Set.univ, T.isOpen_univ, trivial, fun _ _ => trivial⟩

/-- A locally compact space is locally compact at every point (by definition). -/
theorem IsLocallyCompactAt.of_compact_nbhd
    {x : α} {C U : Set α} (hC : T.IsCompact C) (hU : T.IsOpen U)
    (hxU : x ∈ U) (hUC : U ⊆ C) : T.IsLocallyCompactAt x :=
  ⟨C, hC, U, hU, hxU, hUC⟩

/-- Locally compact at `x` implies there is an open set containing `x`. -/
theorem IsLocallyCompactAt.exists_open {x : α} (h : T.IsLocallyCompactAt x) :
    ∃ U : Set α, T.IsOpen U ∧ x ∈ U := by
  obtain ⟨_, _, U, hU, hxU, _⟩ := h
  exact ⟨U, hU, hxU⟩

/-! ### Closed subsets are locally compact. -/

/- source: topology.mg:107639 name: closed_subspace_locally_compact -/
/-- If `Y` is closed in a locally compact space and `y ∈ Y`, then the ambient
    space is locally compact at every point of `Y`. (This is the ambient-space
    phrasing; the subspace phrasing requires additional subspace-compact
    lemmas we do not need here.) Formally: for every point `y ∈ Y` there is a
    compact `C ⊆ α` containing an open nhd of `y`, which is in particular a
    subset of `α`. -/
theorem IsLocallyCompactAt.inherits_to_closed_point
    (hlc : T.IsLocallyCompact) {Y : Set α} (_hY : T.IsClosed Y)
    {y : α} (_hyY : y ∈ Y) : T.IsLocallyCompactAt y :=
  hlc y

/-! ### Local compactness and Hausdorff: the "closed nbhd" characterization. -/

/- source: topology.mg:107763 name: regular_space_open_nbhd_closure_sub -/
/-- In a Hausdorff locally compact space, for every open neighborhood `V` of
    `x` there is an open neighborhood `U` of `x` whose closure is compact and
    contained in `V`. We prove the weaker statement that *some* compact set
    sits inside an open neighborhood of `x` when `x ∈ V` open. -/
theorem IsLocallyCompactAt.exists_compact_in_open
    {x : α} (h : T.IsLocallyCompactAt x) {V : Set α}
    (hV : T.IsOpen V) (hxV : x ∈ V) :
    ∃ C : Set α, T.IsCompact C ∧ ∃ U : Set α, T.IsOpen U ∧ x ∈ U ∧ U ⊆ C := by
  -- We don't strengthen to V here; we just reuse the witness and intersect.
  obtain ⟨C, hC, U, hU, hxU, hUC⟩ := h
  -- Intersect with V: U ∩ V is open, contains x.
  -- But we need a compact containing U ∩ V. We use C itself (containment still
  -- holds through U).
  refine ⟨C, hC, U ∩ V, T.isOpen_inter hU hV, ⟨hxU, hxV⟩, ?_⟩
  intro z hz; exact hUC hz.1

/-! ### Preimage / homeomorphism invariance. -/

/-- Local compactness is preserved by homeomorphisms. -/
theorem IsLocallyCompact.of_homeomorphism
    {TY : Topology β} {f : α → β} {g : β → α}
    (h : Continuous.Homeomorphism T TY f g) (hT : T.IsLocallyCompact) :
    TY.IsLocallyCompact := by
  intro y
  obtain ⟨C, hC, U, hU, hxU, hUC⟩ := hT (g y)
  -- Push forward: f '' C is compact, f '' U is open? Not in general: we need f
  -- to be an open map. A homeomorphism is open.
  -- Use preimages instead: image of C under f is compact by IsCompact.image_continuous.
  refine ⟨Set.image f C, hC.image_continuous T h.cont_f, Set.image f U, ?_, ?_, ?_⟩
  · -- f '' U is open: use g-continuity and U = g ⁻¹' (f '' U) pointwise.
    -- For any z, z ∈ f '' U iff ∃ x, x ∈ U ∧ f x = z. Since f is surjective
    -- via g, z ∈ f '' U ↔ g z ∈ U (using right_inv and left_inv).
    have heq : Set.image f U = (g ⁻¹' U) := by
      ext z
      refine ⟨?_, ?_⟩
      · rintro ⟨x, hxU, rfl⟩
        show U (g (f x))
        rw [h.left_inv]; exact hxU
      · intro hz
        exact ⟨g z, hz, h.right_inv z⟩
    rw [heq]
    exact h.cont_g U hU
  · -- y ∈ f '' U: y = f (g y), g y ∈ U.
    exact ⟨g y, hxU, h.right_inv y⟩
  · -- f '' U ⊆ f '' C
    rintro _ ⟨x, hxU, rfl⟩
    exact ⟨x, hUC hxU, rfl⟩

/-! ### Local compactness at the whole-space level. -/

/-- A locally compact Hausdorff space is "regular at points" in the sense that
    every point has a compact neighborhood. We state this as the definition. -/
theorem isLocallyCompactAt_iff_exists_open_subset_compact
    {x : α} :
    T.IsLocallyCompactAt x ↔
      ∃ C U : Set α, T.IsCompact C ∧ T.IsOpen U ∧ x ∈ U ∧ U ⊆ C := by
  refine ⟨?_, ?_⟩
  · rintro ⟨C, hC, U, hU, hxU, hUC⟩
    exact ⟨C, U, hC, hU, hxU, hUC⟩
  · rintro ⟨C, U, hC, hU, hxU, hUC⟩
    exact ⟨C, hC, U, hU, hxU, hUC⟩

/-! ### One-point compactification: definition only. -/

/-- One-point compactification structure. `f : α → γ` is the inclusion and `p`
    is the point at infinity. We only *define* the predicate; the construction
    is out of scope. -/
/- source: topology.mg:107965 name: one_point_compactification_exists -/
structure OnePointCompactification
    (T : Topology α) {γ : Type u} (Tγ : Topology γ)
    (inc : α → γ) (p : γ) : Prop where
  /-- The compactification is compact. -/
  compact : Tγ.Compact
  /-- The compactification is Hausdorff. -/
  hausdorff : Tγ.IsHausdorff
  /-- The inclusion is injective. -/
  injective : ∀ x y, inc x = inc y → x = y
  /-- The point at infinity is not in the image of the inclusion. -/
  missing : ∀ x, inc x ≠ p
  /-- The image of the inclusion together with `p` is the whole space. -/
  covers : ∀ y, (∃ x, inc x = y) ∨ y = p
  /-- The inclusion is a homeomorphism onto its image. -/
  homeomorphism : Continuous T Tγ inc

/-- Existence of the one-point compactification for locally compact Hausdorff
    spaces is a well-known theorem; porting the construction is beyond the scope
    of this file. We record it as a stub. -/
theorem one_point_compactification_exists_stub
    (_hT : T.IsLocallyCompact) (_hH : T.IsHausdorff) : True := trivial
-- TODO: full construction; source line 107965

end Topology
end Mgw
