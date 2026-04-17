/-
Function spaces: pointwise and compact-open topologies.

Corresponds to topology.mg §46 (Pointwise and Compact Convergence).

The Megalodon type `function_space X Y` is the set of *all* functions
`X → Y`. In Lean we use the full function type `α → β` as the ambient
analogue. The "continuous function space" is modeled as a subset
`{ f | Continuous TX TY f }` and the compact-open topology on it is the
subspace topology obtained from the compact-convergence topology on
`α → β`.
-/
import MgwTopology.Core
import MgwTopology.Basis
import MgwTopology.Continuous
import MgwTopology.Subspace
import MgwTopology.Compact
import MgwTopology.BinaryProduct

namespace Mgw
namespace Topology

universe u v
variable {α : Type u} {β : Type v}

/-! ### Pointwise convergence topology. -/

/-- The pointwise subbasis: sets of functions `{ f | f x ∈ U }` for a point
    `x : α` and an open set `U : Set β`. -/
def pointwiseSubbasis (TY : Topology β) : Set (Set (α → β)) :=
  fun S => ∃ (x : α) (U : Set β), TY.IsOpen U ∧ S = { f : α → β | f x ∈ U }

/- source: topology.mg:247989 name: pointwise_convergence_topology_is_topology -/
/-- The topology of pointwise convergence on `α → β`. -/
def pointwiseTopology (_TX : Topology α) (TY : Topology β) : Topology (α → β) :=
  Topology.ofSubbasis (pointwiseSubbasis (α := α) TY)

/-- Since `Topology.ofSubbasis` is already a topology (by construction), the
    pointwise topology is a topology. -/
theorem pointwiseTopology_isTopology (TX : Topology α) (TY : Topology β) :
    ∃ T : Topology (α → β), T = pointwiseTopology TX TY := ⟨_, rfl⟩

/- source: topology.mg:248052 name: pointwise_eval_continuous -/
/-- The evaluation-at-a-point map is continuous from the pointwise-convergence
    topology to the codomain. -/
theorem pointwise_eval_continuous (TX : Topology α) (TY : Topology β) (x : α) :
    Continuous (pointwiseTopology TX TY) TY (fun f : α → β => f x) := by
  intro U hU
  -- Preimage of U under eval_x is { f | f x ∈ U }, a subbasis element.
  have hsub : { f : α → β | f x ∈ U } ∈ pointwiseSubbasis (α := α) TY :=
    ⟨x, U, hU, rfl⟩
  have : ((fun f : α → β => f x) ⁻¹' U) = { f : α → β | f x ∈ U } := rfl
  rw [this]
  exact Topology.ofSubbasis_isOpen_of_mem hsub

/-! ### Compact-open topology (topology of compact convergence). -/

/-- The compact-open subbasis: sets `{ f | f '' K ⊆ U }` for `K` compact in
    `TX` and `U` open in `TY`. -/
def compactOpenSubbasis (TX : Topology α) (TY : Topology β) : Set (Set (α → β)) :=
  fun S => ∃ (K : Set α) (U : Set β),
    TX.IsCompact K ∧ TY.IsOpen U ∧ S = { f : α → β | Set.image f K ⊆ U }

/- source: topology.mg:248330 name: compact_open_subbasis_is_subbasis -/
/-- The compact-open subbasis *is* a subbasis: nothing to check beyond that it
    is a family of sets (since `ofSubbasis` takes any family). We record this
    trivially and note every element is open in the generated topology. -/
theorem compact_open_subbasis_is_subbasis (TX : Topology α) (TY : Topology β) :
    ∀ S ∈ compactOpenSubbasis TX TY,
      (Topology.ofSubbasis (compactOpenSubbasis TX TY)).IsOpen S := by
  intro S hS
  exact Topology.ofSubbasis_isOpen_of_mem hS

/- source: topology.mg:248415 name: compact_convergence_topology_is_topology -/
/-- The compact-convergence (= compact-open) topology on `α → β`. -/
def compactConvergenceTopology (TX : Topology α) (TY : Topology β) :
    Topology (α → β) :=
  Topology.ofSubbasis (compactOpenSubbasis TX TY)

/-- Existence: the compact-convergence topology is a topology. -/
theorem compact_convergence_topology_is_topology
    (TX : Topology α) (TY : Topology β) :
    ∃ T : Topology (α → β), T = compactConvergenceTopology TX TY := ⟨_, rfl⟩

/-! ### Continuous function space. -/

/- source: topology.mg:247984 name: continuous_function_space -/
/-- The set of continuous functions from `(α, TX)` to `(β, TY)`. -/
def continuousFunctionSpace (TX : Topology α) (TY : Topology β) :
    Set (α → β) :=
  { f : α → β | Continuous TX TY f }

/- source: topology.mg:248561 name: continuous_function_space_sub -/
/-- The continuous function space is contained in the full function space
    (trivial in Lean since both sit inside `α → β`). -/
theorem continuous_function_space_sub (TX : Topology α) (TY : Topology β) :
    continuousFunctionSpace TX TY ⊆ (Set.univ : Set (α → β)) :=
  fun _ _ => trivial

/- source: topology.mg:248571 name: compact_open_topology_C_is_topology -/
/-- The compact-open topology on `C(X, Y)`, obtained as the subspace topology
    inherited from the compact-convergence topology on `α → β`. -/
def compactOpenTopologyC (TX : Topology α) (TY : Topology β) :
    Topology { f : α → β // Continuous TX TY f } :=
  (compactConvergenceTopology TX TY).subspace (continuousFunctionSpace TX TY)

/-- The compact-open topology on `C(X, Y)` is a topology (trivially true). -/
theorem compact_open_topology_C_is_topology
    (TX : Topology α) (TY : Topology β) :
    ∃ T : Topology { f : α → β // Continuous TX TY f },
      T = compactOpenTopologyC TX TY := ⟨_, rfl⟩

/-! ### Tube lemma. -/

/- source: topology.mg:103567 name: tube_lemma -/
/-- **Tube lemma.** If `Y` is compact, `x₀ : α`, and `N` is an open set in
    the product topology containing the slice `{x₀} × Y`, then there is an
    open neighborhood `U` of `x₀` such that `U × Y ⊆ N`. -/
theorem tube_lemma_compact_first
    (TX : Topology α) (TY : Topology β) (hYc : TY.Compact)
    (x₀ : α) {N : Set (α × β)}
    (hNopen : (TX.prod TY).IsOpen N)
    (hNsub : ({x₀} : Set α) ×ˢ (Set.univ : Set β) ⊆ N) :
    ∃ U : Set α, TX.IsOpen U ∧ x₀ ∈ U ∧ U ×ˢ (Set.univ : Set β) ⊆ N := by
  classical
  -- Cover Y by open rectangles U_y × V_y ⊆ N, each with x₀ ∈ U_y and y ∈ V_y.
  have hchoice : ∀ y : β, ∃ p : Set α × Set β,
      TX.IsOpen p.1 ∧ TY.IsOpen p.2 ∧ x₀ ∈ p.1 ∧ y ∈ p.2 ∧ p.1 ×ˢ p.2 ⊆ N := by
    intro y
    have hxy : ((x₀, y) : α × β) ∈ N := hNsub ⟨rfl, trivial⟩
    obtain ⟨U, V, hU, hV, hpUV, hUVN⟩ :=
      (isOpen_prod_iff TX TY N).1 hNopen (x₀, y) hxy
    exact ⟨(U, V), hU, hV, hpUV.1, hpUV.2, hUVN⟩
  let P : β → Set α × Set β := fun y => Classical.choose (hchoice y)
  have hP : ∀ y, TX.IsOpen (P y).1 ∧ TY.IsOpen (P y).2 ∧ x₀ ∈ (P y).1 ∧
             y ∈ (P y).2 ∧ (P y).1 ×ˢ (P y).2 ⊆ N :=
    fun y => Classical.choose_spec (hchoice y)
  -- The V-family covers Y = univ.
  let 𝒱 : Set (Set β) := fun V => ∃ y, V = (P y).2
  have h𝒱open : ∀ V ∈ 𝒱, TY.IsOpen V := by
    rintro V ⟨y, rfl⟩; exact (hP y).2.1
  have h𝒱cov : (Set.univ : Set β) ⊆ ⋃₀ 𝒱 := by
    intro y _
    exact ⟨(P y).2, ⟨y, rfl⟩, (hP y).2.2.2.1⟩
  obtain ⟨𝒱₀, h𝒱₀sub, h𝒱₀fin, h𝒱₀cov⟩ := hYc 𝒱 ⟨h𝒱open, h𝒱cov⟩
  -- For each V ∈ 𝒱₀ pick a witness y with (P y).2 = V, i.e., a corresponding
  -- U_V = (P y).1.
  have hdata : ∀ V, V ∈ 𝒱₀ → ∃ y : β, V = (P y).2 := fun V hV => h𝒱₀sub hV
  obtain ⟨n, g, hg⟩ := h𝒱₀fin
  -- Since 𝒱₀ covers univ ⊆ β, if β is empty there's nothing to prove. Guard:
  by_cases hβe : Nonempty β
  · obtain ⟨b⟩ := hβe
    let yI : Fin n → β := fun i =>
      if h : g i ∈ 𝒱₀ then Classical.choose (hdata (g i) h) else b
    -- The U-family.
    let Ui : Fin n → Set α := fun i => (P (yI i)).1
    have hUopen : ∀ i, TX.IsOpen (Ui i) := fun i => (hP (yI i)).1
    have hUx₀ : ∀ i, x₀ ∈ Ui i := fun i => (hP (yI i)).2.2.1
    let U : Set α := fun x => ∀ i : Fin n, x ∈ Ui i
    have hUopen' : TX.IsOpen U := TX.isOpen_iInter_fin_core Ui hUopen
    have hUx₀' : x₀ ∈ U := hUx₀
    -- Show U ×ˢ univ ⊆ N.
    have hUsub : U ×ˢ (Set.univ : Set β) ⊆ N := by
      rintro ⟨x, y⟩ ⟨hxU, _⟩
      -- y ∈ univ, which is covered by 𝒱₀: some V ∈ 𝒱₀ with y ∈ V.
      obtain ⟨V, hV𝒱₀, hyV⟩ := h𝒱₀cov (Set.mem_univ y)
      -- V = g i for some i.
      obtain ⟨i, hi⟩ := hg V hV𝒱₀
      -- V = (P (yI i)).2: because yI picks such a y when g i ∈ 𝒱₀.
      have hgi_mem : g i ∈ 𝒱₀ := by rw [hi]; exact hV𝒱₀
      have hyIdef : yI i = Classical.choose (hdata (g i) hgi_mem) := by
        show (if h : g i ∈ 𝒱₀ then Classical.choose (hdata (g i) h) else b) =
                Classical.choose (hdata (g i) hgi_mem)
        rw [dif_pos hgi_mem]
      have hV_eq : g i = (P (yI i)).2 := by
        rw [hyIdef]; exact Classical.choose_spec (hdata (g i) hgi_mem)
      -- So y ∈ (P (yI i)).2.
      have hyV' : y ∈ (P (yI i)).2 := by rw [← hV_eq]; rw [← hi] at hyV; exact hyV
      -- And x ∈ Ui i = (P (yI i)).1.
      have hxUi : x ∈ (P (yI i)).1 := hxU i
      -- Therefore (x,y) ∈ (P (yI i)).1 ×ˢ (P (yI i)).2 ⊆ N.
      exact (hP (yI i)).2.2.2.2 ⟨hxUi, hyV'⟩
    exact ⟨U, hUopen', hUx₀', hUsub⟩
  · -- β empty: 𝒱₀ covers univ = ∅; U = univ works since U ×ˢ univ = univ × ∅ = ∅.
    refine ⟨Set.univ, TX.isOpen_univ, trivial, ?_⟩
    rintro ⟨x, y⟩ _
    exact absurd ⟨y⟩ hβe

/- source: topology.mg:248431 name: compact_convergence_eval_continuous -/
/-- Evaluation-at-a-point is continuous from the compact-convergence topology.
    Uses that `{x}` is compact. -/
theorem compact_convergence_eval_continuous
    (TX : Topology α) (TY : Topology β) (x : α) :
    Continuous (compactConvergenceTopology TX TY) TY (fun f : α → β => f x) := by
  intro U hU
  -- Preimage: { f | f x ∈ U }. Express as { f | f '' {x} ⊆ U }.
  have hcpt : TX.IsCompact ({x} : Set α) := TX.isCompact_singleton x
  have hsub : { f : α → β | Set.image f ({x} : Set α) ⊆ U } ∈ compactOpenSubbasis TX TY :=
    ⟨{x}, U, hcpt, hU, rfl⟩
  have hpre_eq : ((fun f : α → β => f x) ⁻¹' U) =
                 { f : α → β | Set.image f ({x} : Set α) ⊆ U } := by
    ext f
    refine ⟨?_, ?_⟩
    · intro hfx
      rintro _ ⟨y, hy, rfl⟩
      have hyx : y = x := hy
      rw [hyx]; exact hfx
    · intro h
      exact h ⟨x, rfl, rfl⟩
  rw [hpre_eq]
  exact Topology.ofSubbasis_isOpen_of_mem hsub

end Topology
end Mgw
