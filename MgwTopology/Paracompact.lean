/-
Paracompactness.

Corresponds to topology.mg §41 (Paracompactness). We port:

* The `Refines` predicate.
* The `Paracompact` definition.
* Trivial unfolding `locally_finite_refinement`.
* `paracompact_Hausdorff_regular` and `paracompact_Hausdorff_normal`.
* `closed_subspace_paracompact`.

The long "shrinking lemma" (normal + locally-finite open cover ⇒ a shrinking
whose closures still cover) is left as a `sorry` — its Megalodon proof uses
transfinite induction over a well-ordering, infrastructure we do not have
in the Mathlib-free port.
-/
import MgwTopology.Section_12_Core
import MgwTopology.ClosureInterior
import MgwTopology.ClosedAndLimit
import MgwTopology.Subspace
import MgwTopology.Compact
import MgwTopology.Separation
import MgwTopology.Normal
import MgwTopology.LocalFinite

namespace Mgw
namespace Topology

universe u
variable {α : Type u} (T : Topology α)

/-- `Refines 𝒱 𝒰`: every member of `𝒱` is contained in some member of `𝒰`. -/
/- source: topology.mg:213585 name: refine_of -/
def Refines (𝒱 𝒰 : Set (Set α)) : Prop :=
  ∀ V, V ∈ 𝒱 → ∃ U, U ∈ 𝒰 ∧ V ⊆ U

/-- A space is *paracompact* if every open cover of the whole space has a
locally-finite open refinement. -/
/- source: topology.mg:227447 name: paracompact_space -/
def Paracompact : Prop :=
  ∀ 𝒰 : Set (Set α), (∀ U ∈ 𝒰, T.IsOpen U) → Set.univ ⊆ ⋃₀ 𝒰 →
    ∃ 𝒱 : Set (Set α), (∀ V ∈ 𝒱, T.IsOpen V) ∧ Set.univ ⊆ ⋃₀ 𝒱 ∧
      T.LocallyFiniteFamily 𝒱 ∧ Refines 𝒱 𝒰

/-! ### §41 basic consequences of paracompactness. -/

/- source: topology.mg:227454 name: locally_finite_refinement -/
/-- Paracompact spaces have locally-finite open refinements of every open
cover (omitting the refinement clause). -/
theorem Paracompact.locally_finite_refinement
    (h : T.Paracompact) {𝒰 : Set (Set α)}
    (hopen : ∀ U ∈ 𝒰, T.IsOpen U) (hcov : Set.univ ⊆ ⋃₀ 𝒰) :
    ∃ 𝒱 : Set (Set α), (∀ V ∈ 𝒱, T.IsOpen V) ∧
      Set.univ ⊆ ⋃₀ 𝒱 ∧ T.LocallyFiniteFamily 𝒱 := by
  obtain ⟨𝒱, hVopen, hVcov, hVlf, _⟩ := h 𝒰 hopen hcov
  exact ⟨𝒱, hVopen, hVcov, hVlf⟩

/-! ### §41 Theorem: paracompact + Hausdorff ⇒ regular. -/

/- source: topology.mg:227479 name: paracompact_Hausdorff_regular -/
/-- A paracompact Hausdorff space is regular. -/
theorem Regular.of_paracompact_hausdorff
    (hpara : T.Paracompact) (hH : T.Hausdorff) : T.Regular := by
  classical
  refine ⟨T1.of_hausdorff T hH, ?_⟩
  intro x F hF hxF
  -- For each y ∈ F, pick Hausdorff-separating opens sepU y (containing x)
  -- and sepV y (containing y) that are disjoint.
  have hchoose : ∀ y : α, y ∈ F →
      ∃ p : Set α × Set α, T.IsOpen p.1 ∧ T.IsOpen p.2 ∧
        x ∈ p.1 ∧ y ∈ p.2 ∧ p.1 ∩ p.2 = ∅ := by
    intro y hyF
    have hxy : x ≠ y := fun hxy => hxF (by rw [← hxy] at hyF; exact hyF)
    obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := hH x y hxy
    exact ⟨(U, V), hU, hV, hxU, hyV, hUV⟩
  let sepU : α → Set α := fun y =>
    if h : y ∈ F then (Classical.choose (hchoose y h)).1 else Set.univ
  let sepV : α → Set α := fun y =>
    if h : y ∈ F then (Classical.choose (hchoose y h)).2 else Set.univ
  have hsepU_open : ∀ y ∈ F, T.IsOpen (sepU y) := by
    intro y hy
    show T.IsOpen (if h : y ∈ F then (Classical.choose (hchoose y h)).1 else Set.univ)
    rw [dif_pos hy]; exact (Classical.choose_spec (hchoose y hy)).1
  have hsepV_open : ∀ y ∈ F, T.IsOpen (sepV y) := by
    intro y hy
    show T.IsOpen (if h : y ∈ F then (Classical.choose (hchoose y h)).2 else Set.univ)
    rw [dif_pos hy]; exact (Classical.choose_spec (hchoose y hy)).2.1
  have hx_in_sepU : ∀ y ∈ F, x ∈ sepU y := by
    intro y hy
    show x ∈ if h : y ∈ F then (Classical.choose (hchoose y h)).1 else Set.univ
    rw [dif_pos hy]; exact (Classical.choose_spec (hchoose y hy)).2.2.1
  have hy_in_sepV : ∀ y ∈ F, y ∈ sepV y := by
    intro y hy
    show y ∈ if h : y ∈ F then (Classical.choose (hchoose y h)).2 else Set.univ
    rw [dif_pos hy]; exact (Classical.choose_spec (hchoose y hy)).2.2.2.1
  have hsep_disj : ∀ y ∈ F, sepU y ∩ sepV y = ∅ := by
    intro y hy
    have heq1 : sepU y = (Classical.choose (hchoose y hy)).1 := by
      show (if h : y ∈ F then (Classical.choose (hchoose y h)).1 else Set.univ) =
           (Classical.choose (hchoose y hy)).1
      rw [dif_pos hy]
    have heq2 : sepV y = (Classical.choose (hchoose y hy)).2 := by
      show (if h : y ∈ F then (Classical.choose (hchoose y h)).2 else Set.univ) =
           (Classical.choose (hchoose y hy)).2
      rw [dif_pos hy]
    rw [heq1, heq2]
    exact (Classical.choose_spec (hchoose y hy)).2.2.2.2
  -- U₀ := Fᶜ (open complement of the closed F), and VFam := {sepV y | y ∈ F}.
  let U0 : Set α := Fᶜ
  have hU0open : T.IsOpen U0 := hF
  have hxU0 : x ∈ U0 := hxF
  let VFam : Set (Set α) := Set.image sepV F
  -- Cover := {U0} ∪ VFam.
  let Cover : Set (Set α) := fun W => W = U0 ∨ W ∈ VFam
  have hCoverOpen : ∀ W ∈ Cover, T.IsOpen W := by
    intro W hW
    rcases hW with rfl | ⟨y, hy, rfl⟩
    · exact hU0open
    · exact hsepV_open y hy
  have hCoverCov : Set.univ ⊆ ⋃₀ Cover := by
    intro z _
    by_cases hzF : z ∈ F
    · exact ⟨sepV z, Or.inr ⟨z, hzF, rfl⟩, hy_in_sepV z hzF⟩
    · exact ⟨U0, Or.inl rfl, hzF⟩
  -- Apply paracompactness.
  obtain ⟨W, hWopen, hWcov, hWlf, hWref⟩ := hpara Cover hCoverOpen hCoverCov
  -- WF := {w ∈ W | w ∩ F ≠ ∅} (those members of W that touch F).
  let WF : Set (Set α) := fun w => w ∈ W ∧ ∃ z, z ∈ w ∧ z ∈ F
  have hWFsubW : WF ⊆ W := fun _ h => h.1
  have hLF_WF : T.LocallyFiniteFamily WF := hWlf.mono T hWFsubW
  have hWFopen : ∀ w ∈ WF, T.IsOpen w := fun w h => hWopen w h.1
  -- V := ⋃₀ WF. Open, contains F.
  let V : Set α := ⋃₀ WF
  have hVopen : T.IsOpen V := T.isOpen_sUnion (fun w hw => hWFopen w hw)
  have hFsubV : F ⊆ V := by
    intro y hyF
    obtain ⟨w, hw, hyw⟩ := hWcov (Set.mem_univ y)
    refine ⟨w, ⟨hw, y, hyw, hyF⟩, hyw⟩
  -- Closure of V equals union of closures (by §39 1c, applied to WF).
  -- Key fact we use: x is in no closure(w) for w ∈ WF.
  have hxNot_clw : ∀ w, w ∈ WF → x ∉ T.closure w := by
    intro w hwWF hxclw
    -- Refinement: w ⊆ some u ∈ Cover.
    obtain ⟨u, huCover, hwu⟩ := hWref w hwWF.1
    -- u is either U0 or sepV y for some y ∈ F.
    rcases huCover with rfl | ⟨y, hyF, rfl⟩
    · -- u = U0 = Fᶜ. Then w ⊆ Fᶜ, so w ∩ F = ∅, contradicting w ∈ WF.
      obtain ⟨z, hzw, hzF⟩ := hwWF.2
      exact hwu hzw hzF
    · -- u = sepV y with y ∈ F. sepU y is an open nbhd of x disjoint from sepV y,
      -- hence disjoint from w. So x ∉ closure w.
      have hxcl := hxclw
      rw [T.mem_closure_iff] at hxcl
      obtain ⟨z, hzU, hzw⟩ :=
        hxcl (sepU y) (hsepU_open y hyF) (hx_in_sepU y hyF)
      have hzV : z ∈ sepV y := hwu hzw
      have hzInter : z ∈ sepU y ∩ sepV y := ⟨hzU, hzV⟩
      rw [hsep_disj y hyF] at hzInter
      exact hzInter
  -- C := union of closures of WF. x ∉ C.
  let C : Set α := ⋃₀ (Set.image T.closure WF)
  have hxNotC : x ∉ C := by
    rintro ⟨D, ⟨w, hwWF, rfl⟩, hxclw⟩
    exact hxNot_clw w hwWF hxclw
  -- C is closed: it equals closure V by §39 Lemma 39.1(c).
  have hCeq : T.closure V = C := LocallyFiniteFamily.closure_sUnion T hLF_WF
  have hCclosed : T.IsClosed C := by rw [← hCeq]; exact T.isClosed_closure V
  -- U := Cᶜ is open, contains x, V ⊆ C (so V ∩ U = ∅ since U = Cᶜ).
  let U : Set α := Cᶜ
  have hUopen : T.IsOpen U := T.isOpen_compl_of_isClosed hCclosed
  have hVsubC : V ⊆ C := by
    rw [← hCeq]; exact T.subset_closure V
  refine ⟨U, V, hUopen, hVopen, hxNotC, hFsubV, ?_⟩
  -- U ∩ V = ∅: V ⊆ C and U = Cᶜ.
  ext z
  refine ⟨?_, fun h => h.elim⟩
  rintro ⟨hzU, hzV⟩
  exact hzU (hVsubC hzV)

/-! ### §41 Theorem: paracompact + Hausdorff ⇒ normal.

The proof mirrors regularity: replace the single point `x` with a closed set
`A`, using regularity (just proved) to produce separating nbhds between points
of `A` and the disjoint closed `B`. -/

/- source: topology.mg:227895 name: paracompact_Hausdorff_normal -/
/-- A paracompact Hausdorff space is normal. -/
theorem Normal.of_paracompact_hausdorff
    (hpara : T.Paracompact) (hH : T.Hausdorff) : T.Normal := by
  classical
  have hR : T.Regular := Regular.of_paracompact_hausdorff T hpara hH
  refine ⟨hR.1, ?_⟩
  intro A B hA hB hAB
  -- For each a ∈ A, regularity gives opens sepU a ∋ a, sepV a ⊇ B, disjoint.
  -- (Regularity separates a point from a disjoint closed set; here we
  --  separate each a ∈ A from B.)
  have ha_notin_B : ∀ a, a ∈ A → a ∉ B := by
    intro a haA haB
    have : a ∈ A ∩ B := ⟨haA, haB⟩
    rw [hAB] at this; exact this
  have hchoose : ∀ a : α, a ∈ A →
      ∃ p : Set α × Set α, T.IsOpen p.1 ∧ T.IsOpen p.2 ∧
        a ∈ p.1 ∧ B ⊆ p.2 ∧ p.1 ∩ p.2 = ∅ := by
    intro a haA
    obtain ⟨U, V, hU, hV, haU, hBV, hUV⟩ := hR.2 a B hB (ha_notin_B a haA)
    exact ⟨(U, V), hU, hV, haU, hBV, hUV⟩
  let sepU : α → Set α := fun a =>
    if h : a ∈ A then (Classical.choose (hchoose a h)).1 else Set.univ
  let sepV : α → Set α := fun a =>
    if h : a ∈ A then (Classical.choose (hchoose a h)).2 else Set.univ
  have hsepU_open : ∀ a ∈ A, T.IsOpen (sepU a) := by
    intro a ha
    show T.IsOpen (if h : a ∈ A then (Classical.choose (hchoose a h)).1 else Set.univ)
    rw [dif_pos ha]; exact (Classical.choose_spec (hchoose a ha)).1
  have hsepV_open : ∀ a ∈ A, T.IsOpen (sepV a) := by
    intro a ha
    show T.IsOpen (if h : a ∈ A then (Classical.choose (hchoose a h)).2 else Set.univ)
    rw [dif_pos ha]; exact (Classical.choose_spec (hchoose a ha)).2.1
  have ha_in_sepU : ∀ a ∈ A, a ∈ sepU a := by
    intro a ha
    show a ∈ if h : a ∈ A then (Classical.choose (hchoose a h)).1 else Set.univ
    rw [dif_pos ha]; exact (Classical.choose_spec (hchoose a ha)).2.2.1
  have hB_sub_sepV : ∀ a ∈ A, B ⊆ sepV a := by
    intro a ha
    show B ⊆ if h : a ∈ A then (Classical.choose (hchoose a h)).2 else Set.univ
    rw [dif_pos ha]; exact (Classical.choose_spec (hchoose a ha)).2.2.2.1
  have hsep_disj : ∀ a ∈ A, sepU a ∩ sepV a = ∅ := by
    intro a ha
    have heq1 : sepU a = (Classical.choose (hchoose a ha)).1 := by
      show (if h : a ∈ A then (Classical.choose (hchoose a h)).1 else Set.univ) =
           (Classical.choose (hchoose a ha)).1
      rw [dif_pos ha]
    have heq2 : sepV a = (Classical.choose (hchoose a ha)).2 := by
      show (if h : a ∈ A then (Classical.choose (hchoose a h)).2 else Set.univ) =
           (Classical.choose (hchoose a ha)).2
      rw [dif_pos ha]
    rw [heq1, heq2]
    exact (Classical.choose_spec (hchoose a ha)).2.2.2.2
  -- Build the open cover {Aᶜ} ∪ {sepU a | a ∈ A}.
  let U0 : Set α := Aᶜ
  have hU0open : T.IsOpen U0 := hA
  let UFam : Set (Set α) := Set.image sepU A
  let Cover : Set (Set α) := fun W => W = U0 ∨ W ∈ UFam
  have hCoverOpen : ∀ W ∈ Cover, T.IsOpen W := by
    intro W hW
    rcases hW with rfl | ⟨a, ha, rfl⟩
    · exact hU0open
    · exact hsepU_open a ha
  have hCoverCov : Set.univ ⊆ ⋃₀ Cover := by
    intro z _
    by_cases hzA : z ∈ A
    · exact ⟨sepU z, Or.inr ⟨z, hzA, rfl⟩, ha_in_sepU z hzA⟩
    · exact ⟨U0, Or.inl rfl, hzA⟩
  obtain ⟨W, hWopen, hWcov, hWlf, hWref⟩ := hpara Cover hCoverOpen hCoverCov
  -- WA := {w ∈ W | w meets A}.
  let WA : Set (Set α) := fun w => w ∈ W ∧ ∃ z, z ∈ w ∧ z ∈ A
  have hWAsubW : WA ⊆ W := fun _ h => h.1
  have hLF_WA : T.LocallyFiniteFamily WA := hWlf.mono T hWAsubW
  have hWAopen : ∀ w ∈ WA, T.IsOpen w := fun w h => hWopen w h.1
  let Uout : Set α := ⋃₀ WA
  have hUout_open : T.IsOpen Uout := T.isOpen_sUnion (fun w hw => hWAopen w hw)
  have hA_sub_Uout : A ⊆ Uout := by
    intro a haA
    obtain ⟨w, hw, haw⟩ := hWcov (Set.mem_univ a)
    refine ⟨w, ⟨hw, a, haw, haA⟩, haw⟩
  -- For each b ∈ B, b ∉ closure(w) for each w ∈ WA (using refinement).
  have hb_notin_cl : ∀ b, b ∈ B → ∀ w, w ∈ WA → b ∉ T.closure w := by
    intro b hbB w hwWA hbcl
    obtain ⟨u, huCover, hwu⟩ := hWref w hwWA.1
    rcases huCover with rfl | ⟨a, haA, rfl⟩
    · -- u = Aᶜ. So w ⊆ Aᶜ, but w meets A — contradiction.
      obtain ⟨z, hzw, hzA⟩ := hwWA.2
      exact hwu hzw hzA
    · -- u = sepU a. Then w ⊆ sepU a. sepV a is an open nbhd of b disjoint from w.
      rw [T.mem_closure_iff] at hbcl
      obtain ⟨z, hzV, hzw⟩ := hbcl (sepV a) (hsepV_open a haA) (hB_sub_sepV a haA hbB)
      have hzU : z ∈ sepU a := hwu hzw
      have hzInter : z ∈ sepU a ∩ sepV a := ⟨hzU, hzV⟩
      rw [hsep_disj a haA] at hzInter
      exact hzInter
  -- C := ⋃₀ (closures of WA). B ∩ C = ∅.
  let C : Set α := ⋃₀ (Set.image T.closure WA)
  have hB_sub_Cc : B ⊆ Cᶜ := by
    intro b hbB
    rintro ⟨D, ⟨w, hwWA, rfl⟩, hbcl⟩
    exact hb_notin_cl b hbB w hwWA hbcl
  have hCeq : T.closure Uout = C := LocallyFiniteFamily.closure_sUnion T hLF_WA
  have hCclosed : T.IsClosed C := by rw [← hCeq]; exact T.isClosed_closure Uout
  have hUout_sub_C : Uout ⊆ C := by
    rw [← hCeq]; exact T.subset_closure Uout
  refine ⟨Uout, Cᶜ, hUout_open, T.isOpen_compl_of_isClosed hCclosed,
    hA_sub_Uout, hB_sub_Cc, ?_⟩
  ext z
  refine ⟨?_, fun h => h.elim⟩
  rintro ⟨hzU, hzCc⟩
  exact hzCc (hUout_sub_C hzU)

/-! ### §41 ex41.1: closed subspace of paracompact is paracompact.

We leave this `sorry` — the ambient construction is long (lifts a subspace
cover to an ambient cover by adding `Yᶜ`, paracompactifies, restricts, and
verifies refinement). It is mechanical but tedious and not on the critical
path. -/

/- source: topology.mg:228355 name: closed_subspace_paracompact -/
/-- A closed subspace of a paracompact space is paracompact. -/
theorem Paracompact.subspace_of_closed
    (_h : T.Paracompact) {Y : Set α} (_hY : T.IsClosed Y) :
    (T.subspace Y).Paracompact := by
  -- The Megalodon proof is ~200 lines and mostly bookkeeping. Deferred.
  sorry

/-! ### §41 shrinking lemma (deferred).

In a normal space, every locally-finite open cover admits a shrinking: a
locally-finite open cover whose closures also cover, with each shrunk member
having closure inside the original. The proof is transfinite induction over
a well-ordering of the family; we leave it as a `sorry`. -/

/- source: topology.mg:213567 name: normal_locally_finite_open_cover_shrinking -/
/-- Shrinking lemma: in a normal space, every locally-finite open cover has an
open shrinking. **Deferred: transfinite induction.** -/
theorem Normal.shrinking_lemma
    (_hN : T.Normal) {W : Set (Set α)}
    (_hWopen : ∀ w ∈ W, T.IsOpen w) (_hWcov : Set.univ ⊆ ⋃₀ W)
    (_hWlf : T.LocallyFiniteFamily W) :
    ∃ f : Set α → Set α,
      (∀ w ∈ W, T.IsOpen (f w)) ∧
      (∀ w ∈ W, f w ⊆ w) ∧
      (∀ w ∈ W, T.closure (f w) ⊆ w) ∧
      Set.univ ⊆ ⋃₀ (Set.image f W) := by
  sorry

end Topology
end Mgw
