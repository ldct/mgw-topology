/-
Connected spaces.

Corresponds to topology.mg §23 (Connected Spaces), §25 (Components).
-/
import MgwTopology.Section_12_Core

namespace Mgw
namespace Topology

universe u
variable {α : Type u} (T : Topology α)

/-- A space is connected iff it cannot be partitioned into two disjoint
    nonempty open sets. -/
def Connected : Prop :=
  ¬ ∃ U V : Set α, T.IsOpen U ∧ T.IsOpen V ∧
      U ≠ ∅ ∧ V ≠ ∅ ∧ U ∩ V = ∅ ∧ U ∪ V = Set.univ

end Topology
end Mgw
