# MgwTopology Dependency Graph

Intra-project import DAG of the `MgwTopology` library. External
dependencies (Batteries, Lean core) are not shown. Click any node
to open its source file on GitHub.

The graph below is the **transitive reduction** of the raw import
graph (21 nodes, 78 direct imports → 29 non-redundant edges).
An edge `A --> B` means `A` imports `B` directly, and there is no
longer alternative path `A → … → B` through other modules.

```mermaid
graph TD
    Baire[Baire]
    Basis[Basis]
    BinaryProduct[BinaryProduct]
    ClosedAndLimit[ClosedAndLimit]
    ClosureInterior[ClosureInterior]
    Compact[Compact]
    Connected[Connected]
    Continuous[Continuous]
    Core[Core]
    Countability[Countability]
    Examples[Examples]
    FunctionSpace[FunctionSpace]
    LocalCompact[LocalCompact]
    LocalFinite[LocalFinite]
    Normal[Normal]
    Order[Order]
    Paracompact[Paracompact]
    Product[Product]
    Separation[Separation]
    SetLib[SetLib]
    Subspace[Subspace]

    Baire --> Countability
    Basis --> Core
    BinaryProduct --> ClosedAndLimit
    BinaryProduct --> Continuous
    ClosedAndLimit --> Subspace
    ClosureInterior --> Core
    Compact --> ClosedAndLimit
    Compact --> Continuous
    Connected --> Core
    Continuous --> Subspace
    Core --> SetLib
    Countability --> Compact
    Examples --> Core
    FunctionSpace --> BinaryProduct
    FunctionSpace --> Compact
    LocalCompact --> BinaryProduct
    LocalCompact --> Compact
    LocalFinite --> Countability
    Normal --> Countability
    Normal --> LocalCompact
    Normal --> Separation
    Order --> Basis
    Paracompact --> LocalFinite
    Paracompact --> Normal
    Product --> Continuous
    Separation --> BinaryProduct
    Subspace --> Basis
    Subspace --> ClosureInterior
    Subspace --> Examples

    click Baire "https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Baire.lean"
    click Basis "https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Basis.lean"
    click BinaryProduct "https://github.com/ldct/mgw-topology/blob/main/MgwTopology/BinaryProduct.lean"
    click ClosedAndLimit "https://github.com/ldct/mgw-topology/blob/main/MgwTopology/ClosedAndLimit.lean"
    click ClosureInterior "https://github.com/ldct/mgw-topology/blob/main/MgwTopology/ClosureInterior.lean"
    click Compact "https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Compact.lean"
    click Connected "https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Connected.lean"
    click Continuous "https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Continuous.lean"
    click Core "https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Core.lean"
    click Countability "https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Countability.lean"
    click Examples "https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Examples.lean"
    click FunctionSpace "https://github.com/ldct/mgw-topology/blob/main/MgwTopology/FunctionSpace.lean"
    click LocalCompact "https://github.com/ldct/mgw-topology/blob/main/MgwTopology/LocalCompact.lean"
    click LocalFinite "https://github.com/ldct/mgw-topology/blob/main/MgwTopology/LocalFinite.lean"
    click Normal "https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Normal.lean"
    click Order "https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Order.lean"
    click Paracompact "https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Paracompact.lean"
    click Product "https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Product.lean"
    click Separation "https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Separation.lean"
    click SetLib "https://github.com/ldct/mgw-topology/blob/main/MgwTopology/SetLib.lean"
    click Subspace "https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Subspace.lean"
```

## Modules (topological order)

- **[SetLib](https://github.com/ldct/mgw-topology/blob/main/MgwTopology/SetLib.lean)** (L0) — A minimal `Set α` library for the MgwTopology port.
- **[Core](https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Core.lean)** (L1) — Core topology definitions.
- **[Basis](https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Basis.lean)** (L2) — Bases and subbases for a topology.
- **[ClosureInterior](https://github.com/ldct/mgw-topology/blob/main/MgwTopology/ClosureInterior.lean)** (L2) — Closure, interior, and boundary operators.
- **[Connected](https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Connected.lean)** (L2) — Connected spaces.
- **[Examples](https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Examples.lean)** (L2) — Example topologies and the finer/coarser relation.
- **[Order](https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Order.lean)** (L3) — The order topology.
- **[Subspace](https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Subspace.lean)** (L3) — The subspace topology.
- **[ClosedAndLimit](https://github.com/ldct/mgw-topology/blob/main/MgwTopology/ClosedAndLimit.lean)** (L4) — Closed sets and limit points.
- **[Continuous](https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Continuous.lean)** (L4) — Continuous maps.
- **[BinaryProduct](https://github.com/ldct/mgw-topology/blob/main/MgwTopology/BinaryProduct.lean)** (L5) — Binary product topology (X × Y).
- **[Compact](https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Compact.lean)** (L5) — Compact spaces.
- **[Product](https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Product.lean)** (L5) — Indexed product topology (finite index / box topology version).
- **[Countability](https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Countability.lean)** (L6) — Countability axioms.
- **[FunctionSpace](https://github.com/ldct/mgw-topology/blob/main/MgwTopology/FunctionSpace.lean)** (L6) — Function spaces: pointwise and compact-open topologies.
- **[LocalCompact](https://github.com/ldct/mgw-topology/blob/main/MgwTopology/LocalCompact.lean)** (L6) — Locally compact spaces.
- **[Separation](https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Separation.lean)** (L6) — Separation axioms: T1, Hausdorff, regular, normal.
- **[Baire](https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Baire.lean)** (L7) — Baire spaces and G_δ / F_σ sets.
- **[LocalFinite](https://github.com/ldct/mgw-topology/blob/main/MgwTopology/LocalFinite.lean)** (L7) — Local finiteness.
- **[Normal](https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Normal.lean)** (L7) — Normal spaces.
- **[Paracompact](https://github.com/ldct/mgw-topology/blob/main/MgwTopology/Paracompact.lean)** (L8) — Paracompactness.
