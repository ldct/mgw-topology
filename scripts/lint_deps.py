#!/usr/bin/env python3
"""Lint that DEPENDENCIES.md matches the actual Lean import graph.

Checks:
1. The set of modules (nodes) in DEPENDENCIES.md matches the .lean files.
2. The edges in DEPENDENCIES.md are exactly the transitive reduction of the
   actual import graph parsed from `import MgwTopology.X` statements.
"""

import re
import sys
from pathlib import Path

PROJECT = "MgwTopology"
ROOT = Path(__file__).resolve().parent.parent
SRC_DIR = ROOT / PROJECT
DEPS_MD = ROOT / "DEPENDENCIES.md"


def parse_lean_imports() -> dict[str, set[str]]:
    """Return {module_name: {imported_module_names}} for intra-project imports."""
    graph: dict[str, set[str]] = {}
    for f in sorted(SRC_DIR.glob("*.lean")):
        mod = f.stem
        imports: set[str] = set()
        for line in f.read_text().splitlines():
            m = re.match(rf"^import\s+{PROJECT}\.(\w+)", line)
            if m:
                imports.add(m.group(1))
        graph[mod] = imports
    return graph


def transitive_reduction(graph: dict[str, set[str]]) -> dict[str, set[str]]:
    """Compute the transitive reduction of a DAG."""
    # For each node, compute full set of transitive descendants (via DFS).
    cache: dict[str, set[str]] = {}

    visiting: set[str] = set()

    def reachable(node: str) -> set[str]:
        if node in cache:
            return cache[node]
        if node in visiting:
            return set()  # cycle detected
        visiting.add(node)
        result: set[str] = set()
        for child in graph.get(node, set()):
            result.add(child)
            result |= reachable(child)
        visiting.discard(node)
        cache[node] = result
        return result

    reduced: dict[str, set[str]] = {}
    for node, children in graph.items():
        keep: set[str] = set()
        for child in children:
            # Keep edge node->child only if child is NOT reachable
            # through any *other* direct child of node.
            redundant = False
            for other in children:
                if other != child and child in reachable(other):
                    redundant = True
                    break
            if not redundant:
                keep.add(child)
        reduced[node] = keep
    return reduced


def parse_deps_md() -> tuple[set[str], dict[str, set[str]]]:
    """Parse DEPENDENCIES.md and return (nodes, {src: {dst}})."""
    text = DEPS_MD.read_text()
    # Extract the mermaid block
    m = re.search(r"```mermaid\s*\n(.*?)```", text, re.DOTALL)
    if not m:
        sys.exit("ERROR: No mermaid block found in DEPENDENCIES.md")
    body = m.group(1)

    nodes: set[str] = set()
    edges: dict[str, set[str]] = {}

    for line in body.splitlines():
        line = line.strip()
        # Node declaration: Name[Name]
        node_m = re.match(r"^(\w+)\[\w+\]$", line)
        if node_m:
            nodes.add(node_m.group(1))
            continue
        # Edge: A --> B
        edge_m = re.match(r"^(\w+)\s*-->\s*(\w+)$", line)
        if edge_m:
            src, dst = edge_m.group(1), edge_m.group(2)
            edges.setdefault(src, set()).add(dst)

    return nodes, edges


def main() -> int:
    errors: list[str] = []

    lean_graph = parse_lean_imports()
    lean_modules = set(lean_graph.keys())

    md_nodes, md_edges = parse_deps_md()

    # Check nodes
    missing_from_md = lean_modules - md_nodes
    extra_in_md = md_nodes - lean_modules
    if missing_from_md:
        errors.append(f"Modules in Lean but not in DEPENDENCIES.md: {sorted(missing_from_md)}")
    if extra_in_md:
        errors.append(f"Modules in DEPENDENCIES.md but not in Lean: {sorted(extra_in_md)}")

    # Check for import cycles
    def _find_cycle(node: str, path: list[str], visited: set[str]) -> list[str] | None:
        if node in path:
            return path[path.index(node):] + [node]
        if node in visited:
            return None
        visited.add(node)
        path.append(node)
        for dep in lean_graph.get(node, set()):
            cycle = _find_cycle(dep, path, visited)
            if cycle:
                return cycle
        path.pop()
        return None

    for mod in sorted(lean_graph):
        cycle = _find_cycle(mod, [], set())
        if cycle:
            errors.append(f"Import cycle detected: {' -> '.join(cycle)}")
            break

    # Check edges (transitive reduction)
    reduced = transitive_reduction(lean_graph)

    # Build flat edge sets for comparison
    actual_edges: set[tuple[str, str]] = set()
    for src, dsts in reduced.items():
        for dst in dsts:
            actual_edges.add((src, dst))

    md_edge_set: set[tuple[str, str]] = set()
    for src, dsts in md_edges.items():
        for dst in dsts:
            md_edge_set.add((src, dst))

    missing_edges = actual_edges - md_edge_set
    extra_edges = md_edge_set - actual_edges

    if missing_edges:
        for src, dst in sorted(missing_edges):
            errors.append(f"Edge {src} --> {dst} is in transitive reduction but missing from DEPENDENCIES.md")
    if extra_edges:
        for src, dst in sorted(extra_edges):
            errors.append(f"Edge {src} --> {dst} is in DEPENDENCIES.md but not in transitive reduction")

    if errors:
        print("DEPENDENCIES.md is out of sync:")
        for e in errors:
            print(f"  - {e}")
        return 1
    else:
        print("DEPENDENCIES.md is in sync with Lean imports.")
        return 0


if __name__ == "__main__":
    sys.exit(main())
