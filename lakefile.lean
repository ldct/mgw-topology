import Lake
open Lake DSL

package "MgwTopology" where
  version := v!"0.1.0"

require batteries from git
  "https://github.com/leanprover-community/batteries.git" @ "v4.29.0"

@[default_target]
lean_lib «MgwTopology» where
  -- add library configuration options here
