# The plan

The plan of the library, in the TOML that [tracker](https://github.com/bridgekat/tracker/) reads.
One file per group; the file stem is the group's name.

```
lake build                  # the tracker reads oleans, so build first
lake exe tracker check      # resolve every node against the compiled library
lake exe tracker status     # counts per group, rolled up through parents
lake exe tracker lint       # plan errors, cycles, placement and kind mismatches
lake exe tracker show <group | id>
lake exe tracker graph --under <group> [--dot]
```

## What a node is

**A node is a result the library stands behind, not every declaration it contains.** The library
writes some six thousand declarations; this plan names 2590 of them, by two rules:

* In the backbone, the nodes of a module are what its own docstring advertises under
  `## Main definitions` and `## Main results`. A module with no such section — a short one, or a
  flat list of utilities like `Order.EReal` — contributes all of its declarations.
* In a surface, the nodes are the book's numbered results, at the granularity the book states them:
  one node per result, or one per clause where the library states the clauses separately, each
  citing the result in its `source`. The definitions a surface introduces for the book's vocabulary
  are nodes too.

What is left out is the working material — the intermediate lemmas, the `simp` companions, the
variant forms — and leaving it out costs nothing, because the tracker reads a proof's real
dependencies straight through untracked constants of the project. An edge from a node to a node is
drawn whether or not the proof passed through helpers on the way.

Everything here is proved, so the nodes carry nothing but their ids: kind, description and
dependencies are superseded by the declaration, its doc comment and its proof. The exceptions are
the few nodes whose declaration has no doc comment, which keep a `desc` until it gets one, and the
surface nodes, which keep the `source` they state.

## Shape

Group names are module names without the `Tdaf.` prefix, so `Analysis.Convex.Closure` is the plan
of `Tdaf.Analysis.Convex.Closure`. Every group names the module its declarations must live in, and
`lint` reports one that lands elsewhere. Groups without a module of their own are the directories,
and exist to roll counts up.

The backbone and the surfaces are different root groups: `Analysis`, `Order` and `LinearAlgebra`
against `Surface`. Nothing joins them, because nothing should — a surface depends on the backbone,
never the other way round, and `graph` shows that as a one-way flow.

## Building on it

A later project appends its own groups — a backbone one under `Analysis`, a surface per book under
`Surface` — and names ids from these groups in the `deps` of its open nodes. `tracker show <id>`
then prints the signature the new work has to meet, and `tracker ready` will not offer a task
before what it rests on is proved. Only `Tdaf` is tracked, so Mathlib and core never appear as
nodes.

Do not restate an existing node under a new name. If a new project needs to depend on something the
library has but this plan does not name, add the node to the group that owns it — that is the plan
admitting the declaration is API.
