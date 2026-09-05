# The plan

The plan of the library, in the TOML that [tracker](https://github.com/bridgekat/tracker/) reads.
One file per group, and a group is the plan for one module.

```
lake build                  # the tracker reads oleans and never builds, so build first
lake exe tracker status     # counts per group, rolled up through parents
lake exe tracker lint       # plan errors, cycles, placement and kind mismatches
lake exe tracker show <group | id>
lake exe tracker graph --under <group> [--dot]
```

Every command resolves the plan against the compiled library first when the cache is stale, so
`check` is only needed to do that step alone or, with `--force`, to redo it. An edit that has not
been built is invisible, which is why `lake build` comes first.

## What a node is

**A node is a result the library stands behind, not every declaration it contains.** The library
writes some six thousand declarations; this plan names 2590 of them, by two rules:

* In the backbone, the nodes of a module are what its own docstring advertises under
  `## Main definitions` and `## Main results`. A module with no such section — a short one, or a
  flat list of utilities like `Tdaf/Order/EReal` — contributes all of its declarations.
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

A group *is* a module, named by the module's path, so this directory is a copy of `Tdaf/` with
`.lean` replaced by `.toml`, one level deeper than it looks:
`tracker/Tdaf/Analysis/Convex/Closure.toml` is the plan for `Tdaf.Analysis.Convex.Closure`, and the
group is `Tdaf/Analysis/Convex/Closure`. That name is the whole of the correspondence — there is no
field pointing at the module — and `lint` reports a declaration that lands in a module other than
its group's. Groups nest as the modules do, and there is one root, `Tdaf`, because that is where
the module tree has its root; the backbone and the surfaces are `Tdaf/Analysis` and `Tdaf/Surface`,
which nothing joins below `Tdaf` itself. A surface depends on the backbone and never the other way
round, and `graph` shows that as a one-way flow.

A group standing for a module that is only a directory — `Tdaf/Analysis`, `Tdaf/Order`, the eight
subdirectories of `Tdaf/Analysis/Convex` — has no nodes, and exists to roll counts up and to carry
a description of what the directory is for. Those descriptions are the only ones the plan writes:
every other group has a real module whose `/-! … -/` doc comment describes it, and a plan copy
would only be superseded. `Tdaf.toml` is empty for the same reason, and exists because a directory
must have the group file of its name beside it.

A group is addressed by its path or by an unambiguous trailing part of it, so `tracker show
Convex/Closure` and `tracker show Rockafellar/Part7/Section33` both work. Two groups share a stem
often enough — `Closure` is a module of both `Convex` and `Convex/Saddle` — that the last component
alone is not always enough.

## Building on it

A later project appends its own groups — a backbone one under `Tdaf/Analysis`, a surface per book
under `Tdaf/Surface` — one per module it intends to write, and names ids from these groups in the
`deps` of its open nodes. `tracker show <id>` then prints the signature the new work has to meet,
and `tracker ready` lists the modules that can be worked on now, never one whose dependencies here
are unproved. Only `Tdaf` is tracked, so Mathlib and core never appear as nodes.

Do not restate an existing node under a new name. If a new project needs to depend on something the
library has but this plan does not name, add the node to the group that owns it — that is the plan
admitting the declaration is API.
