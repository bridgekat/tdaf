/-
Copyright (c) 2026 TDAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TDAF contributors
-/
import Tdaf.Surface.Rockafellar.Part8.Section38
import Tdaf.Surface.Rockafellar.Part8.Section39

/-!
# Rockafellar, Part VIII: Convex Algebra

Sections 38–39: the algebra of convex bifunctions — addition, scalar multiplication, application,
composition, and how each behaves under taking adjoints — and convex processes, the multivalued
maps whose graphs are convex cones containing the origin. This module imports the two section
modules and adds nothing of its own.

| § | module | subject |
|---|---|---|
| 38 | `Part8.Section38` | The Algebra of Bifunctions |
| 39 | `Part8.Section39` | Convex Processes |

Every numbered result of the Part is proved in the backbone over a general real vector space, so
both surface modules are thin specialisations. The book's closing pages sketch an algebra of
oriented processes and a proposed duality for multivalued maps without proof; nothing there is
numbered.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §§38–39.
-/
