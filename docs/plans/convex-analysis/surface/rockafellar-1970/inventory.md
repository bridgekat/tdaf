# Rockafellar, *Convex Analysis* (1970) — result inventory

Extracted from `convex-analysis.md` (18 591 lines) by two independent readers, one per half.
Line numbers are into that file.

**Totals: 241 theorems + 221 corollaries + 9 lemmas = 471 numbered results**, plus 51 clause-level
rows in the multi-clause theorems. Earlier plan drafts said "448" and "≈461"; both
undercounted, for the two reasons below.

| class | meaning | §1–22 | §23–39 | total |
|---|---|---|---|---|
| **G** | survives generalisation beyond `ℝⁿ` | 125 | 94 | **219** |
| **C** | genuinely needs coordinates, finite dimension, Heine–Borel, Lebesgue measure, or polyhedrality | 154 | 96 | **250** |
| **E** | worked example / conjugate pair | 0 | 0 | **0** |
| **X** | stated without proof | 1 | 1 | **2** |

**E = 0 is the finding that matters.** Not one numbered result in the book is a worked example.
Every conjugate pair and every computation is *unnumbered running text*, so the surface's example
corpus must be harvested by line range, not by label. Richest deposits: §4 (1211–1290), §8
(2523–2557, 2773–2819), §12 (4043–4352), §13 (4528–4561, 4722–4753), §14 (4959–4997), §15
(5143–5149, 5465–5553), §16 (6042–6183), §19 (6753–6776), §28 (10989, 11007, 11309–11596), §30
(12671, 12715, 12731–13136), §31 (13381–13465, 13691–13733), §32 (14017–14043), §26 (10085, 10093,
10263), §39 (17199–17268).

## Extraction hazard: 23 mixed-case labels

A case-sensitive scan for `THEOREM`/`COROLLARY` silently drops these:

§1–22: `Theorem 3.4`, `3.6`, `5.4`, `6.1`; `Corollary 2.5.1`, `6.6.2`, `9.1.3`, `9.2.2`, `11.5.1`,
`11.5.2`, `12.1.2`, `13.1.1`, `16.2.2`, `16.4.2`, `17.1.3`, `22.3.1`.
§23–39: `Corollary 23.8.1`, `27.2.2`, `28.3.1`, `29.1.5`, `31.5.1`, `38.7.2`; **`Theorem 38.1`**.

**Theorem 5.4 is the definition site of the infimal-convolution notation `□`**, and Theorem 38.1
carries the orientation-dependent `∞−∞` convention. Both are mixed-case.

## Extraction hazard: 10 eponym-titled labels

A scan for `LABEL n.m.` followed by whitespace also drops every label that carries a parenthetical
name before the period, and the one label printed with no period at all:

`THEOREM 4.3 (Jensen's Inequality)` (1145), `THEOREM 17.1 (Carathéodory's Theorem)` (6337),
`THEOREM 18.6 (Straszewicz's Theorem)` (6625), `COROLLARY 21.3.2 (Helly's Theorem)` (7589),
`Corollary 22.3.1 (Farkas' Lemma)` (7945), `THEOREM 22.7 (Tucker's Complementarity Theorem)` (8277),
`Corollary 28.3.1 (Kuhn-Tucker Theorem)` (11175), `THEOREM 31.1 (Fenchel's Duality Theorem)` (13153),
`THEOREM 31.5 (Moreau)` (13735), and **`COROLLARY 33.1.2`** (14207), which has no terminating period.

These ten are exactly the results a reader is most likely to look for by name, and they are exactly
the ones a naive extractor loses. Together with the 23 mixed-case labels above they account for the
whole gap between the earlier drafts' "448" / "≈461" and the correct 471. Counting all three classes
gives 241 + 221 + 9 = 471, and the per-Part totals below sum to it exactly.

## Per-Part totals

| Part | §§ | results | G | C | X |
|---|---|---|---|---|---|
| I | 1–5 | 49 | 42 | 7 | 0 |
| II | 6–10 | 84 | 21 | 63 | 0 |
| III | 11–16 | 77 | 55 | 21 | 1 |
| IV | 17–22 | 70 | 7 | 63 | 0 |
| V | 23–26 | 49 | 18 | 31 | 0 |
| VI | 27–32 | 63 | 31 | 31 | 1 |
| VII | 33–37 | 58 | 24 | 34 | 0 |
| VIII | 38–39 | 21 | 21 | 0 | 0 |
| | | **471** | **219** | **250** | **2** |

Parts I–IV total 280 and Parts V–VIII total 191; the two halves were inventoried independently and
the per-section lists below are what these totals are computed from.

---

# Part I — Basic Concepts (§1–§5)

## §1 Affine Sets (303–582, pp. 3–9)

Defines: affine set; translate; parallel; `dim M` (`dim ∅ = −1`); `L⊥`; hyperplane and its normal;
`aff S`; affine independence; barycentric coordinates; affine transformation; adjoint `A*`;
**Tucker representation** (553–581, described only procedurally).

| label | line | statement | class |
|---|---|---|---|
| Thm 1.1 | 331 | subspaces = affine sets containing `0` | G |
| Thm 1.2 | 365 | every non-empty affine `M` is parallel to a unique subspace `M − M` | G |
| Thm 1.3 | 393 | hyperplanes are exactly `{x | ⟨x,b⟩ = β}`, `b ≠ 0`, unique up to scaling | C |
| Thm 1.4 | 405 | affine sets are exactly `{x | Bx = b}` | C |
| Cor 1.4.1 | 453 | every affine set is an intersection of *finitely many* hyperplanes | C |
| Thm 1.5 | 503 | affine maps are exactly `Tx = Ax + a` | G |
| Thm 1.6 | 523 | affinely independent `(m+1)`-sets are carried onto each other by a bijective affine `T` | C |
| Cor 1.6.1 | 527 | same for affine sets of equal dimension | C |

Notes: Thm 1.4 covers `∅` and `ℝⁿ` via degenerate `B`. The identity `L⊥ = graph(−A*)` (531–551) is
unnumbered running text but §22 depends on it.

## §2 Convex Sets and Cones (583–770, pp. 10–15)

Defines: convex set; half-spaces; polyhedral convex set; convex combination; `conv S`; polytope,
simplex; `dim C`; cone, convex cone; orthants and componentwise order; positive linear combination;
`ray S`, `cone S`; normal; barrier cone.

Thm 2.1 (607) arbitrary intersections convex · Cor 2.1.1 (611) solution sets of linear systems ·
Thm 2.2 (635) convex ⟺ closed under convex combinations · Thm 2.3 (653) `conv S` = set of convex
combinations · Cor 2.3.1 (669) simplex form · Thm 2.4 (677) `dim C` = max simplex dimension ·
Thm 2.5 (705) intersections of cones · `Corollary 2.5.1` (709) homogeneous systems ·
Thm 2.6 (723) cone ⟺ closed under `+` and positive scaling · Cor 2.6.1 (727) · Cor 2.6.2 (729) ·
Cor 2.6.3 (735) · Thm 2.7 (761) `K − K = aff K`, `(−K) ∩ K` largest subspace. **All 13 are G.**

Trap: `cone S` is *defined* to contain the origin (745) while Cors 2.6.2/2.6.3's cone need not.
Propagates through §§8, 9, 14, 19.

## §3 The Algebra of Convex Sets (771–1038, pp. 16–22)

Defines: `λC`, `−C`; `C₁ + C₂`; `AC`, `A⁻¹D`; direct sum `C ⊕ D`; **partial addition** (971–985,
informal); inverse addition `C₁ # C₂`; umbra, penumbra.

Thm 3.1 (785) · Thm 3.2 (869) `(λ₁+λ₂)C = λ₁C + λ₂C` · Thm 3.3 (887) · `Theorem 3.4` (921) images
and preimages · Cor 3.4.1 (925) · Thm 3.5 (931) direct sum · `Theorem 3.6` (943) partial addition ·
Thm 3.7 (987) inverse sum · Thm 3.8 (1013) `K₁ + K₂ = conv(K₁ ∪ K₂)`, `K₁ # K₂ = K₁ ∩ K₂`.
**All 9 are G.**

Hazard: the "eight natural operations" of §5 rest on the informal partial-addition construction
here; Thm 5.8's proof appeals to it.

## §4 Convex Functions (1039–1438, pp. 23–31)

Defines: `epi f`; `dom f`; `dim f := dim (dom f)`; extended arithmetic (`0·∞ = 0`, `inf ∅ = +∞`,
`∞ − ∞` deliberately undefined); proper/improper; concave, affine; Hessian; `δ(x|C)`; `δ*(x|C)`;
`γ(x|C)`; `d(x,C)`; level sets; positively homogeneous.

| label | line | statement | class |
|---|---|---|---|
| Thm 4.1 | 1127 | convexity ⟺ secant inequality on `(0,1)` | G |
| Thm 4.2 | 1135 | convexity via strict inequalities | G |
| Thm 4.3 (Jensen) | 1145 | convexity ⟺ Jensen for finite convex combinations | G |
| Thm 4.4 | 1161 | `C²` on an interval convex ⟺ `f″ ≥ 0` | C |
| Thm 4.5 | 1243 | `C²` on open convex `C ⊆ ℝⁿ` convex ⟺ Hessian PSD | C |
| Thm 4.6 | 1321 | level sets of a convex function are convex | G |
| Cor 4.6.1 | 1325 | solution sets of convex inequality systems | G |
| Thm 4.7 | 1395 | p.h. convex ⟺ subadditive | G |
| Cor 4.7.1 | 1405 | · | G |
| Cor 4.7.2 | 1413 | `f(−x) ≥ −f(x)` | G |
| Thm 4.8 | 1417 | p.h. proper convex linear on `L` ⟺ `f(−x) = −f(x)` on `L` | G |

## §5 Functional Operations (1439–1816, pp. 32–42)

Defines: outer composition `φ∘f`; **infimal convolution `□`** (1505, at mixed-case `Theorem 5.4`);
left/right scalar multiplication `λf`, `fλ`, `f0`; p.h. function generated by `h`; gauge; Tchebycheff
norm; `conv g`, `conv{fᵢ}`; `Ah`, `gA`; the eight natural binary operations (1751–1778, informal).

Thm 5.1 (1445) · Thm 5.2 (1475) · Thm 5.3 (1493) · `Theorem 5.4` (1505) · Thm 5.5 (1591) pointwise
sup · Thm 5.6 (1661) `conv{fᵢ}` formula · Thm 5.7 (1717) · Thm 5.8 (1779). **All 8 are G.**

Traps: properness is **not** preserved by `□` (1535, explicit); `f0` is defined *by cases*
(1558–1561) and that discontinuity recurs in §§8, 9, 13, 15, 19.

---

# Part II — Topological Properties (§6–§10)

## §6 Relative Interiors (1817–2132, pp. 43–50)

Defines: `cl C`, `int C`, **`ri C`**, relative boundary, relatively open.

Thm 6.1 (1903) G · **Thm 6.2 (1919) `ri C ≠ ∅` for non-empty convex `C`** C · Thm 6.3 (1943) C ·
Cors 6.3.1–6.3.3 (1955, 1957, 1959) C · Thm 6.4 (1965) C · Cor 6.4.1 (1969) C · Thm 6.5 (1973) C ·
Cors 6.5.1–6.5.2 (2001, 2009) C · Thm 6.6 (2019) `ri(AC) = A(ri C)` C · Cor 6.6.1 (2035) G ·
`Corollary 6.6.2` (2051) C · Thm 6.7 (2065) C · Thm 6.8 (2087) slices C · Cor 6.8.1 (2097) C ·
Thm 6.9 (2105) C. **2 G, 16 C.**

This section is the finite-dimensional heart of the book: Thm 6.2 is false in infinite dimensions
and silently underwrites most of §§7, 9, 10, 11, 16, 18, 20.

## §7 Closures of Convex Functions (2133–2486, pp. 51–59)

Defines: lsc/usc, lsc hull, **`cl f` (case-split at 2177)**, closed convex function.

Thm 7.1 (2159) G · Thm 7.2 (2209) improper convex `≡ −∞` on `ri(dom f)` G · Cors 7.2.1–7.2.3
(2219, 2229, 2235) C/C/G · **Lemma 7.3** (2247) C · Cors 7.3.1–7.3.4 (2299, 2303, 2313, 2319) C ·
Thm 7.4 (2343) C · Cors 7.4.1–7.4.2 (2359, 2361) C · Thm 7.5 (2371) C · Cor 7.5.1 (2417) C ·
Thm 7.6 (2433) C · Cor 7.6.1 (2465) C. **3 G, 14 C.**

Hazard: `epi (cl f) = cl (epi f)` is asserted "by definition" (2185) but holds only for proper `f`.

## §8 Recession Cones and Unboundedness (2487–2906, pp. 60–71)

Defines: **direction** (a quotient of half-lines, never formally typed); `0⁺C`; the cone `K` in
`ℝⁿ⁺¹`; lineality space, lineality, rank; **`f0⁺`**; recession cone of a function; constancy space;
partial affine function.

Thm 8.1 (2503) G · Thm 8.2 (2585) C · Thm 8.3 (2609) G · Cors 8.3.1–8.3.4 (2613, 2615, 2621, 2629)
C/G/G/G · Thm 8.4 (2637) bounded ⟺ `0⁺C = {0}` C · Cor 8.4.1 (2641) C · Thm 8.5 (2705) G ·
Cors 8.5.1–8.5.2 (2725, 2751) G · Thm 8.6 (2823) G · Cors 8.6.1–8.6.2 (2839, 2845) G ·
Thm 8.7 (2861) G · Cor 8.7.1 (2865) C · Thm 8.8 (2869) G. **13 G, 5 C.**

Note `f0⁺` is deliberately overloaded with §5's `fλ`, and the "recession cone of `f`" is neither
`0⁺(dom f)` nor `0⁺(epi f)` — the book warns of this itself.

## §9 Some Closedness Criteria (2907–3354, pp. 72–81)

No new concepts. Thm 9.1 (2941) C · Cors 9.1.1–9.1.3 (3021, 3053, 3063) C · Thm 9.2 (3073) C ·
Cors 9.2.1–9.2.2 (3101, 3133) C · Thm 9.3 (3177) G · Thm 9.4 (3209) G · Thm 9.5 (3229) G ·
Thm 9.6 (3233) C · Cor 9.6.1 (3253) C · Thm 9.7 (3259) C · Cor 9.7.1 (3275) C · Thm 9.8 (3295) C ·
Cors 9.8.1–9.8.3 (3327, 3343, 3351) C. **3 G, 15 C.**

**The `λ ≥ 0⁺` convention** (3301, restated 3236): `λᵢCᵢ` means `0⁺Cᵢ` when `λᵢ = 0`. Used by
Thms 9.6, 9.7, 9.8 and 19.5.1, 19.6, 19.7.

## §10 Continuity of Convex Functions (3355–3724, pp. 82–94)

Defines: continuity relative to a set; **locally simplicial**; Lipschitzian relative to a set;
equi-Lipschitzian; pointwise/uniformly bounded families.

Thm 10.1 (3363) · Cor 10.1.1 (3373) · Thm 10.2 (3419) · Thm 10.3 (3431) · Thm 10.4 (3455) ·
Thm 10.5 (3497) · Cors 10.5.1–10.5.2 (3525, 3533) · Thm 10.6 (3559) · Thm 10.7 (3619) ·
Thm 10.8 (3651) · Cor 10.8.1 (3703) · Thm 10.9 (3717). **0 G, 13 C — the whole section.**

Hazard: "locally simplicial" is defined but the barycentric-coordinate fact Thm 10.2 needs is
called "intuitively obvious" (3417) and never proved; Thm 20.5 supplies it, also by assertion.

---

# Part III — Duality Correspondences (§11–§16)

## §11 Separation Theorems (3725–3906, pp. 95–101)

Defines: separate / properly / strictly / strongly; supporting half-space and hyperplane.

Thm 11.1 (3733) G · Thm 11.2 (3775) C · Thm 11.3 (3783) proper separation ⟺ `ri C₁ ∩ ri C₂ = ∅` C ·
Thm 11.4 (3809) G · Cors 11.4.1–11.4.2 (3831, 3835) C · Thm 11.5 (3843) G ·
`Corollary 11.5.1` (3847) G · `Corollary 11.5.2` (3851) C · Thm 11.6 (3863) C ·
Cors 11.6.1–11.6.2 (3867, 3869) C · Thm 11.7 (3873) G · Cors 11.7.1–11.7.3 (3895, 3899, 3903)
G/G/C. **7 G, 9 C.**

The book defines *strict* separation and then never numbers a result about it.

## §12 Conjugates of Convex Functions (3907–4370, pp. 102–111)

Defines: **`f*`**; Fenchel's inequality; symmetry under an orthogonal group; partial quadratic
convex function; **monotone conjugate `g⁺`**.

Thm 12.1 (3941) G · Cor 12.1.1 (3963) G · `Corollary 12.1.2` (3967) G · Thm 12.2 (3997) G ·
Cor 12.2.1 (3999) G · Cor 12.2.2 (4001) C · Thm 12.3 (4135) G · Cor 12.3.1 (4281) G ·
**Thm 12.4 (4353) X — stated with NO PROOF**, and its concave `g⁻` companion likewise.
**7 G, 1 C, 1 X.**

## §13 Support Functions (4371–4754, pp. 112–120)

Defines: `δ*(x*|C)` as an extremum tool; barrier cone; **co-finite**.

Thm 13.1 (4407) C (the `cl C` clause alone is G) · `Corollary 13.1.1` (4429) G · Thm 13.2 (4471) G ·
Cor 13.2.1 (4497) G · Cor 13.2.2 (4505) C · Thm 13.3 (4567) G · Cors 13.3.1–13.3.3 (4585, 4589,
4593) G · Cor 13.3.4 (4619) C · Thm 13.4 (4631) C · Cors 13.4.1–13.4.2 (4655, 4659) C ·
Thm 13.5 (4683) G · Cor 13.5.1 (4689) G. **9 G, 6 C.**

## §14 Polars of Convex Sets (4755–5068, pp. 121–127)

Defines: `K°` (cone polar), `C°` (set polar).

Thm 14.1 (4769) G · Thm 14.2 (4797) G · Cors 14.2.1–14.2.2 (4843, 4847) G/C · Thm 14.3 (4851) G ·
Thm 14.4 (4869) G · Thm 14.5 (4949) G · Cor 14.5.1 (4951) G · Thm 14.6 (5001) G ·
Cor 14.6.1 (5005) C · Thm 14.7 (5023) G. **9 G, 2 C.**

Hazard: Thms 14.1 and 14.5 carry **no `Proof.` paragraph** — the argument is in the preceding prose.
`C°° = cl(conv(C ∪ {0}))` (4944) is an important unnumbered identity.

## §15 Polars of Convex Functions (5069–5656, pp. 128–139)

Defines: gauge; `k°`; norm; Minkowski metric; **gauge-like**; p.h. of degree `p`; `f°`; **obverse**.

Thm 15.1 (5101) · Cors 15.1.1–15.1.2 (5135, 5137) · Thm 15.2 (5225) · Thm 15.3 (5315) ·
Cors 15.3.1–15.3.2 (5429, 5445) · Thm 15.4 (5563) · Cor 15.4.1 (5589) · Thm 15.5 (5635) ·
Cor 15.5.1 (5639). **All 11 are G.**

## §16 Dual Operations (5657–6286, pp. 140–152)

No new concepts — the dual-operations dictionary.

Thm 16.1 (5669) G · Cors 16.1.1–16.1.2 (5673, 5685) G · **Lemma 16.2** (5689) C ·
Cor 16.2.1 (5709) C · `Corollary 16.2.2` (5725) C · Thm 16.3 (5787) G · Cors 16.3.1–16.3.2 (5831,
5853) G · Thm 16.4 (5943) G · Cor 16.4.1 (6001) G · `Corollary 16.4.2` (6025) G · Thm 16.5 (6187) G ·
Cors 16.5.1–16.5.2 (6225, 6239) G. **12 G, 3 C.**

**The uniform pattern worth encoding once**: each theorem is *identity* (general) + *closure-removal
and attainment under a relative-interior qualification* (finite-dimensional). Splitting each into
two lemmas makes the surface far more reusable. Thm 16.5's last part needs the `cl(dom fᵢ)` to be
*equal*, a stronger hypothesis than 16.4's `ri` condition — easy to conflate.

---

# Part IV — Representation and Inequalities (§17–§22)

## §17 Carathéodory's Theorem (6287–6534, pp. 153–161)

Defines: **`conv S` for a mixed set of points and directions**; `ray S₁`, `cone S₁`; affine
independence for points and directions; generalized simplex; skew orthant.

Thm 17.1 (6337) · Cors 17.1.1–17.1.2 (6347, 6357) · `Corollary 17.1.3` (6361) ·
**Cor 17.1.4 (6373) — FALSE as stated** · Cor 17.1.5 (6383) · **Cor 17.1.6 (6393) — FALSE as
stated** · Thm 17.2 (6405) · Cor 17.2.1 (6439) · Thm 17.3 (6497). **0 G, 10 C.**

The mixed point/direction idiom starts here and runs through §§18–19.

## §18 Extreme Points and Faces (6535–6650, pp. 162–169)

Defines: face; extreme point/ray/direction; exposed face/point/ray/direction; face lattice;
tangent hyperplane.

Thm 18.1 (6555) G · Cors 18.1.1–18.1.2 (6559, 6563) G · Cor 18.1.3 (6567) C · Thm 18.2 (6573) C ·
Thm 18.3 (6581) G · Cor 18.3.1 (6591) G · Thm 18.4 (6599) C · Thm 18.5 (6605) C ·
Cors 18.5.1–18.5.3 (6609, 6611, 6615) C · Thm 18.6 Straszewicz (6625) C · Thm 18.7 (6629) C ·
Cor 18.7.1 (6633, **no proof**) C · Thm 18.8 (6641) C. **5 G, 11 C.**

Thm 18.5 is stated only for sets containing no lines; the "obvious extension to arbitrary
lineality" (6603) is never stated or proved, and a surface will want it.

## §19 Polyhedral Convex Sets and Functions (6651–7002, pp. 170–178)

Defines: polyhedral convex set/cone; finitely generated; polytope; polyhedral convex function;
finitely generated convex function.

Thm 19.1 (6681) Minkowski–Weyl · Cor 19.1.1 (6705) · Cor 19.1.2 (6751) · Thm 19.2 (6779) ·
Cors 19.2.1–19.2.2 (6807, 6815) · Thm 19.3 (6819) · Cors 19.3.1–19.3.4 (6847, 6851, 6855, 6859) ·
Thm 19.4 (6917) · Thm 19.5 (6945) · Cor 19.5.1 (6949) · **Thm 19.6 (6973, no proof)** ·
Thm 19.7 (6983) · Cor 19.7.1 (6991). **0 G, 17 C.**

## §20 Applications of Polyhedral Convexity (7003–7250, pp. 179–184)

Thm 20.1 (7029) · Cor 20.1.1 (7151) · Thm 20.2 (7163) · Cor 20.2.1 (7185) · Thm 20.3 (7201) ·
Cor 20.3.1 (7217) · Thm 20.4 (7223) · **Thm 20.5 (7241)**. **0 G, 8 C.**

Thm 20.1 is the subtlest constraint qualification in Parts I–IV: the *polyhedral* members need only
`dom`, the others need `ri dom`. Thm 20.5 (every polyhedral set is locally simplicial) is the
missing link making Thm 10.2 applicable, and its proof is a two-line sketch.

## §21 Helly's Theorem and Systems of Inequalities (7251–7836, pp. 185–197)

Defines: system of convex inequalities (weak and strict parts); consistent.

Thm 21.1 (7283) G · Thm 21.2 (7365) G · Thm 21.3 (7459) C · Cors 21.3.1–21.3.2 (7555, 7589) C ·
Thm 21.4 (7639) C · Thm 21.5 (7787) C · Thm 21.6 (7805) C · Cors 21.6.1–21.6.2 (7811, 7833) C.
**2 G, 8 C.**

**The book cites "Corollary 21.3.3" in its Comments (17309); no such result exists** — the text has
21.3.2. Thm 21.1's hypothesis is `dom fᵢ ⊇ ri C` (not `⊇ C`) and is deliberate.

## §22 Linear Inequalities (7837–8294, pp. 198–212)

Defines: consequence of a system; matrix form; the interval form `ζⱼ ∈ Iⱼ`; **real interval** (loose,
8033); support of a vector; **elementary vector**; directed graph, circulation/tension spaces.

Thm 22.1 (7841) · Thm 22.2 (7865) · Thm 22.3 (7913) · `Corollary 22.3.1` Farkas (7945) ·
**Lemma 22.4** (8155) · Cor 22.4.1 (8159) · **Lemma 22.5** (8163) · Thm 22.6 (8191) ·
Thm 22.7 Tucker (8277). **0 G, 9 C.**

`Σ ζ*ⱼIⱼ > 0` means the *interval sum is contained in* `(0,∞)` (convention stated once at 8067, 120
lines before Thm 22.6). The elementary-vector definition at 8119 is OCR-truncated — verify against a
clean copy. The graph-theoretic material (8121–8153) is motivation only and used in no proof.

**Deferred by scope** (substantial combinatorial matroid theory): Lemmas 22.4, 22.5, Cor 22.4.1,
Thms 22.6, 22.7.

---

# Part V — Differential Theory (§23–§26)

## §23 Directional Derivatives and Subgradients (8295–8954, pp. 213–226)

Defines: `f′(x;y)`; `f′₊`, `f′₋`; subgradient and the subgradient inequality; `∂f(x)`;
subdifferentiable; normal cone as `∂δ(·|C)`; **ε-subgradient**, `∂_ε f(x)`.

Thm 23.1 (8325) G · Thm 23.2 (8425) G · Thm 23.3 (8445) C · Thm 23.4 (8463) C ·
**Thm 23.5 (8489) — 7 clauses** (a) 8491 (b) 8493 (c) 8495 (d) 8497 (a*) 8501 (b*) 8503 (a**) 8505,
all G · Cors 23.5.1–23.5.4 (8521 **no proof**, 8523, 8533, 8537) G · Thm 23.6 (8583) G ·
Thm 23.7 (8679) G · Cor 23.7.1 (8705) G · Thm 23.8 (8725) G · `Corollary 23.8.1` (8767) G ·
Thm 23.9 (8881) G · Thm 23.10 (8927) C. **13 G, 3 C.**

Thm 23.8 has **two** proofs; the alternative (8773) uses only separation and avoids §16's conjugacy
machinery — the better route for a port. Line 8477 leaves `rec(∂f(x))` = normal cone to `dom f` as
an unproved exercise, verified only later inside Thm 25.6's proof. The example at 8479 shows
`dom ∂f` need not be convex — keep as a test case.

## §24 Differential Continuity and Monotonicity (8955–9632, pp. 227–240)

Defines: `dom ∂f`, `range ∂f`, `graph ∂f`; **complete non-decreasing curve**; **cyclically
monotone**; monotone; maximal.

Thm 24.1 (8991) C · Thm 24.2 (9101) C · Cor 24.2.1 (9171) C · Thm 24.3 (9199) C · Thm 24.4 (9219) G ·
Thm 24.5 (9235) C · Cor 24.5.1 (9309) C · Thm 24.6 (9355) C · Thm 24.7 (9437) C · Thm 24.8 (9527) G ·
Thm 24.9 (9559) G. **3 G, 8 C.**

Line 9631 warns explicitly that maximal *monotonicity* of `∂f` (Cor 31.5.2) does **not** follow from
Thm 24.9 plus "cyclically monotone ⇒ monotone". Keep the two separate.

**Deferred by scope**: Thm 24.2's integral formula `f(x) = ∫ₐˣ φ` only, and nothing in the book uses it. **Cor 24.2.1 is not deferred** — `Subgradient/Integral.lean` proves it in full, and that module's docstring says the Lebesgue-theory reason does not apply. Thm 24.2's *existence* clause is reachable too, via `Subgradient/Primitive.lean`, with no integral at all.

## §25 Differentiability of Convex Functions (9633–10008, pp. 241–250)

Defines: `∇f(x)`; the differentiability set `D`.

Thm 25.1 (9685) · Cors 25.1.1–25.1.3 (9747, 9753, 9757) · Thm 25.2 (9767) · Thm 25.3 (9779) ·
Thm 25.4 (9783) · Thm 25.5 (9825) · Cor 25.5.1 (9829, **no proof**) · Thm 25.6 (9835) ·
Thm 25.7 (9945). **0 G, 11 C — the most irreducibly finite-dimensional section in the book.**

The one general fragment: the *forward* half of Thm 25.1 (differentiable ⇒ `∇f(x) ∈ ∂f(x)`).

## §26 The Legendre Transformation (10009–10384, pp. 251–262)

Defines: **essentially smooth** (three-part (a)(b)(c), 10027); condition (c′); strictly convex;
**essentially strictly convex**; **Legendre conjugate** `(C,f) ↦ (D,g)`; **convex function of
Legendre type**.

Thm 26.1 (10037) C · **Lemma 26.2** (10043) G · Thm 26.3 (10099) C · Cors 26.3.1–26.3.3 (10117,
10123, 10151) C · Thm 26.4 (10231) G · Cor 26.4.1 (10235) C · Thm 26.5 (10277) C · Thm 26.6 (10351) C ·
**Lemma 26.7** (10363) C. **2 G, 9 C.**

Line 10275 warns that "the Legendre conjugate of the Legendre conjugate" is *undefined* in general;
involutivity holds only within the Legendre-type class. **Do not state a naive involution lemma.**
Counterexamples at 10085, 10093 and 10263 (`ξ₁²/4ξ₂` on the open upper half-plane, whose `D` is a
parabola — not convex) pin down why the hypotheses cannot be weakened.

---

# Part VI — Constrained Extremum Problems (§27–§32)

## §27 The Minimum of a Convex Function (10385–10748, pp. 263–272)

Defines: `lev_α f`; `inf f`; **minimum set**.

**Thm 27.1 (10421) — 9 clauses**: (a) 10423 G · (b) 10425 C · (c) 10427 G · (d) 10429 C ·
**(e) 10431 C** · (f) 10433 C · (g) 10435 G · (h) 10437 G · (i) 10443 G.
Thm 27.2 (10453) C · Cor 27.2.1 (10457, **no proof**) C · `Corollary 27.2.2` (10465) C ·
Thm 27.3 (10495) C · Cors 27.3.1–27.3.3 (10505, 10523, 10527) C · Thm 27.4 (10651) G.
**1 G, 8 C** at result level; clause level as above.

Thm 27.1's proof (10449) is a one-line pointer list to §§8, 13, 14, 23, 25. Clause (e) is the one
the backbone excluded as needing a reflexive pairing — `ℝⁿ` is reflexive, so the surface needs it.

## §28 Ordinary Convex Programs and Lagrange Multipliers (10749–11596, pp. 273–290)

Defines: **ordinary convex program as the `(m+3)`-tuple `(C, f₀,…,f_m, r)`** (10761); extension
conventions; feasible solution, `C₀`; objective; optimal value/solution; **Kuhn–Tucker vector**;
perturbation function `p(u)`; perturbed program; **Lagrangian `L(u*,x)`** and `E_r`; Lagrange
multiplier; **saddle-point**.

Thm 28.1 (10809) · Cor 28.1.1 (10849) · Thm 28.2 (10915) · Cors 28.2.1–28.2.2 (10961, 10981
**no proof**) · **Thm 28.3 (11065) — 3 clauses** (a) 11067 (b) 11069 (c) 11071 ·
`Corollary 28.3.1` Kuhn–Tucker (11175, **no proof**) · Thm 28.4 (11229) ·
Cor 28.4.1 (11281, **no proof**). **0 G, 9 C.**

Rockafellar is emphatic (10761, 10797) that `(P)` is **the tuple, not the objective function** —
two programs with the same objective can have different Lagrangians and different Kuhn–Tucker
vectors. The surface must carry the tuple as primitive and the program ↔ Lagrangian correspondence
(11047–11057) as a theorem. Two unnumbered counterexamples (10989, 11007) justify the
qualification and must be kept.

## §29 Bifunctions and Generalized Convex Programs (11597–12152, pp. 291–306)

Defines: **bifunction**; graph function; convex/closed/proper bifunction; `dom F`; indicator
bifunction of `A`; generalized convex program; `F0`; **perturbation function `inf F`**;
**Kuhn–Tucker vector**; **Lagrangian**; **strongly/strictly consistent**; polyhedral bifunction;
**`cl F`**.

Thm 29.1 (11863) G · Cor 29.1.1 (11885) G · Cor 29.1.2 (11899) C · Cor 29.1.3 (11913) C ·
Cor 29.1.4 (11943) G · `Corollary 29.1.5` (11951) C · Cor 29.1.6 (11955) C · Thm 29.2 (12029) C ·
Thm 29.3 (12035) G · Cor 29.3.1 (12097) G · Thm 29.4 (12109) C ·
**Cor 29.4.1 (12151) — X: no proof at all, and drops Thm 29.4's properness hypothesis.**
**5 G, 6 C, 1 X.**

Two defects, both confirmed independently from the Lean side: Cor 29.4.1's clause that the
perturbation functions agree near `0` is **false** without properness; and **Thm 29.4's printed
proof is wrong at 12139**, claiming `((cl F)u)(y) = −∞` for all `y` in the improper case when
`cl f = +∞` outside `cl(dom f)`. The theorem survives; the argument does not.

## §30 Adjoint Bifunctions and Dual Programs (12153–13136, pp. 307–326)

Defines: concave conjugate; concave bifunction and program; **adjoint `F*`**; concave indicator
bifunction of `A*`; **dual program `(P*)`**; **normal** program; normality for a dual pair.

Thm 30.1 (12303) G · Thm 30.2 (12487) G · Cors 30.2.1–30.2.3 (12557, 12569, 12597) G ·
**Thm 30.3 (12631) — 3 clauses** (a)(b)(c) 12633–12637 G ·
**Thm 30.4 (12643) — 10 clauses**: (a) 12645 G · (b) 12647 G · (c) 12649 G · (d) 12651 G ·
(e) 12653 C · (f) 12655 C · (g) 12657 C · (h) 12659 C · (i) 12661 C · (j) 12663 C ·
Thm 30.5 (12693) G · **Cor 30.5.1 (12703) — 3 clauses** (a)(b)(c) 12705–12709 G ·
Cor 30.5.2 (12729) G. **9 G, 1 C.**

Thm 30.4's printed proof covers only (a), (c), (e) and dualises. Two load-bearing unnumbered
counterexamples: 12671 (an *abnormal* closed proper program with a genuine duality gap:
`(Fu)(x) = exp(−√(ux))` on the first quadrant, `inf F0 = 1` but `sup F*0 = 0`) and 12715 (a normal
program with an optimal solution whose dual has none). Line 12667 names Thm 30.4(e)/(f) applied to
linear programs the **Gale–Kuhn–Tucker Duality Theorem** without a separate statement.

## §31 Fenchel's Duality Theorem (13137–13916, pp. 327–341)

Defines: **proximation `prox(z|f)`** (13832).

**Thm 31.1 (13153) — 2 clauses** (a) 13161 (b) 13163, G · Thm 31.2 (13257) G ·
**Cor 31.2.1 (13365) — 2 clauses** (a) 13373 (b) 13375, G · Thm 31.3 (13467) G · Cor 31.3.1 (13517) G ·
**Thm 31.4 (13575) — 2 clauses** (a) 13589 (b) 13591, G · Cor 31.4.1 (13623) C · Cor 31.4.2 (13643) G ·
Cor 31.4.3 (13673) C · **Thm 31.5 Moreau (13735)** G · `Corollary 31.5.1` (13889, **no proof**) G ·
Cor 31.5.2 (13897) `∂f` maximal monotone G. **10 G, 2 C.**

Cor 31.2.1's polyhedral strengthening (13379) is asserted with the proof **explicitly omitted**.
The contraction property of `prox` (13851–13885) is derived in unnumbered running text and is what
makes Cor 31.5.2 work — it should be a named lemma.

## §32 The Maximum of a Convex Function (13917–14068, pp. 342–348)

No new concepts. Thm 32.1 (13927) G · Cor 32.1.1 (13949) G · Thm 32.2 (13957) G ·
Cor 32.2.1 (13967) G · Thm 32.3 (13973) C · Cors 32.3.1–32.3.4 (13995, 13999, 14005, 14009) C ·
Thm 32.4 (14047) G · Cor 32.4.1 (14057) G. **6 G, 5 C.**

The two examples at 14017–14043 show `C ⊆ ri(dom f)` in Cor 32.3.2 cannot be weakened to
`C ⊆ dom f` even for closed `f`. Keep both. Cor 32.3.4 is the theoretical basis of the simplex
method (14013, a remark).

---

# Part VII — Saddle-functions and Minimax Theory (§33–§37)

## §33 Saddle-Functions (14069–14492, pp. 349–358)

Defines: **concave-convex / convex-concave / saddle-function**; lower and upper **simple
extension**; **`cl₁K`, `cl₂K`**; `⟨f, x*⟩ = f*(x*)`; `⟨Fu, x*⟩`; convex-closed / concave-closed;
image-closed bifunction; **fully closed**; **lower closed / upper closed**.

Thm 33.1 (14145) G · Cor 33.1.1 (14187) G · Cor 33.1.2 (14207, **no proof**) G · Cor 33.1.3 (14217) C ·
Thm 33.2 (14247) G · Cor 33.2.1 (14285) C · Cor 33.2.2 (14295) C · Thm 33.3 (14413) G ·
Cors 33.3.1–33.3.3 (14435, 14463, 14473) G. **8 G, 3 C.**

**Orientation trap**: `cl₁` closes the *concave* argument, `cl₂` the *convex* one (mnemonic at
14409). Getting it backwards silently swaps every result in §§34–37. The `⟨·,·⟩` notation is
overloaded three ways here and a fourth in §38 — use distinct names, not overloading.

## §34 Closures and Equivalence Classes (14493–14950, pp. 359–369)

Defines: lower/upper closure `cl₂cl₁K`, `cl₁cl₂K`; `dom₁K`, `dom₂K`, `dom K`; proper;
**equivalent**; **closed** saddle-function; `Ω(F)`; **kernel**; **simple**.

Thm 34.1 (14509) G · Thm 34.2 (14657) C · Cor 34.2.1 (14761, **no proof**) C · Cor 34.2.2 (14763) G ·
Cor 34.2.3 (14819, **no proof**) G · Cor 34.2.4 (14823) G · **Thm 34.3 (14835) — 6 clauses**
(a)–(f) 14837–14847, all C · Thm 34.4 (14891) C · Thm 34.5 (14921) C · Cor 34.5.1 (14947) C.
**4 G, 6 C.**

**Design consequence**: the natural primitive is *not* a saddle-function but the pair (lower closed
`K̲`, upper closed `K̄`) — equivalently a closed convex bifunction. Thm 34.2 licenses this and
should be stated first.

## §35 Continuity and Differentiability of Saddle-Functions (14951–15302, pp. 370–378)

Defines: `K′(u,v;u′,v′)`; **`∂₁K`** (concave side), **`∂₂K`** (convex side), `∂K = ∂₁K × ∂₂K`.

Thm 35.1 (14955) C · Thm 35.2 (14985) C · Thm 35.3 (15019) C · Thm 35.4 (15025) C · Thm 35.5 (15035) C ·
**Thm 35.6 (15059) G — the splitting identity** · Thm 35.7 (15195) C · Cor 35.7.1 (15215) C ·
Thm 35.8 (15225) C · Cor 35.8.1 (15259) C · Thm 35.9 (15263) C · Thm 35.10 (15291) C.
**1 G, 11 C.**

Thm 35.6's splitting identity is the pivot on which `∂K = ∂₁K × ∂₂K` rests — get it in first.
The sign asymmetry (`∂₁K` concave, `∂₂K` convex) means `∂K` is **not** the subdifferential of `K` as
a function on `ℝᵐ⁺ⁿ`; §37 inserts a sign flip to recover monotonicity. This is the single most
common source of error in porting Part VII.

## §36 Minimax Problems (15303–15688, pp. 379–387)

Defines: **minimax / saddle-value**; **saddle-point**; the orientation convention (15449);
**inverse bifunction `F_*`**.

**Lemma 36.1** (15321) G · **Lemma 36.2** (15355) G · Thm 36.3 (15453) C · Cor 36.3.1 (15483) C ·
Thm 36.4 (15491) G · Thm 36.5 (15585) G · Thm 36.6 (15681, **no proof printed**) C.
**4 G, 3 C.**

**Thm 36.5 is the structural pay-off of Part VII**: Lagrangians of convex programs = upper closed
concave-convex functions, so "regularized minimax problem" and "dual pair of convex programs" are
the same object. With Cor 34.2.2 (unique upper closed member per class) it fixes the canonical
representative. **The orientation convention declared at 15449 is in force for the rest of the
book**; Thms 36.3–36.6 and all of §37 are false verbatim under the opposite one.

## §37 Conjugate Saddle-Functions and Minimax Theorems (15689–16178, pp. 388–400)

Defines: `⟨u*, F_*x⟩`; **lower conjugate `K̲*`** (`sup_v inf_u`); **upper conjugate `K̄*`**
(`inf_u sup_v`); conjugate effective domain `C* × D*`.

Thm 37.1 (15723) G · Cor 37.1.1 (15777) G · Cor 37.1.2 (15807) C · Cor 37.1.3 (15851, **no proof**) C ·
Thm 37.2 (15861) C · Cor 37.2.1 (15917) C · **Thm 37.3 (15929) — 2 clauses** (a) 15931 (b) 15933, C ·
Cors 37.3.1–37.3.2 (15937, 15943) C · Thm 37.4 (15963) C · Cor 37.4.1 (15993) G ·
**Thm 37.5 (16011) — 4 clauses** (a) 16019 (b) 16021 (c) 16023 (d) 16025, G ·
Cor 37.5.1 (16093) G · **Cor 37.5.2 (16101) G** · Cor 37.5.3 (16131) G · Thm 37.6 (16151) C ·
Cors 37.6.1–37.6.2 (16155, 16159) C. **7 G, 11 C.**

Conjugacy depends only on the **equivalence class** (Cor 37.1.1), so the surface should conjugate
classes or bifunctions, never raw saddle-functions. Cors 37.3.2 and 37.6.2 are the finite-dimensional
minimax theorems; their infinite-dimensional analogues (Kneser–Fan, Sion) need *compactness* as a
hypothesis, not boundedness — flag the substitution.

---

# Part VIII — Convex Algebra (§38–§39)

## §38 The Algebra of Bifunctions (16179–16730, pp. 401–412)

Defines: **`F₁□F₂`**; **`Fλ`**; **`Ff`**; **`GF`**; **`⟨f,g⟩`** (a *partial* operation, 16527);
**co-finite bifunction**.

`Theorem 38.1` (16211) · Thm 38.2 (16249) · Cor 38.2.1 (16293) · Thm 38.3 (16333) · Thm 38.4 (16373) ·
Cor 38.4.1 (16409) · Thm 38.5 (16433) · Cor 38.5.1 (16495) · **Lemma 38.6** (16545) · Thm 38.7 (16585) ·
Cor 38.7.1 (16665) · `Corollary 38.7.2` (16673). **All 12 are G.**

Thm 38.1 carries the **orientation-dependent `∞−∞` convention**: `−∞` for convex bifunctions, `+∞`
for concave. `□` and bifunction multiplication are commutative/associative only "to the extent that
they are defined" (16239, 16507) — improper bifunctions break both. The co-finite discussion
(16693–16729) is unnumbered but states three important facts without proof labels; a closed convex
`F` is co-finite iff `dom F = ℝᵐ` **and** `dom F* = ℝⁿ` (16701), the class where every `ri`
hypothesis evaporates and hence the natural first target.

## §39 Convex Processes (16731–17268, pp. 413–424)

Defines: **convex process**; graph as a convex cone containing `0`; `dom A`, `range A`, `A⁻¹`;
polyhedral convex process; `cl A`; `λA`, `A+B`, `AC`, `Af`, `BA`; **supremum / infimum orientation**
(a formal *pair*, 16945–16965); indicator bifunction of an oriented process; **adjoint `A*`**;
`⟨C,D⟩`, `⟨C,h⟩`, `⟨h,D⟩`.

Thm 39.1 (16817) · Thm 39.2 (17017) · Thm 39.3 (17049) · Thm 39.4 (17071) · Thm 39.5 (17155) ·
Thm 39.6 (17165) · Thm 39.7 (17169) · Cor 39.7.1 (17181) · Thm 39.8 (17191). **All 9 are G.**

**Orientation must be data.** Thms 39.5 and 39.8 require the two processes to have the **same**
orientation and Thm 39.2 **flips** it, so both orientations must be simultaneously expressible; a
global convention cannot state 39.5. Thm 39.1's hypothesis "`A0` bounded" is used only to force
`A0 = {0}` — stating it that way is strictly more general and drops the finite-dimensional need.
`A⁻¹A ≠ id` (16929): convex processes form a non-commutative semigroup, and a complete lattice
under inclusion (16943). The closing material (17199–17268) is a research-programme sketch stated
without proof — do not mine it for theorems.
