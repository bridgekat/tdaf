# Part III — Duality Correspondences (§11–§16)

`Tdaf/Surface/Rockafellar/Part3.lean` → `Part3/Section11.lean` … `Section16.lean`.

**77 numbered results: 55 G, 21 C, 1 X.** This is where the dual-pair decision
([D3](../../00-overview.md#d3-duality-is-developed-for-a-dual-pair-not-for-ℝⁿ-and-not-for-the-dual-space))
is tested, and therefore the earliest high-value alignment check after §4–§5.

| § | module | results | G/C | backbone it specialises |
|---|---|---|---|---|
| 11 | `Section11.lean` | 16 | 7/9 | `Separation.lean` |
| 12 | `Section12.lean` | 9 | 7 G, 1 C, 1 X | `Duality/Conjugate.lean` |
| 13 | `Section13.lean` | 15 | 9/6 | `Duality/{Support,Level,Barrier}.lean` |
| 14 | `Section14.lean` | 11 | 9/2 | `Duality/Polar.lean` |
| 15 | `Section15.lean` | 11 | 11/0 | `Duality/{Gauge,GaugeLike}.lean` |
| 16 | `Section16.lean` | 15 | 12/3 | `Duality/{Ops,Exact}.lean` |

## Gated on remediation

* **§14** wants the bipolar theorem stated for `PointedCone` (remediation §4.3). Today
  `polarCone_polarCone` takes three unbundled hypotheses and the pattern recurs 26 times, so every
  §14 statement would re-discharge them.
* **§15** wants `IsNorm k → ∃ p : Seminorm ℝ E, ∀ x, k x = p x` (remediation §4.7), declined in the
  backbone on layer-C grounds that do not apply on `ℝⁿ`.
* **§16** wants the bundled adjoint (§4.1) and `m`-ary `infConv`/`IsExactSum` (§4.4): Thm 16.4 is
  stated for `f₁ □ ⋯ □ f_m`, and every `A*` in this section is currently an explicit argument plus
  an `IsAdjointPair` hypothesis.

## Receives from the backbone

Per remediation §6: `polarCone_nonnegOrthant` and `section Orthant` move here (§14), and the
power / Young's-inequality cluster — `powHalfLine`, `monotoneConj_powHalfLine`, `PosHomogeneousDeg`,
`degGauge`, `posHomogeneousDeg_iff_exists_isGauge`, `polarGauge_degGauge`,
`pairing_le_rpow_mul_rpow` — moves here from `Duality/GaugeLike.lean` (§15, Cors 15.3.1/15.3.2).

## Hazards

* **Theorem 12.4 is stated with NO PROOF** (4353): the monotone-conjugacy involution `g ↦ g⁺`. Its
  concave companion `g⁻` is likewise asserted. The surface must supply the entire argument, and the
  statement is coordinate-dependent (non-negative orthant, componentwise order).
* **Theorems 14.1 and 14.5 carry no `Proof.` paragraph** — each is derived in the running text
  immediately preceding it (4759–4767, 4907–4947). Recover the argument from prose.
* `C°° = cl(conv(C ∪ {0}))` for general `C` (4944) is an important **unnumbered** identity.
* **§16's uniform shape is worth encoding once**: every theorem is *identity* (general) +
  *closure-removal and attainment under a relative-interior qualification* (finite-dimensional).
  Splitting each into two lemmas makes the surface far more reusable.
* Thm 16.5's last clause requires the `cl(dom fᵢ)` to be **equal** — strictly stronger than 16.4's
  `ri` condition. Easy to conflate.
* Cor 13.3.2's proof (4591) delegates a substantial step: "As an exercise in separation theory…".
* This Part holds the book's densest deposits of **unnumbered** conjugate tables: 4043–4352 (§12,
  including the pseudo-inverse `Q′` whose construction is left to the reader), 4528–4561 and
  4722–4753 (§13), 4959–4997 (§14), 5143–5149 and 5465–5553 (§15), 6042–6183 (§16, entropy and
  log-sum-exp).
* Mixed-case labels: `Corollary 11.5.1`, `11.5.2`, `12.1.2`, `13.1.1`, `16.2.2`, `16.4.2`.
