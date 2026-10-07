# Verification record — JSP-000690

Toolchain: `leanprover/lean4:v4.20.0` + Mathlib `v4.20.0` (rev `c211948581bde9846a99e32d97a03f0d5307c31e`)
Verified: 2026-10-08

## Clean build

The project's own build directory was removed and the project rebuilt from scratch
(Mathlib's own oleans were already present in the dependency cache, which is the state a
normal `lake exe cache && lake build` produces):

```
$ rm -rf .lake/build
$ lake build
ℹ [6784/6786] Built Jsp.JSP690
✔ [6785/6786] Built Jsp
Build completed successfully.
```

Wall time: 1m 21s (6786 modules, warm dependency cache).

## Axiom audit

`Jsp/JSP690.lean` ends with `#print axioms JSP000690`, which `lake build` emits:

```
info: Jsp/JSP690.lean:314:0: 'JSP690.JSP000690' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's three standard axioms, built into the kernel. No `axiom` declaration is
introduced by this development.

## Completeness checks

```
$ grep -nE "^\s*(by\s*)?\{?\s*(sorry|admit)\b|:= *sorry|:= *admit" Jsp/JSP690.lean
(no output)
$ grep -nE "^\s*(axiom|constant)\s" Jsp/JSP690.lean
(no output)
$ grep -n "sorry\|admit\|native_decide\|unsafe\|implemented_by\|extern" Jsp/JSP690.lean
16:so the file is `sorry`-free and uses no `native_decide`.
```

The only textual match is line 16, which is prose inside the module docstring asserting
that the file is `sorry`-free — not a proof term. Concretely:

- no `sorry` term,
- no `admit` term,
- no `native_decide` — every finite check is a kernel reduction via `decide`,
- no added `axiom` or `constant` declaration,
- no `unsafe`, `@[implemented_by]` or `@[extern]` escape hatch.

`set_option maxRecDepth 100000` appears once at the top of the file. It raises the
recursion depth available to `decide` when evaluating the `Finset.filter`-cardinality
tests; it changes evaluation budget only and does not affect the trusted base.

## What is proved

`JSP000690` (line 301) exhibits an explicit hypergraph and proves every clause of the
catalog question:

| Requirement | Lemma | Line |
| --- | --- | --- |
| 9 vertices, 22 edges | `V_card`, `E_card` | 165, 167 |
| 3-uniform | `uniform` | 175 |
| edges inside vertex set | `edge_subset_V` | 179 |
| minimum degree ≥ 7 | `min_degree` | 183 |
| not 2-colourable | `not_two_colorable` | 206 |
| 3-colourable | `three_colorable` | 264 |
| edge-critical | `edge_critical` | 268 |
| vertex-critical | `vertex_critical` | 283 |

The theorem is closed with an explicit witness tuple, so it is a complete answer to the
existential question, not a conditional or partial result.

## Reproduction

```bash
git clone https://github.com/kunjunsong-code/jsp-000690-lean
cd jsp-000690-lean
git checkout 74e3458370f6fda8fa12afa3c44aff35db87aec3
lake exe cache      # optional: download Mathlib oleans instead of building from source
lake build
```

`lakefile.lean` pins Mathlib to `v4.20.0`; `lake-manifest.json` pins all nine transitive
dependencies by revision, so the build is reproducible. Without a warm Mathlib cache the
build compiles Mathlib from source and takes hours rather than minutes.