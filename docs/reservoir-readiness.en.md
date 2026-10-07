# Reservoir readiness: v0.5.12 release candidate

Checked 2026-10-07 while preparing v0.5.12 from public baseline c4d6d779552d5b52b71778464f2048f0fa22c4a8 and private Simon snapshot 8a58301154937e277e38e417dda503cff403e1b6. Metadata readiness and registry acceptance are separate results. The public validation is recorded in [release v0.5.12](release-v0.5.12.en.md).

## Inclusion criteria

[Reservoir's official criteria](https://reservoir.lean-lang.org/inclusion-criteria) specify automatic GitHub indexing, normally approximately daily. They require public non-fork sources (template-generated repositories are also excluded), a root lake-manifest.json, a GitHub-recognized OSI license, and at least two stars.

| Check | Observed result |
|---|---|
| Public source | GitHub API private=false |
| Fork/template origin | fork=false; no template_repository reported |
| Root manifest | lake-manifest.json present, with pinned dependency revisions |
| License | GitHub recognizes Apache-2.0; LICENSE exists; lakefile licenseFiles=["LICENSE"] |
| Stars | 3 at inspection time |
| Package metadata | name, version, description, keywords, homepage, license all present |
| Toolchain/dependency pin | Lean v4.33.1 and Mathlib v4.33.1 retained |
| Release candidate | v0.5.12; the publication requires all checks and an atomic main/tag push |
| Registry visibility | Public package page returned HTTP 404 at inspection time; inclusion is not confirmed |

GitHub API: https://api.github.com/repos/solanaqubits/lean-verification-components

Package page checked: https://reservoir.lean-lang.org/@solanaqubits/lean-verification-components

The metadata already meets the requested shape. The release updates version to 0.5.12. The existing descriptive metadata, license, toolchain and dependency pins are retained. The homepage points to the public repository. Reservoir metadata guidance permits a homepage; it does not make all descriptive fields independent hard inclusion criteria.

## Commands and limits

The installed Lake v5.0.0-src+819816b (Lean 4.33.1) documents `lake pack` as archiving existing build outputs: it does not build, validate source metadata, submit a package or prove acceptance. No undocumented `reservoir-cli` registration step is claimed. See [Lake documentation](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/).

Readiness requires strict builds on the pinned toolchain and a root default library target, both covered by the public release verification and by the fresh export checks recorded in [Simon validation](simon-verification.en.md). No toolchain upgrade is inferred from the registry's newer releases.

Status: the inspected public repository meets the listed observable inclusion criteria; indexing remains unconfirmed. Recheck the page after the automatic indexing interval. If it remains absent for several days, the official criteria suggest filing a registry issue. No issue, message or registration request was sent by this task. The separate release procedure authorizes publication of v0.5.12; it does not register or guarantee Reservoir acceptance.
