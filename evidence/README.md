# Evidence

Raw results behind the README. Nothing here is edited by hand; each file is the output of the command in the README's *Reproduce* section or of the tool named below.

| File | Produced by |
|---|---|
| `build.txt` | `lake build` (raw exit, job list) |
| `axiom_audit.txt` | `lake env lean scripts/AxiomAudit.lean` |
| `intent_axioms.txt` | `lake env lean scripts/PrintAxioms.lean` |
| `claims_check.txt` | `CLAIMS=evidence/CLAIMS.json lake env lean scripts/ClaimsCheck.lean` |
| `CLAIMS.json` | the claims registry: one entry per property sentence of `README.md`, `README.zh-CN.md`, `docs/RATIONALE.md`, `docs/RATIONALE.zh-CN.md`, with theorem names, modules, statement hashes and axioms; English and Chinese sentences share claim ids |
| `kernel_replay_per_module.txt`, `kernel_replay_fresh.txt` | `lean4checker` |
| `nanoda/` | export and independent kernel check, with its negative control |
| `rcc/` | the RCC executable over the intent obligation graph (`intents_*`) and over the claims graph (`claims_*`, with a tampered negative control) |
| `audit/` | independent review of the claims against their theorems |
| `native_decide.txt` | the list of `native_decide` theorems in scope (empty) |

## Redacted copies

These three files are redacted copies: a local directory path was replaced by a neutral placeholder (`<publish-dir>`, `the publication tree`). Nothing else was changed. sha256 of each original:

| file | sha256 of original |
|---|---|
| `evidence/nanoda/nanoda_config.json` | `706121f09ccbe35adbf460072f09014dca84c205dd7554cff81856d328c3fd8c` |
| `evidence/audit/REFEREE_DELTA_round2.md` | `9918da658d4f9b3d97c49751ccc5bd55f6e705f0996310f6e1df611828453635` |
| `evidence/audit/REFEREE_DELTA_round1_40_overclaims.md` | `c0b87e3e606442731a67915f8c5def6b245d24bc5999eb6c0d31631d9077ed0c` |
