# Independent kernel check (Nanoda)

* Exporter: `lean4export` at commit `e6c7eaf` (export format 2.0.0) with `lean4export_414.patch` (qualifies `HashMap` as `Std.HashMap` so it compiles against Lean 4.14.0), run interpreted with a wrapper that takes `::` as the separator before the constant list (`exported_constants.txt`: the theorem, definition and axiom constants of the shipped modules).
* Checker: `nanoda_lib` tag `v0.3.2` (commit `66cca78`), an independent Rust implementation of the Lean 4 kernel. Config: `nanoda_config.json` (permitted axioms: `propext`, `Classical.choice`, `Quot.sound` only; an unpermitted axiom is a hard error).
* Result: `nanoda_run.txt`.
* Negative control: `negative_control_native_decide.txt`.
