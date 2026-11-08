# Proof task

Work only in `Solution.lean`. It starts as an exact copy of `Challenge.lean`.

Prove every theorem listed in `config.json`. You may add helper definitions and lemmas to
`Solution.lean`, but do not change the target theorem statements or the definitions used by those
statements. Do not import `Challenge`, and do not use `sorry`, `admit`, new axioms, or unsafe escape
hatches. Network access and web research are allowed.

The CPSLib library source is available under `CPSLib/Core` and `CPSLib/Tactic`. Inspect and use it.
Before proving, read and follow `.agents/skills/cpslib-prover/SKILL.md`.
Check progress with:

    lake env lean Solution.lean

Finish only after `Solution.lean` compiles and the target theorem has no placeholder.
