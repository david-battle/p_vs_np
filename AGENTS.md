# AGENTS.md

Repo: notes and analysis on the P vs NP question and its surrounding
foundational discussions (the Axiom of Choice, forcing and absoluteness,
"new axioms", independence, and GEB-style self-reference intuitions).

Split off from the sibling `immortal_kangaroo_sequence` repo, where these
discussions had grown out of the AC example in the comma-sequence notes.
P vs NP content lives here; kangaroo-sequence content stays there.

## Files

- `p_vs_np_notes.md` — the discussion: AC's (ir)relevance to P vs NP, forcing
  absoluteness vs arithmetic incompleteness, the "P≠NP as a new axiom" question
  (and the correction on independence), the GEB "prophetic" reading, the
  user's self-referential-structure intuition, the machine-Gödel proof-search
  construction, and where self-reference can honestly attach (witness, proof
  space, budget). Includes the AC framing (kangaroo as "for" example,
  Vitali/Banach–Tarski as "against") that motivated it.
- `recommendation.md` — which research direction from the notes to pursue:
  bounded-arithmetic (un)provability of lower bounds (Krajíček → Pich–Santhanam
  → Chen–Li–Oliveira 2024), and why not the others.
- `detailed_recommendation.md` — candidate "favorite lower bounds" for a
  CLO24-style equivalence with a pigeonhole principle, with later corrections
  (items #1 and #2 are largely Jeřábek 2004; the residue is over PV₁).
- `specific_recommendation.md` — standalone plan for the K^t-incompressibility
  problem: literature check, formal statement, target theorem (parameter-free
  vs parameterized dWPHP as unconditional vs conditional K^t), then
  formalizing Liu–Pass in APC₁. Intentionally self-contained; it does not
  reference the other files here.
- `modified_specific_recommendation.md` — revised plan: fixed-stretch Eval
  reversal and the UAPC₁/APC₁ conditional separation as the first milestone,
  full-schema equivalences as optional extension; gates, outcome tree.
- `step0_baseline.md` — Step 0 execution record: source table (CG, Korten,
  PS21, ILW23) with locators, convention decisions (halting-output,
  `<= floor(n/2)`), exact Eval instance, implication ledger, `T^0_APC`
  shortcut (§5a), Gate A handoff.
- `step1_decoder.md` — Step 1: one-sorted definitions (sentinel encoding,
  `Sim_c`/`CSim_c`, `Inc_c`, `CInc_c`, `EvalAvoid_4`), parameterized and
  unary decoders with coverage lemmas, guarded universal lemmas L0–L3, the
  `T^0_APC` derivation of the conditional separation (T1–T3), and the
  Step 1 finalization (§6): PV₁ basis and metatheorems, discharge of the
  forward lemmas (F1/F2, outcome 1a at paper level), the ILW23 encoding
  check reducing source binding to properties (E-a)/(E-b), the isolated
  remaining obligation (L2 in PV₁), and the Gate B decision.
- `check_step1.py` — finite sanity checks for Step 1 (`python3
  check_step1.py`); standard library only. Not a PV₁ proof.

## Resume Here

Read `step1_decoder.md` Sections 6.7-6.8 first: they hold the accepted
Step 1 outcome and the next-context handoff. Then read Sections 6.5 and 4
for the remaining T3 interface work. Use its Section 5.3 as the current
result ledger; the Step 0 ledger is historical. The handoff supersedes
earlier next-action lists and does not depend on chat history.

## Operating norms

- The assistant makes commits when asked; the user performs the final push
  manually. Do not run `git push` (or the `push` alias) for this repo unless
  explicitly asked to do so.
- Default branch is `main`; remote is
  `https://github.com/david-battle/p_vs_np`.
- Keep commits small and scoped to what was asked. Match the concise style of
  the sibling `immortal_kangaroo_sequence` repo.
- Durable knowledge about this project belongs in this file or in the notes
  files, not duplicated across several documents.
