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
- `step2_conditional_separation.md` — Step 2 priority target: the concrete
  gate-list encoding for `NativeCirc`/`NativeEval`, properties (E-a)/(E-b),
  and the explicit transfer of ILW23's negative result via its Theorems 25
  (KPT witnessing) and 28 (AVOID hardness) directly, bypassing the paper's
  `Eval`; residual assumptions (§5), audit record (§7), status (§8).
- `check_step2.py` — finite checks of the Step 2 encoding, W1–W3 with the
  real evaluator, and the solver's control flow (`python3 check_step2.py`).
  Standard library only. Not a PV₁ proof.
- `gate_d_novelty.md` - focused novelty assessment: explicit RSW22
  conditional bridges, ILW23/CLOW26 separation machinery, source/version
  comparisons, bounded audit, and the stop-or-extension decision.
- `gate_e_stretch_check.md` - precheck of the full-schema targets 2b/2c:
  the incompressibility schemata sit in the squaring-stretch class, and
  the step to APC₁'s near-equal (or ILW23's `n+1`) stretch is Jeřábek's
  2007 open question, refuted relativized (JLC 2007, Cor. 3.6). Proposed
  form 2b', the 2f-candidate, Astra's mixed-oracle correction and
  bounded feasibility-check recommendation (Sections 4-5), and the first
  pass at that check with the residual obligation `(*)` (Section 6).

## Resume Here

**Step 2 is closed as plan outcome 2g (reconstruction endpoint), with both
reviewers' concurrence.** Read the Step 2 execution update in
`modified_specific_recommendation.md` Section 5, then `gate_d_novelty.md`
Sections 3 and 5. The conditional separation T3' stands at paper level
under the residual assumptions in `step2_conditional_separation.md`
Section 5; its review cycle (Section 7) is closed. Novelty is not
established. The 2f-candidate feasibility check (Astra's mixed-oracle
formulation, `gate_e_stretch_check.md` Sections 4-5) has had its first
pass (Section 6): the direct ILW23 adaptation fails for an identified
quantitative reason (planted-`y` failure probability `2^{-Ω(km)}` vs
random-reply legality error `2^{-t}` at medium `t`), leaving the sharper
obligation `(*)` (average-case white-box AVOID hardness with an inversion
oracle). Next action is the user's decision among Section 6.4's options:
tier-2 outreach with the sharp question (needs explicit authorization),
a bounded literature check on `(*)`, or stop. No proof campaign is
authorized. The full-schema targets 2b/2c are closed as routes in the
current plan, not refuted unrelativized (the missing stretch step is
false relativized; see the Gate E note).
`step1_decoder.md` Section 5.3 is the Step 1 result ledger; the Step 0
ledger is historical. Nothing depends on chat history.

Lessons recorded from Steps 1-2: a reversal over `T_PV` suffices for a
separation (nonprovability descends to subtheories), so an internal PV₁
proof is only needed for a characterization; write finite check scripts
early, since they caught two spec errors before review; and do the novelty
check before, not after, investing in internal formalization.

## Operating norms

- At the end of every round, including discussion-only and review rounds,
  make any new conclusions, corrections, recommendations, decisions, and
  operating rules durable in the appropriate project notes or this file.
  Update the handoff when the next action changes; do not leave durable
  knowledge only in chat or duplicate it across documents. Then verify and
  commit that round's scoped changes without waiting for a separate request.
  Do not create empty commits or include unrelated work.
- The user performs the final push manually. Do not run `git push` (or the
  `push` alias) for this repo unless explicitly asked to do so.
- Default branch is `main`; remote is
  `https://github.com/david-battle/p_vs_np`.
- Keep commits small and scoped to what was asked. Match the concise style of
  the sibling `immortal_kangaroo_sequence` repo.
- Durable knowledge about this project belongs in this file or in the notes
  files, not duplicated across several documents.
- Keep temporary working files inside this repository directory, not in
  `/tmp` or another external directory. Exclude them locally through
  `.git/info/exclude`, not tracked `.gitignore`; do not commit them or
  mention their filenames in tracked notes or commit messages.
