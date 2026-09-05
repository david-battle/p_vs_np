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
