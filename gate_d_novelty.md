# Gate D: Novelty Check for the Conditional Separation

**First-pass assessment (September 5, 2026): known separation mechanism,
with an explicit incompressibility specialization. The exact arithmetic
nonimplication was not located; its novelty is not established.** The
mathematical status and assumptions of T3' are unchanged. This is a
bounded literature assessment, not a new proof or a priority claim.

## Work Record

Started September 5, 2026, 22:52 UTC (Astra). Target: assess the novelty of
T3' in [step2_conditional_separation.md](step2_conditional_separation.md),
not reopen its closed transfer audit. Cap: 60 minutes of focused public
literature work plus one bounded independent audit. No outreach,
publication, full-schema extension, or L2-in-PV_1 work in this pass.

Two disjoint research passes covered the incompressibility sources and
adjacent/follow-up literature; the lead pass checked ILW23/PS21 and exact
phrase searches, then re-read the decisive RSW22, CLOW26, KK26, and CG
passages. Sources were checked at the locators below, not audited in full.

## 1. Comparison Target

Under Step 2 Section 5's residual assumptions, including JLS-secure iO and
`coNP not contained in i.o.NP/poly`, there is one fixed standard `c_0` with:

```text
UAPC_1 proves Inc_c                         for every fixed standard c>=1;
APC_1 proves CInc_c                         for every fixed standard c>=1;
T^0_APC does not prove CInc_{c_0};
PV_1 + {Inc_c : c>=1} does not prove CInc_{c_0}.
```

The exact sentences, machine contract, half-length threshold, arbitrary
uncharged auxiliary input, and combined-input clock are in
[step1_decoder.md](step1_decoder.md) Sections 0 and 6.4. The negative result
uses true universal PV facts, not an internal PV_1 proof of L2. The exponent
is existentially fixed at the metalevel, not a certified numeral.

Compare separately: the theory separation; ordinary incompressibility
from parameter-free pigeonhole axioms; auxiliary-input incompressibility
as the separating sentence; and the implementation/encoding details.
Failure to locate the exact formulation will not establish novelty or
open-problem status.

## 2. Source Map

Page numbers are printed pages in the linked versions. `Explicit` means
the source states the result; it does not mean the source uses our exact
machine, formula, or theory presentation. Dates pin public versions, not
claims that all later published versions were inspected.

| Source and version | Locator and explicit content | Match to this project |
| --- | --- | --- |
| Pich-Santhanam, *Strong Co-Nondeterministic Lower Bounds for NP Cannot Be Proved Feasibly* (PS21), [March 2021 STOC-final PDF](https://users.ox.ac.uk/~coml0742/papers/stoc-final.pdf) | Section 2.1, pp. 7-8: parameterized versus parameter-free dWPHP, hard functions and approximate counting in the latter. Theorem 4, pp. 9-10: circuit-KPT witnessing for `T^0_APC_1`. | Exact theory/witnessing antecedent. Its `forall Sigma^b_1` conservativity is not an Inc/CInc theorem. |
| Ilango-Li-Williams, *Indistinguishability Obfuscation, Range Avoidance, and Bounded Arithmetic* (ILW23), [ECCC TR23-038, March 28, 2023](https://eccc.weizmann.ac.il/report/2023/038/download) | Section 4.3, Theorem 24, p. 17; Theorems 25-28, pp. 17-19: `T^0_APC` does not prove circuit avoidance for any constructive polynomial output length larger than the input length, under our two hypotheses. | The `UAPC_1`/`APC_1` separation and its nonuniform witnessing mechanism are already explicit. Our fixed `4m` output length is covered. |
| ILW23, same version | Section 2.4, Definitions 15-16, p. 9; Section 5, Hypothesis 30 and Theorem 31, pp. 20-21: conditional time-bounded Kolmogorov complexity and a conditional refutation of its oracle-derandomization hypothesis. | Free auxiliary input and compression using a circuit supplied as auxiliary input already occur in the very paper supplying our negative theorem. This is an algorithmic result, not the Inc/CInc arithmetic nonimplication. |
| Korten, *The Hardest Explicit Construction*, [arXiv:2106.00875v3, February 10, 2022](https://arxiv.org/pdf/2106.00875v3) | Section 3.5, Definitions 13-14 and Theorem 6, p. 14: ordinary high-`K^t` construction reduces to Empty using an `n-1` input / `n` output padded decoder. | Explicit ordinary decoder antecedent. No arithmetic base or free auxiliary parameter in that theorem. |
| Ren-Santhanam-Wang, *On the Range Avoidance Problem for Circuits* (RSW22), [ECCC TR22-048, April 4, 2022](https://eccc.weizmann.ac.il/report/2022/048/download) | Definitions 6.3-6.4, pp. 47-48; Theorem 6.6 and proof, pp. 48-49: conditional incompressibility, its decoder, and its evaluator reversal in an FNP/proof-generator characterization. Theorem 6.7, pp. 49-50: ordinary incompressibility and unary avoidance/uniform generators. | Closest direct antecedent for both bridges and the ordinary/auxiliary-input distinction. Not a PV_1 provability theorem. See Section 3. |
| Carmosino-Grosser, *Student-Teacher Constructive Separations and (Un)Provability in Bounded Arithmetic: Witnessing the Gap* (CG), [ECCC TR25-045 revision 1, April 12, 2025](https://eccc.weizmann.ac.il/report/2025/045/revision/1/download) | Theorem 4.18, p. 23: `VAPC proves HiKt[c]`. Theorem 1.16's proof, p. 6, describes `dWPHP(U_d)` proofs of ordinary incompressibility; Section 1.6, p. 8, says they use a weaker uniform dWPHP. | Explicit ordinary incompressibility provability and anticipation of uniform pigeonhole reasoning. Not a displayed theorem for our exact `UAPC_1`/Inc formula. Their WHUP-based ordinary incompressibility unprovability concerns different theories and hypotheses. |
| Chen-Li-Oliveira-Williams, *A Theory for Probabilistic Polynomial-Time Reasoning* (CLOW26), [arXiv:2602.09302v1, February 10, 2026](https://arxiv.org/pdf/2602.09302v1) | Section 5.3.2, Definition 5.11 and Theorems 5.12-5.13, pp. 78-79; Corollary 5.14, p. 79: under the same hypotheses, any extension of PV_1 admitting circuit-KPT witnessing misses a `forall Sigma^b_2(PV)` theorem of APC_1. | Explicit generalization of the separation mechanism, labelled "Implicit in [ILW23, Theorem 24]". Does not identify its separating sentence with our CInc. Applies it to APX_1, not an asserted extension of UAPC_1. |
| Kabanets-Kolokolova, *Kolmogorov's Approach to P vs NP: Chain Rules for Time-Bounded Kolmogorov Complexity* (KK26), [ECCC TR25-089 revision 1, March 13, 2026](https://eccc.weizmann.ac.il/report/2025/089/revision/1/download) | Section 2.4, pp. 15-16, especially p. 16 and footnote 7: polynomial-time equivalence of constant-factor-stretch avoidance and finding conditionally incompressible strings. | Explicit recognition of the conditional-`K^t`/AVOID correspondence as established machinery. No bounded-arithmetic equivalence or Inc/CInc separation is stated there. |

### Adjacent Results Checked

These help delimit the claim; none is imported as a new premise of T3'.

| Source | Locator and relevance | Why not an exact match |
| --- | --- | --- |
| Jerabek, *Dual Weak Pigeonhole Principle, Boolean Complexity, and Derandomization* (APAL 2004), [author version dated November 25, 2003](https://users.math.cas.cz/~jerabek/papers/wphp.pdf) | Lemma 3.2 and Proposition 3.5, pp. 20-21; Corollary 3.6, p. 21: range avoidance and hard truth tables. Proposition 1.14/Corollary 1.15, pp. 10-11: parameter-free generator machinery for `forall Sigma^b_1` consequences. | The hard-function equivalence is over `S^1_2`, not PV_1. Its `dWPHP'(f,g)` denotes a witnessed/retraction principle, not PS21's parameter-free prime. |
| Chen-Li-Oliveira, *Reverse Mathematics of Complexity Lower Bounds* (CLO24), [October 4, 2024 author version](https://www.dcs.warwick.ac.uk/~igorcarb/documents/papers/CLO24.pdf) | Section 1.2.1, p. 8, footnote 8: ILW23's parameter distinction obstructs simply transferring Jerabek's hard-function equivalence to PV_1. | Main reversals concern other pigeonhole variants and lower bounds; this footnote is not an incompressibility equivalence. |
| Krajicek, *Proof Complexity Generators*, [August 2024 author draft](https://msekce.karlin.mff.cuni.cz/~krajicek/k4.pdf), subsequently published 2025 | Section 4.1, Theorem 4.1.4, p. 50: transfer from a uniform generator to a clocked universal-machine generator; the range inclusion is stated to be formalizable in PV_1. | Close formalization method, but a propositional hardness transfer with charged descriptions, not our arbitrary free auxiliary input or arithmetic nonimplication. It does not certify our particular L2 implementation. |
| Ren-Wang-Zhong, *Hardness of Range Avoidance and Proof Complexity Generators from Demi-Bits* (RWZ26), [arXiv:2511.14061v2, March 13, 2026](https://arxiv.org/pdf/2511.14061v2) | Theorems 1.5-1.7, pp. 5-6; Section 4.1, pp. 17-18: PV_1/APC_1 separation and uniform Student lower bounds from demi-bits. | Theorem 1.5 assumes superlinear-output demi-bits secure against `AM/O(1)`. Theorem 1.6 concerns uniform polynomial-time Students, not the circuit Students extracted from `T^0_APC`. Theorem 1.7 is proof-system-relative pseudo-surjectivity. No replacement for our exact negative import is established here. |
| Ilango, *The Oracle Derandomization Hypothesis Is False (And More) Assuming No Natural Proofs*, [ECCC TR25-190, November 2025](https://eccc.weizmann.ac.il/report/2025/190/download) | Theorem 3.6 and the following remark, p. 13: oracle truth-table generators; the remark extends the argument to conditional time-bounded Kolmogorov complexity. | Algorithmic/propositional hardness under different assumptions, not a UAPC_1 or Inc/CInc theorem. |

## 3. What Was Already Present

### 3.1 The Conditional Bridges Are Explicit Prior Art

RSW22 Definition 6.3 minimizes only the length of `d` in
`U(d,y,1^{t(|d|+|y|)})=x`. The string `y` is free auxiliary input, not a
charged payload. Definition 6.4 supplies `(1^n,y)` as the construction
problem's input. Theorem 6.6's proof then supplies both directions:

1. A decoder circuit with `n-c` input bits and `n` output bits simulates
   `U(d,y)` and covers the relevant compressible outputs.
2. For the reverse direction, supply a circuit description as `y` and
   describe a range element by its preimage plus a fixed evaluator. On
   pp. 48-49 the source explicitly pads the circuit description for the
   clock and derives `cK^t(v given <C>) <= input_length + |d_Eval|` for
   `v` in the range of `C`.

Theorem 6.7 treats the ordinary/unary/uniform-generator counterpart
separately. Thus neither free auxiliary input, the two decoder directions,
nor the association of this distinction with uniformity originates here.
KK26 p. 16 restates the computational correspondence; its footnote calls
the conditional case an immediate generalization. The direct antecedent
is RSW22's own conditional theorem, not just that later attribution.

Important differences prevent citing these as literal proofs of our
sentences. RSW22 uses near-maximal thresholds (`n-c`, or `n-c log n` in
the ordinary theorem), grants output length to ordinary programs for free,
and clocks the conditional computation by `t(|d|+|y|)`. Its simulator
allows polynomial overhead relative to the simulated program's steps.
KK26 supplies the time budget separately in unary and discusses output
length larger than `(1+epsilon)` times input length. Our half-length
threshold, halting-output test, U-step clock `(n+|z|+1)^c`, sentinel
resources, small-length repairs, and arbitrary circuit-description length
remain separately specified and justified in Steps 1-2. No same-clock
machine equivalence or PV_1 interpretation of RSW22/KK26 is claimed.

CG is also closer to the positive direction than the Step 0 source table
alone makes apparent: its introduction explicitly mentions uniform dWPHP.
But that prose does not identify PS21's precise parameter-free interval
schema or discharge the unary length-resource proof. Its charged
two-part input and the threshold/output-convention discrepancies remain
as recorded in Step 0; we do not import a silently corrected HiKt theorem.

### 3.2 The Separation Mechanism Is Known

ILW23 Theorem 24 already proves the theory separation and unprovability in
the stronger true-universal base. Its proof uses precisely circuit-KPT
witnessing and hardness with a constant number of inversion gates.
CLOW26 Theorem 5.13 explicitly states the abstract version: the
circuit-KPT property is enough. It therefore confirms that applying the
method beyond the original named theory is not a new general technique.
It still does not identify a particular CInc sentence, or give the
encoding/clock bridge needed to do so.

ILW23 Theorem 31 is another close antecedent, but a different endpoint:
it rules out the specified efficient conditional-hard-string construction
under `NP != coNP` and JLS-secure iO. Definition 16 uses a clock in the
output length, and Hypothesis 30 relates auxiliary and output lengths
polynomially. It neither supplies the constant-round circuit-Student
lower bound needed for our arithmetic result nor justifies weakening
T3's hypotheses. Keep Theorem 28, not Theorem 31, as the negative import.

### 3.3 Remaining Contribution and Limits

| Component | Gate D classification |
| --- | --- |
| `UAPC_1` versus `APC_1`; stronger `T^0_APC` negative endpoint | Known, explicitly ILW23. |
| Circuit-KPT transfer to avoidance hardness | Known; explicitly generalized by CLOW26. |
| Ordinary incompressibility from pigeonhole reasoning | Known decoder/provability antecedents in Korten and CG; uniform use anticipated by CG. The exact F2 formula was not located. |
| Free-auxiliary decoder and circuit-evaluation reversal | Explicit RSW22 prior art; further explicit in ILW23 and KK26. |
| Exact `PV_1+{Inc_c}` nonprovability of one `CInc_{c_0}` with our conventions | Not located as a stated arithmetic theorem. Best treated as a concrete specialization/corollary of known machinery, reconstructed here under explicit contracts. Novelty unestablished. |
| Internal PV_1 reversal / full-schema equivalences | Still incomplete/deferred. This search neither proves them nor establishes that they are open or new. |

The value retained is a checked implementation of the argument at ordinary
paper-proof level: exact sentences, explicit unary parameter removal, one
fixed sufficient clock exponent at the metalevel, and an audited circuit
interface. These are useful reconstruction details. Neither their amount
nor the absence of an identical displayed formula establishes a substantial
new research theorem. Conversely, we have not found a source that can
replace all those details by an exact citation.

## 4. Search Scope and Limits

Search date: September 5, 2026. The passes combined targeted phrase
searches, ECCC/arXiv version records, author pages, and the citation trails
in CG, RSW22, CLO24, and the 2025 surveys. Representative queries actually
used (not an exhaustive log of noisy query variants):

```text
"conditional Kolmogorov complexity" "pigeonhole"
"UAPC" "Kolmogorov"
"parameter-free" "incompressibility" pigeonhole
"conditional incompressibility" "UAPC"
"auxiliary input" "dual weak pigeonhole"
"parameter-free" "Kolmogorov" "PV"
2026 "parameter-free" "dWPHP"
2026 "proof complexity generators" "conditional" "Kolmogorov"
"auxiliary-input" "incompressibility" "bounded arithmetic" 2026
2026 "range avoidance" "bounded arithmetic" separation
"A Theory for Probabilistic" "UAPC"
"On the Range Avoidance Problem for Circuits" "conditional" "Kolmogorov"
```

Many acronym/phrase queries returned unrelated material; empty or noisy
search results carry little weight. The assessment rests on positive
primary-source matches, not search-engine coverage. The relevant sections
were read in full; this was not an exhaustive citation-index search or a
proof audit of every cited theorem.

Version/access limits: the live CG ECCC record lists revision 1; the
later [STOC 2025 publication](https://doi.org/10.1145/3717823.3718216) was
identified, but its publisher full text returned 403. The
[CLO24 SICOMP publication](https://doi.org/10.1137/24M1717865) was likewise
identified in 2026, but only the October 2024 author text was inspected.
The CLOW26 and RWZ26 arXiv version records and KK26 revision record were
checked; the 2026 sources cited above predate this search. The survey
trails were Oliveira's [2025 survey](https://arxiv.org/pdf/2504.04416v1),
Section 6, pp. 23-24, and Li's [2025 introductory notes](https://eccc.weizmann.ac.il/report/2025/086/download),
Section 1.5, pp. 15-16. No outreach or unpublished priority information.

## 5. Gate Decision and Handoff

**Recommendation: accept a coherent reconstruction endpoint for the first
milestone; do not invest in L2-in-PV_1 solely to make this separation look
novel.** Outcome 1a and the paper-level conditional separation (2g) remain
the mathematical results, under their existing assumptions. Gate D has
now assessed their literature position: familiar machinery, exact
specialization unlocated, no novelty claim. This is not outcome 0a
(an exact source match) and does not establish the BEST outcome of the
modified plan.

The next decision is **stop or deliberately choose an extension**, not
automatically start an internal simulation proof. Stopping preserves a
useful result and source map. If further research is chosen, first select
one precise target and state what it adds beyond RSW22/ILW23/CLOW26;
then time-box its source/feasibility check. A PV_1-internal reversal may be
a worthwhile learning/formalization target, but its research novelty is
not certified by this pass. Full-schema equivalences, Liu-Pass, weaker
cryptographic hypotheses, and APX_1 applications are not authorized by
this handoff as automatic next tasks.

For the mathematics, resume from Step 2 Sections 5 and 7-8 and Step 1's
ledger in Section 5.3. Do not reopen the closed T3' transfer audit absent
a concrete new counterexample. This note supersedes only their
"novelty unassessed / Gate D next" status, not their definitions or proofs.

## 6. Audit and Verification

Bounded independent read-only source-comparison audit, September 5, 2026:
no blocking or should-fix source-comparison or scope defects found.
Decisive passages were checked in RSW22, CLOW26, KK26, CG, ILW23, and
PS21, with adjacent-source spot checks and confirmation of the principal
ECCC/arXiv version dates. The audit accepted the distinctions in Sections
3 and 5; it did not certify exhaustive novelty or priority, inspect the
later publisher texts, or reopen the closed T3' transfer review. This is
one bounded independent audit, not a claim of cross-model concurrence.

Verification: `python3 check_step1.py` and `python3 check_step2.py` both
passed; `git diff --check` passed. The scripts were unchanged and provide
finite regression checks only, not evidence of novelty or a PV_1 proof.
The current status pointers and the next-action decision are updated in
Steps 1-2 and AGENTS.md. No new mathematical premise or proof is added.
