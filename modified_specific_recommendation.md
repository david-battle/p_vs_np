# Research Plan: Time-Bounded Incompressibility over PV_1

## 1. Objective and Scope

Determine which dual weak pigeonhole principles are sufficient and necessary
to prove the existence of time-bounded incompressible strings over Cook's
theory PV_1. Compare strings with no auxiliary input against strings that
remain incompressible relative to an arbitrary auxiliary input.

The immediate objective is a checked chain of implications, beginning with
bounded universal-machine decoding and fixed-stretch pigeonhole instances.
The first research milestone is a conditional separation between ordinary
and auxiliary-input incompressibility, using ILW23 and a fixed-stretch Eval
reversal. Attempt this before full-schema stretch conversions. Equivalences
with the full parameter-free or parameterized pigeonhole schema are the
more ambitious extension. Novelty and the target reductions are unverified;
reconstructing a known result is an acceptable outcome.

If this work provides sufficient technical preparation, pursue a separate
question: can the Liu-Pass equivalence between one-way functions and
average-case hardness of time-bounded Kolmogorov complexity be proved in
APC_1?

**Operating constraints**

- Keep planned AI-token expenditure below $1000, plus the researcher's time.
- Work from public literature. Defer outreach unless explicitly authorized.
- Do not publish or push material without explicit authorization.
- Accept some duplication risk rather than requiring exhaustive novelty checks.
- Keep the initial work on incompressibility and pigeonhole principles;
  postpone other lower-bound candidates and broad unprovability projects.

## 2. Mathematical Setup

**Base theories.** PV_1 formalizes polynomial-time algorithms and reasoning
with quantifier-free induction. Buss's S^1_2 extends it with stronger
induction and is useful as a comparison theory. A proof in S^1_2 is not
automatically a proof in PV_1.

For a polynomial-time function f, use the following parameterized dual weak
pigeonhole principle, in schematic notation:

```text
dWPHP(f):
  forall a > 0, forall b in Log, forall z,
  exists v < a(b+1), forall u < ab, f(u,z) != v.
```

Here `b in Log` means that b is the bit length of an available number; it
supplies a unary-sized parameter. The parameter-free version `dWPHP'(f)`
drops z and uses f(u). Neither a nor b is an additional input to that unary
function. Each principle ranges over all appropriate PV function symbols,
giving the schemata `dWPHP(PV)` and `dWPHP'(PV)`.

Define `APC_1 = PV_1 + dWPHP(PV)` and
`UAPC_1 = PV_1 + dWPHP'(PV)`. APC_1 supports approximate counting of sets
defined by polynomial-time predicates. The distinction between the two
schemata is central: Ilango-Li-Williams (STOC 2023, ILW23), Theorem 24,
conditionally separates these theories under JLS-secure indistinguishability
obfuscation and
`coNP not contained in i.o.NP/poly`. The latter means that no language in
NP/poly agrees with a certain coNP language on infinitely many input lengths.

**Stretch conventions.** Always record both cardinalities and bit lengths.
For a = 2^m:

| Domain and codomain sizes | Input and output bit lengths |
| --- | --- |
| a and 2a | m and m+1 |
| a and a^2 | m and 2m |
| a and a^4 | m and 4m |

A result for the squaring schema is an intermediate result, not yet an
equivalence with the near-equal-cardinality schema defined above.

## 3. Step 0: Establish the Literature Baseline

**Execution record (September 5, 2026):** the
[Step 0 baseline](step0_baseline.md) contains the checked sources, convention
decisions, exact Eval instance, implication ledger, and Gate A handoff.
Gate A's research deliverables are complete via outcome 0b; proceed to
Step 1. The baseline distinguishes source verification from the PV_1 proofs
still to construct.

Time-box the first pass to roughly one or two weeks of available research
time. Read the specified sections for exact statements and proof ingredients,
not every paper in full. Use additional reading only to resolve a concrete
question needed for the next proof step.

Complete items 1-3 for the first milestone. Consult items 4-5 as concrete
reversal or stretch obligations arise, and item 6 before starting Step 3.
Do not delay the first decoder proof for an exhaustive literature search.

1. **Identify the incompressibility statement.** Read
   [Carmosino-Grosser, ECCC TR25-045, Revision 1, April 12, 2025](https://eccc.weizmann.ac.il/report/2025/045/revision/1/download),
   Sections 2.7 and 4. Extract the machine convention, description encoding,
   threshold, schema indexing, and VAPC provability statement. VAPC and VPV
   are two-sorted counterparts of APC_1 and PV_1. Record the translation
   required for this project's one-sorted setting. Resolve strict versus
   non-strict threshold inequalities explicitly.
2. **Extract the decoder reduction.** Read
   [Korten, The Hardest Explicit Construction, full version v3](https://arxiv.org/pdf/2106.00875v3),
   Section 3.5, Definition 14 and Theorem 6. The theorem reduces construction
   of high-K^t strings to Empty, the problem of finding a string outside a
   stretching circuit's range. Extract the actual circuit and reconstruction
   argument, then identify the arithmetic facts needed to formalize it.
3. **Fix the exact pigeonhole schemata.** Read
   [Pich-Santhanam, STOC 2021 (PS21)](https://users.ox.ac.uk/~coml0742/papers/stoc-final.pdf),
   Section 2.1, and
   [Ilango-Li-Williams, STOC 2023](https://eccc.weizmann.ac.il/report/2023/038/download),
   Section 4.3, equation (7) and Theorem 24. Record the parameter-free theory,
   its hard-function and conservativity results, and the exact separation
   hypotheses. Use PS21 Section 3.1, Theorem 4 when nonuniform witnessing
   becomes relevant.
4. **Study the reversal methods.** Read
   [Chen-Li-Oliveira, Reverse Mathematics of Complexity Lower Bounds](https://www.dcs.warwick.ac.uk/~igorcarb/documents/papers/CLO24.pdf),
   Section 2.4, footnote 8, and a representative reversal proof. Then read
   Jerabek, "Dual weak pigeonhole principle, Boolean complexity, and
   derandomization" (APAL 129, 2004), Section 3, especially Proposition 3.5.
   Separate constructions of polynomial-time functions from proofs that
   their ranges have the required properties.
5. **Check the stretch conversions.** Read
   [Jerabek, Approximate Counting in Bounded Arithmetic](https://users.math.cas.cz/~jerabek/papers/apx.pdf)
   (2007), Section 1. Follow citations specifically concerning equivalence
   between near-equal-cardinality and squaring schemata over PV_1, including
   the parameter-free case. Search for matching K^t reversals under
   "incompressibility", "range avoidance", and "proof complexity generators".
6. **Check the follow-on's status.** Use
   [Oliveira's 2025 survey](https://arxiv.org/abs/2504.04416) and citation trails
   for Liu-Pass formalizations in bounded arithmetic. Record any matching
   result and its base theory. A search with no match leaves novelty
   unverified; it does not establish an open problem.

**Deliverable:** a compact source table recording statement, version and
theorem number, base theory, parameters, stretch, and relevance to the target.
For each target implication, label it `cited theorem`, `proof to reconstruct`,
or `unresolved`. Distinguish a search reduction from an explicitly formalized
arithmetic theorem.

**Decision:** if the chosen target is already known, reconstruct the most
useful proof as a learning exercise and reassess the follow-on. Otherwise,
proceed with the missing implication identified as precisely as possible.

## 4. Step 1: Fix the Definitions and Prove the Decoder Lemmas

**Execution update (September 5, 2026):** outcome **1a accepted at paper
level** after finalization and concurrence review. The parameterized and
unary decoder forward proofs are established under the definitions in
[step1_decoder.md](step1_decoder.md). Task 4 below (internal simulation and
overhead proofs) remains incomplete; this is not an unqualified completion
of all Gate B tasks. Sections 6.7-6.8 of that note give the authoritative
consensus and next action: close and audit the T3 circuit interface via
the `T_PV` route before novelty work or L2-in-PV_1. No separation or novelty
claim is included in the accepted Step 1 outcome.

### Definitions

Fix a concrete efficient universal machine U with two-part descriptions of a
machine and its input, an explicit halting/output convention, and a specified
simulation clock. Define K^t(x) as the length of the shortest description
that makes U halt with output x within t(|x|) steps. Auxiliary input z is
supplied separately and is not charged to description length.

For each standard integer constant c >= 1, define:

```text
Inc_c(n):
  exists x in {0,1}^n, forall descriptions d with |d| <= floor(n/2),
  U(d) does not halt with output x within n^c steps.

CInc_c(n):
  forall auxiliary strings z, exists x in {0,1}^n,
  forall descriptions d with |d| <= floor(n/2),
  U(d,z) does not halt with output x within (n+|z|+1)^c steps.
```

The combined-input clock in CInc allows simulation of general PV functions
f(u,z), whose runtime can depend polynomially on both input lengths.

Use n in Log, or supply 1^n explicitly, when translating the string notation
into one-sorted arithmetic. Preserve leading zeros in the string encoding.
The bounded simulation matrix is polynomial-time; the length-universal
existence statements have the form `forall Sigma^b_2`. The index c labels
separate sentences, rather than a variable exponent inside one sentence.

Take a fixed starting cutoff n_0 = 4 for the half-length threshold. Record
and justify any larger cutoffs used in individual reductions. Compare the
chosen U convention with each source before importing its K^t statements.

### Proof Tasks

1. **Construct a total decoder.** Set m = floor(n/2). Encode every description
   of length at most m in m+1 bits, for example as `0^(m-|d|) 1 d`. Send the
   unused all-zero code, failed simulations, and wrong-length outputs to
   `0^n`. Define the conditional decoder with z as a separate parameter.
2. **Prove the forward implications from full dWPHP.** There are
   `2^(m+1)-1` short descriptions, and the padded domain has size `2^(m+1)`.
   For n >= 4 this is at most half of `2^n`. Instantiate dWPHP with the
   properly encoded decoder and prove that a missing output satisfies Inc_c
   or CInc_c. Include the default-output and interval/string translations.
3. **Remove parameters for the unconditional case.** Construct unary
   decoders with no free n, clock, or advice argument. Derive lengths from
   the input encoding, handling even and odd output lengths separately if
   needed. Prove the connection to dWPHP'(PV), including the translation
   from encoded strings to the numeric interval schema. Do not leave 1^n
   as a hidden function parameter.
4. **Prove simulation and overhead bounds.** For each fixed PV algorithm f,
   exhibit its U description, a constant C_f, and a polynomial simulation
   bound. Verify the needed correctness facts in PV_1. These are the lemmas
   used to turn range membership into a short-description witness.

**Deliverable:** explicit PV definitions and proofs of the established
forward implications, with the unary-decoder reduction separately checked.
Document any remaining formalization gap rather than treating ordinary
counting as a substitute for the required PV_1 proof.

## 5. Step 2: Prove the Reversals in Increasing Strength

### Fixed-Stretch Target

Use this construction as a proof template, specializing to Eval for the
priority milestone below. A complete classification of fixed-stretch
schemata is not a prerequisite for that milestone.

Start with a single parameter-free polynomial-time algorithm f satisfying
`f: {0,1}^m -> {0,1}^{2m}` at each input length m. For a sufficiently generous
polynomial clock, membership in its range gives a description of length at
most `m+C_f`.
Keep the half-length incompressibility threshold and create sufficient
output-length slack to absorb C_f.

Write `f(x)=u||v`, with both blocks of length m, and define
`F(x)=f(u)||f(v)`. Then F maps m bits to 4m bits. Formalize the implication
that surjectivity of f at length m implies surjectivity of F at that length:
choose preimages of the two desired output blocks, then a preimage of their
concatenation. This requires three calls to f and finitely many existential
witnesses.

An output of F has a description of length `m+C_F`. For sufficiently large
m, this is at most 2m, so an Inc_c witness at output length 4m cannot be in
the range of F, provided c covers the simulation time. Use this to derive
the fixed-stretch non-surjectivity statement. Handle the finite remaining
lengths separately.

Repeat with a fixed auxiliary input z throughout the construction, using
CInc_c and its combined-input clock. Prove the resulting statements first
for length-respecting string functions, then establish whatever translation
to numeric interval principles is required.

**First deliverable:** checked fixed-stretch reverse implications, with all
constants, clocks, parameters, and finite exceptions accounted for.

### Priority Target: Conditional Separation

Before attempting full-schema conversions, check whether the decoder and a
single Eval reversal suffice to transfer ILW23 Theorem 24:

1. Establish the Step 1 forward proof that UAPC_1 proves every
   length-universal Inc_c sentence.
2. Take Eval with a circuit description z as auxiliary input, restricted to
   circuits mapping m bits to 4m bits. A range output has a U description
   of length m + O(1), with z supplied separately. Prove in PV_1 that a
   CInc_c witness of length 4m avoids that range, for one fixed c covering
   evaluation and universal simulation. Check malformed encodings, finite
   small lengths, and the exact translation to ILW23's Eval schema.
3. Apply ILW23's unprovability of this fixed-stretch Eval principle in
   UAPC_1, under the hypotheses in Section 2. If the two bridges are
   checked, then PV_1 + {Inc_c} is a subtheory of UAPC_1 and so cannot
   prove CInc_c for the fixed c used in bridge 2. This is a single-sentence
   unprovability result, stronger than failure to prove the whole schema.

**Deliverable and decision:** a short conditional-separation proof note with
the two bridges, exact imported theorem, and novelty status. This can be a
standalone endpoint; neither full equivalence below is required. If a bridge
is unresolved, retain the checked lemmas and identify its precise obligation
rather than claiming a separation. Assess this result before extending scope.

### Optional Extension: Full-Schema Target

Test the following equivalences over PV_1, using the exact schemata in
Section 2:

```text
{ forall n in Log, n >= 4 -> Inc_c(n)  : c >= 1 } <=> dWPHP'(PV)

{ forall n in Log, n >= 4 -> CInc_c(n) : c >= 1 } <=> dWPHP(PV)
```

These are candidate equivalences between theories over a common base.
Prove or locate each remaining stretch conversion rather than identifying
the fixed-stretch result with the full schema.

1. Map the proved string versions to doubling and squaring cardinalities.
2. Attempt the missing conversions to the near-equal-cardinality schema,
   separately with and without function parameters.
3. For any variable-depth construction, bound runtime in terms of the
   complete output length and identify the induction or collection used
   to prove surjectivity. A depth-i expansion writes `2^i m` bits.
4. If a proof requires S^1_2, establish that comparison result and isolate
   the exact use of stronger reasoning. Investigate its elimination as a
   separate task.

Only after these steps, test sensitivity to other integer description bounds,
such as `n-ceil(log_2 n)`. Compute the resulting domain size each time. A
bound of n-1 includes every description shorter than n and gives a tight
counting gap rather than a weak one.

**Decision:** each full equivalence would characterize the corresponding
theory; both would also give the conditional separation above. If only
fixed-stretch or stronger-base results are obtained, state those precisely.
An unsuccessful conversion is an unresolved step, not evidence that the
principles are inequivalent.

**Deliverable:** a short proof note containing the strongest checked result,
its source dependencies, and a sharply stated remaining question. Assess
novelty before considering publication.

## 6. Step 3: Audit and Formalize Liu-Pass in APC_1

Treat this as a separate follow-on after completing a coherent result or
learning exercise in Steps 1 and 2. Existence of incompressible strings is
not the same claim as hardness of computing their complexity.

A one-way function is polynomial-time computable but infeasible to invert
with non-negligible success probability for probabilistic polynomial-time
attackers. Mild average-case hardness of K^t means that some inverse-polynomial
error rate defeats every such heuristic on uniformly random n-bit strings,
for all sufficiently large lengths. Match the exact quantifier order,
randomness, and machine conventions in the theorem being formalized.

The target is an APC_1 proof of the equivalence between existence of one-way
functions and mild average-case hardness of K^t for some polynomial t.

1. Read [Liu-Pass, On One-way Functions and Kolmogorov Complexity](https://arxiv.org/abs/2009.11514),
   Sections 2-5. Write finite, resource-bounded versions of the security and
   hardness assertions suitable for arithmetic. Choose uniform or nonuniform
   adversaries explicitly and keep that choice fixed throughout.
2. Audit Section 4, Theorem 4.1: hardness of K^t yields a weak one-way
   function through program evaluation and a counting argument. Formalize
   this reduction first, with explicit loss in success probability.
3. Audit the weak-to-strong one-way-function amplification separately.
4. Audit Section 5: one-way functions yield K^t hardness through conditionally
   entropy-preserving pseudorandom generators. List and formalize the needed
   hashing, entropy, counting, and security-reduction lemmas.
5. Record the weakest theory actually used for each lemma. If APC_1 does not
   suffice for an available proof, identify the precise missing ingredient
   or stronger theory rather than claiming unprovability.

**Deliverable:** a dependency table followed by formalized reductions, one
direction at a time. Continue to a full equivalence only if the dependencies
fit the chosen theory and remaining budget.

## 7. Execution and Decision Points

The table describes the original gate structure; use the current handoff
in [step1_decoder.md](step1_decoder.md), Sections 6.7-6.8, for the immediate
execution order and deferred obligations. The optional extensions remain
choices, not prerequisites for completing the initial project.

| Gate | Next Action | Exit Deliverable |
| --- | --- | --- |
| A. Baseline | Complete Step 0 items 1-3; extract the decoder and exact ILW23 instance. | Source table and explicit proof obligations; reconstruct or stop if the target is already known. |
| B. Decoder | Prove full-dWPHP forward implications, then the unary decoder and simulation bounds. | Checked PV definitions and proofs, with any remaining gap isolated. |
| C. First payoff | Prove the fixed-stretch Eval reversal and test the two bridges in Section 5. | Conditional-separation note if both work; otherwise the strongest checked partial result. |
| D. Consolidate | Independently audit the note and check matching literature. | A coherent endpoint and an assessment of novelty, not an assumed publication. |
| E. Optional extension | Choose one precise full-schema conversion or the Step 3 Liu-Pass audit. | A further theorem, reconstruction, or dependency table; not a commitment to finish both programs. |

Before each gate or new proof attempt, record the target lemma and a time
cap. At the cap, continue only if there is a
checked new step or a sharper obligation supporting a bounded next attempt;
otherwise narrow or stop that branch. The researcher handles billing and
the Section 1 budget; no assistant-maintained spending ledger or balance
reconciliation is required. Record results against the outcome tree below.

Learn additional bounded-arithmetic tools when a specific proof obligation
requires them; use Krajicek's *Proof Complexity* (2019) and Buss's *Bounded
Arithmetic* (1986) as references rather than prerequisite reading in full.

Use AI for locating sources, checking encodings, developing candidate proofs,
and adversarial review. Require an explicit argument or a traceable theorem
for every implication. Before accepting a result, recheck its quantifiers,
description lengths, simulation time, parameter use, and base theory
independently of the prose that proposed it.

## 8. Possible Outcomes and Their Implications

### Best, Worst, and Expected

| Outcome | Research Result | Value and Implications |
| --- | --- | --- |
| **BEST** | The conditional separation (2g) is checked and new, and at least one full-schema equivalence (2b or 2c) or a nonimplication (2f) is also proved; a further success could formalize Liu-Pass in APC_1. | Potentially publishable specialist advances connecting bounded arithmetic, complexity, and cryptography. Any new stretch theorem could have independent value, once its reductions and novelty are checked. Not a P versus NP breakthrough. |
| **WORST** | The available budget is spent without a useful new theorem, checked reconstruction, or sharply isolated proof obligation. | No publication and poor research leverage. The time caps are intended to prevent prolonged unproductive attempts. Finding a known result early is a useful exit, not this worst case. |
| **EXPECTED (TENTATIVE)** | Reconstruct forward implications, obtain some fixed-stretch results, and identify remaining obligations. Test the conditional-separation route as the first potential new result; if Step 3 is attempted, budget initially for an audit rather than a full formalization. | Useful technical progress, with publishability depending on actual novelty and completeness. Full-schema equivalences and a full Liu-Pass formalization are ambitions, not expected deliverables. This is a working planning assumption, not a consensus forecast or numerical probability. |

### Outcome Tree

```text
Literature baseline
|-- Exact target known -> reconstruct or stop (0a): useful early exit
`-- Missing implications or translations identified (0b)
    |-- Decoder proofs stall -> partial note and precise gap (1b)
    `-- Forward proofs checked (1a)
        |-- Eval reversal stalls -> retain fixed-stretch results, if any (2a)
        `-- Eval reversal and ILW23 bridge checked -> conditional separation (2g)

Audit novelty and consolidate any coherent endpoint above; stop or extend:
|-- Full schemata -> equivalence(s) (2b/2c), stronger base (2d),
|                   unresolved conversion, or nonimplication (2f)
`-- Liu-Pass -> known (3a), partial/audit (3b/3c), or full (3d)

At any stalled branch: apply the time/spend cap, preserve checked work,
and narrow or stop. Exhaustion without a useful deliverable is WORST.
Reconstruction/partial results are the EXPECTED baseline; genuinely new,
substantial completed results lead toward BEST, subject to novelty review.
```

Use these labels at the Section 7 reviews to record established results and
remaining obligations, not predicted success rates. Outcomes can coexist.
Here `{Inc_c}` and `{CInc_c}` denote the full length-universal schemata in
Section 5, with c ranging over standard positive integers, not a single
clock exponent. Target implications remain conditional on their checked
proofs and exact source conventions.

### Step 0

- **0a. Exact target already known.** Reconstruct a useful proof and record
  its conventions and dependencies. A checked reconstruction is a valid
  stopping point or preparation for Step 3, without a novelty claim.
- **0b. Only part of the target located.** Identify the precise missing
  implication or translation. A search without a matching result leaves
  novelty and current open-problem status unverified.

### Step 1

- **1a. Both forward directions proved.** Establishes UAPC_1 as sufficient
  for `{Inc_c}` and APC_1 as sufficient for `{CInc_c}`. Necessity still
  requires reversals.
- **1b. One or both forward proofs incomplete.** Record the established
  implication and the unresolved encoding or arithmetic step. Failure to
  remove a hidden length parameter does not show that UAPC_1 cannot prove
  Inc. The hard-function theorem alone does not supply the missing proof:
  high circuit complexity implies the required time-bounded description
  complexity only if an appropriate quantitative reduction is established.

### Step 2

- **2a. Fixed-stretch results only.** Record each implication for the exact
  string or interval schema, including parameters and clocks. Claim an
  equivalence only when both directions are checked. Such results identify
  a counting principle captured by incompressibility, but do not yet
  characterize UAPC_1 or APC_1 with the full near-equal-cardinality schema.
- **2b. Full parameterized equivalence: {CInc_c} <=> dWPHP(PV) over PV_1.**
  Would characterize APC_1 as PV_1 plus conditional incompressibility.
  Carrying a and b in z resolves access to parameters, not the induction
  or collection needed for stretch amplification. Verify those obligations
  over PV_1 rather than importing a stronger-base conversion.
- **2c. Full parameter-free equivalence: {Inc_c} <=> dWPHP'(PV) over PV_1.**
  Would similarly characterize UAPC_1 using ordinary incompressibility.
  Any resulting stretch equivalence must specify both endpoint schemata
  and the checked reductions. PS21 Section 2.1's unresolved equivalence
  concerned parameter elimination, not stretch conversion; ILW23 later
  conditionally separates those parameterized and parameter-free theories.
  Neither citation establishes the current status of this stretch target.
- **2d. Reversal obtained only over S^1_2.** Record the comparison theorem
  and the stronger reasoning used in its proof. Parameterized and
  parameter-free dWPHP are equivalent over S^1_2, as PS21 records, but
  translating the exact Inc statements remains a proof obligation.
  Using stronger induction does not prove that PV_1 cannot avoid it.
- **2e. Sanity check.** A derivation of `{Inc_c} => {CInc_c}` over PV_1,
  combined with both full equivalences, would contradict the conjunction
  of ILW23's hypotheses. Require independent scrutiny of the reductions
  and assumptions before accepting such a conclusion.
- **2f. Genuine nonimplication proved.** A model or unprovability argument,
  with any assumptions stated, could refute a target equivalence and locate
  a real difference in proof strength. An unsuccessful proof attempt is
  not such an argument. Nonprovability in a weak theory would concern proof
  strength, not failure of finite counting in the standard model.
- **2g. Conditional separation from fixed-stretch proofs.** Completing the
  priority target in Section 5 would show, under ILW23's hypotheses, that
  ordinary incompressibility does not suffice to prove conditional
  incompressibility over PV_1. This is a concrete potential contribution
  before full-schema equivalences; its novelty remains to be assessed.

### Consequences and Limits

- **Which unprovability transfers.** A PV_1/APC_1 separation transfers
  through 2b to failure of PV_1 to prove all of `{CInc_c}`. Neither that
  separation nor UAPC_1/APC_1 separation alone establishes unprovability
  of `{Inc_c}`: PV_1 = UAPC_1 < APC_1 is compatible with those separations.
  Ordinary Inc unprovability needs a separate argument or hypothesis.
- **Propositional proof complexity.** Equivalences of existence schemata
  transfer arithmetic provability, not automatically EF hardness of
  tautologies asserting that a particular string is incompressible or
  outside a range. Incompressibility formulas can encode range exclusion
  for a bounded universal decoder, but hardness transfers require explicit
  proof transformations and fixed parameters. An identification with a
  particular proof-complexity-generator conjecture is a separate target.
- **Provability and explicit construction.** For a sufficiently large fixed
  c, a PV_1 proof of length-universal Inc_c would yield an FP^NP construction
  via KPT witnessing: NP search can supply the counterexample descriptions
  to a constant-round Student. At table length N, circuits of size N^(1/2)
  have descriptions of O(N^(1/2) log N) bits and their tables can be printed
  in polynomial time in N. Choosing c to cover this simulation makes Inc_c
  witnesses hard truth tables. At N = 2^m, constructing and indexing them
  gives an E^NP language requiring ordinary circuits larger than 2^(m/2)
  for all sufficiently large m. Spell out the machine bounds when using
  this consequence. Korten's Theorems 9-10 then connect hard-table
  construction with Empty; Theorem 6 alone reduces incompressibility
  construction to Empty, not conversely. No full Step 2 equivalence is
  needed here, and separate proofs for different c need not yield a
  uniform runtime bound across c.

### Step 3

- **3a. Exact formalization already known.** Reconstruct it or stop with a
  source map, checking the base theory and security conventions.
- **3b. One direction formalized; the other unresolved.** Gives a checked
  reduction and a concrete list of missing lemmas, not an unprovability
  result. P-definability of inverter success does not settle Theorem 4.1:
  Liu-Pass also compare the size of a set where a heuristic disagrees with
  K^t. Audit that comparison and weak-to-strong amplification as well as
  the reverse direction's hashing, entropy, and generator dependencies.
- **3c. Bounded formalization or counting estimates unresolved.** Exact
  K^t correctness has an immediate definition as a conjunction of a
  Sigma^b_1 condition and a Pi^b_1 condition; it is not known to be
  P-definable in general. This is not an expressibility barrier for APC_1.
  Jerabek 2007, Definitions 2.8 and 2.20, allow size and probability
  comparisons for definable sets more generally than the counting-circuit
  theorem. Section 4 supplies stronger, relativized counting tools, with
  APC_2 covering P^NP predicates, but does not establish their necessity
  for Liu-Pass or formalize its full proof. A shortest-program output
  still requires checking that no shorter program works; it does not make
  exact success P-checkable. Any changed hardness formulation needs its
  own equivalence proof. The outcome is a precise remaining obligation or
  a checked stronger-base result, not a claim that APC_1 is insufficient.
- **3d. Both directions in APC_1.** Provability and unprovability results
  for either precise assertion transfer to the other over APC_1.
  Witnessing requires a suitable finite search statement of the prescribed
  syntactic form; it does not apply automatically to the full cryptographic
  equivalence. The result calibrates the proof strength of known reductions,
  not the truth of their hardness assumptions.

### Stopping and Scope

A reconstruction, fixed-stretch theorem, stronger-base theorem, or precisely
isolated proof obligation can each be a useful endpoint. Only 2b establishes
the full APC_1 characterization; 2a alone does not. Assess novelty and
publication value after checking the result, and feasibility from actual
time and token expenditure rather than predicted likelihoods.

Neither the target incompressibility equivalences nor a formalization of
Liu-Pass would by itself prove one-way functions exist, settle P versus NP,
or establish independence from ZFC. The program's direct payoff is a clearer
account of which weak-theory axioms and proof methods support these results.
