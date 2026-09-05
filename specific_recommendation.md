# Research plan: time-bounded incompressibility as a pigeonhole principle over PV₁

A concrete, self-contained plan for one problem in the "reverse mathematics of
complexity lower bounds": pin down which weak-pigeonhole principle the
statement "incompressible strings exist" is equivalent to over Cook's theory
PV₁, and then push from *existence* of incompressible strings toward
*hardness of computing* time-bounded Kolmogorov complexity, where the
connection to one-way functions (Liu–Pass) lives.

## 1. Background

**Theories.** PV₁ is Cook's first-order theory of polynomial-time reasoning:
one function symbol per poly-time algorithm, induction only for open
(quantifier-free) formulas. S¹₂ is Buss's theory (PV₁ plus polynomial
induction for NP-predicates); its provably total functions are exactly the
poly-time ones. APC₁ = PV₁ + dWPHP(PV) is Jeřábek's theory for probabilistic
polynomial-time reasoning.

**Pigeonhole principles.** For a poly-time function f (possibly with a
parameter z):

- WPHP(f): f cannot map [2a] injectively into [a] (injective weak PHP).
- dWPHP(f): a dual / surjective weak PHP. Keep its cardinality ratio
  explicit: [a] to [a²], [a] to [2a], and near-equal sizes are different
  formulations, not interchangeable by definition over PV₁ (see §5).
- WPHP_WIT(f): a witnessing variant used by Chen–Li–Oliveira.
- "Weak" includes a relative gap inverse-polynomial in the bit length, not
  just a large constant factor. The *tight* onto-PHP (a vs a+1) must be
  distinguished from these weak principles.
- dWPHP′(PV) / dWPHP₀(PV): the *parameter-free* ("uniform") version, in
  which f may not take an extra parameter z. Pich–Santhanam (STOC 2021, §2.1)
  record equivalence with dWPHP(PV) over S¹₂ and, as of that paper, no known
  equivalence over PV₁. They also state that PV₁ + dWPHP′(PV) proves the
  existence of hard Boolean functions and Jeřábek's Nisan–Wigderson theorem,
  and that S¹₂ + dWPHP(PV) is ∀Σ^b₁-conservative over this theory. The checked
  STOC version uses the prime notation; the superscript zero occurs in
  T⁰_APC₁ = T_PV + dWPHP′(PV), where T_PV is the true universal PV theory.
- Ilango–Li–Williams (STOC 2023, "ILW23"), §4.3, Theorem 24 explicitly
  separates APC₁ from UAPC₁ = PV₁ + dWPHP′(PV), assuming **JLS-secure iO
  and coNP ⊄ i.o.NP/poly**. In fact, T⁰_APC₁ does not prove dWPHP_ℓ(Eval)
  for any constructive bit-length stretch n < ℓ(n) ≤ poly(n). The witnessing
  argument uses polynomial-size circuits rather than uniform algorithms;
  the nonuniform lower-bound assumption is essential to the stated result.
  This is the theorem cited by CLO24 footnote 8, not merely an inference
  from ILW23's separation of PV₁ and APC₁.
- Ren–Wang–Zhong (ITCS 2026) obtain a PV₁ vs APC₁ separation from demi-bits
  generators secure against AM/O(1). This is an alternative hypothesis,
  not a separation known from ordinary one-way functions alone.

For the target schemata below, use the PS21 / ILW23 near-equal-cardinality
form, with b ∈ Log supplying a unary-sized ratio parameter:

    dWPHP(f): ∀a>0 ∀b∈Log ∀z ∃v<a(b+1) ∀u<ab  f(u,z) ≠ v.

The primed version drops z and uses f(u); neither a nor b is an extra input
to f. A theorem about a different stretch must explicitly connect to this
schema before being called an equivalence with dWPHP′(PV) or dWPHP(PV).

**The reversal template.** Chen–Li–Oliveira, "Reverse mathematics of
complexity lower bounds" (FOCS 2024, "CLO24"), take PV₁ as base theory and
show that several textbook lower bounds (one-way communication complexity of
Equality and Set Disjointness, the Ω(n²) one-tape Turing machine bound for
Palindromes, bounds for error-correcting codes) are each *equivalent* over
PV₁ to a specific pigeonhole principle (WPHP(PV), WPHP′(PV), WPHP_WIT(PV)).
They close with the invitation to "find equivalences between your favorite
lower bound statement and a combinatorial principle."

**What is already known about the natural candidate.** Jeřábek, "Dual weak
pigeonhole principle, Boolean complexity, and derandomization" (Annals of
Pure and Applied Logic 129, 2004), Lemma 3.2 and Prop. 3.5: over S¹₂,
dWPHP(PV) is equivalent to the existence of Boolean functions of exponential
circuit complexity (Shannon's counting lower bound, made formal). CLO24
footnote 8 remarks that this equivalence is *unlikely to hold over PV₁*,
because the existence of hard functions is provable in the weaker
PV₁ + dWPHP′(PV), conditionally strictly weaker than APC₁ by ILW23
Theorem 24. Krajíček's proof-complexity-generator program (the
truth-table generator tt_{s,k}, whose range is the set of truth tables of
small circuits; and the τ-formulas asserting a string is outside a
generator's range) is the same object seen from propositional proof
complexity. Krajíček, "Small circuits and dual weak PHP in the universal
theory of p-time algorithms", shows that if P ⊆ SIZE(n^d) then the true
universal theory of p-time functions does not prove dWPHP(tt).

**Time-bounded Kolmogorov complexity.** Fix a universal machine U. K^t(x) is
the length of the shortest description d such that U(d) outputs x within
t(|x|) steps; K^t(x|z) allows auxiliary input z. With n supplied in unary,
bounded simulation for polynomial t is a PV function. Turning it into a
total map to n-bit strings requires an encoding of descriptions and a
default output for failed or wrong-length simulations. There are 2^{m+1} − 1
descriptions of length ≤ m, not 2^m; encode them in m+1 bits, sending the
unused code to the default output. Liu–Pass (FOCS 2020): one-way functions
exist iff K^t is mildly hard on average for some polynomial t. Exact machine
and output conventions must be specified when comparing formalizations.

**The K^t existence statement is already studied; reversal status unverified.**
Korten (FOCS 2021, "The hardest explicit construction"), full version §3.5,
Theorem 6, reduces constructing strings with K^t(x) ≥ n−1 to Empty for
each fixed polynomial time bound. This is a search reduction; the checked
versions do not state a separate APC₁ provability theorem for these strings.
Carmosino–Grosser (ECCC TR25-045, "Student-Teacher Constructive Separations
and (Un)Provability in Bounded Arithmetic: Witnessing the Gap") attribute
the APC₁ consequence to Korten and state VAPC ⊢ HiKt[c] in Theorem 4.18.
Use **ECCC Revision 1, April 12, 2025** for the references here. Their
Formalization 4.1, over VPV (a two-sorted counterpart of PV₁), reads

    HiKt[c] := ∀n>n₀ ∃X(|X|=n) ∀D(|D|<n/2)  run(π₁(D), π₂(D), n^c) ≠ X

(one sentence per constant c). Their nearby matrix uses |D| ≤ n/2 and
Definition 4.3 uses K^{n^c}(X) > n/2, so the boundary convention needs
reconciliation. Their §2.7 uses two-part descriptions and simulated tape
contents after a bounded number of U steps, not simply a halting-output
definition. The translation to §4 below is therefore not yet complete.

Their Theorem 4.5 states that no n^c-time Student solves ∃HiKt[2c+1], using
self-referential descriptions to answer the Student's queries. Under their
respective poly-runtime-schema Witnessing Hypotheses 4.14 and 4.16,
Corollaries 4.15 and 4.17 give VPV and V¹ unprovability for infinitely many
c. These are conditional unprovability results, not consequences of the
Student bound alone. The older author-hosted PDF has a different exponent
in Theorem 4.5; do not mix versions. No HiKt-to-dWPHP reversal was located
in the checked revision. They mention a "weaker, uniform" dWPHP, but do not
give the proposed primed-schema classification. Their APC₁-unprovability
question concerns a different, possibly zero-error notion of complexity,
not the same HiKt schema already provable in VAPC.

## 2. Three corrections to the naive formulation

1. **Full incompressibility has a tight counting gap.** The statement
   "∃x ∈ {0,1}^n, K^t(x) ≥ n" excludes all 2ⁿ−1 descriptions shorter than
   n. This has the shape of a tight onto-PHP instance, not a weak one; it
   does not by itself establish equivalence to the full tight schema.
   Thresholds such as n/2 or n − log n give weak counting gaps, after fixing
   strict versus non-strict inequalities and the decoder encoding.

2. **The forward direction is counting; the converse still needs a proof.**
   Apply an appropriate dWPHP instance to the bounded decoder to obtain
   incompressible strings. Jeřábek's Prop. 3.5 suggests studying the converse
   through blockwise amplification of a hypothetical surjection. A depth-i
   binary expansion from m to 2^i m output bits has runtime polynomial in
   the output length (for fixed f), not polynomial in i·m in general.
   Variable-depth surjectivity arguments, parameter handling, and the base
   theory must be checked rather than declaring a K^t equivalence folklore.

3. **Description overhead requires a higher threshold or more output bits.**
   For a fixed parameter-free f: {0,1}^m → {0,1}^{2m}, its outputs satisfy
   K^t(f(u)) ≤ m + C_f for sufficiently large polynomial t. To exclude such
   outputs directly requires K^t(X) > m + C_f. Lowering the threshold to
   m − O(1), or choosing δ < 1/2 at output length 2m, makes the assertion
   weaker and does not fix the problem. Raising δ above 1/2 absorbs a fixed
   C_f for sufficiently large m. Alternatively, retain δ = 1/2 and increase
   output length to 4m, where the threshold 2m exceeds m + C_f. The
   fixed-depth construction in §5 shows how this latter slack can arise.

## 3. Step 0 — Literature check (1–2 weeks, before proving anything)

**Status (Sept 2026).** Targeted searches and primary-source checks establish
the following, without establishing that the proposed project is new:

- *Does anyone state a K^t existence principle?* Yes: Korten gives the
  search reduction; Carmosino–Grosser studies HiKt[c] over VPV and states
  provability in VAPC. No matching reversal has been located; **novelty is
  unverified**, not established by its absence from those papers. The
  conditional schema, encodings, and one-sorted translation still need work.
- *ILW23 and the parameter-free principle?* Theorem 24 explicitly gives the
  separation, with the hypotheses recorded in §1. PS21 §2.1 states the
  hard-function and conservativity facts, and its §3.1, Theorem 4 supplies
  the nonuniform witnessing used by ILW23. CLO24's bootstrapping Lemmas
  2.16–2.18 cover WPHP, WPHP′ and WPHP_WIT, not dWPHP; their omission alone
  is not evidence of a new separation between stretch variants.
- *Has anyone formalized Liu–Pass in APC₁?* No such formalization was
  located in the targeted searches. Nearby work: Pich–Santhanam 2023 ("Towards
  P ≠ NP from Extended Frege lower bounds") formalizes OWF-related reductions
  in S¹₂ + dWPHP(PV); Pich–Santhanam 2021 shows T⁰_APC₁ cannot prove Rudich
  super-bits exist. Absence of a search hit is weak evidence.

**Operating constraint.** Defer outreach unless explicitly authorized. Work
from public literature, with a planned AI-token expenditure below $1000 plus
the researcher's own time. Accept some risk of duplicating known work, and
avoid premature disclosure. Lack of a search hit is not confirmation of a gap.

Read targeted sections in this order; the broader references are context,
not a requirement to read every paper or book in full:

- [Carmosino–Grosser, ECCC Revision 1](https://eccc.weizmann.ac.il/report/2025/045/revision/1/download),
  §2.7 (K^t conventions), §4 (HiKt[c], Prop. 4.4, Thm. 4.5 and the
  reflection-template proof, Hypotheses 4.14/4.16, Thm. 4.18), and §1.7
  (open problems). Reconcile the threshold and machine conventions in §1.
- [Korten, full version v3](https://arxiv.org/pdf/2106.00875v3), §3.5,
  Definition 14 and Theorem 6. The conference version's corresponding
  informal statement is Theorem 7 in §III.E. Identify the decoder instance
  and write out the bounded-arithmetic consequence instead of attributing
  an explicit APC₁ theorem to Korten's text.
- [CLO24](https://www.dcs.warwick.ac.uk/~igorcarb/documents/papers/CLO24.pdf),
  §2.4 (Defs. 2.5–2.7, 2.13; Lemmas 2.16–2.18), footnote 8, §1.4 (open
  problems), §6.2 (WPHP_WIT and ∀Σ^b₁-conservativity).
- [Pich–Santhanam 2021](https://users.ox.ac.uk/~coml0742/papers/stoc-final.pdf),
  "Strong co-nondeterministic lower bounds for NP cannot be proved feasibly",
  §2.1 for dWPHP′(PV) and T⁰_APC₁; §3.1, Theorem 4 for witnessing with
  nonuniform advice.
- [Ilango–Li–Williams 2023](https://eccc.weizmann.ac.il/report/2023/038/download),
  §4.3, equation (7) and Theorem 24; §2.1 for JLS security; Remark 14 for
  stretch conventions; Appendix D for hard truth tables in UAPC₁.
- [Ren–Wang–Zhong](https://arxiv.org/abs/2511.14061), "Hardness of range
  avoidance and proof complexity generators from demi-bits" (ITCS 2026):
  a different sufficient hypothesis for separating APC₁ from PV₁. Keep the
  required security against AM/O(1) explicit.
- Jeřábek 2004, §3 (Lemma 3.2, Cor. 3.3, Lemma 3.4, Prop. 3.5) and §1
  (conventions for dWPHP, and the remark that the codomain ratio is
  inessential over S¹₂).
- [Jeřábek, "Approximate counting in bounded arithmetic"](https://users.math.cas.cz/~jerabek/papers/apx.pdf)
  (JSL 2007), §1: equivalence over S¹₂ between the near-equal-cardinality
  schema and the squaring schema, with the PV₁ reduction left unclear.
  Follow subsequent citations before treating this as a current open problem.
- Krajíček, "Small circuits and dual weak PHP in the universal theory of
  p-time algorithms"; and the chapters on the truth-table generator and
  τ-formulas in Krajíček, *Proof Complexity* (Cambridge, 2019) and *Proof
  Complexity Generators* (Cambridge, 2024).
- Oliveira, "Meta-mathematics of computational complexity theory" (SIGACT
  News, 2025), §6 in particular, for the current map of what is formalized
  where and for any mention of Liu–Pass.

Remaining questions for this reading:

- Which exact decoder and PV₁ proof connect Korten's reduction to the
  unconditional existence schema, with the chosen threshold and output rule?
- Which equivalences between near-equal cardinalities, doubling, and squaring
  are proved over PV₁, separately for primed and parameterized schemata?
- Has a matching K^t reversal appeared under different terminology? Record
  exact statements found, not just whether a paper uses the notation HiKt.
- Any mention of Liu–Pass, or any OWF ⇔ meta-complexity equivalence, being
  formalized in APC₁ or related theories — in Oliveira's survey or in the
  citation trails of Pich–Santhanam 2023 and Carmosino–Grosser.

## 4. Step 1 — Fix the formal statement

Working definitions, for an integer constant c ≥ 1 and rational constant
δ ∈ (0,1), using a fixed efficient universal machine U:

    Inc_{c,δ}(n):  ∃x ∈ {0,1}^n  ∀d (|d| ≤ floor(δn) → U(d) does not halt with output x within n^c steps).

This is schematic string notation. In the one-sorted translation, supply
length bounds using n ∈ Log or an explicit unary input 1^n. With these
bounds, Inc is a Σ^b₂ formula with a poly-time matrix; its universal closure
over lengths is a ∀Σ^b₂ sentence. The candidate conditional form is:

    CInc_{c,δ}(n):  ∀z ∃x ∈ {0,1}^n ∀d (|d| ≤ floor(δn) → U(d,z) does not halt with output x within (n+|z|+1)^c steps).

The conditional clock now depends on the auxiliary-input length: a general
PV function f(z,u) runs in time polynomial in |z|+|u|, not in |u| alone.
The earlier n^c-clock definition would instead restrict which parts of an
arbitrarily long z could be used. These are different candidates; no
equivalence between them is being assumed. The combined-input clock is
intended for comparison with the parameterized dWPHP schema.

Decisions to record explicitly, because each affects which principle you land
on:

- Base theory PV₁ (to match CLO24), not S¹₂.
- Time exponent c: an external index of a schema, not a quantified exponent
  inside a single PV₁ sentence. This is also how HiKt[c] is indexed.
- Threshold: start with floor(n/2), including the endpoint. Other thresholds
  require an explicit integer-valued bound s(n). In particular, s(n)=n−1
  excludes all descriptions shorter than n and returns to the tight counting
  gap; do not assume it interchangeable with weak thresholds over S¹₂.
  For the direct reversal, absorb C_f by raising the threshold or increasing
  output length, never by lowering the threshold at the same output length.
- Parameter-free (Inc) versus conditional (CInc), including the latter's
  dependence on |z| in its clock.
- Encoding: fix two-part descriptions, a halting/output rule, and a precise
  simulation clock. Compare these with Carmosino–Grosser §2.7 rather than
  assuming equality with their tape-contents convention. Preserve leading
  zeros and encode all short descriptions when building the total decoder.
- Length cutoff: take an explicit fixed n₀ large enough for the chosen
  threshold's rounding and weak counting gap (n₀ ≥ 4 suffices for the
  half-length decoder encoding described here). Handle finite exceptions
  separately and record any changes of cutoff in a reduction.

Warm-up: write out dWPHP(PV) ⊢_{PV₁} ∀n∈Log (n≥n₀ → Inc_{c,1/2}(n)),
including the decoder's input encoding, clock, and default output. Then
compare the primed instance and the conditional version, and check whether
Jeřábek's Lemma 3.2 adapts. Learn the KPT witnessing theorem
(Krajíček–Pudlák–Takeuti 1991) and Buss's witnessing as needed for the
reversal and unprovability arguments.

## 5. Step 2 — The target theorem

Candidate equivalences over PV₁, not established results or verified new
open problems. Fix n₀ as in §4 and interpret "for all c" as a schema over
standard integer constants:

- (a) {∀n∈Log (n≥n₀ → Inc_{c,1/2}(n)) : c≥1} ⇔ dWPHP′(PV).
- (b) {∀n∈Log (n≥n₀ → CInc_{c,1/2}(n)) : c≥1} ⇔ dWPHP(PV).

Use the near-equal-cardinality schemata fixed in §1. An equivalence for
square-size codomains alone would not establish either target as written.
The intuition for the split is that a fixed function's code has constant
description length, whereas an unbounded auxiliary string does not. This
motivates conditional complexity but does not prove the reductions: coding
overhead, clocks, length bounds, and stretch must all be accounted for.

If both hold with these exact schemata, ILW23 Theorem 24 would imply, under
JLS-secure iO and coNP ⊄ i.o.NP/poly, that the unconditional existence
schema is strictly weaker over PV₁ than the conditional one. This is a
conditional consequence of the proposed equivalences, not a result yet.

**Separate cardinalities from bit lengths.** For a=2^m:

| Domain and codomain sizes | Input and output bit lengths |
| --- | --- |
| a and 2a | m and m+1 |
| a and a² | m and 2m |
| a and a⁴ | m and 4m |

The passage from m→4m to m→2m bit-length instances is not the claimed
parameter obstacle. For f: {0,1}^m → {0,1}^{2m}, write f(x)=u‖v with
|u|=|v|=m and define F(x)=f(u)‖f(v). If f were onto at this length, F
would be onto {0,1}^{4m}: choose preimages u,v of the desired two output
blocks, then a preimage x of u‖v. This uses three calls to f and finitely
many existential witnesses, with no variable-depth induction. For a
parameter-free length-respecting f, m is recovered from the input length;
no extra advice parameter is introduced. Formal string coding remains to
be written out, but this is not an unbounded amplification argument.

The relevant remaining question is which PV₁ proofs connect the squaring
schema to doubling or near-equal cardinalities, with and without function
parameters. Jeřábek 2007 leaves the near-equal-to-squaring equivalence over
PV₁ unclear; Step 0 must check later work. Fixed-depth block expansion does
not settle that question. Nor does failure of one amplification proof
establish inequivalence between thresholds. Compare the exact principles
before claiming a new separation or a classification indexed by δ.

Relation to Carmosino–Grosser: their results are unprovability (conditional
on a witnessing hypothesis) and a Student–Teacher lower bound; (a) and (b)
would address a complementary equivalence question. Their unconditional
Theorem 4.5 does not refute (a): it forbids a Student of time n^c for
∃HiKt[2c+1], whereas a PV₁-proof of HiKt[2c+1] would yield a Student whose
running time depends on the proof.

First deliverable: a precise statement and source/proof record for each
implication, including unresolved steps. A short research note is a possible
later outcome only if substantive results are established and their novelty
checked. Outreach or publication remains subject to explicit authorization.

## 6. Step 3 — From existence to hardness (the higher-payoff target)

"Incompressible strings exist" is the Kolmogorov analogue of Shannon's
counting bound: an existence statement, dWPHP-shaped. It is a different lower
bound from "K^t is hard to *compute*" (MK^tP ∉ P/poly, or Liu–Pass's "K^t is
mildly hard on average"). Only the second connects to one-way functions.

Target question: **does APC₁ prove the Liu–Pass equivalence
"OWFs exist ⇔ K^t is mildly hard on average"?** APC₁ supplies approximate
counting and tools for probabilistic reasoning, making it a candidate base.
That does not establish that it supports every ingredient of Liu–Pass.
Fix the formal hardness statements and audit the proof dependencies before
treating this as routine formalization. If it goes through:

- "One-way functions exist" and "K^t is mildly hard on average" become
  interchangeable *axioms* over APC₁, making precise the slogan that
  complexity lower bounds are axioms with far-reaching consequences.
- One can then ask the CLO24-style question for either: is "K^t is mildly
  hard on average" equivalent over PV₁ or APC₁ to any combinatorial principle,
  or does it sit strictly above all pigeonhole variants? A negative or
  conditional answer would itself be informative about why cryptographic
  hardness resists proof.
- It gives a template for trading the cryptographic hypotheses used in
  current unprovability results (CLO24, Krajíček) for meta-complexity ones.

Formalize in stages, following [Liu–Pass](https://arxiv.org/abs/2009.11514):
(i) §4, Theorem 4.1, hardness of K^t ⇒ a weak OWF, using program evaluation
and a counting argument; then account for the weak-to-strong OWF amplification;
(ii) §5, OWF ⇒ hardness of K^t, using conditionally entropy-preserving PRGs
and their analysis; (iii) check which axioms beyond PV₁ each stage uses,
and whether full or only parameter-free dWPHP suffices. Do not infer
APC₁-provability merely from the probabilistic vocabulary of the proof.

## 7. Prerequisites and budget

- Krajíček, *Proof Complexity* (2019): chapters on PV and S¹₂, the KPT
  witnessing theorem, dWPHP and APC₁, and proof-complexity generators.
- Jeřábek's PhD thesis (Prague, 2005) for APC₁ and approximate counting.
- Buss, *Bounded Arithmetic* (1986), for the witnessing theorems.
- Korten, "The hardest explicit construction" (FOCS 2021); Carmosino–Grosser
  (ECCC TR25-045, 2025); Ren–Wang–Zhong (ITCS 2026) — the range-avoidance /
  K^t side and the current separations of APC₁ from PV₁.
- Liu–Pass, "On one-way functions and Kolmogorov complexity" (FOCS 2020), and
  follow-ups, for §6.

The background may require months of reading, but no new theorem or paper
is promised. Prioritize the narrow questions in Step 0 within the operating
constraint in §3. Reconstructing a known result can still be a useful outcome.

## 8. What to skip for now

Other CLO24-style candidates (parity formula lower bounds, Inner Product
communication complexity, time–space tradeoffs) are reasonable calibration
exercises but dilute the effort. Keep scope on §3–§5; §6 is a possible later
direction, not a promised paper.

## 9. Caveats

- The targeted primary-source checks cover ILW23 §4.3, PS21 §2.1 and its
  witnessing argument, Korten's reduction, the pinned Carmosino–Grosser
  revision, CLO24's cited material, and the directions of Liu–Pass. They
  are not complete independent verifications of those papers' proofs.
- Korten's search reduction and Carmosino–Grosser's APC₁ attribution are
  distinct claims. The local formalization still needs a decoder construction
  and a translation between the machine, boundary, and theory conventions.
- No matching K^t reversal or APC₁ formalization of Liu–Pass has been located
  in this search. Neither absence nor novelty has been established. Continue
  from public sources without outreach unless explicitly authorized.
- The target equivalences in §5 remain unproved. In particular, the
  conditional clock was changed to depend on auxiliary-input length, and
  the exact stretch schemata still matter. Failure of a proposed proof does
  not by itself yield a counterexample, separation, or publishable result.
