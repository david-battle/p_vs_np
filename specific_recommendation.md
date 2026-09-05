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
- dWPHP(f): f cannot map [a] onto [a²] (or onto [2a], or onto [(1+1/n)a] —
  see §4 on why the ratio matters). Dual / surjective weak PHP.
- WPHP_WIT(f): a witnessing variant used by Chen–Li–Oliveira.
- "Weak" means the domain and codomain differ by a large factor. The *tight*
  onto-PHP (a vs a+1) is a much stronger principle, not expected provable in
  bounded arithmetic at all.
- dWPHP′(PV) / dWPHP₀(PV): the *parameter-free* ("uniform") version, in
  which f may not take an extra parameter z. Pich–Santhanam (STOC 2021, §2.1)
  record the basic facts: dWPHP(PV) and dWPHP₀(PV) are equivalent over S¹₂
  but not known to be over PV₁; PV₁ + dWPHP₀(PV) already proves that hard
  Boolean functions exist and Jeřábek's Nisan–Wigderson theorem; and
  S¹₂ + dWPHP(PV) is ∀Σ^b₁-conservative over PV₁ + dWPHP₀(PV). CLO24
  (footnote 8, verified verbatim) attribute to Ilango–Li–Williams (STOC 2023)
  the claim that, under indistinguishability obfuscation, PV₁ + dWPHP(PV) is
  strictly stronger than PV₁ + dWPHP′(PV). ILW23's own abstract and §4 state
  only dWPHP(Eval) ⊬ in PV₁ (via KPT over T_PV); whether ILW23 itself treats
  the primed theory or CLO24 is glossing is still to be checked (Step 0).
  Ren–Wang–Zhong (ITCS 2026) reprove the PV₁ vs APC₁ separation from
  demi-bits generators, a Minicrypt-flavoured assumption in place of iO.

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
PV₁ + dWPHP′(PV), which (they say, citing ILW23) is conditionally strictly
weaker than PV₁ + dWPHP(PV). Krajíček's proof-complexity-generator program (the
truth-table generator tt_{s,k}, whose range is the set of truth tables of
small circuits; and the τ-formulas asserting a string is outside a
generator's range) is the same object seen from propositional proof
complexity. Krajíček, "Small circuits and dual weak PHP in the universal
theory of p-time algorithms", shows that if P ⊆ SIZE(n^d) then the true
universal theory of p-time functions does not prove dWPHP(tt).

**Time-bounded Kolmogorov complexity.** Fix a universal machine U. K^t(x) is
the length of the shortest description d such that U(d) outputs x within
t(|x|) steps; K^t(x|z) allows advice z. For polynomial t, "U^t restricted to
descriptions of length ≤ m" is a poly-time function {0,1}^m → {0,1}^n, hence a
PV function symbol. Liu–Pass (FOCS 2020): one-way functions exist iff K^t is
mildly hard on average for some polynomial t.

**The K^t statement is already in the literature — without the reversal.**
Korten (FOCS 2021, "The hardest explicit construction") reduces constructing
high-K^poly strings to the range-avoidance problem; Carmosino–Grosser (ECCC
TR25-045, April 2025, "Student-Teacher Constructive Separations and
(Un)Provability in Bounded Arithmetic") attribute to Korten the result that
APC₁ proves high-K^{n^c} strings exist for every c, each proof invoking
dWPHP(U_d) for the n^d-step universal-machine function symbol (attribution
not yet checked against Korten's text). Carmosino–Grosser then formalize, over
VPV (two-sorted PV₁), the schema

    HiKt[c] := ∀n>n₀ ∃X(|X|=n) ∀D(|D|<n/2)  run(π₁(D), π₂(D), n^c) ≠ X

(one sentence per constant c; two-part machine/advice descriptions following
Liu–Pass §2.2) and prove: unconditionally, no n^c-time Student wins the
Student–Teacher game for ∃HiKt[2c+1], by a self-referential construction (a
machine that simulates the Student and answers its queries with copies of its
own code, so everything the Student proposes has a short description); and,
conditionally on a "Witnessing Hypothesis for Uniform Proofs" (a
Kreisel-conjecture analogue, no cryptography), VPV ⊬ HiKt[c] and even
V¹ (= S¹₂) ⊬ HiKt[c] for infinitely many c, separating VAPC from V¹. They
prove **no reversal** (HiKt ⇒ any dWPHP variant), never mention the
parameter-free principle, and leave open extending unprovability to APC₁
(they expect a zero-error K^t is needed). Their HiKt[c] is §4's
Inc_{c,1/2}(n) up to encoding; adopt their conventions.

## 2. Three corrections to the naive formulation

1. **"∃x, K^t(x) ≥ |x|" is the wrong principle.** It says the 2ⁿ−1 short
   descriptions do not cover the 2ⁿ strings of length n: the *tight*
   onto-PHP, not a weak one. Relax to "K^t(x) ≥ |x|/2" (or |x| − log|x|).
   That is literally dWPHP(U^t) for U^t: {0,1}^{n/2} → {0,1}^n.

2. **Once relaxed, the plain equivalence is a near-corollary of Jeřábek.**
   dWPHP(PV) ⊢ "incompressible strings exist" is one line (apply dWPHP to
   U^t). The converse follows Jeřábek's Prop. 3.5 amplification argument with
   "circuit" replaced by "short program": a poly-time surjection
   {0,1}^m → {0,1}^{2m} iterates to a surjection onto {0,1}^{2^i m} computable
   in time poly(i·m), giving every string a short, fast description. Expect
   this to be folklore among specialists. The interesting content is entirely
   in the fine structure over PV₁ (§4) and in the move from existence to
   hardness (§6).

3. **Threshold exactly |x|/2 breaks even the trivial reversal, by an additive
   constant.** Given a parameter-free f: {0,1}^n → {0,1}^{2n} and X of length
   2n with K^t(X) > n, the description ⟨code_f, u⟩ of X = f(u) has length
   n + O(1), not n, so X may still lie in the range of f. Either state the
   incompressibility threshold as |x|/2 − O(1) (or a fixed δ < 1/2;
   Carmosino–Grosser's own introduction uses |x|/4), or aim the reversal at
   dWPHP′ with stretch 4 first and amplify afterwards (see §5).

## 3. Step 0 — Literature check (1–2 weeks, before proving anything)

**Status (Sept 2026).** A first web pass, plus a close read of CLO24 and
Carmosino–Grosser, answered the original three questions as follows:

- *Does anyone state the K^t version, and over which theory?* Yes:
  Korten 2021 (APC₁ proves it) and Carmosino–Grosser 2025 (HiKt[c] over VPV;
  unprovability results; no reversal). See §1. So §4 is essentially done by
  others, and the reversal in §5(a) is open and has an obvious home as the
  missing converse.
- *ILW23 and the parameter-free principle?* CLO24 footnote 8 says what this
  plan remembered it saying. Whether ILW23 itself proves the primed
  separation is unverified; Pich–Santhanam 2021 §2.1 is the cleaner primary
  source for dWPHP₀(PV) facts. Also from CLO24 §2.4: their weak principles
  use stretch a vs a(1+1/c), c ∈ Log; the primed versions simply drop the
  parameter argument; and their bootstrapping lemmas (stretch 1+1/c ≡
  stretch ≥ 2 over PV₁, Lemmas 2.16–2.18) are stated for WPHP, WPHP′ and
  WPHP_WIT but **not** for dWPHP — consistent with the codomain-ratio wrinkle
  in §5 being real.
- *Has anyone formalized Liu–Pass in APC₁?* No evidence from three searches
  with varied phrasing. Nearest neighbours: Pich–Santhanam 2023 ("Towards
  P ≠ NP from Extended Frege lower bounds") formalizes OWF-related reductions
  in S¹₂ + dWPHP(PV); Pich–Santhanam 2021 shows T⁰_APC₁ cannot prove Rudich
  super-bits exist. Absence of a search hit is weak evidence.

**Operating constraint.** Do not consult the research community during
Steps 0–2. Reasons: no publication record in this area, so outreach is
unlikely to be productive; the budget is small (well under $1000 in tokens
plus own time), so duplicating known work is a cheap risk; and no wish to
disclose the direction early. Confirm gaps from the literature only.

Read, in this order:

- Carmosino–Grosser 2025, §2.7 (K^t conventions), §4 (HiKt[c], Prop. 4.4,
  Thm. 4.5 and the reflection-template proof, the Witnessing Hypotheses
  4.14/4.16, Thm. 4.18), and §1.7 (open problems).
- Korten 2021, the section on bounded arithmetic: verify the claim that
  APC₁ ⊢ HiKt[c] and exactly which dWPHP instance is used.
- CLO24, §2.4 (Defs. 2.5–2.7, 2.13; Lemmas 2.16–2.18), footnote 8, §1.4
  (open problems), §6.2 (WPHP_WIT and ∀Σ^b₁-conservativity).
- Pich–Santhanam 2021, "Strong co-nondeterministic lower bounds for NP cannot
  be proved feasibly" (STOC 2021), §2.1: dWPHP₀(PV), its relation to
  dWPHP(PV), and the theory T⁰_APC₁.
- Ilango–Li–Williams 2023, §4 and Remark 14: check whether the primed theory
  is treated, and how the stretch m(n) is handled.
- Ren–Wang–Zhong, "Hardness of range avoidance and proof complexity
  generators from demi-bits" (ITCS 2026; arXiv 2511.14061): the demi-bits
  separation of APC₁ from PV₁, as a Minicrypt-flavoured alternative to iO.
- Jeřábek 2004, §3 (Lemma 3.2, Cor. 3.3, Lemma 3.4, Prop. 3.5) and §1
  (conventions for dWPHP, and the remark that the codomain ratio is
  inessential over S¹₂).
- Jeřábek, "Approximate counting in bounded arithmetic" (JSL 2007): the
  remark that dWPHP with codomain (1+1/n)a and with codomain a² are
  equivalent over S¹₂ but not known to be equivalent over PV₁.
- Krajíček, "Small circuits and dual weak PHP in the universal theory of
  p-time algorithms"; and the chapters on the truth-table generator and
  τ-formulas in Krajíček, *Proof Complexity* (Cambridge, 2019) and *Proof
  Complexity Generators* (Cambridge, 2024).
- Oliveira, "Meta-mathematics of computational complexity theory" (SIGACT
  News, 2025), §6 in particular, for the current map of what is formalized
  where and for any mention of Liu–Pass.

Remaining questions for this reading:

- Does Korten's text actually prove APC₁ ⊢ HiKt[c], with which encoding and
  threshold? (Carmosino–Grosser's attribution is second-hand here.)
- Does ILW23 itself separate PV₁ + dWPHP(PV) from PV₁ + dWPHP′(PV), or is
  that CLO24's inference? Does the KPT argument survive adding dWPHP′
  axioms (their witnesses depend only on n, so they act as advice, making
  the Student nonuniform — which assumption then covers it)?
- Is stretch amplification for the *parameter-free* dWPHP′ over PV₁
  addressed anywhere? (§5 argues this is the crux of conjecture (a).)
- Any mention of Liu–Pass, or any OWF ⇔ meta-complexity equivalence, being
  formalized in APC₁ or related theories — in Oliveira's survey or in the
  citation trails of Pich–Santhanam 2023 and Carmosino–Grosser.

## 4. Step 1 — Fix the formal statement

Define, for constants c ≥ 1 and δ ∈ (0,1):

    Inc_{c,δ}(n):  ∃x ∈ {0,1}^n  ∀d ∈ {0,1}^{≤δn}  U(d) does not output x within n^c steps.

This is a Σ^b₂ sentence in the language of PV₁ (an existential over x, a
bounded universal over d, a poly-time matrix). Its conditional form:

    CInc_{c,δ}(n):  ∀z  ∃x ∈ {0,1}^n  ∀d ∈ {0,1}^{≤δn}  U(d, z) does not output x within n^c steps.

Decisions to record explicitly, because each affects which principle you land
on:

- Base theory PV₁ (to match CLO24), not S¹₂.
- Time exponent c: a parameter; the statement is really a family, one per c.
  This matches Carmosino–Grosser's HiKt[c] schema exactly.
- Threshold δ: 1/2 versus 1 − (log n)/n versus 1 − 1/n. Over S¹₂ these are
  interchangeable by Jeřábek's amplification; over PV₁ they may not be. And
  per §2(3), exactly |x|/2 loses an additive constant against the code of f;
  use |x|/2 − O(1), or δ < 1/2, or absorb the constant into the stretch.
- Parameter-free (Inc) versus conditional (CInc).
- Encoding: follow Carmosino–Grosser §2.7 (two-part ⟨machine, advice⟩
  descriptions, a fixed efficient universal machine, time measured in steps
  of U) so that results are directly comparable with theirs.

Warm-up in the machinery: write out dWPHP(PV) ⊢_{PV₁} ∀n∈Log Inc_{c,1/2}(n)
in full, then redo Jeřábek's Lemma 3.2 with U^t in place of the truth-table
function. This is also the place to learn the KPT witnessing theorem
(Krajíček–Pudlák–Takeuti 1991) and Buss's witnessing, which every reversal in
this area uses.

## 5. Step 2 — The target theorem

Conjecture, over PV₁:

- (a) ∀n∈Log Inc_{c,1/2}(n) (for all c) ⇔ dWPHP′(PV), the *parameter-free*
  dual weak PHP.
- (b) ∀n∈Log CInc_{c,1/2}(n) (for all c) ⇔ dWPHP(PV), the *parameterized*
  dual weak PHP.

Why the split is natural: the universal machine absorbs the *code* of any
poly-time f into a constant-length prefix of the description, so every
parameter-free dWPHP(f) instance reduces to an Inc instance. It cannot absorb
an *advice string* z of unbounded length, so parameterized dWPHP(f(z,·))
needs the conditional form K^t(x|z).

Corollary if both hold: by ILW23, under iO-type assumptions, "unconditional
incompressible strings exist" is strictly weaker over PV₁ than "incompressible
strings exist relative to every advice". That is a clean, quotable
reverse-mathematics classification in CLO24's style, even if the proofs are
mostly assembly of known pieces.

Real technical wrinkle, and a genuine sub-question: since equivalence of
dWPHP across codomain ratios is not known over PV₁, the thresholds δ = 1/2 and
δ = 1 − (log n)/n may give PV₁-inequivalent statements. "How much
incompressibility is one dWPHP instance worth over PV₁?" is open and is the
kind of thing a first paper in this area can settle or at least sharpen.

The likely crux of (a), made concrete: from Inc with threshold δ one gets
dWPHP′ for stretch about 1/δ directly (a string outside the range of any
parameter-free f: {0,1}^{δn} → {0,1}^n). To reach dWPHP′(PV) as usually
stated one must then pass from "f: n → 4n is not onto at length n" to
"g: n → 2n is not onto at length n" *for the same n*. The standard
Jeřábek/Thapen amplification encodes the iterated composition in the
parameter, which dWPHP′ forbids; composing g with itself lands at other
lengths, and counting the range is exactly what PV₁ cannot do. So
"stretch amplification for the parameter-free dWPHP′ over PV₁" is either a
known lemma to be located in Step 0 or the first thing to prove or refute.
If it fails, (a) splits into a family indexed by stretch, and the honest
result is a classification of Inc_{c,δ} by δ.

Relation to Carmosino–Grosser: their results are unprovability (conditional
on a witnessing hypothesis) and a Student–Teacher lower bound; (a) and (b)
are the complementary equivalence. Their unconditional Theorem 4.5 is
consistent with (a): it forbids only a Student of time n^c for ∃HiKt[2c+1],
whereas a PV₁-proof of HiKt[2c+1] would yield a Student whose running time
depends on the proof.

Deliverable: a short note (10–15 pages) with §4's definitions, (a), (b), the
ILW23 corollary, and whatever can be said about thresholds. Venue: a logic or
complexity workshop / arXiv, in the style of CLO24's individual theorems.

## 6. Step 3 — From existence to hardness (the higher-payoff target)

"Incompressible strings exist" is the Kolmogorov analogue of Shannon's
counting bound: an existence statement, dWPHP-shaped. It is a different lower
bound from "K^t is hard to *compute*" (MK^tP ∉ P/poly, or Liu–Pass's "K^t is
mildly hard on average"). Only the second connects to one-way functions.

Target question: **does APC₁ prove the Liu–Pass equivalence
"OWFs exist ⇔ K^t is mildly hard on average"?** APC₁ is built for exactly the
probabilistic reasoning (approximate counting, amplification, hybrid
arguments) that the Liu–Pass proof uses, so the answer is plausibly yes and
the work is a careful formalization. If it goes through:

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

Formalize in stages: (i) the easy direction of Liu–Pass (OWF ⇒ hardness of
K^t) in APC₁; (ii) the harder direction (hardness ⇒ OWF, via a
pseudorandom-generator construction and a hybrid argument); (iii) check which
axioms beyond PV₁ were actually used, and whether dWPHP(PV) was needed in
full or only in the parameter-free form.

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

Budget several months of reading before the first new theorem. The community
(Krajíček, Jeřábek, Pich, Santhanam, Oliveira, Chen, Li, Hirahara, Ilango,
Williams) is small and very strong; the leverage for a newcomer is the K^t
framing and the meta-complexity bridge of §6, not raw technique.

## 8. What to skip for now

Other CLO24-style candidates (parity formula lower bounds, Inner Product
communication complexity, time–space tradeoffs) are reasonable calibration
exercises but dilute the effort. Keep scope on §3–§5, and let §6 be the
paper.

## 9. Caveats

- Statements about Jeřábek 2004, CLO24 (including footnote 8 and §2.4) and
  Carmosino–Grosser were checked against the papers' text. Still unverified:
  the ILW23 details (whether the primed theory is treated in ILW23 itself),
  Korten's APC₁ claim (known only via Carmosino–Grosser's attribution), and
  the Pich–Santhanam 2021 §2.1 facts about dWPHP₀(PV) (taken from a search
  excerpt, not the full paper).
- The claim that nobody has formalized Liu–Pass in bounded arithmetic rests
  on web searches only, and by the operating constraint in §3 will not be
  checked by asking anyone. Treat it as provisional.
- Conjectures (a) and (b) in §5 are plausible but unproven; the codomain-ratio
  issue over PV₁ (sharpened in §5 to stretch amplification for the
  parameter-free principle) could make them false as stated, which would
  itself be worth writing up.
