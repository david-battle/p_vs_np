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
- dWPHP′(PV) / dWPHP₀(PV): the *parameter-free* version, in which f may not
  take an extra parameter z. Ilango–Li–Williams (STOC 2023) show, under
  cryptographic assumptions (indistinguishability obfuscation), that
  PV₁ + dWPHP(PV) is strictly stronger than PV₁ + dWPHP′(PV).

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
because by ILW23 the existence of hard functions is provable in the weaker
PV₁ + dWPHP′(PV). Krajíček's proof-complexity-generator program (the
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

## 2. Two corrections to the naive formulation

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

## 3. Step 0 — Literature check (1–2 weeks, before proving anything)

Read, in this order:

- Jeřábek 2004, §3 (Lemma 3.2, Cor. 3.3, Lemma 3.4, Prop. 3.5) and §1
  (conventions for dWPHP, and the remark that the codomain ratio is
  inessential over S¹₂).
- CLO24, §2 (formal definitions of PV₁, WPHP, dWPHP, WPHP_WIT, and exactly
  how parameters and codomain sizes are handled), footnote 8, and the open
  problems section.
- Ilango–Li–Williams 2023, "Indistinguishability obfuscation, range
  avoidance, and bounded arithmetic" (STOC 2023): the separation of
  dWPHP(PV) from dWPHP′(PV), and precisely which formalization of "hard
  functions exist" falls on which side.
- Jeřábek, "Approximate counting in bounded arithmetic" (JSL 2007): the
  remark that dWPHP with codomain (1+1/n)a and with codomain a² are
  equivalent over S¹₂ but not known to be equivalent over PV₁.
- Krajíček, "Small circuits and dual weak PHP in the universal theory of
  p-time algorithms"; and the chapters on the truth-table generator and
  τ-formulas in Krajíček, *Proof Complexity* (Cambridge, 2019) and *Proof
  Complexity Generators* (Cambridge, 2024).
- Oliveira, "Meta-mathematics of computational complexity theory" (survey,
  2025), for the current map of what is formalized where.

Questions to answer from this reading:

- Does anyone state the K^t version explicitly, and over which base theory
  (S¹₂ or PV₁)?
- In ILW23, is the "hard functions" statement the parameter-free dWPHP of
  the truth-table function? If so, the K^t version is a small generalization
  and §4(a) is essentially theirs; the value is then in §4(b) and §6.
- Has anyone formalized Liu–Pass, or any OWF ⇔ meta-complexity equivalence,
  in APC₁ or a related theory?

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
- Threshold δ: 1/2 versus 1 − (log n)/n versus 1 − 1/n. Over S¹₂ these are
  interchangeable by Jeřábek's amplification; over PV₁ they may not be.
- Parameter-free (Inc) versus conditional (CInc).

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

- Statements about Jeřábek 2004 and CLO24 above were checked against the
  papers' text; the ILW23 details (exact hypotheses, exact formalization of
  "hard functions") and the claim that nobody has formalized Liu–Pass in
  bounded arithmetic are from memory and must be verified in Step 0.
- Conjectures (a) and (b) in §5 are plausible but unproven; the codomain-ratio
  issue over PV₁ could make them false as stated, which would itself be
  worth writing up.
