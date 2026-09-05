# P vs NP — Notes

Notes on the P vs NP question and its foundational surroundings, split off
from the `immortal_kangaroo_sequence` repo where the discussion grew out of
the Axiom of Choice example in the comma-sequence notes. It records the
reasoning, including the corrections the discussion forced.

## 1. AC framing (the motivation)

The discussion started from an Axiom of Choice example in the kangaroo notes.
The kangaroo is a crisp illustration of why one *might want* AC: it grants
non-constructive existence of the immortal path in the comma-sequence child
graph. The mirror-image argument *against* full AC is the **Banach–Tarski
paradox** and its engine, the **Vitali set**, where choice forces some subset
of the circle to have no well-defined length:

- Partition the unit circle by `x ~ y` iff one is a rational rotation of the
  other. Pick one representative per class (that's the AC move) to get a
  Vitali set `V`.
- Rational translates of `V` tile the circle; by additivity its "length" must
  equal a countable sum of equal terms, which is impossible unless it is 0 —
  yet a sum of 0s can't be the circle's circumference. So `V` is
  non-measurable. Banach–Tarski then reassembles a ball into two copies from
  finitely many such pieces.

Both examples are *consistent* facts about choice, not contradictions: ZF alone
doesn't settle them, and you may consistently add AC *or* "all sets are
Lebesgue measurable" (Solovay's model). The kangaroo proof needs only
**DC** (dependent choice), a weak fragment of AC, while Banach–Tarski needs a
stronger fragment. As the objects become more finite, choice goes from
essential (kangaroo/DC) → optional (Banach–Tarski) → irrelevant (P vs NP).

## 2. AC is irrelevant to P vs NP

- P vs NP is a statement about **finite objects**: "∃ TM M, ∃ polynomial p,
  ∀ x, M decides SAT within p(|x|)". It is a **Σ⁰₂ arithmetic sentence**.
- AC only governs infinite/high-cardinality set-theoretic operations; it never
  touches a finite computation. Arithmetic statements are **absolute**: their
  truth is fixed by ℕ alone, independent of the set-theoretic universe. So
  AC (or any fragment, even none) cannot change the truth of P=NP.
- **Shoenfield absoluteness**: every Σ¹₂ sentence (hence every arithmetic
  sentence) provable in ZFC is already provable in ZF. So no proof of P vs NP
  can essentially depend on choice. The door "prove it with choice but not
  without" is closed.
- Caveat: Shoenfield covers ZFC-vs-ZF only. *Beyond* ZFC, strong axioms can
  decide some arithmetic sentences (e.g. an inaccessible proves Con(ZFC), a
  Π⁰₁ sentence). Whether any natural large-cardinal axiom decides P vs NP is
  **genuinely open**.

## 3. Forcing is powerless; independence would be arithmetic, not CH-like

- P vs NP is **forcing-absolute** (arithmetic). Unlike CH, no forcing extension
  changes its truth. So if it is independent, the independence is *not*
  "CH-like" (a genuine choice about the set universe); it is **arithmetic
  incompleteness** — a failure of ZFC about the single structure ℕ, which has a
  determinate fact of the matter.
- This is the crux that separates P vs NP from AC/CH: AC and CH are
  **constitutional** choices about the shape of the set universe (both sides
  coherent and productive); P vs NP is a **matter of fact about ℕ**.

**Arithmetic independence is producible — but only by one route.** Forcing is
powerless, yet proof theory is not: Paris–Harrington is a Π⁰₂ sentence
independent of PA; Goodstein, Kruskal (Friedman), and Friedman's Boolean
relation theory give Π⁰₁/Π⁰₂ sentences independent of ZFC and provable from
large cardinals. Every such method works through **consistency strength /
fast-growing functions**: a true Π⁰₂ sentence `∀a ∃b φ(a,b)` is unprovable in a
sound theory T only if its Skolem function (least `b` for each `a`) outgrows
every T-provably-total function.

**Ben-David–Halevi (1991):** apply that to P≠NP = "∀(M,p) ∃x, M fails on x
within p(|x|)". The least counterexample would have to grow faster than anything
ZFC can prove total. Turned around: if P≠NP is unprovable in PA + all true Π⁰₁
sentences, then SAT is solvable in time `n^{f(n)}` for an `f` slower than any
provably-total function — "almost polynomial". So independence would not be a
neutral silence: it would mean P≠NP is **true but practically false**, with a
quantitative signature nothing in complexity theory hints at. This is the
strongest concrete reason the "prophetic independence" reading (§5) looks
unlikely. Reference: Aaronson, "Is P versus NP formally independent?" (2003).

## 4. "Make P ≠ NP a new axiom" — the case against and the correction

Initial (too-strong) claim: "We resolve matters of fact by proof, not by
amendment." **This is false, and Gödel's G refutes it**: G is a true, Π⁰₁,
arithmetic matter of fact, unprovable in PA, resolvable only by moving to a
stronger system (PA + Con(PA), or ZFC). So amendment genuinely is how some
arithmetic facts get resolved. The real distinction is **principled amendment
vs ad hoc stipulation**, not "provable vs amendable."

**Why amending for G is principled (and P≠NP initially seemed ad hoc):**
- *Self-justifying*: Con(PA) vouches for the very system it extends; accepting
  it is compelled by believing PA coherent, not a bet on a contested fact.
- *Cascading*: it climbs a tower (PA ⊂ PA+Con(PA) ⊂ ... ⊂ ZFC ⊂ ...), a general
  reflection schema, each rung productive and revealing a new target.
- *Amendment supplies axioms; the fact then becomes provable in the new system.*
  It's not stipulating the fact; it's finding the next principle under which the
  fact is a theorem.

**Why P≠NP-as-axiom seemed ad hoc by the same test:**
- *Not self-justifying*: its truth is precisely what's in question.
- *Terminal, not cascading*: no new "P'≠NP" appears, no tower, no general schema.
- *No principled host*: no known natural general principle has P≠NP as a
  consequence.

**The correction (the user's point):** if P vs NP were **provably independent
of ZFC**, the situation changes categorically:
- It stops being a bet — an independence proof *certifies* ZFC is silent either
  way, removing the "you might be wrong" objection.
- It becomes *like the G ladder*: P≠NP is best read as **a theorem of a stronger
  system we haven't yet identified**, not a bare stipulation. The only reason it
  looks like a stipulation now is that we lack that stronger system in hand.
- Caveat: the quality of the independence proof matters. Robust, forcing-absolute
  independence supports the "next foundation" reading; a weak/pathological
  independence proof is less compelling.
- Bottom line: it is **not "is it a matter of fact" that separates these cases,
  but "do we have a certified silence of ZFC, or just a guess."** Certification
  flips the verdict.

**The correction is stronger than it first looks: an independence proof would
name its own host.** Any proof that X is independent of ZFC proves Con(ZFC)
(Gödel 2), so it cannot be carried out *in* ZFC — unlike CH, whose independence
is a ZFC theorem about relative consistency. Given §3, an arithmetic
independence proof for P vs NP would have to show that P≠NP carries consistency
strength (something of the shape "P≠NP ⇒ Con(ZFC)", or provability from a
reflection principle / large cardinal). If that happened, the "no principled
host" objection dissolves automatically: the proof itself points at the next
rung (ZFC + reflection, or ZFC + the relevant large cardinal). Certified silence
for an arithmetic sentence comes bundled with a pointer to the stronger system
— exactly the G-ladder shape.

**"Terminal" and "not self-justifying" are also weaker than stated.** A tower
of hardness axioms is already in daily use: P≠NP ⊂ NP ⊄ P/poly ⊂ ETH ⊂ SETH ⊂
specific crypto assumptions, each stronger, each yielding a rich, falsifiable
theory (fine-grained complexity, all of cryptography). These are justified
*extrinsically* — fruitfulness and failure to refute — which is Gödel's own
criterion for new set-theoretic axioms and how large cardinals are actually
defended. The real difference from the Con tower is uniformity (Con is generated
by a single reflection schema; the hardness tower is not), not that "we don't
legislate contested facts" — the field legislates them constantly and calls
them assumptions.

## 5. The "prophetic" reading (Hofstadter, GEB) — and why it's a loose rhyme

The user's direction intuition: every barrier result has pushed toward
independence, making GEB prophetic.

**What supports it:**
- Relativization (Baker–Gill–Solovay), natural proofs (Razborov–Rudich), and
  algebraization (Aaronson–Wigderson) each *eliminated a family of proof
  techniques*. The systematic failure of every broad lower-bound method is real
  evidence the proof (if it exists) won't look like anything known — and it
  rhymes with GEB's thesis that a system's power and limits are intertwined.

**What undercuts it:**
- Barriers apply to *independence proofs too* — an independence result faces the
  same gauntlet, so barriers don't differentially favor independence over "just
  very hard."
- Historical pattern is new *techniques* (non-relativizing, non-natural,
  non-algebrizing), not new *axioms* — momentum is toward more cleverness, not
  toward legislating.
- **P vs NP has no self-reference.** GEB's core is self-reference (G says "I am
  not provable"); P vs NP has none — no fixed point, no diagonalization over its
  own provability. Its independence would be arithmetic incompleteness, a
  different phenomenon from Gödelian self-reference; the only known route to it
  is consistency strength (§3), which for P≠NP would force the Ben-David–Halevi
  "almost polynomial" signature.
- Concrete version of "barriers apply to independence too": Hartmanis–Hopcroft
  (1976) built a computable oracle A for which P^A vs NP^A is independent of
  ZFC, while for other oracles it is provable either way (P^B = NP^B for
  PSPACE-complete B; P^C ≠ NP^C for the BGS oracle). A relativizing
  independence proof would therefore be contradictory — independence proofs must
  be non-relativizing just like separation proofs.
- Verdict: the intuition is a live hypothesis, not a trend line. Barriers cut
  both ways; GEB is a loose rhyme, not a roadmap.

## 6. The user's 90's insight: a hint of self-referential structure

(Loose, not a proof — the user knows this. Recorded as an intuition.)

- **P ≠ NP ⇒ OWFs** (loosely; the direction P≠NP ⇒ OWF is not known
  unconditionally, but OWF ⇒ P≠NP *does* hold). Hardness of *deciding* is
  entangled with hardness of *inverting*.
- **OWFs ⇒ near-perfect hashing** (loosest link; note tension: a one-way hash
  hides the structure a "fake fast algorithm" would need to exploit).
- **Perfect hashing ⇒ fast NP-complete algorithms**: the concrete seed. A
  perfect hash isolating a unique satisfying assignment is the territory of
  **downward self-reducibility** and **Valiant–Vazirani isolation** — real,
  studied self-referential-feeling structures: "decide if there's a solution by
  isolating a unique one via hashing."

**Direction problem in the hashing chain.** Valiant–Vazirani uses
pairwise-independent hash families to *isolate* a unique solution, but what it
proves is that Unique-SAT is as hard as SAT — isolation doesn't help. So
"perfect hashing ⇒ fast NP-complete algorithms" runs opposite to what VV
establishes. And OWFs are by definition the *obstruction* to finding structure,
so OWF ⇒ hashing ⇒ fast algorithms would close a loop P≠NP ⇒ P=NP; one link
must break, and that is the candidate.

**The genuine kernel of self-reference:** P vs NP asks whether *deciding* can
outrun *verifying* — "can the machine that recognizes truth also find truth?" —
a structural echo of self-reference. The concrete, honest instance is
**downward self-reducibility** (SAT decides by reducing to smaller SAT), which
is real mathematics.

**A firmer anchor: Levin's universal search.** Levin's algorithm `L` dovetails
all programs and verifies any claimed witness. It solves SAT-search in
polynomial time *iff* P=NP. So P=NP is equivalent to a Σ⁰₂ statement about one
fixed machine: `∃k ∀x, L(x) halts within |x|^k`. The existential over
algorithms collapses into an algorithm that searches for algorithms — the most
honestly reflexive object in the area. Combined with downward self-reducibility
(search ⇔ decision for SAT), this is the concrete home for "can the recognizer
also be the finder." It is still computational reflex, not a Gödelian fixed
point, so the verdict below stands — but it is a firmer kernel than the hashing
chain.

**But the direction of the reflex is productive, not toward independence:**
self-reducibility and isolation are *tools for algorithms*, not a doorway out of
ZFC. The self-structure found so far is algorithmic and productive. The
self-reference P vs NP exhibits is *computational-reflex*, not
*formal-incompleteness* — which is exactly why the intuition doesn't lead to
independence. It's a good intuition to hold; it's just not the Gödelian kind.

## 7. Machine-Gödel: proof-search, budgets, and the self-defeating search

An attempt to give the L intuition a *genuinely* Gödelian flavor (a real
arithmetic fixed point, not a loose rhyme), by letting the machine search for
proofs about itself. It works — with the caveat that the self-reference lives
in the *budget*, not in the search.

**The bridge: P=NP ⇒ proof-search is in P.** Proofs are certificates, so
`{⟨φ,1^k⟩ : φ has a ZFC-proof of length ≤ k}` is in NP (guess + verify) and
hence in P if P=NP: there is a poly-time proof-finder. This is the honest
content of "P=NP would make math easy." The budget `k` is essential.

**The fixed point (genuine self-reference).** Gödel's diagonal lemma: for any
formula ψ(x) there is a sentence φ with ZFC ⊢ φ ↔ ψ(⌜φ⌝). Let A be a poly-time
proof-searcher and set

  G_A := "A does not output a ZFC-proof of me within |⌜G_A⌝|^k steps."

The lemma manufactures the self-reference: G_A speaks about whether A finds a
proof of G_A — the same machinery that builds G ("I am not provable"), with a
time budget instead of PA.

**The theorem: the machine's speed casts its own shadow.** If ZFC is sound,
G_A is true, and no ZFC-proof of it fits A's budget. If A found one, G_A would
be provable hence true, but its truth says A did *not* find it — contradiction.
So the search is empty, and G_A is true because it says the search is empty.

This is *conditional on P=NP*: if P=NP, a poly-time A exists and there is
arithmetic truth A provably cannot reach even at full speed — diagonalization
outruns the budget. If P≠NP, no such A exists and nothing casts a shadow. So
P=NP doesn't mean "we find all proofs fast"; it means "there is a fast finder,
and here is a true sentence it provably cannot find." Power manufactures the
limit — the GEB flavor, made rigorous.

**The user's scenario ("if P=NP then L finds a proof that P≠NP") is
self-defeating by cases:**
- *If P=NP is true:* P≠NP is false; a sound system proves no falsehood, so L's
  search for the proof of its own failure returns empty *precisely because L
  succeeded*. The machine can't find the proof that it's slow, because being
  fast makes that claim false.
- *If P≠NP is true:* L is slow, so "L finds a proof of P≠NP" holds only if
  P≠NP has a *short* proof — the question degenerates to "is there a
  poly-length ZFC proof of P≠NP," a genuinely open Π⁰₁ question, consistent
  with P≠NP being true but only long-provable (Ben-David–Halevi territory, §3).

So "L finds a proof that L is slow" can never bite: in the world where L is
fast, its target is false; in the world where the target is true, L is too slow
to reach it. **L's speed and the truth of P≠NP mutually exclude each other's
proofs** — a clean self-referential closure.

**"Mutual exclusion" is not independence — and is near-tautological.** It is
easy to conflate the two, because both end up saying "not provable." But the
mutual exclusion is conditional on whichever world is actual:
- *If P=NP:* P≠NP is false, so a sound system doesn't prove it. But that holds
  for **any** false arithmetic sentence — it is soundness applied to a
  falsehood, says nothing about P vs NP, and is compatible with **ZFC proving
  P=NP**.
- *If P≠NP:* L doesn't find a *short* proof within its fixed budget. This does
  not even say ZFC doesn't prove P≠NP — ZFC could prove it with an arbitrarily
  long proof and the mutual exclusion would still hold.

So the "exclusion" is: *given the actual world, the opposite claim isn't
(shortly) provable* — compatible with anything, and it *flips* depending on the
world. Independence, by contrast, is unconditional (same claim in both worlds):
ZFC ⊬ P=NP **and** ZFC ⊬ P≠NP, a substantive metamathematical theorem about
ZFC's silence in both directions, not a consequence of soundness, and hard to
prove (non-relativizing, §5; consistency-strength-bearing, §3). The mutual
exclusion therefore gives **zero** evidence about independence — the "never
bites" verdict stands precisely because the construction never rises to an
unconditional claim about ZFC.

**Where self-reference actually bites (not this construction).** The vacuity is
structural; the genuine bites live elsewhere:
- **Löb's theorem (ties to §4).** If a sound theory T proves □_T(φ) → φ, then
  T ⊢ φ. Add the single, un-refusable reflection axiom "Prov_ZFC(P≠NP) →
  P≠NP" (i.e. "ZFC is sound at this sentence"); by Löb, ZFC + that axiom
  ⊢ P≠NP. **The mildest belief one can't help holding — soundness at this one
  sentence — already forces the resolution.** There is no room to keep P≠NP
  independent while believing soundness; reflection at that sentence converts
  it into a theorem. It bites by *forcing a decision*, not by collapsing the
  theory — the escape hatch is that "ZFC is sound" can't be formalized in ZFC
  (Gödel 2). This is the precise form of §4's "amendment."
- **Time-hierarchy diagonalization.** A machine that (via Kleene's recursion
  theorem) refers to its own description and runs slower than anything that
  could simulate it yields a real separation: P ≠ EXP is a theorem. Genuine,
  productive self-reference that bites. It fails to port to P vs NP precisely
  because it relativizes (oracles with P^A = NP^A), which is the barrier of §5.
- **PH-collapse / Cook–Reckhow.** P=NP ⇒ NP=coNP ⇒ short *propositional* proofs
  of every tautology (a proof system with polynomial bounds) and PH = P. A bite
  in the sense of a massive, falsifiable collapse; self-referential-flavored
  ("every true sentence has a short proof" ≡ a complexity collapse), but a
  collapse, not an inconsistency.

**Honesty caveat.** Unbounded proof-search is always r.e. — dovetail over
proofs and verify, which is already Levin-style search, no P=NP needed. P=NP
only buys the *budget* (poly-time halting). That is why every G_A needs its `k`:
without a budget, "A finds a proof of φ" is trivially r.e. and the construction
dissolves. The self-reference lives in the budget, not in the search.
