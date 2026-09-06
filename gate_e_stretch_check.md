# Gate E Precheck: The Full-Schema Targets 2b/2c and the Stretch Gap

Bounded source check, September 5, 2026, before any proof work on the
optional full-schema extension of `modified_specific_recommendation.md`
Section 5. Question asked: what is the closest existing statement to

```text
2b:  { CInc_c : c >= 1 }  <=>  dWPHP(PV)   over PV_1
2c:  { Inc_c  : c >= 1 }  <=>  dWPHP'(PV)  over PV_1
```

with `dWPHP` the near-equal schema of `step1_decoder.md` Section 0.5
(`a|b| -> a(|b|+1)`, PS21/Jerabek convention), and what exactly separates
that statement from the target. Method: read the primary passages, not
search-engine coverage. Outcome: the gap is a named, published obstacle,
not an unexamined conversion.

## 1. Where the incompressibility schemata sit

Write `sPHP^a_b(PV)` for "no PV function with parameters maps `[0,a)`
onto `[0,b)`" (Jerabek's notation). Three stretch classes matter:

| Class | Representative | Natural `K^t` threshold |
| --- | --- | --- |
| polynomial ("squaring") | `forall a>1 sPHP^a_{a^2}` | `K^t(x|z) >= n/2` (this project's `CInc_c`, `Inc_c`) |
| constant-factor ("doubling") | `forall a>0 sPHP^a_{2a}` | `K^t(x|z) >= n - k`, `k` constant (RSW22 Def. 6.3; ILW23's `APC_1`, stretch `n+1`) |
| near-equal | `forall a,b sPHP^{a|b|}_{a(|b|+1)}` | none with an integer length threshold; this is `APC_1` in Jerabek 2007+ and the schema in Section 0.5 |

Within a class, variants are `PV_1`-equivalent by constant-depth
composition, product, and restriction (Jerabek, JLC 2007, Lemma 3.8, p. 12;
these are the only circuit manipulations `PV_1` needs). Across classes
they are not known to be, see Section 2.

The project's schemata are in the squaring class:

- Forward (F1, `step1_decoder.md` Section 2.3). The decoder `CDec_c` is
  nontrivial only on `[1, 2^(m+1))`, `m = floor(n/2)`, and the proof only
  needs the avoided value to miss that segment. The instance with
  `a = 2^(m+1)` and codomain `2^n` (stretch at least `a^2/4`) therefore
  suffices; the `a = 2^(n-1), b = 1` instance as written is a convenience.
  So `PV_1 + forall a>1 sPHP^a_{a^2}(PV)` proves every `CInc_c`.
- Reverse (L2 route, `step1_decoder.md` Section 4, `T_PV` level). A
  `CInc_{c_0}` witness of length `4m` avoids the range of any circuit
  `m -> 4m` bits, i.e. `sPHP^a_{a^4}(Eval)`; by Lemma 3.8 this gives the
  squaring class over `PV_1` once L2 is internalized.

Hence the proposed equivalence suggested by this project's machinery is

```text
2b':  PV_1 + { CInc_c : c >= 1 }  ==  PV_1 + forall a>1 sPHP^a_{a^2}(PV),
```

pending internalization, including L2 in `PV_1`. The analogue 2c' with
`Inc_c` and the parameter-free squaring schema is a separate
formalization target, not a completed characterization.

## 2. The closest existing statements

1. **Jerabek, *Approximate counting in bounded arithmetic*, JSL 2007,
   p. 4** (author PDF `apx.pdf`): the near-equal `dWPHP(PV)` "is over
   `S^1_2` equivalent to the more usual schema `x -> x^2`, but it is not
   clear whether this reduction also works over `PV_1`." Same paper,
   p. 13: whether existence of hard-on-average functions implies
   `dWPHP(PV)` over `PV_1` is also left open (this second one is the
   parameter obstruction; CLO24 fn. 8 records that it is conditionally
   false by ILW23, and it is what this project's free auxiliary `z`
   avoids).

2. **Jerabek, *On independence of variants of the weak pigeonhole
   principle*, JLC 17 (2007) 587-604** (author PDF `wphpvar.pdf`). This
   is the decisive source, not previously in the project's source table.
   - Theorem 3.1 (pp. 5-6): the stretch variants are equivalent over
     `S^1_2(alpha)` for the surjective principle, but over `PV_1(alpha)`
     only for the injective and retraction principles. The surjective
     proof uses `Sigma^b_1(alpha)`-LIND to show an iterated surjection is
     surjective.
   - Theorem 3.3 (p. 7): `PV_1(alpha)` + "the `k`-fold iterate of a
     surjective circuit is surjective" (SCIP) equals `S^1_2(alpha)`. So
     the natural amplification step is exactly `Sigma^b_1` induction.
   - Theorem 3.4 and Corollary 3.6 (pp. 8-12), relativized to
     `PV_1(alpha)`:
     ```text
     (iii) sPHP^a_{a^2}                 does not prove  sPHP^a_{2a}
     (iv)  sPHP^a_{2a}                  does not prove  sPHP^{a||a||}_{a(||a||+1)}
     (v)   sPHP^{a||a||}_{a(||a||+1)}   does not prove  sPHP^{a|a|}_{a(|a|+1)}
     ```
     Example 3.7: equivalence with `sPHP^a_{2a}` over `PV_1(alpha)`
     forces `P(a) = a + Omega(a)`.
   The proof is KPT witnessing plus a random-injection oracle argument,
   the same mechanism ILW23 later use unrelativized under iO.

3. **Jerabek, *Approximate counting by hashing*, JSL 2009, p. 5**
   (`hash.pdf`): restates that the stretch equivalence holds over
   `PV_1(Gamma)` for `rWPHP` and `iWPHP` but "does not hold for `sWPHP`
   (we need `S^1_2(Gamma)` to prove the equivalence)", citing item 2.

4. **ILW23, Remark 14, p. 8** (ECCC TR23-038): "we cannot prove an
   equivalence between `dWPHP(PV)` with different stretch functions within
   `PV_1` ... Jerabek [Jer07b] also proved that `PV_1(alpha)` cannot prove
   the equivalence of `dWPHP(alpha)` between different parameters." ILW23
   define `APC_1` with stretch `m(n) = n+1` (eq. (1), p. 8), i.e. the
   doubling class, and sidestep the issue because their negative result
   holds for arbitrarily large polynomial stretch. Footnote 9 is the
   separate parameter point.

5. **CLOW26, Theorem 6.5, p. 87** (arXiv:2602.09302v1): stretch reduction
   "in PV" is stated for the *retraction* principle `rWPHP` (Thapen 2002,
   Jerabek 2005), consistent with item 2 and with nothing new for the
   surjective principle. Atserias-Tzameret (STOC 2025) likewise prove
   their hitting-set reversal over `S^1_2`, not `PV_1`.

No source was found that proves, conjectures, or refutes the
*unrelativized* implication `PV_1 + sPHP^a_{a^2}(PV) |- sPHP^a_{2a}(PV)`
or its near-equal strengthening. No source was located stating an arithmetic
equivalence between an incompressibility schema and any `dWPHP` variant
over `PV_1`; the 2b' form is a specialization of RSW22's two bridges
plus Lemma 3.8 and was not located as a displayed theorem (consistent
with `gate_d_novelty.md` Section 3.3).

## 3. The exact gap

```text
2b  =  2b'  +  [ PV_1 + forall a>1 sPHP^a_{a^2}(PV)  |-  dWPHP(PV) near-equal ]
```

- 2b' is a proposed characterization with close antecedents (RSW22
  bridges, Lemma 3.8), not a completed internal proof; L2 inside `PV_1`
  remains an obligation. As with Gate D, a substantial novelty claim
  has not been justified. Failure to locate the formula establishes
  neither novelty nor that it lacks publication value.
- The bracket is Jerabek's 2007 question, and Corollary 3.6 (iii)-(v)
  refutes its relativization in three separate steps (squaring -> doubling
  -> `||a||`-granularity -> near-equal). Every construction in Steps 1-2
  (decoders, `Sim_c`, `NativeEval`, compositions, wrappers) relativizes,
  so this project's route cannot close the bracket. Any proof would have
  to exploit a property of polynomial-time computation that oracle
  circuits lack; no such technique is known to us or cited by ILW23 or
  CLOW26.
- The same gap applies with ILW23's convention (`n+1` stretch): 2b would
  then need the bracket's first step, (iii), which is already refuted
  relativized.
- 2c has the identical stretch gap plus the parameter-free composition
  problem (`a` is not available as a parameter when iterating `f` at
  different scales), so it is at least as hard.

Consequences for the plan's outcome tree (`modified_specific_recommendation.md`
Section 8): the stretch step is not a routine unresolved conversion;
its relativized form is false. Subject to establishing 2b', target 2b
would require settling the unrelativized stretch question. The
correct record is: 2b' proposed (a characterization of the squaring-class
theory, which is relativized-strictly and unrelativized-conjecturally weaker
than `APC_1` under either convention); 2b/2c unreachable by the planned
route. This also grounds `specific_recommendation.md` Section 5's remark
that "different thresholds may be `PV_1`-inequivalent": Corollary 3.6 gives
the relativized hierarchy `n/2 < n-k < near-equal`.

## 4. The 2f-Candidate and Astra's Review

One candidate for which no matching theorem was located is an
*unrelativized, assumption-based* stretch separation over `PV_1`:

```text
2f-candidate:  under cryptographic hypotheses,
               PV_1 + forall a>1 sPHP^a_{a^2}(PV)
                 does not prove forall a>0 sPHP^a_{2a}(PV).
```

**Astra preliminary review, September 5, 2026:** supports one bounded
feasibility check, but corrects the earlier oracle-replacement formulation
and the unqualified claim that inversion collapses the stretches. The
relevant source passages were checked; neither the full mixed-oracle
transfer nor an extension of ILW23's lower bound has been proved.

### 4.1 Addition, Not Replacement

The KPT route must retain both kinds of Teacher response. In
[Jerabek's Theorem 3.4 proof](https://users.math.cas.cz/~jerabek/papers/wphpvar.pdf),
pp. 8-9, the Student proposes either a target non-output or a source
surjection. The corresponding counterexamples are:

- A preimage under the target circuit, if the proposed non-output lies
  in its range.
- A value outside the proposed source circuit's range, refuting its
  claimed surjectivity.

Thus the sufficient hardness target is deterministic AVOID at stretch
`n+1` with **both** constantly many target-circuit inversion queries and
constantly many square-AVOID queries. It is not hardness with square-AVOID
queries replacing inversion queries. In the bit-string formulation:

- The input is `C: {0,1}^n -> {0,1}^{n+1}`. Every inversion query is to
  this original `C`, not to an arbitrary circuit.
- A square-AVOID query supplies an ordinary circuit
  `D: {0,1}^t -> {0,1}^{2t}`, with `t >= 1`, and receives any value
  outside its range.
  The queried `t` can vary and need not equal `n`; queries can depend on
  `C` and previous answers.
- Runtime and query descriptions must be polynomially bounded in the
  target encoding length. Query counts are proof-dependent constants,
  independent of input length.
- Correctness must hold for every legal choice of oracle answers,
  including consistent choices on repeated queries.

Writing the exact guarded extraction and its bounds is the first
deliverable, not a completed theorem of this review. A uniform lower
bound suffices for the stated `PV_1` target; a nonuniform circuit lower
bound is a stronger sufficient target. ILW23 Theorem 21 handles the
uniform inversion-only model under JLS-secure iO and
`coNP not contained in i.o.AM`; Theorem 28 handles the nonuniform model
under JLS-secure iO and `coNP not contained in i.o.NP/poly`. Neither
theorem supplies the mixed-oracle result, and those hypotheses have not
been shown sufficient for it.

### 4.2 Query Budget and Proof Bottleneck

[ILW23 Lemma 34](https://eccc.weizmann.ac.il/report/2023/038/download),
pp. 27-28, reduces `n -> n+1` avoidance to one `n -> 2n` avoidance
query and **up to n inversions** of the original circuit. It does not
give a constant-inversion reduction and therefore does not refute the
mixed constant-query hardness target.

Theorem 21's Claim 22 and its `j`-good predicate, pp. 14-16, provide a
concrete feasibility bottleneck. The proof tests a fixed transcript with
a polynomial-size circuit, needed for both iO indistinguishability and
the counting protocol. An inversion answer is efficiently checked by
evaluating `C(x)`. In contrast, legality of an avoidance answer requires

```text
forall u in {0,1}^t, D(u) != v.
```

The source supplies no general polynomial-time test for this
range-nonmembership condition. Naively adding avoidance replies breaks
the efficient-verification step. An adaptation must preserve legal
replies through the argument without assuming such a test, or replace
that part of the proof. This is an identified obstacle to the naive
adaptation, not a proof that every adaptation fails.

## 5. Decision

**Latest recommendation:** following the user's interest in pursuing
2f and Astra's review, conduct one bounded feasibility check of the
corrected mixed-oracle target. Set a time cap before starting. The
preliminary source review is complete; this full check is not yet run.

1. Write the exact mixed Student-Teacher game extracted from the
   hypothetical stretch implication, with query sizes, constant bounds,
   and answer quantifiers.
2. Audit Claim 22's induction and the `j`-good predicate against that
   game. Test whether avoidance-answer legality can be handled while
   preserving efficient verification and the probability estimates.
3. Only if that works, consider Theorem 28's nonuniform upgrade; the
   uniform target already suffices for the stated theory separation.

Work directly with dWPHP stretches. Do not first invest in L2 or a
`K^t` translation; exact incompressibility characterizations and
threshold conventions remain separate proof obligations. This replaces
the earlier informal identification of 2f with an exact
`(n-1)`-incompressibility nonimplication.

At the cap, record a checked adaptation, a precise unresolved lemma, or
an obstruction to this method. Continue only if a checked new step or
sharper obligation justifies a bounded next attempt. Otherwise stop or
narrow the branch. This is not a commitment to finish a proof campaign;
2b/2c remain closed as routes under the existing plan, not refuted
unrelativized. The closed Step 2 result is unchanged.

**Novelty calibration:** the established result has close antecedents,
and a substantial novelty claim has not been justified. Earlier claims
that nothing is novel in substance or that nobody bothered to write
down the specialization exceeded the evidence. Neither failure to find
a theorem nor an apparently successful adaptation establishes novelty
or publishability. The 2f separation remains a candidate, not a result.

Verification scope: the cited source passages were read; page numbers
are printed page numbers. This is a preliminary mathematical review,
not a completed proof or a new novelty search. The finite check scripts
are unchanged and cannot verify the mixed-oracle claims.

Round-end verification: `git diff --check`, `python3 check_step1.py`,
and `python3 check_step2.py` passed. The scripts provide finite
regression checks only.

## 6. Fable 5.1 Concurrence and First Pass at the Check

September 5, 2026. Both of Section 4's source claims were re-read and
confirmed: Lemma 34 uses "at most n oracle queries to the circuit-inversion
oracle" (p. 28), and Claim 22's failure event has probability
`2^{-Omega((2k-j)m)}` over the iO seed (p. 14). The Section 4.1 correction
is accepted: the earlier "replace inversion gates" formulation and the
unqualified "collapse" claim were errors. Steps 1-2 of Section 5 were then
carried out on paper, with the result below.

### 6.1 The mixed game, exactly

Suppose `PV_1 + forall b>1 sPHP^b_{b^2}(PV) |- forall a>0 sPHP^a_{2a}(PV)`.
By the deduction theorem, Parikh, and the `eval` presentation, `PV_1`
proves an `exists-forall-exists` sentence whose KPT witnessing gives a
constant `k` and a poly-time Student. On input `C: {0,1}^n -> {0,1}^{n+1}`
of description length `s`, in each of at most `k` rounds the Student
proposes either

- (T) a target candidate `y in {0,1}^{n+1}`; a legal Teacher reply is
  `x` with `C(x) = y`, or "none" if `y` is outside the range; or
- (S) a source circuit `D: {0,1}^t -> {0,1}^{2t}` (`t >= 1`, `|D| <= s^d`,
  `t` of the Student's choosing); a legal reply is any
  `v in {0,1}^{2t}` outside the range of `D`.

Soundness of the disjunction in the standard model: against every legal
Teacher, some (T) proposal is answered "none" within `k` rounds. Hardness
target: for every such Student there exist `C` and a consistent legal
Teacher that never answers "none". Uniform Students suffice for the
`PV_1` target.

### 6.2 Obstacle (a) is removable; obstacle (b) is the real one

Astra's obstacle (a): legality of an (S) reply, `forall u D(u) != v`, is
a coNP condition the Verifier of Algorithm 1 cannot check if the Prover
supplies `v`. The natural patch removes it: let the *Verifier* generate
`v` as part of its randomness, brute-forcing a legal `v` when
`t <= c log s` and sampling `v` uniformly from `{0,1}^{2t}` otherwise
(this is ILW23's own device in Theorem 33, p. 29, at stretch `t -> t^2`).
Then nothing coNP is checked; the `j`-good predicate on `(r, w)` remains a
poly-size test, and the Prover's message is as before (`phi_i, x_i, y_i`,
plus the fixed `D_i` for (S) rounds, fixed by the same averaging that
fixes `y_j`, at a loss of `2^{-poly}` matching the existing loss).

Obstacle (b), quantitative: the argument then needs
`Pr_{r,w}[j-good and all v legal] > 0` (noticeable, for Goldwasser-Sipser).
But `Pr[j-good] >= 2^{-Omega(km)}` while `Pr[some v illegal] <= k 2^{-t_min}`,
with `t_min` the smallest non-brute-forced `t` the Student uses. The
difference bound is positive only if `t_min >= Omega(km)`. Brute force
covers `t = O(log s)`; the Student is free to query
`O(log s) < t < Omega(km)`, and later `j`-goodness may correlate with
`v_i` through the Student's subsequent proposals, so conditioning does
not help. Thus the direct ILW23 adaptation plus randomized replies fails
for adversarial Students querying medium `t`. Producing legal replies for
medium `t` without an NP oracle is AVOID at stretch `2t` itself, so (b)
cannot be patched on the reply side.

### 6.3 What (b) says about the route

The `2^{-Omega(km)}` comes from fixing each `y_j` by averaging over
`{0,1}^m`; it is intrinsic to ILW23's planted-`y` construction. Jerabek's
relativized proof (Section 2, item 2) has no such loss: with a random
injection as target, the Student fails with probability `>= 4^{-c'}`, a
constant, which is what lets random source replies (legal w.p. `-> 1`) be
absorbed. So the sharpened obligation is:

```text
(*)  Under cryptographic hypotheses, a distribution on
     (C: {0,1}^n -> {0,1}^{n+1}, legal inversion oracle for C)
     on which every poly-time Student with k inversion queries fails
     with probability Omega(1) (or at least >> 2^{-t} for every
     t > O(log s)), not 2^{-Omega(km)}.
```

`(*)` is a strengthening of ILW23 Theorem 21 from worst-case existence to
average-case failure. Given `(*)`, the Section 6.2 patch completes the
transfer and the 2f-candidate follows. Whether `(*)` is known, or follows
from iO with puncturable-PRF techniques (Sahai-Waters style, replacing
the planted-`y` circuit by an obfuscated pseudorandom map), was not
checked and is a research question, not a bounded audit. Nothing here is
a proof that `(*)` is false or that 2f is false.

### 6.4 Result of the check and next step

Outcome of the time-boxed check: **no for the direct adaptation, with an
identified reason**, and a sharper obligation `(*)`. Per Section 5's
stopping rule, this supports at most one further bounded action, not a
proof campaign. Recommended, in order:

1. Tier-2 outreach with the now-sharp question, e.g. to Li or Jerabek:
   "Is AVOID at stretch `n+1` known to be hard for poly-time algorithms
   with `O(1)` inversion queries to the input circuit *and* `O(1)`
   AVOID-at-stretch-`2t` queries, under iO? Equivalently, is the
   unrelativized stretch inequivalence `PV_1 + dWPHP_{a^2} |-/- dWPHP_{2a}`
   known under any assumption?" A one-line answer settles both novelty
   and feasibility faster than further reading.
2. If the answer is "not known" and the user wants to proceed: a bounded
   literature check on `(*)` (average-case white-box AVOID hardness with
   an inversion oracle; ILW23 follow-ups on AVOID hardness), before any
   construction attempt.
3. Otherwise stop; the program's durable output is the source map,
   the closed reconstruction 2g, and the two obstacles above.

Outreach requires the user's explicit authorization
(`specific_recommendation.md` Section 5).
