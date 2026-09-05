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
  So `PV_1 + forall a sPHP^a_{a^2}(PV)` proves every `CInc_c`.
- Reverse (L2 route, `step1_decoder.md` Section 4, `T_PV` level). A
  `CInc_{c_0}` witness of length `4m` avoids the range of any circuit
  `m -> 4m` bits, i.e. `sPHP^a_{a^4}(Eval)`; by Lemma 3.8 this gives the
  squaring class over `PV_1` once L2 is internalized.

Hence the equivalence this project's machinery can reach is

```text
2b':  PV_1 + { CInc_c : c >= 1 }  ==  PV_1 + forall a>1 sPHP^a_{a^2}(PV),
```

modulo L2 in `PV_1`. Analogously for 2c' with `Inc_c` and the
parameter-free squaring schema.

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
or its near-equal strengthening. No source states an arithmetic
equivalence between an incompressibility schema and any `dWPHP` variant
over `PV_1`; the 2b' form is a specialization of RSW22's two bridges
plus Lemma 3.8 and was not located as a displayed theorem (consistent
with `gate_d_novelty.md` Section 3.3).

## 3. The exact gap

```text
2b  =  2b'  +  [ PV_1 + forall a sPHP^a_{a^2}(PV)  |-  dWPHP(PV) near-equal ]
```

- 2b' is expected true and is folklore-level (RSW22 bridges, Lemma 3.8);
  its only open obligation is L2 inside `PV_1`. Its novelty status is
  that of Gate D: unlocated as a formula, not substantial.
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
Section 8): outcome 2b as stated is not an "unresolved conversion"; it is
equivalent to an open problem whose relativized form is false. The
correct record is: 2b' reachable (a characterization of the squaring-class
theory, which is relativized-strictly and unrelativized-conjecturally weaker
than `APC_1` under either convention); 2b/2c unreachable by the planned
route. This also grounds `specific_recommendation.md` Section 5's remark
that "different thresholds may be `PV_1`-inequivalent": Corollary 3.6 gives
the relativized hierarchy `n/2 < n-k < near-equal`.

## 4. What would be new, and why it is not authorized here

The only statement in this vicinity with no located antecedent is an
*unrelativized, assumption-based* stretch separation over `PV_1`, e.g.

```text
2f-candidate:  under cryptographic hypotheses,
               PV_1 + forall a sPHP^a_{a^2}(PV)  does not prove  sPHP^a_{2a}(PV),
```

in `K^t` language: `PV_1` plus conditional half-length incompressibility
does not prove conditional `(n-1)`-incompressibility. ILW23's method would
require AVOID at stretch `n+1` to be hard for polynomial-size circuits
with constantly many AVOID-at-stretch-`2n` oracle gates (Teacher answers
for squaring-class counterexamples), not the constant-inversion-gate
hardness of ILW23 Theorem 28. Whether iO-based techniques give this is a
research question with unknown feasibility, not an extension of the
checked repo material, and Lemma 34 of ILW23 (p. 27: `n+1` reduces to
`2n` given an inversion oracle) shows the two stretches collapse as soon
as inversion is available. Per `gate_d_novelty.md` Section 5 this is not
an automatic next task; if chosen, it needs its own time-boxed feasibility
check and an explicit statement of what it adds beyond Jerabek JLC 2007
and ILW23.

## 5. Decision

Do not start the full-schema extension in the form 2b/2c. The recorded
options are now: stop (unchanged default); 2b' as a formalization exercise
with low novelty (requires L2 in `PV_1`); or the 2f-candidate above as a
genuinely open, high-risk research target. Recommendation unchanged from
Gate D: stop unless the 2f-candidate is deliberately chosen.

Verification: passages quoted above were read in the author/ECCC/arXiv
PDFs listed; page numbers are the printed ones. No proof in this note is
new; `check_step1.py` and `check_step2.py` are unaffected.
