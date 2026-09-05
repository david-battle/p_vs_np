# Step 0 Baseline: Time-Bounded Incompressibility

## Work Record

Started 2026-09-05, 20:09 UTC. Target: close Gate A of the modified plan by
extracting the source conventions, decoder reduction, and exact Eval
principle, with a labelled dependency table and explicit Step 1 obligations.
This is source verification and proof preparation, not a completed PV_1 proof.

Limits for this pass: 60 minutes; three bounded source-extraction tasks and
one independent write-up audit; no exhaustive novelty search. No paid
external services, outreach, or publication are part of this pass.

Status: Gate A's research deliverables are complete (outcome 0b); proceed
to Step 1.

## 1. Source Table

This records Step 0 items 1-3 of the
[modified plan](modified_specific_recommendation.md#3-step-0-establish-the-literature-baseline).
The specified primary PDFs were checked on September 5, 2026. Page numbers
are printed pages; CG's PDF page is printed page + 1, ILW23's is printed
page + 2, and Korten's and PS21's agree with their printed pages.

| Source and pinned version | Statement and locator | Base theory | Parameters | Stretch / threshold | Relevance |
| --- | --- | --- | --- | --- | --- |
| [Carmosino-Grosser (CG), ECCC TR25-045, Revision 1, April 12, 2025](https://eccc.weizmann.ac.il/report/2025/045/revision/1/download) | Section 2.7, p. 14; Formalization 4.1, Remark 4.2, Definition 4.3, p. 17; Theorem 4.18, p. 23: `VAPC proves HiKt[c]` for each standard `c` | Statement over VPV; provability in VAPC | Two-part charged description; external index `c`; fixed unspecified cutoff; no free auxiliary string | Half-length descriptions; strict/non-strict discrepancy below. Thm. 4.18 does not display its pigeonhole instance | Explicit theory assertion for the source's schema, not a ready-made proof of our exact Inc/CInc |
| [Korten, arXiv:2106.00875v3, February 10, 2022](https://arxiv.org/pdf/2106.00875v3) | Section 3.5, Definitions 13-14 and Theorem 6, p. 14; Empty: Definition 3, p. 8 | Ordinary polynomial-time search reduction; no named arithmetic base in Thm. 6 | Fixed machine `U` and polynomial `t`; input `1^n` | Circuit `n-1 -> n` bits, or `2^(n-1) -> 2^n` points; output complexity `>= n-1` | Explicit padded decoder and range-covering argument |
| [Pich-Santhanam (PS21), March 2021 STOC-final PDF](https://users.ox.ac.uk/~coml0742/papers/stoc-final.pdf) | Section 2.1, pp. 7-8: near-equal dWPHP and its parameter-free restriction | `APC_1 = PV_1 + dWPHP(PV)`; parameter-free extension of PV_1 | General PV function with parameters versus unary `f(u)` only | `ab -> a(b+1)` points, `b in Log` | Exact interval-schema definitions |
| PS21, same version | Section 2.1, p. 8: hard Boolean functions and the NW approximate-counting theorem; `forall Sigma^b_1` conservativity | `S^1_2 + dWPHP(PV)` conservative over `PV_1 + dWPHP'(PV)` in the stated class | Parameter-free axioms suffice for the cited hard-function/NW results | Hard truth tables, not an asserted half-length K^t bound | These results do not themselves transfer our `forall Sigma^b_2` sentences |
| PS21, same version | Section 3.1, Theorem 4, pp. 9-10: constant-round witnessing by polynomial-size circuits for the parameter-free theory | `T^0_APC_1 = T_PV + dWPHP'(PV)` | Nonuniform witnessing functions; parameterized version instead has randomized witnessing | Not a stretch conversion | Dependency of ILW23, not a uniform construction of incompressible strings |
| [Ilango-Li-Williams (ILW23), ECCC TR23-038, original March 28, 2023 report](https://eccc.weizmann.ac.il/report/2023/038/download) | Section 4.1, p. 13: `dWPHP_ell(Eval)`; Section 4.3, equation (7), p. 16, and Theorem 24, p. 17 | `UAPC_1 = PV_1 + dWPHP'(PV)`; unprovability even in `T^0_APC = T_PV + dWPHP'(PV)` | Arbitrary circuit `C` as parameter; hypotheses stated in Section 4 below | Any constructive `m < ell(m) <= poly(m)`; use `ell(m)=4m` for positive `m` | Exact negative endpoint for the conditional-separation target |
| ILW23, same version | Section 2.1, Definition 10, p. 7; Section 2.3, footnote 10 and Remark 14, pp. 8-9 | External security assumptions and arithmetic conventions | Nonuniform iO adversaries; PV-representable stretch | Different dWPHP stretch presentations require care over PV_1 | Pins the hypotheses; prevents silently importing full-schema conversions |

PS21 uses a **prime** in `dWPHP'(PV)` and a **zero** in `T^0_APC_1`.
PDF text extraction can confuse them; the notation was checked visually.
The hard-function/NW and conservativity assertions above are statements
reported by PS21, not newly reconstructed proofs of its cited antecedents.

## 2. Resolve the Incompressibility Conventions

### What CG Actually Specifies

CG Section 2.7 uses

```text
pair(M,w) = dbl(M) || 01 || w
|pair(M,w)| = 2|M| + 2 + |w|.
```

The displayed pairing domain has nonempty components. For a fixed machine,
the charged input therefore costs `|w| + C_M`, where `C_M = 2|M|+2`.
Only the machine part is doubled. The definition of `run_U(M,w,1^t)` returns
the entire nonblank contents of the simulated tape after `t` steps of U;
it does not impose an explicit halting condition. It promises polynomial
simulation overhead, not an exact exponent or a same-clock comparison to a
different universal machine. Parsing a description outside `run_U` is also
not automatically the same clock as running a machine on the complete `d`.

Formalization 4.1 excludes descriptions with `|D| < n/2`. Its nearby matrix
uses `|D| <= n/2`, and Definition 4.3 asks for `K^{n^c}(X) > n/2`. That
definition's counterexample prose reverts to `< n/2` and says the described
machine **halts** with X on its tape. Thus both boundary and output
conventions drift within the source. Theorem 4.18 states VAPC provability
and its proof attributes that assertion to Korten; it supplies no detailed
translation resolving those discrepancies.

Here is the exact threshold comparison for one fixed output predicate.
Interpret the strict bound as `2|D| < n`, not strict comparison with an
integer-division term:

| Length | Source's strict formula forbids | Project's chosen formula forbids |
| --- | --- | --- |
| `n=2m` | `|D| <= m-1`, expressing complexity `>= m` | `|D| <= m`, expressing complexity `>= m+1` |
| `n=2m+1` | `|D| <= m`, expressing complexity `>= m+1` | `|D| <= m`, expressing complexity `>= m+1` |

If the source intended integer division instead, even the odd-length
comparison changes. We do not settle the authors' intention by editing the
statement. Our bound is unambiguously `2|d| <= n`, equivalently
`|d| <= floor(n/2)`.

### Project Decision

Retain the modified plan's **halting-output** definitions, with separate
sentences for standard constants `c >= 1` and starting length `n >= 4`:

```text
Inc_c(n):
  exists x of length n, no d with 2|d| <= n makes U(d)
  halt with exactly output x within n^c steps.

CInc_c(n):
  forall z, exists x of length n, no d with 2|d| <= n makes U(d,z)
  halt with exactly output x within (n+|z|+1)^c steps.
```

The auxiliary string is not charged to description length. CG's second
pair component is charged input, not this free auxiliary input. Its cutoff
is an unspecified absolute constant, not a source for our particular 4.
Our cutoff comes from the decoder inequality in Section 3.

For Step 1, use the pair-code pattern above with a nonempty valid machine
code, allow an empty payload, and define malformed descriptions to fail.
The bounded test checks actual steps of the chosen U, including its parsing;
the outer decoder's own parsing is not charged against that U clock. Fix the
actual U, its halt/output convention, and its simulation implementation in
Step 1. Pair-code length alone does not prove the necessary compiler bounds.

If the same simulator provably freezes the same represented output after
halting, snapshot incompressibility implies halting incompressibility at
the same description bound and clock. This is only a conditional comparison,
not a verified bridge between CG's machine and ours. Nonhalting snapshots
need not persist at later clocks, so one must not assume snapshot complexity
is monotone when increasing `c`.

**Do not import a corrected HiKt theorem.** Reconstruct our direct decoder
instead. This avoids making the CG boundary correction or a general
two-sorted interpretation a prerequisite for the first proof.

### One-Sorted Interface

Use the following concrete representation when writing that reconstruction:

| String-side object | One-sorted representation / obligation |
| --- | --- |
| Arbitrary finite binary string `s` | `enc(s)=2^|s|+val(s)`; `enc(empty)=1`, and `len(enc(s))=|enc(s)|-1`. Leading zeros are preserved |
| Length `n` | `n=|N|` for an available number N, or supply `1^n`; binary `n` alone is not a sufficient size resource |
| Exactly n-bit x | `2^n <= X < 2^(n+1)`; for a range witness `v<2^n`, use `X=2^n+v` |
| All descriptions of length at most m | `1 <= D < 2^(m+1)`, with d obtained by removing the leading sentinel of D |
| Auxiliary string z | A separately encoded Z, with its **string** length `len(Z)` used in the clock |
| Bounded simulation | A PV predicate on the encoded strings and available size resource, one function/predicate for each fixed c |

Powers of two here denote polynomial-output-length constructions supported
by the length witness, not unrestricted exponentiation. Prove their PV
definitions and bounds. The translated existence sentences have
`forall Sigma^b_2` form. Moving CG's entire VAPC proof into APC_1 would
additionally require an interpretation preserving its functions, axioms,
and machine predicate; the table is an explicit target encoding, not that
interpretation theorem. Direct one-sorted reconstruction bypasses it.

## 3. Korten's Decoder and the Reconstruction Interface

Korten Definition 13 permits **any fixed** machine U and defines description
length as the raw input length. Theorem 6 constructs a circuit Phi_n with
`n-1` input bits and n output bits. For an input of the form `0*1d`, it
simulates U on d for `t(n)` steps and pads/truncates the result to n bits.
The all-zero input maps to `0^n`.

The source explicitly represents each description of length `k <= n-2` by

```text
e_n(d) = 0^(n-k-2) || 1 || d.
```

Thus `|e_n(d)|=n-1`, and every successful description of length at most
`n-2` supplies a preimage of its exact n-bit output. A missing output has
complexity `>= n-1`. The reduction returns that output unchanged. This is
range **inclusion**, not equality with the compressible strings; additional
outputs introduced by padding/truncation cause no problem.

The circuit is polynomial-time constructible from `1^n` for fixed U and t.
The source does not give a detailed timeout/output-stability convention,
gate bound, or a PV_1 simulation proof. Its explicit default branch is for
the all-zero **circuit input**; returning zero on a failed simulation is our
choice, not a quoted feature of its proof.

For our half-length threshold, set `m=floor(n/2)` and adapt the construction:

```text
encode_n(d) = 0^(m-|d|) || 1 || d       (m+1 bits)

Dec_c(1^n,z,p):
  if p is all zero, return 0^n;
  otherwise remove the zeros and first delimiter 1 to recover d;
  run the chosen U(d,z) with the specified clock;
  if it halts with exactly n output bits, return those bits;
  otherwise return 0^n.
```

Use the no-auxiliary machine mode and `n^c` for ordinary Inc; the conditional
version has z separate and clock `(n+|z|+1)^c`. The source states only the
ordinary reduction; this uniform conditional adaptation must be proved.

There are `2^(m+1)-1` short descriptions and `2^(m+1)` padded inputs. For
`n >= 4`, `m+1 <= n-1`. Consequently the parameterized forward proof can
use the **exact given interval schema**, with

```text
a = 2^(n-1), b = 1, domain [0,a), codomain [0,2a).
```

Use a total PV function whose parameter tuple supplies `1^n` and, when
needed, z. On numeric inputs below `2^(m+1)`, decode as an `(m+1)`-bit
string; send other inputs to zero. Its value is the raw n-bit output's
numeric value, not its sentinel encoding. A missing value `v<2^n` gives
`enc(x)=2^n+v`; every forbidden description has an explicit preimage within
`[0,a)`. No near-equal-to-squaring conversion is needed here.

This is a concrete proof template, **not yet an internal PV_1 proof**.
Define behavior for out-of-range inputs and parameters as well, since the
function symbol must be total. Prove decoding, simulation coverage, interval
bounds, and the chosen size-resource construction in PV_1.

The parameter-free case requires an additional construction. The numeric
value of `0^m1` is always 1, so the padded code by itself cannot tell a unary
function which n was intended. Passing n, the length witness, or the clock as
an extra argument is not allowed. Korten's uniform circuit constructor does
not by itself solve this parameter-elimination problem.

**Proposed unary layout (Fable 5.1 amendment, not yet checked in PV_1).**
Recover n from the bit length of u. For `u` with `|u| = n-1`, i.e.
`2^(n-2) <= u < 2^(n-1)`:

```text
u = 1 || (n-3-m ignored bits) || 0^(m-|d|) 1 d,     n := |u|+1,  m = floor(n/2)

f(u):
  n := |u|+1; if n < 5, return 0;
  read the low m+1 bits as the padded code; if all zero, return 0;
  recover d, run U(d) for n^c steps;
  if it halts with exactly n output bits, return their value; else 0.
```

The code field fits iff `m+1 <= n-2`, which holds for all `n >= 5` and
fails at `n = 4` (field 3, room 2). Inputs of other lengths map to 0 and are
harmless, since only coverage of compressible outputs matters. `Inc_c(4)` is
a single closed true sentence (7 descriptions, 16 candidate strings) and is
provable in PV_1 by finite evaluation. So the unary decoder has cutoff 5 with
n = 4 as a finite case; no even/odd split is needed. Coverage with
`a = 2^(n-1), b = 1`: every short halting description d has
`u_d = 2^(n-2) + code(d) < 2^(n-1)` and `f(u_d) = val(x)`.

## 4. Exact Pigeonhole and Eval Imports

PS21 Section 2.1 and ILW23 equation (7) support the plan's schema:

```text
forall a>0, forall b in Log, forall z,
  exists v<a(b+1), forall u<ab, f(u,z) != v.
```

The primed version drops z and uses only `f(u)`. Neither a, b, nor a witness
to `b in Log` is an input to f. One may expand b as `|B|`; a itself need not
belong to Log. There is no separate range-boundedness premise for f.

Keep the following distinctions explicit:

- `T_PV` is the true universal theory in the PV language, not another name
  for PV_1. Since `PV_1` is contained in `T_PV`, `UAPC_1` is contained in
  `T^0_APC = T_PV + dWPHP'(PV)`.
- PS21's `forall Sigma^b_1` conservativity does not transfer Inc, CInc, or
  Eval, whose existence matrices have `Sigma^b_2` form. Its hard-function/NW
  facts do not automatically supply the required K^t threshold either.
- ILW23 Section 2.3 presents parameterized APC using a one-extra-output-bit
  string schema; its Section 4.3 uses the near-equal **parameter-free**
  interval schema. We import that base and its exact Eval nonprovability,
  not an unproved identification of every APC/stretch presentation over PV_1.
- ILW23 footnote 14 (p. 16) asserts that the near-equal `dWPHP'(f)` implies
  the string version `dWPHP'_ell(f)` for every `ell(n) >= n+1` "in any
  reasonable base theory". This is a footnote claim, not a numbered theorem;
  our forward instance with `b = 1` uses the schema directly and does not
  depend on it.

For positive m, write the required fixed-stretch sentence as

```text
EvalAvoid_4:
  forall m in Log, m>=1,
  forall circuits C: {0,1}^m -> {0,1}^{4m},
  exists y in {0,1}^{4m}, forall x in {0,1}^m, Eval(C,x) != y.
```

This is ILW23 Section 4.1's sentence specialized to `ell(m)=4m`. The circuit
parameter has **no fixed bound `|C| <= m^k`**. A faithful explicit formula
guards the existential statement by `Circ_{m,4m}(C)` and retains a witness
for `m in Log`. Choose an ordinary explicit circuit encoding, a PV validity
predicate, and a total evaluator; invalid codes impose no obligation under
the guard. The paper does not specify bit-level malformed-code behavior.

Theorem 24 applies to constructive polynomial stretches. The linear
function 4m is time-constructible and a PV function. If zero is in the source
length domain, apply the theorem with `ell_*(m)=max(1,4m)` and prove the
elementary zero-length instance separately to connect its full sentence to
EvalAvoid_4. There is no stretch-amplification issue here.

The exact external hypotheses are:

- JLS-secure indistinguishability obfuscation as in Definition 10: perfect
  functionality, nonuniform adversary circuits of size
  `S(lambda)=lambda^{omega(1)}`, and distinguishing advantage at most
  `2^(-lambda^delta)` for some fixed `delta>0`. Do not replace this by
  ordinary polynomial security or require the paper's stronger
  subexponential-size-adversary notion.
- `coNP` is not contained in `i.o.NP/poly`: some coNP language has no
  NP/poly language agreeing with it on all strings at infinitely many
  complete input lengths. This concerns full length slices, not isolated
  inputs.

Under those hypotheses, Theorem 24 states
`T^0_APC does not prove dWPHP_ell(Eval)`. Nonprovability in UAPC_1 follows
by theory inclusion, not conservativity. These are external assumptions
for the metatheorem, not extra axioms of the target PV_1 proofs.

### Eval Bridge to Reconstruct

For one fixed evaluator program E, supply C as the free auxiliary string
and use `pair(E,x)` as the charged description. The pair encoding gives
length `m+C_E`. Establish a uniform polynomial simulation bound
`q(m+|C|+1)` and choose one fixed c with

```text
q(m+|C|+1) <= (4m+|C|+1)^c.
```

At sufficiently large m, `m+C_E <= 2m`; therefore a CInc_c witness of length
4m must avoid the range of C. The bound must hold for **arbitrary** circuit
description length, which is why the conditional clock includes `|z|`.

For each of the finitely many positive lengths below the overhead cutoff,
evaluate all `2^m` inputs and find a missing output among `2^m+1` distinct
4m-bit candidates. This is polynomial-time in `|C|` when m is fixed. Its
PV_1 correctness still needs a proof. These are finitely many **lengths**,
not finitely many circuit descriptions. Include the zero-length repair
above if needed. Finish by verifying the circuit/interval/string interface
to the exact ILW23 sentence.

## 5. Implication Ledger

`cited theorem` means a source asserts the stated result in that setting;
it does not mean every part of its proof has been independently audited.
`proof to reconstruct` identifies a concrete proof template whose internal
arithmetic verification remains. `unresolved` means no completed derivation
or matching source has been established here.

| Implication / result | Status | What is still required |
| --- | --- | --- |
| Empty solves Korten's `K_U^t-Random` | `cited theorem` | Search reduction only; U and t fixed, input `1^n` |
| `VAPC proves CG's HiKt[c]` | `cited theorem` | Source's convention discrepancies recorded, not silently repaired |
| CG's exact theorem transfers to our Inc_c | `unresolved` | Machine, boundary, and two-sorted interpretation; bypass rather than rely on this |
| `APC_1 proves Inc_c` and `APC_1 proves CInc_c`, each fixed c | `proof to reconstruct` | Direct parameterized decoder with `a=2^(n-1), b=1`; all PV definitions and coverage proofs |
| `UAPC_1 proves Inc_c`, each fixed c | `proof to reconstruct` | Genuinely unary decoder, including prefix costs and initial-interval coverage |
| `PV_1 + CInc_c proves EvalAvoid_4`, for one sufficiently large fixed c | `proof to reconstruct` | Evaluator description, uniform clock, validity guard, finite-length repair, and source coding bridge |
| Under ILW23 hypotheses, `T^0_APC` does not prove the specified Eval sentence | `cited theorem` | Apply Thm. 24 with positive-length 4m and the zero-length convention recorded above |
| Under ILW23 hypotheses, `PV_1 + {Inc_c}` does not prove the chosen CInc_c, via `T^0_APC` | `proof to reconstruct` | Section 5a shortcut: define the unary decoder and evaluator description; correctness lemmas are true universal sentences, hence axioms of `T_PV`; then apply Thm. 24 |
| Same conclusion with the bridges proved inside PV_1 (`UAPC_1 proves Inc_c`; `PV_1 + CInc_c proves EvalAvoid_4`) | `proof to reconstruct` | The rows above; needed for the positive characterizations, not for the separation itself |
| Full Inc/dWPHP' and CInc/dWPHP equivalences over PV_1 | `unresolved` | Full-schema reversals and precise stretch conversions; deferred, not prerequisites |

Here `Inc_c` and `CInc_c` in theory assertions mean the length-universal
sentences with cutoff 4. The unconditional schema has a separate sentence
for each standard c; the priority negative target is one conditional
sentence for a fixed c, not merely failure to prove the entire schema.

### 5a. Weaker-Base Shortcut to the Conditional Separation

Fable 5.1 amendment; own reasoning, not a source theorem, and not yet
independently checked. The plan's priority conclusion is

```text
PV_1 + {Inc_c : c >= 1}  does not prove  CInc_{c0}   (under ILW23's hypotheses)
```

for one fixed c0. This does not require the bridges to be proved inside
PV_1. It suffices that:

1. `T^0_APC proves Inc_c` for every c, so `PV_1 + {Inc_c}` is a subtheory
   of `T^0_APC`;
2. `T^0_APC + CInc_{c0} proves EvalAvoid_4`;
3. `T^0_APC does not prove EvalAvoid_4` (Thm. 24 with `ell_* = max(1,4m)`).

Then (2) and (3) give `T^0_APC does not prove CInc_{c0}`, and (1) transfers
this down to `PV_1 + {Inc_c}`.

Since `T_PV` contains every true universal PV sentence, the correctness
lemmas behind (1) and (2) are axioms of `T^0_APC` rather than proof
obligations, provided they have the form `forall (quantifier-free)` with
PV-decidable matrix and are true in N. Concretely:

- For (1): `forall N, d, x: (|d| <= m and Halt_c(d, x, n^c)) -> (u_d < 2^(n-1)
  and f(u_d) = val(x))` for the Section 3 unary f. What remains is to
  *define* f as a PV function and instantiate `dWPHP'(f)` with
  `a = 2^(n-1), b = 1`; the n = 4 case is a closed true sentence.
- For (2): `forall m, C, x': (valid(C) and |x'| = m) -> Halt_{c0}(pair(E,x'),
  C(x'), 4m, C)` for a fixed evaluator E and one clock exponent c0 covering
  evaluation plus universal simulation, and, for each fixed `m < M`, the
  universal correctness of a brute-force PV function returning a string
  outside the range of C. What remains is to define E, choose c0 and M, and
  fix the circuit validity predicate and evaluator.

The `PV_1`-internal proofs (D1, D2, D4 below) remain necessary for the
positive statements `UAPC_1 proves Inc_c` and `PV_1 + CInc_c proves
EvalAvoid_4`, and for any later equivalence. They are not needed for outcome
2g. This reorders Step 1: the cheapest first milestone is (1) and (2) over
`T^0_APC`, then upgrading the bridges to PV_1.

## 6. Gate A Decision and Handoff

**Decision: proceed to Step 1 via outcome 0b (only part of the target
located).** The required source statements,
threshold choices, and Eval instance are now identified. We will reconstruct
our own forward proof rather than claim a literal transfer of CG. No
primary-source question found in this pass requires delaying that decoder
proof. No exact matching classification or separation has been established
as known or new by this limited check.

Step 1 should produce these obligations in order:

1. **D1: representation and simulation.** Fix the concrete U and total
   halting predicate with the Section 2 encodings. Prove recovery, leading
   zero preservation, clock semantics, and polynomial bounds in PV_1.
2. **D2: parameterized decoder.** Define the Section 3 decoder as a total
   PV function and prove the explicit preimage implication for every short
   successful description. Instantiate the displayed doubling interval to
   obtain the APC_1 forward sentences.
3. **D3: unary decoder.** Define the Section 3 unary layout as a PV function
   (cutoff 5, n = 4 finite) and prove the precise numeric interval instance
   including lower input-length slices. For the Section 5a shortcut only the
   definition and the truth of its correctness lemmas are needed; for
   `UAPC_1 proves Inc_c` the lemmas must be proved in PV_1.
4. **D4: fixed-program simulation.** Prove additive description overhead and
   uniform polynomial simulation bounds, specializing to the evaluator as
   preparation for Section 4's Step 2 reversal.

There is no completed Step 1 proof in this note. In particular, neither
hard-function existence nor ordinary counting substitutes for D3. If an
argument only works over S^1_2 or T_PV, record that fact instead of silently
promoting it to a PV_1 proof; Section 5a is deliberately such a `T_PV`-level
argument and is labelled as one.

Step 0 items 4-5 remain deferred until a specific reversal/stretch question
requires them; item 6 remains deferred until before Step 3. Exhaustive
novelty work is not a prerequisite, and the lack of a matching result in
this pass does not establish an open problem. Before the next research
pass, record the next target and time cap.

### Verification Record

An independent write-up audit checked the supplied primary-source extracts,
the source locators, threshold arithmetic, decoder interval, Eval instance,
security hypotheses, and status labels. It found no actionable errors or
remaining Step 0 blockers. This was not a complete independent verification
of the cited papers' proofs or of the antecedents cited by PS21, and did not
establish novelty.

Finite sanity checks for `n=4..16` covered 1,507 description instances:
delimiter recovery, preservation of leading zeros and the empty string,
agreement with sentinel numeric values, injectivity, strict/non-strict
threshold counts, and the doubling-domain inequality. All passed. These
checks are not a PV_1 proof. Whitespace checks passed for both this new note
and the modified plan.
