# Step 2: Concrete Circuit Encoding and the Transfer of ILW23's Negative Result

**Status (September 5, 2026): T3 interface closed at paper level after
audit and Astra's concurrence corrections (Section 7); Fable 5.1's
rebuttal review is next. Conditional separation T3' stands under the
residual assumptions of Section 5. Novelty unassessed.** This note fixes one concrete circuit
encoding for `(NativeCirc, NativeEval)`, verifies properties (E-a)/(E-b) of
[step1_decoder.md](step1_decoder.md) Section 6.5 for it, and writes the
explicit transfer from `T^0_APC proves NativeAvoid_4` to a contradiction
with ILW23, going through ILW23's Theorems 25 and 28 rather than the
statement of Theorem 24. Definitions, lemma names, and the sentences
`Inc_c`, `CInc_c`, `EvalAvoid_4`, `NativeAvoid_4` are those of
`step1_decoder.md`; nothing there is redefined.

## Work Record

Started 2026-09-05, 22:19 UTC (Fable 5.1), following `step1_decoder.md`
Section 6.8. Cap: 90 minutes plus one bounded independent audit. Target:
items 1-3 of the 6.8 list. Source: ECCC TR23-038 (original March 2023
report) text-extracted again; Section 4.1 (p. 13), Definition 19,
Theorems 20-21 (pp. 13-14), Theorems 24-25, Definition 26, Theorems 27-28
(pp. 17-18) were read directly, not from memory. No literature search;
novelty remains unassessed.

## 1. What the source provides, re-read

ILW23 derives Theorem 24 (`T^0_APC` does not prove `dWPHP_ell(Eval)`)
from three pieces:

- **Theorem 25** ([PS21, Theorem 4]). For every quantifier-free
  `phi(x,y,z)` in `L(PV)`, if `T^0_APC proves forall x exists y forall z
  phi(x,y,z)`, then there are `k in N` and functions `f_1(x)`,
  `f_2(x,z_1)`, ..., `f_k(x,z_1,...,z_{k-1})`, each computable by a family
  of polynomial-size deterministic circuits, such that for all `x` and all
  `m_1,...,m_k`, some disjunct `phi(x, f_i(x,m_1,...,m_{i-1}), m_i)` is
  true in the standard model. `x` may be a tuple.
- **Definition 26.** A polynomial-size circuit family `{F_s}` with at most
  `k` circuit-inversion oracle gates (fan-in `s`, fan-out `s`) solves AVOID
  with stretch `m` if for every circuit `C:{0,1}^n->{0,1}^m` of size `s`
  and every `O:{0,1}^m->{0,1}^n` that returns a preimage whenever one
  exists, `F_s(C)` outputs `y in {0,1}^m` with `C(O(y)) != y`, the gates
  being interpreted as `O` (the `s-m` unused gate inputs are ignored; the
  `s-n` unused gate outputs are 0). So `n <= s` and `m <= s` are implicit.
- **Theorem 27.** If `T^0_APC proves dWPHP_ell(Eval)` then AVOID with
  stretch `ell` has such a family. Its proof applies Theorem 25 to the
  Eval sentence and runs the Student-Teacher game with the oracle gate as
  Teacher, on "circuits encoded by an s-bit string", computing `n` from
  the code.
- **Theorem 28.** For `m(n)=poly(n)` with `m>=n+1` and `k=O(1)`, under
  JLS-secure iO and `coNP not in i.o.NP/poly`, AVOID with `m` outputs has
  no polynomial-size circuit family with at most `k` inversion gates. The
  paper gives a proof sketch reducing to the proof of Theorem 21.

Consequence for us. Theorem 25 is a statement about arbitrary open
`L(PV)` matrices; Theorem 28 is a statement about the search problem
AVOID on Boolean circuits. Neither mentions the paper's `Eval`. Theorem 27
is the only encoding-dependent step, and it is a template: we can apply
Theorem 25 to *our* sentence `NativeAvoid_4` and build the Definition 26
solver ourselves. The paper's evaluator, its validity predicate, and the
statement of Theorem 24 then never enter. This is a sharper reading than
Section 6.5 of `step1_decoder.md`, which still framed the obligation as
matching Theorem 24's sentence; what survives from 6.5 is exactly (E-a)
(an efficient map from AVOID instances into our codes) and (E-b) (output
bound, used by the wrapper W2/W3).

What does remain encoding-dependent is the *input format* of Theorem 28:
its AVOID instances are "Boolean circuits of size s" in the paper's
unspecified description. This gives the one residual interface
assumption, (P) in Section 5.

## 2. The concrete encoding

A native circuit code is a number `B>=1`; the description is the string
`p = str(B)` (Section 0.1 sentinel convention, so `B = enc(p)` and every
binary string, including those with leading zeros, is a code). `B=0` is
invalid.

**Format.** With `w>=1` the index width, `k>=0` the number of inputs,
`l>=0` the number of outputs, `g>=0` the number of gates, and `bin_w(r)`
the `w`-bit big-endian numeral of `r<2^w`:

```text
p = 1^w 0 . 1^k 0 . bin_w(l) . bin_w(g) . gate_0 ... gate_{g-1} . out_0 ... out_{l-1}
gate_j = op_j . bin_w(a_j) . bin_w(b_j)        (op_j two bits)
out_i  = bin_w(o_i)
|p| = (w+1) + (k+1) + 2w + g(2+2w) + l*w
```

Wires are numbered `0..k+g-1`: wire `i<k` is input `i`, wire `k+j` is
gate `j`. Operations: `00` AND(`a`,`b`), `01` OR(`a`,`b`), `10` NOT(`a`)
(`b` ignored), `11` constant 1 (`a`,`b` ignored). Input arity is unary so
that `|p| >= k+1`; output count and gate count are `w`-bit numerals, so
`|p| >= l*w >= l` and `|p| >= 2g`.

**Validity `Valid(p)`.** All of:

- (V1) `p` starts with `1` (so `w>=1`); the header `1^w 0 1^k 0` and the
  two `w`-bit fields are present;
- (V2) the total length is exactly `(w+1)+(k+1)+2w+g(2+2w)+l*w`;
- (V3) for each gate `j`: `a_j < k+j` when `op_j` is `00`, `01`, or
  `10`; `b_j < k+j` when `op_j` is `00` or `01`; no constraint for `11`
  (a constant gate at wire 0 has no earlier wire to name);
- (V4) for each output `i`: `o_i < k+g`.

Header fields are read by PV functions `In(B)`, `NativeOut(B)` (returning
`k`, `l` when `B>=1` and `Valid(str(B))`, else 0). `NativeOut` is distinct
from Step 1's sentinel bound `Out(X) = max(2, Top(X)^4)`. Define

```text
NativeCirc(B,k,l) := B>=1 and Valid(str(B)) and In(B)=k and NativeOut(B)=l.
```

**Evaluation.** `NativeEval(B,u)`: if `B=0` or not `Valid(str(B))`,
return 0. Otherwise set `v_i := bit_i(u)` for `i<k` (bit `i` of `u` is the
`2^i` digit, `MSP(u,i) mod 2`; digits of `u` at positions `>= k` are
ignored), evaluate gates in order `j=0..g-1` by the table above, and
return

```text
y = sum_{i<l} v_{o_i} * 2^i.
```

Malformed codes and widths: any failure of (V1)-(V4) makes `NativeCirc`
false for every `(k,l)` and `NativeEval` return 0. Descriptions have
arbitrary length; no bound `|B| <= m^c` is imposed anywhere. The
zero-input case `k=0` is a valid header `1^w 0 0 ...`; such a circuit has
only constant and NOT/AND/OR gates over earlier gates, and
`NativeEval(B,0)` is its constant value. No circuit output count is
required to be positive; `l=0` yields `y=0<2^0`.

**Resources.** Parsing is linear in `|p|`. Since `k+1 <= |p|` and
`2g <= |p|`, the wire array has at most `|p|` entries; each gate costs
`O(w)` bit operations plus two lookups; each input bit costs one shift of
`u` by `i < |p|`. So `Valid`, `In`, `NativeOut`, `NativeCirc`, and `NativeEval`
are polynomial-time in `|B|+|u|+|k|+|l|`, hence PV functions. (Had `k`
been stored in binary, a code could name exponentially many inputs; the
unary field is what makes the arity a length resource, matching
Definition 26's implicit `n <= s`.)

**Standard semantics.** For a valid code with arities `(k,l)`, write
`G_p(u)` for the value computed by the straight-line program `p` on input
bits `bit_0(u),...,bit_{k-1}(u)`, output read as the `l`-bit number with
`out_i` at digit `2^i`. This is the ordinary semantics of a gate list;
`NativeEval` computes it by definition.

## 3. Properties (E-a) and (E-b)

**(E-b).** `NativeCirc(B,k,l) -> NativeEval(B,u) < 2^l` for every `u`,
not only `u<2^k`: the return value is a sum of `l` bits at digits
`0..l-1`. The bound is a true universal PV sentence. It enters W2 (`v <
Out(X)` never fails for valid `C=Wrap(B)` at the required arities) and W3.

**(E-a), native format.** Take `code = identity`. For every valid `p`
with arities `(k,l)`, `NativeCirc(enc(p),k,l)` holds and
`NativeEval(enc(p),u) = G_p(u)` for all `u`; arities are unique (`In`,
`NativeOut` are functions of `p`) and PV-readable; `|code(G)| = |G|`.

**(E-a), other standard descriptions.** Call a description scheme `S` for
Boolean circuits *standard* if from an `S`-description of length `s` one
can compute in `poly(s)` time the input arity `n<=s`, output arity
`m<=s`, and a topologically ordered gate list over a constant-fan-in
basis (unbounded fan-in AND/OR expanded into binary trees, any other
constant-fan-in basis gate replaced by its fixed `{AND,OR,NOT,1}`
subcircuit). Then `code_S` writes `w = max(1, |k+g|, |l|)` (so that all
wire indices, `g`, and `l` fit in `w` bits), the header, the gates, and
the outputs; it runs in `poly(s)` time, with
`|code_S(G)| = O(w(g+l+1)+k+1) = poly(s)`. The definition of `S` bounds
the expanded gate count `g` only by `poly(s)`, not necessarily `O(s)`;
the polynomial bound is all the transfer needs. Also,
`NativeEval(code_S(G),u) = G(u)` for
`u<2^n` because both sides compute the same straight-line program on the
same input bits. Semantics preservation is the correctness of a
syntactic re-encoding; it is needed as a *true* statement (Section 4
uses it in the standard model), not as a PV_1 theorem.

**Consistency with the Step 1 interfaces.** Everything in
`step1_decoder.md` that referred to the abstract pair is satisfied:

- 0.4: `NativeCirc` is a PV validity/arity predicate with unique arities;
  `NativeEval` is total PV; evaluation on `u<2^k` is below `2^l`.
- W1-W3 (4.4): W1 is `Val(Wrap(B))=B`; W2 needs (E-b) at `l=4m`; W3 is the
  sentinel identity. All remain true universal PV sentences.
- Zero-length identity (4.4, 6.1): `NativeCirc(B,0,1) -> NativeEval(B,0)
  < 2`, by (E-b).
- E's algorithm (4.1): reads `m=|x'|`, decodes `B` from raw `z`, checks
  the canonical word and `NativeCirc(B,m,ell(m))`, computes
  `NativeEval(B,val(x'))`, writes `ell(m)` bits. Polynomial in `m+|z|`;
  the L2 clock argument and `c_0 = d + ceil(log_2 K)` are unchanged.
- L3 (4.1): for constant `k<M_0`, evaluates `2^k` inputs; polynomial in
  `|C|`.

No definition of Step 1 changes; the abstract contract is now instantiated.

## 4. The transfer

### 4.1 Logical form

Let `Guard(M,B) := |M|>=1 and NativeCirc(B,|M|,4|M|)` and

```text
phi(M,B,y,u) := not Guard(M,B)
                or ( y < Pow(M)^4 and ( not u < Pow(M) or NativeEval(B,u) != y ) ).
```

`phi` is quantifier-free in `L(PV)` (the predicates are 0/1-valued PV
functions, `Pow(M)^4` a PV term). `NativeAvoid_4` of Section 4.4 is
logically equivalent to `forall M forall B exists y forall u
phi(M,B,y,u)`: if the guard fails any `y` works; if it holds, the bounded
witness of one form is the witness of the other. Hence `T^0_APC proves
NativeAvoid_4` iff `T^0_APC proves forall M,B exists y forall u phi`.

### 4.2 Theorem T3' (conditional separation, interface closed)

Assume (H1) JLS-secure iO exists and (H2) `coNP` is not contained in
`i.o.NP/poly`, exactly as in `step0_baseline.md` Section 4. Assume
Theorem 25 and Theorem 28 of ILW23 as stated, and (P) of Section 5. Fix
the encoding of Section 2 and the efficient-machine contract of Section
0.3 with its constants `E, K, d, c_0`. Then

```text
T^0_APC  does not prove  NativeAvoid_4;
T^0_APC  does not prove  CInc_{c_0};
```

hence neither `UAPC_1` nor `PV_1 + {Inc_c : c>=1}` proves `CInc_{c_0}`,
while `APC_1` proves it (F1, accepted at paper level in `step1_decoder.md`
Section 6.4).

### 4.3 Proof

**Step 1 (witnessing).** Suppose `T^0_APC proves NativeAvoid_4`. By 4.1
and Theorem 25 with `x=(M,B)`, `y=y`, `z=u`, there are `k` and
`f_1,...,f_k`, computable by polynomial-size circuits in the bit-lengths
of their arguments, such that for all `M,B` and all `u_1,...,u_k` some
`phi(M,B, f_i(M,B,u_1,...,u_{i-1}), u_i)` is true.

**Step 2 (the solver).** Let `ell_*(n) = max(1,4n)`. Let `S` be the
description scheme of Definition 26's instances (assumption (P): it is
standard in the sense of Section 3). Following the proof of Theorem 27,
`s` is the description length ("circuits encoded by an s-bit string");
(P)'s `n, m <= s` refers to this `s`. Strings and numbers are identified
by one convention throughout: bit `i` of an input `x in {0,1}^n` is the
`2^i` digit of the number `x`, and likewise for outputs `y in {0,1}^m`;
this same convention is used for `C(x)`, for the oracle's `m`-bit query
and `n`-bit answer, and in `NativeEval` (Section 2). Define the circuit
family `{F_s}`, on an `S`-description `C` of length `s` of a circuit
`{0,1}^n -> {0,1}^{ell_*(n)}`:

```text
0. Compute n and m from C.  If n=0 (so m=1): evaluate C() and output 1-C().
1. B := code_S(C);  M := 2^n - 1  (an n-bit number).
2. For i = 1..k:
     y_i := f_i(M, B, x_1, ..., x_{i-1});
     if y_i < 2^{4n}:
        x_i := O(y_i)   [oracle gate; the n used output bits]
        if C(x_i) != y_i: output y_i (as a 4n-bit string) and halt;
     else x_i := 0^n.
3. Output 0^m.   [unreachable, shown below]
```

`C(x)` in step 2 is standard evaluation of the `S`-description, a
`poly(s)`-size subcircuit. The `4n`-bit query occupies `4n <= s` of the
gate's `s` input wires, the rest fixed as Definition 26 prescribes.

Within one `F_s`, choose a polynomial bound `L(s)>=1` on each argument's
canonical bit length. At stage `i`, `f_i` has `r_i=i+1<=k+1` arguments
(`M,B,x_1,...,x_{i-1}`). For every length profile
`lambda in {0,...,L(s)}^{r_i}`, hardwire a circuit computing `f_i` on
canonical arguments of those lengths, using the tuple encoding of the
witnessing family. Compute the actual argument lengths from their
fixed-width storage (`|0|=0`); feed each copy the bits for its profile,
zero-extend its numerical output to a common polynomial width, and
select the output of the matching copy. Only that copy must receive
valid canonical inputs. There are at most `(L(s)+1)^{r_i}` copies, each
of polynomial size. Since `k` is constant, the entire selector has
polynomial size and uses only ordinary Boolean gates. Select `y_i`
**before** the stage's single inversion gate; do not duplicate oracle
gates for the profiles. This constructs one `F_s` without assuming that
the witnessing circuits tolerate leading-zero padding of their inputs.

**Step 3 (correctness).** Fix `n>=1`, `C`, and an inverter `O` as in
Definition 26. By (E-a) for `S`, `NativeCirc(B,n,4n)` and
`NativeEval(B,u) = C(u)` for `u<2^n`; with `|M|=n`, `Guard(M,B)` holds and
`Pow(M) = 2^n`, `Pow(M)^4 = 2^{4n}`. Suppose the run reaches step 3. Then
for every `i`, not (`y_i < 2^{4n}` and `C(x_i) != y_i`). Apply Step 1 with
`u_i := x_i` (each `x_i < 2^n = Pow(M)`): some disjunct is true, and since
the guard holds it says `y_i < 2^{4n}` and `NativeEval(B,x_i) != y_i`,
i.e. `C(x_i) != y_i`. Contradiction. So the run halts in step 2 at some
`i` with `y_i < 2^{4n}` and `x_i = O(y_i)` and `C(O(y_i)) != y_i`, which
is what Definition 26 requires. For `n=0` the output `1-C()` avoids the
range directly.

**Step 4 (size and gate count).** `code_S` is `poly(s)`; `M` has `n<=s`
bits; each `f_i` receives total argument length at most
`|M|+|B|+(i-1)n = poly(s)`. Its length-profile circuit bank and selector
from Step 2 have polynomial size. The evaluations `C(x_i)`, comparisons,
and padding to `4n <= s` bits are also `poly(s)`. Each of the `k` stages
uses at most one inversion gate after selection, so there are at most
`k` oracle gates, `k` a constant fixed by Step 1. Thus `{F_s}` is a
polynomial-size family solving AVOID with stretch `ell_*`.

**Step 5 (Theorem 28).** `ell_*(n) = poly(n)` and `ell_*(n) >= n+1` for
all `n`. Under (H1), (H2), Theorem 28 says no such family exists.
Therefore `T^0_APC` does not prove `NativeAvoid_4`.

**Step 6 (descent).** By T2, `T^0_APC + CInc_{c_0} proves EvalAvoid_4`;
by the wrapper implication of 4.4 (W1-W3, true universal sentences, now
instantiated by Section 3), `T_PV proves EvalAvoid_4 -> NativeAvoid_4`.
So `T^0_APC proves CInc_{c_0}` would give `T^0_APC proves NativeAvoid_4`.
Hence `T^0_APC` does not prove `CInc_{c_0}`. By T1, `PV_1 + {Inc_c}` is a
subtheory of `T^0_APC`, and `UAPC_1 = PV_1 + dWPHP'(PV)` is one by
definition; nonprovability descends to both. `APC_1 proves CInc_{c_0}` is
F1. QED.

### 4.4 Audit notes on quantifiers and resources

- Theorem 25 is applied to a single `exists y forall u` block with the
  bounds folded into `phi`; the tuple `x=(M,B)` is allowed by the
  statement. The disjunction is used only at `u_i := x_i`, all below
  `Pow(M)`, so the `not u < Pow(M)` branch of `phi` is never the true
  one.
- The witness output must lie in `{0,1}^{4n}`; this is why the solver
  tests `y_i < 2^{4n}` before querying and why the `else` branch supplies
  a dummy `x_i`. Without the test, an early `y_i` with `C(x_i) != y_i`
  but `y_i >= 2^{4n}` would be an invalid output.
- Definition 26 quantifies over *all* inverters `O`; the argument uses
  only `C(O(y)) = y` when a preimage exists, and never inverts the native
  code, so the gate semantics match exactly.
- `n <= s` and `4n <= s` are needed for `M` and the padded queries; both
  are implicit in Definition 26 (gate fan-in/fan-out `s`) and hold for
  every standard scheme in the sense of Section 3.
- The zero-length repair of 4.4 (`ell_*`, witness `5-Eval(C,1)`) is not
  used in this route: Theorem 25 is applied to the positive-length
  sentence and the solver treats `n=0` directly. The repair remains
  correct and is kept for a statement-level citation of Theorem 24, which
  this note does not rely on.
- Theorem 28 is applied with `m(n) = ell_*(n)`, not `4n`, so that
  `m(0) >= 1`; for `n>=1` the two agree.
- The proof of Theorem 28 in the source is a sketch relative to Theorem
  21; we cite the theorem as stated. This is the same reliance the paper's
  own Theorem 24 has.

## 5. Residual assumptions, exactly

The result of 4.2 rests on:

- (H1), (H2): the two hypotheses of ILW23 Theorem 24/28, unchanged.
- Cited: ILW23 Theorem 25 (= PS21 Theorem 4) and Theorem 28, as stated.
- (P): the AVOID instances of Definition 26 / Theorem 28 are Boolean
  circuits given in a standard description scheme in the sense of Section
  3 (polynomial-time extraction of arities `n,m <= s` and an ordered gate
  list). The paper writes "a circuit `C:{0,1}^n->{0,1}^m` of size `s`"
  and "circuits encoded by an s-bit string" and never fixes bits; (P)
  is what "Boolean circuit" means in that sentence. It is the only
  encoding assumption, and it concerns the paper's format, not ours.
- The efficient-machine contract of Section 0.3 and the truth of L0-L3,
  W1-W3, E0/E1, A1-A6 for the fixed `U` and the Section 2 encoding (the
  `T_PV` route of Section 4 of `step1_decoder.md`).

Not claimed: a PV_1 proof of L2 or of the wrapper; a certified concrete
`U` or numeral for `c_0`; novelty (Gate D); any statement about `PV_1`
versus `UAPC_1`; any full-schema equivalence.

## 6. Finite checks

[check_step2.py](check_step2.py) implements the Section 2 encoding and
evaluator, generates random valid gate lists at small arities, and
checks: `NativeEval` agrees with an independent reference evaluator on
every input ((E-a) with `code = identity`); the output bound (E-b) on
all inputs including `u >= 2^k`; arity uniqueness and readability;
rejection of `B=0`, `w=0`, truncated and over-long codes, out-of-order
wire references, and out-of-range outputs; the zero-input case; and the
wrapper identities W1-W3 and the zero-length identity with the real
`NativeEval` substituted into the Section 0.4 `Eval`. It also runs the
Section 4.3 solver against brute-force `f_i` stand-ins on tiny instances
to exercise the `y_i < 2^{4n}` test and the halting logic. Run:

```sh
python3 check_step2.py
```

Standard library only. These are finite sanity checks of the encoding
and the solver's control flow; they do not implement Theorem 25's
witnessing functions or the length-profile circuit construction, `U`,
or ILW23's format, and prove nothing in PV_1.

## 7. Audit record

Initial bounded independent audit, September 5, 2026 (fresh context; read this
note, the ILW23 excerpt including the proof of Theorem 21, and
`step1_decoder.md` Sections 0, 4, 6.5; ran `check_step2.py`). Findings by
question: (a) logical form for Theorem 25, OK; (b) Definition 26
compliance including the `y_i < 2^{4n}` test, the dummy round, `n=0`,
and the choice `u_i := x_i`, OK; (c) size bounds and `M = 2^n-1`, OK;
(d) Theorem 28 hypotheses, OK; (e) (P) is the only encoding assumption
and nothing needs the paper's `Eval`, encoding invariance, or PV_1
provability, OK; (f) encoding V1-V4, totality, arity uniqueness, (E-b),
polynomial time, edge cases `l=0`, `k=0`, `k=g=0`, OK; (g) descent and
W1-W3 needing only (E-b) plus Step 1 arithmetic, OK; (h) status wording,
OK. That audit reported no BLOCKING or SHOULD-FIX items. Four MINOR
clarifications were requested and applied in Section 4.3 at that time:
`s` is description length as in
Theorem 27's proof; one string/number bit convention shared by `C`, `O`,
and `NativeEval`; the `f_i` are hardwired at a fixed padded argument
length inside `F_s`; F1 carries its paper-level status label. Its verdict
was that the transfer closes the T3 interface obligation at ordinary
paper-proof level, subject to the residual assumptions of Section 5.
The padding clarification and the no-should-fix verdict are superseded
by the concurrence review below.

Two spec errors were caught earlier by writing `check_step2.py`, before
the audit: (V3) originally constrained the operand of constant gates,
which made the zero-input circuit unencodable; and `code_S` chose the
index width from `k+g` alone, too narrow for `l = 4k`. Both are fixed in
Section 2 and Section 3 as now written.

**Astra concurrence and corrections, September 5, 2026.** The mathematical
route and intended separation were accepted, but three local corrections
were required before an unqualified paper-level sign-off:

1. Theorem 25 does not promise that a circuit for a larger canonical input
   length computes `f_i` correctly on padded shorter arguments. Section
   4.3 now uses a polynomial-size bank indexed by argument-length
   profiles, with selection before each inversion gate. A targeted
   independent check confirmed this objection and repair; the constant
   number of oracle gates is unchanged.
2. The new output-arity function collided with Step 1's `Out(X)` sentinel
   bound. It is now `NativeOut` in Section 2 and `check_step2.py`;
   Step 1's definition is unchanged.
3. Section 3's definition of a standard scheme guarantees only a
   polynomial-size expanded gate list. The unsupported `O(s log s)`
   bound for `code_S` is replaced by `poly(s)`, which suffices.

With these corrections, Astra accepts T3' at ordinary paper-proof level
under Section 5's assumptions, not as a novelty claim or a PV_1-internal
reversal. Fable 5.1's rebuttal review of these corrections is pending;
no such review is claimed here.

## 8. Status

| Result | Status | Remaining |
| --- | --- | --- |
| Concrete `(NativeCirc, NativeEval)` | Fixed (Section 2); PV, total, arbitrary description length | None |
| (E-a), (E-b) | Established for the fixed encoding; (E-a) for other standard schemes via `code_S` | None at the `T_PV` level |
| `T^0_APC` does not prove `NativeAvoid_4` | Derived from Theorem 25 + explicit solver + Theorem 28 under (H1), (H2), (P); audit and concurrence corrections in Section 7 | Fable's rebuttal review |
| T3' (`T^0_APC`, `UAPC_1`, `PV_1+{Inc_c}` do not prove `CInc_{c_0}`) | Derived from the above, T1, T2, and the wrapper; accepted by Astra after corrections | Fable's rebuttal review; novelty (Gate D) |
| Statement-level citation of Theorem 24 | Not used; would additionally need the paper's `Eval` identified | Optional |

Not machine-checked; `check_step2.py` is a finite sanity check only.

**Next:** Fable 5.1's rebuttal review, focused on the three concurrence
corrections in Section 7, especially the length-profile construction in
Section 4.3. Do not begin Gate D until that review is resolved.

After that review, the research target remains the focused novelty check
(Gate D), per `step1_decoder.md` Section 6.8, before any work on L2 inside
PV_1. Suggested terms are listed there. A reconstruction of a known
result is an acceptable endpoint.
