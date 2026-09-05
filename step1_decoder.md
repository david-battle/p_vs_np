# Step 1: Definitions, Decoder Lemmas, and the T^0_APC Route

## Work Record

Started 2026-09-05, 20:40 UTC (Fable 5.1, first pass on Step 1, following
[step0_baseline.md](step0_baseline.md) and Astra's three corrections).
Target: fix the one-sorted definitions; prove the forward implications from
the parameterized and unary decoders at the level of explicit lemma
statements; write the guarded universal lemmas L0-L3 and derive the
conditional separation over `T^0_APC`; isolate what remains for the PV_1
versions. Time cap for this pass: 90 minutes. No literature search.

What this note is: a structured proof with every lemma stated explicitly
and its provability status labelled. What it is not: a checked PV_1
derivation. Every "PV_1: routine" label is an expectation to be discharged,
not a claim already verified.

## 0. Conventions

### 0.1 Strings as numbers

A binary string `s` is represented by its sentinel encoding

```text
enc(s) = 2^|s| + val(s)        enc(empty) = 1,     |enc(s)| = |s| + 1.
```

Leading zeros of `s` are preserved. `0` is not the encoding of any string and
serves as the universal failure value. For a number `S >= 1` write `str(S)`
for the string it encodes and `len(S) = |S| - 1` for that string's length.

Fact E1 (sentinel encoding). For all strings `s` and all `S >= 1`:
`str(enc(s)) = s`, `enc(str(S)) = S`, `len(enc(s)) = |s|`, and
`enc(s) < 2^(k+1)  iff  |s| <= k`.
Status: true; PV_1: routine (open induction on notation over the standard
PV definitions of `|.|`, `2^|.|`, and bit operations).

A useful coincidence: the `(m+1)`-bit padded code `0^(m-|d|) 1 d` used by
Korten's construction has numeric value `2^|d| + val(d) = enc(d)`. So
"pad `d` to `m+1` bits with a leading 1" and "take the sentinel encoding of
`d`" are the same number, and the set of all descriptions of length at most
`m` is exactly `{D : 1 <= D < 2^(m+1)}`.

### 0.2 Length witnesses

Bit lengths are supplied by numbers: `n = |N|`. Every function below reads
`N` only through `|N|`; a running time of `|N|^c` steps is polynomial in the
bit length of the input `N`, so such functions are PV functions. Binary `n`
alone would not be an adequate resource. Write `Pad4(M)` for a PV term with
`|Pad4(M)| = 4|M|` (for example `(1#M)^4 - 1`, with `1#M = 2^|M|`).

### 0.3 The machine and the simulation function

Fix once and for all:

- a universal machine `U` taking a description `d` and an optional auxiliary
  string `z`, with a definite halting convention and a designated output
  tape; `U(d,z)` "halts with output `x` within `t` steps" has the obvious
  meaning; the auxiliary input is not charged to `|d|`;
- the CG pairing `pair(M,w) = dbl(M) || 01 || w` for two-part descriptions,
  `|pair(M,w)| = 2|M| + 2 + |w|`, with `M` nonempty; a description that does
  not parse as a pair is treated by `U` as a non-halting computation.

For each standard `c >= 1` define PV functions

```text
Sim_c(D, N)      = enc(x)  if D >= 1 and U(str(D)) halts with output x
                           within |N|^c steps;
                 = 0       otherwise.

CSim_c(D, Z, N)  = enc(x)  if D >= 1, Z >= 1, and U(str(D), str(Z)) halts
                           with output x within (|N| + |Z|)^c steps;
                 = 0       otherwise.
```

The clock `(|N| + |Z|)^c` equals the plan's `(n + |z| + 1)^c` because
`|Z| = |z| + 1`. Both functions are polynomial-time in `|D| + |Z| + |N|` and
depend on `N` only through `|N|`.

Fact S0 (length-only dependence). `|N| = |N'|  ->  Sim_c(D,N) = Sim_c(D,N')`,
and likewise for `CSim_c`.
Status: true; PV_1: routine if `Sim_c` is defined by a PV term in which `N`
occurs only inside `|N|`.

### 0.4 The target sentences

With `m(N) = floor(|N|/2)`:

```text
Inc_c  :=  forall N [ |N| >= 4 ->
             exists X ( |X| = |N|+1  and
               forall D ( 1 <= D < 2^(m(N)+1)  ->  Sim_c(D,N) != X ) ) ]

CInc_c :=  forall N forall Z [ |N| >= 4 and Z >= 1 ->
             exists X ( |X| = |N|+1  and
               forall D ( 1 <= D < 2^(m(N)+1)  ->  CSim_c(D,Z,N) != X ) ) ]
```

`|X| = |N|+1` says `str(X)` has length `n`; `1 <= D < 2^(m+1)` says `str(D)`
is a description of length at most `m`; `Sim_c(D,N) != X` says `U(str(D))`
does not halt with output `str(X)` within `n^c` steps. Both sentences are
`forall Sigma^b_2`. Write `Inc_c(N)` and `CInc_c(N,Z)` for the matrices.

For circuits, fix an explicit encoding with a PV validity predicate
`Circ(C, k, l)` ("C encodes a circuit with k inputs and l outputs") and a
total PV evaluator `Eval(C, X)` returning `enc(C(str(X)))` when
`Circ(C, len(X), l)` holds for some `l`, and `0` otherwise. Then

```text
EvalAvoid_4 :=  forall M forall C [ |M| >= 1 and Circ(C, |M|, 4|M|) ->
                  exists Y ( |Y| = 4|M|+1  and
                    forall X ( |X| = |M|+1  ->  Eval(C,X) != Y ) ) ]
```

This is ILW23's `dWPHP_ell(Eval)` for `ell(m) = 4m` at positive lengths,
under our encoding (see Assumption A-enc in Section 4.4).

### 0.5 The pigeonhole schemata

```text
dWPHP(f)  :  forall a>0 forall b in Log forall z
               exists v < a(b+1) forall u < ab   f(u,z) != v
dWPHP'(f) :  forall a>0 forall b in Log
               exists v < a(b+1) forall u < ab   f(u) != v
```

`APC_1 = PV_1 + dWPHP(PV)`, `UAPC_1 = PV_1 + dWPHP'(PV)`,
`T^0_APC = T_PV + dWPHP'(PV)`, where `T_PV` is the set of all true universal
PV sentences. Every instance below uses `b = 1` (so `b in Log` is witnessed
by the number 1) and `a = 2^(|N|-1)`, a PV term in `N`. The instance is then

```text
exists v < 2^n  forall u < 2^(n-1)   f(u[,z]) != v.
```

## 1. Arithmetic Facts

All are true; all are expected to be PV_1-routine.

- A1. For `n >= 4`: `m+1 <= n-1`, hence `2^(m+1) <= 2^(n-1)`.
- A2. For `n >= 5`: `m+1 <= n-2`, hence `2^(m+1) <= 2^(n-2)`.
- A3. For `1 <= D < 2^(m+1) <= 2^(n-2)`: `|2^(n-2) + D| = n-1` and
  `(2^(n-2) + D) mod 2^(m+1) = D`.
- A4. For `v < 2^n`: `X := 2^n + v` satisfies `|X| = n+1` and `X - 2^n = v`.
- A5. `|Pad4(M)| = 4|M|`, and `floor(4|M|/2) = 2|M|`.
- A6. For `m >= 1`: `2^m + 1 <= 2^(4m)`.

## 2. Parameterized Decoders and the APC_1 Forward Direction

### 2.1 Definitions

```text
Dec_c(N, u)     = Sim_c(u, N) - 2^|N|     if 1 <= u < 2^(m(N)+1)
                                          and |Sim_c(u,N)| = |N|+1;
                = 0                        otherwise.

CDec_c(N, Z, u) = CSim_c(u, Z, N) - 2^|N|  if 1 <= u < 2^(m(N)+1), Z >= 1,
                                           and |CSim_c(u,Z,N)| = |N|+1;
                = 0                        otherwise.
```

The decoder's input `u` *is* the sentinel encoding of the description (by
the coincidence in 0.1), so no separate unpadding step is needed. Its output
is the raw numeric value `val(x) < 2^n` of the exactly-n-bit output string,
or `0` for the unused code, a failed simulation, or a wrong-length output.
Both are total PV functions; `Dec_c` has parameter `N`, `CDec_c` has
parameters `(N, Z)`.

### 2.2 Coverage lemma

Lemma C1 (parameterized coverage). For all `N, Z, D, X`:

```text
|N| >= 4  and  1 <= D < 2^(m(N)+1)  and  |X| = |N|+1  and  CSim_c(D,Z,N) = X
   ->   D < 2^(|N|-1)   and   CDec_c(N,Z,D) = X - 2^|N|.
```

Same statement with `Sim_c`/`Dec_c` and no `Z`.

Proof. `D < 2^(m+1) <= 2^(n-1)` by A1. Under the hypotheses the first branch
of `CDec_c` applies, and its value is `CSim_c(D,Z,N) - 2^|N| = X - 2^n`.
Status: true; PV_1: routine (unfold the definition of `CDec_c`, then A1).
This is where defining the decoder from the same `CSim_c` used in the target
sentence pays off: no separate simulation-correctness fact is needed.

### 2.3 Theorem F1 (APC_1 proves CInc_c and Inc_c, each fixed c)

Claim: `PV_1 + dWPHP(CDec_c) proves CInc_c`, and
`PV_1 + dWPHP(Dec_c) proves Inc_c`, modulo E1, S0, A1, A4, C1.

Proof (conditional case). Fix `N` with `n = |N| >= 4` and `Z >= 1`.
Instantiate `dWPHP(CDec_c)` with `a = 2^(n-1)`, `b = 1`, parameter `(N,Z)`:

```text
exists v < 2^n  forall u < 2^(n-1)   CDec_c(N,Z,u) != v.
```

Take such `v` and set `X := 2^n + v`; by A4, `|X| = n+1`. Suppose toward a
contradiction that some `D` with `1 <= D < 2^(m+1)` has `CSim_c(D,Z,N) = X`.
By C1, `D < 2^(n-1)` and `CDec_c(N,Z,D) = X - 2^n = v`, contradicting the
displayed instance at `u = D`. Hence `forall D (1 <= D < 2^(m+1) ->
CSim_c(D,Z,N) != X)`, and `X` witnesses `CInc_c(N,Z)`. The unconditional case
is identical with `Dec_c`, `Sim_c`, and no `Z`.

Status of the theorem: the logical skeleton is complete; each cited lemma is
labelled PV_1-routine but not yet written out as a PV_1 derivation. Over
`T_APC = T_PV + dWPHP(PV)` the theorem holds outright, since E1, S0, A1, A4,
C1 are true universal sentences.

## 3. Unary Decoder and the UAPC_1 Forward Direction

### 3.1 Definition

For each `c >= 1`, define the parameter-free PV function

```text
f_c(u):
  n := |u| + 1;  if n < 5, return 0;
  m := floor(n/2);  D := u mod 2^(m+1);  if D = 0, return 0;
  S := Sim_c(D, 2u);                       -- |2u| = n serves as length witness
  if |S| = n+1, return S - 2^n;  else return 0.
```

`f_c` reads its length information from `|u|`; it takes no `N`, clock, or
advice argument. The middle bits of `u` (positions `m+1 .. n-3`) are ignored.
Running time is polynomial in `|u|`. An input of some other bit length is
decoded relative to its own `n' = |u|+1` and may return a nonzero value; this
is harmless because only coverage matters (Astra's correction 1).

### 3.2 Coverage lemma

Lemma C2 (unary coverage). For all `N, D, X`, with `n = |N|`:

```text
n >= 5  and  1 <= D < 2^(m(N)+1)  and  |X| = n+1  and  Sim_c(D,N) = X
   ->   u_D < 2^(n-1)   and   f_c(u_D) = X - 2^n,      where u_D := 2^(n-2) + D.
```

Proof. By A2, `D < 2^(m+1) <= 2^(n-2)`, so by A3 `|u_D| = n-1` and
`u_D mod 2^(m+1) = D`; also `u_D < 2^(n-1)`. Unfolding `f_c(u_D)`: it
computes `n' = |u_D|+1 = n >= 5`, `m' = m`, `D' = D != 0`, then
`S = Sim_c(D, 2u_D)`. Since `|2u_D| = n = |N|`, S0 gives
`S = Sim_c(D,N) = X`, and `|S| = n+1`, so `f_c(u_D) = X - 2^n`.
Status: true; PV_1: routine given E1, S0, A2, A3.

### 3.3 The finite case n = 4

For each `c`, there are `2^3 - 1 = 7` descriptions of length at most 2 and
`16` strings of length 4, so some 4-bit string `x_{4,c}` is not the output of
any of them within `4^c` steps. Let `X_{4,c} := enc(x_{4,c})`, a numeral.

Lemma L0_c. `forall N forall D [ |N| = 4 and 1 <= D < 8 -> Sim_c(D,N) != X_{4,c} ]`.
Status: true (by choice of `x_{4,c}`); universal with PV matrix, hence an
axiom of `T_PV`; PV_1: provable, since for `|N| = 4` the matrix reduces by
S0 to 7 closed true PV inequations.

### 3.4 Theorem F2 (UAPC_1 proves Inc_c, each fixed c)

Claim: `PV_1 + dWPHP'(f_c) proves Inc_c`, modulo E1, S0, A2-A4, C2, L0_c.

Proof. Fix `N`, `n = |N| >= 4`. If `n = 4`, take `X := X_{4,c}`; L0_c gives
the required `forall D`. If `n >= 5`, instantiate `dWPHP'(f_c)` with
`a = 2^(n-1)`, `b = 1`:

```text
exists v < 2^n  forall u < 2^(n-1)   f_c(u) != v.
```

Set `X := 2^n + v`. If some `D` with `1 <= D < 2^(m+1)` had `Sim_c(D,N) = X`,
then by C2 `u_D < 2^(n-1)` and `f_c(u_D) = v`, contradicting the instance.
So `X` witnesses `Inc_c(N)`.

Status: skeleton complete; PV_1 lemmas labelled routine, not yet derived.
Over `T^0_APC` the theorem holds outright (Section 4).

## 4. The T^0_APC Route to the Conditional Separation

Astra's correction 3 applies throughout: `T_PV` is stronger than `PV_1`. What
this route removes is the obligation to *derive* the correctness lemmas
inside PV_1; it does not remove the obligation to make them *true*, which
depends on the concrete definitions of `U`, `E`, `c_0`, `M_0` in Section 5.

### 4.1 Universal lemmas with guards

Each of the following has the form `forall (quantifier-free PV)`, so if true
it is an axiom of `T_PV`.

- **L0_c** (Section 3.3): for each `c >= 1`.
- **L1_c** (= C2 restated): for each `c >= 1`,
  ```text
  forall N, D, X [ |N| >= 5 and 1 <= D < 2^(m(N)+1) and |X| = |N|+1
                   and Sim_c(D,N) = X
                   ->  2^(|N|-2) + D < 2^(|N|-1)
                       and f_c(2^(|N|-2) + D) = X - 2^|N| ].
  ```
  Guards: `n = |N| >= 5`; `D` a valid description encoding of length at most
  `m`; `X` an exactly-n-bit output (the decoder rejects other lengths).
- **L2** (evaluator bridge). Fix a program `E` such that `U(pair(E,x'), C)`
  halts with output `C(x')` whenever `Circ(C, |x'|, l)`; let
  `P(X') := enc(pair(E, str(X')))`, a PV term. Fix `M_0 := 2|E| + 2` and a
  constant `c_0` such that the running time of `U` on `pair(E,x')` with
  auxiliary `C` is at most `(4|x'| + |C| + 1)^{c_0}` for all `|x'| >= 1`
  (possible since evaluation plus universal simulation is polynomial in
  `|x'| + |C|`). Then
  ```text
  forall M, C, X' [ |M| >= M_0 and Circ(C, |M|, 4|M|) and |X'| = |M|+1
                    ->  1 <= P(X') < 2^(2|M|+1)
                        and CSim_{c_0}(P(X'), C, Pad4(M)) = Eval(C, X') ].
  ```
  Guards: exact arities `|M| -> 4|M|`; `|X'|` exactly `m+1`; `|M| >= M_0`
  ensures `|pair(E,x')| = 2|E| + 2 + m <= 2m = floor(4m/2)`, i.e.
  `P(X') < 2^(2m+1)`. The clock: `(|Pad4(M)| + |C|)^{c_0} = (4m + |C|)^{c_0}`,
  and `|C| >= |z_C| + 1` gives `4m + |C| >= 4m + |z_C| + 1`, so the bound
  on `U`'s running time applies.
- **L3** (finite-length repair). Let `R(C)` be the PV function that, when
  `Circ(C, k, 4k)` for some `1 <= k < M_0`, evaluates `C` on all `2^k` inputs
  and returns the encoding of the first `4k`-bit string (in some fixed order
  of `2^k + 1 <= 2^(4k)` candidates, A6) not among the outputs; `0`
  otherwise. Since `k < M_0` is a constant bound, `R` is polynomial-time.
  ```text
  forall M, C, X' [ 1 <= |M| < M_0 and Circ(C, |M|, 4|M|) and |X'| = |M|+1
                    ->  |R(C)| = 4|M|+1  and  Eval(C, X') != R(C) ].
  ```

Also needed as `T_PV` axioms: E1, S0, A1-A6, and the trivial zero-length
Eval instance in 4.4. All are true universal PV sentences.

### 4.2 Theorem T1: `T^0_APC proves Inc_c` for every `c >= 1`

Proof. Exactly the proof of F2, with E1, S0, A2-A4, L0_c, L1_c now axioms of
`T_PV` and `dWPHP'(f_c)` an axiom of `T^0_APC`. Consequently
`PV_1 + {Inc_c : c >= 1}` is a subtheory of `T^0_APC`.

### 4.3 Theorem T2: `T^0_APC + CInc_{c_0} proves EvalAvoid_4`

Proof. Fix `M` with `m = |M| >= 1` and `C` with `Circ(C, m, 4m)`.

Case `m >= M_0`. Let `N := Pad4(M)`, so `|N| = 4m` and `m(N) = 2m` (A5).
Instantiate `CInc_{c_0}` at `(N, C)` (note `C >= 1` as a valid encoding):
obtain `X` with `|X| = 4m+1` and `forall D (1 <= D < 2^(2m+1) ->
CSim_{c_0}(D, C, N) != X)`. Set `Y := X`. Suppose `|X'| = m+1` and
`Eval(C, X') = Y`. By L2, `1 <= P(X') < 2^(2m+1)` and
`CSim_{c_0}(P(X'), C, N) = Eval(C, X') = X`, contradicting the property of
`X` at `D = P(X')`. So `forall X' (|X'| = m+1 -> Eval(C,X') != Y)`.

Case `1 <= m < M_0`. Set `Y := R(C)`. L3 gives `|Y| = 4m+1` and
`Eval(C, X') != Y` for every `X'` with `|X'| = m+1`.

Both cases are provable in `T^0_APC` (the case split is on `|M| >= M_0`,
decidable). This uses `CInc_{c_0}` only at the single exponent `c_0`.

### 4.4 Theorem T3 (conditional separation)

Assumption A-enc. ILW23's `dWPHP_ell(Eval)` (their Section 4.1) is
formalized with our `Circ`/`Eval`, or with any encoding from which ours is
obtained by a PV_1-provable translation. ILW23 do not fix a bit-level
encoding; their Theorem 24 proof (KPT witnessing plus the iO construction)
does not depend on the encoding beyond standard efficiency properties. This
is a modelling assumption and is recorded as such.

Zero-length instance. With `ell_*(m) = max(1, 4m)`, ILW23's sentence at
`|M| = 0` says: for every circuit `C` with 0 inputs and 1 output there is a
1-bit string not equal to `C(empty)`. `PV_1` proves it with witness
`1 - Eval(C, 1)` (the encoding of the empty input is `1`). Hence, over
`PV_1`, `dWPHP_{ell_*}(Eval)` is equivalent to `EvalAvoid_4`.

Theorem T3. Assume JLS-secure iO exists and `coNP` is not contained in
`i.o.NP/poly` (ILW23 Theorem 24's hypotheses), and A-enc. Then

```text
T^0_APC  does not prove  CInc_{c_0},
```

and therefore neither does its subtheory `PV_1 + {Inc_c : c >= 1}`. In
particular `UAPC_1` does not prove `CInc_{c_0}`.

Proof. By Theorem 24 with the constructive stretch `ell_*`,
`T^0_APC` does not prove `dWPHP_{ell_*}(Eval)`, hence (zero-length instance)
does not prove `EvalAvoid_4`. By T2, if `T^0_APC` proved `CInc_{c_0}` it would
prove `EvalAvoid_4`. So it does not. By T1, `PV_1 + {Inc_c} subset T^0_APC`,
and `UAPC_1 subset T^0_APC` by definition.

Status of T3: complete as a derivation, conditional on (i) the truth of L0-L3
for the concrete `U`, `E`, `c_0`, `M_0` fixed in Section 5, (ii) A-enc,
(iii) ILW23 Theorem 24 as cited. Nothing here has been checked for novelty.

Remark (what T3 does and does not say). It says that ordinary
incompressibility sentences, even all of them together over `PV_1`, do not
yield conditional incompressibility at exponent `c_0`, under ILW23's
hypotheses. It does not say anything about `PV_1` versus `UAPC_1`, and it
does not use or establish any full-schema equivalence. The positive
counterpart `APC_1 proves CInc_{c_0}` is F1 (over `T_APC` it is immediate).

## 5. What Remains for PV_1 and for the Concrete Definitions

### 5.1 Concrete definitions still to be pinned (D1)

- The machine `U`: tape alphabet, halting state, output-tape convention,
  parsing of `pair(M,w)`, behaviour on malformed descriptions (non-halting),
  handling of the auxiliary tape. Any standard efficient universal machine
  works; the choice fixes `E`, `M_0`, `c_0`.
- `Sim_c` and `CSim_c` as PV terms with `N` occurring only inside `|N|`
  (this makes S0 syntactic).
- `Circ`, `Eval`, and the circuit encoding; `Pad4`.
- The evaluator program `E` and the constants `M_0 = 2|E| + 2` and `c_0`.
- The numerals `X_{4,c}` (computable by brute force for each `c`).

Once these are fixed, L0-L3 are concrete true-or-false universal sentences;
their truth is a finite check (L0), a definition-unfolding (L1), and the
standard correctness of `E` plus a polynomial bound (L2, L3).

### 5.2 PV_1 obligations, by theorem

| Theorem | PV_1 lemmas needed | Expected difficulty |
| --- | --- | --- |
| F1 (`APC_1 proves Inc_c, CInc_c`) | E1, S0, A1, A4, C1 | Routine: encoding identities and definition unfolding. No simulation correctness. |
| F2 (`UAPC_1 proves Inc_c`) | E1, S0, A2-A4, C2, L0_c | Routine, plus 7 closed evaluations for `n = 4`. No simulation correctness. |
| `PV_1 + CInc_{c_0} proves EvalAvoid_4` | A5, A6, L2, L3 in PV_1 | L2 is the real work: PV_1 must prove that `U` correctly simulates the fixed program `E` within the clock. This is the standard "PV_1 formalizes polynomial-time computation for a fixed machine" fact (cf. CG Lemma 2.12 for VPV), but must be carried out for our `U`. L3 is a constant-size case analysis. |

The notable outcome of Sections 2-3: the forward directions need **no**
universal-simulation correctness lemma, because the decoders are defined
from the same `Sim_c` that appears in the target sentence. The only place
simulation correctness enters is L2, i.e. the reversal.

### 5.3 Ledger update

| Result | Status | Remaining |
| --- | --- | --- |
| T1: `T^0_APC proves Inc_c`, all c | derivation complete modulo truth of L0_c, L1_c | pin `U`, `Sim_c`; verify L0_c by computation, L1_c by unfolding |
| T2: `T^0_APC + CInc_{c_0} proves EvalAvoid_4` | derivation complete modulo truth of L2, L3 | pin `U`, `E`, `c_0`, `M_0`, `Circ`, `Eval`; verify L2 (correctness + clock), L3 (constant cases) |
| T3: conditional separation | complete modulo T1, T2, A-enc, ILW23 Thm 24 | as above; novelty unassessed |
| F1: `APC_1 proves Inc_c, CInc_c` | skeleton complete; PV_1 lemmas labelled routine | write E1, S0, A1, A4, C1 as PV_1 derivations |
| F2: `UAPC_1 proves Inc_c` | skeleton complete; PV_1 lemmas labelled routine | write E1, S0, A2-A4, C2, L0_c as PV_1 derivations |
| `PV_1 + CInc_{c_0} proves EvalAvoid_4` | proof to reconstruct | L2 in PV_1 (fixed-machine simulation correctness) |

### 5.4 Finite checks performed

A Python check (not stored) verified for `n = 4..14`: the padded-code /
sentinel-encoding coincidence and E1 for `m <= 7`; A1-A3, A6; C1 and C2 on
417 covered instances against an arbitrary stand-in for `Sim_c` (random
partial function depending on `N` only via `|N|`), confirming that the
coverage lemmas are definition-unfolding facts independent of what `Sim_c`
computes; existence of an avoided 4-bit string for 7 descriptions; and the
`M_0 = 2|E| + 2` threshold for `|E| = 1..5`. These are not PV_1 proofs.

### 5.5 Suggested next actions

1. Independent check of Sections 2-4 for quantifier, guard, and length
   errors (Astra).
2. D1: write the concrete `U`, `Sim_c`, `Circ`, `Eval` definitions and fix
   `E`, `M_0`, `c_0`; then state L0-L3 with the concrete constants and
   confirm their truth.
3. Only then: PV_1 derivations for F1/F2 (routine) and for L2 (the real
   obligation), in that order.
