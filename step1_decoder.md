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

Astra correction pass, September 5, 2026, started 20:56 UTC: preserve the
size resource, repair sentinel and clock conventions, state literal
universal interfaces, and save all finite checks. Time cap: 60 minutes plus
one bounded audit. The status ledger in Section 5.3 distinguishes the
mathematical derivations from the remaining PV_1 and source-import work.

## 0. Conventions

### 0.1 Strings as numbers

A binary string `s` is represented by its sentinel encoding

```text
enc(s) = 2^|s| + val(s)        enc(empty) = 1,     |enc(s)| = |s| + 1.
```

Leading zeros of `s` are preserved. `0` is not the encoding of any string and
serves as the universal failure value. For a number `S >= 1` write `str(S)`
for the string it encodes and `len(S) = |S| - 1` for that string's length.

The identities `str(enc(s))=s` and `enc(str(S))=S` explain the string
notation; they are not themselves one-sorted PV formulas quantifying over
a separate string sort. Fact E1 below uses only numbers and PV functions.

A useful coincidence: the `(m+1)`-bit padded code `0^(m-|d|) 1 d` used by
Korten's construction has numeric value `2^|d| + val(d) = enc(d)`. So
"pad `d` to `m+1` bits with a leading 1" and "take the sentinel encoding of
`d`" are the same number, and the set of all descriptions of length at most
`m` is exactly `{D : 1 <= D < 2^(m+1)}`.

### 0.2 Length witnesses

Bit lengths are supplied by numbers: `n = |N|`, with the convention
`|0|=0`. A computation taking `|N|^c` steps is polynomial in the input
length when **N remains an input**, not when it is replaced by binary n.
Semantic dependence only on `|N|` does not permit discarding that resource.

Here are total PV terms used to expand the powers of two in this note.
Subtraction is truncated at zero; division is integer division. The smash
function is `A#B=2^(|A||B|)`, and `MSP(N,k)` is right shift, returning zero
when `k>=|N|`. It runs in polynomial time even for a large binary shift k.

| Name | PV definition | Value under the indicated guard |
| --- | --- | --- |
| `Pow(N)` | `1#N` | `2^|N|` |
| `Ones(N)` | `Pow(N)-1` | the number represented by `|N|` ones |
| `Top(S)` | `floor(Pow(S)/2)` | `2^(|S|-1)` for `S>=1`; zero at S=0 |
| `Val(S)` | `S-Top(S)` | value of the encoded string for `S>=1` |
| `Short(N)` | `2*Pow(MSP(N, |N|-floor(|N|/2)))` | `2^(floor(|N|/2)+1)` |
| `A(N)` | `floor(Pow(N)/2)` | `2^(|N|-1)` for `|N|>=1` |
| `H(N)` | `floor(Pow(N)/4)` | `2^(|N|-2)` for `|N|>=2` |
| `Pad4(M)` | `Pow(M)^4-1` | length `4|M|`, including M=0 |
| `Wrap(B)` | `Pow(B)+B` | sentinel around the canonical binary representation of number B |

For invalid string code 0, set `len(0)=0`; otherwise `len(S)=|S|-1`.
The string displays `enc` and `str` are explanatory notation; algorithms
using them act on sentinel numbers via bit operations. Fixed powers such
as `Pow(M)^4` are repeated multiplication. No unrestricted exponentiation
function on a binary exponent is being introduced.

Fact E1 (numeric encoding interface), universally closed:

```text
S>=1 -> Top(S)<=S and S<2*Top(S) and Val(S)<Top(S)
         and S=Top(S)+Val(S);
D>=1 -> (D<Short(N) <-> |D|<=floor(|N|/2)+1);
Wrap(B)>=1 and |Wrap(B)|=|B|+1 and Val(Wrap(B))=B.
```

These are true quantifier-free PV matrices. Their PV_1 proofs from the
standard bit-operation equations remain to be supplied. The related
identity `|N|=|N'| -> Ones(N)=Ones(N')` will be denoted E0.

### 0.3 The machine and the simulation function

Fix once and for all:

- a fixed deterministic efficient universal machine `U` taking a description
  d and, in conditional mode, a separate raw auxiliary string z. For each
  fixed program it has polynomial simulation overhead in the total input
  length and simulated time. Its output stream is initially empty; a halt
  returns exactly the bits written, including leading zeros. The clock
  counts U's own steps, including parsing; z is not charged to `|d|`;
- the CG pairing `pair(M,w) = dbl(M) || 01 || w` for two-part descriptions,
  `|pair(M,w)| = 2|M| + 2 + |w|`, with `M` nonempty; a description that does
  not parse as a pair is treated by `U` as a non-halting computation. Pair
  parsing reads doubled bits in aligned pairs until the delimiter `01`;
  the payload may be empty. Invalid program codes also fail. No valid
  description has length below 4.

These are explicit requirements on U, not an assertion that mere
universality implies efficient simulation. The following reasoning is for
any fixed implementation satisfying them; no transition table or numerical
program code is certified by this note.

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
depend semantically on N only through its length.

To obtain that invariance without losing the size resource, define them by

```text
Sim_c(D,N)    = Run_c(D, Ones(N));
CSim_c(D,Z,N) = CRun_c(D,Z, Ones(N)).
```

`Run_c(D,W)` is the bounded simulation algorithm above with deadline
`|W|^c`; `CRun_c(D,Z,W)` has deadline `(|W|+|Z|)^c`. The actual word W is
retained as an input/resource for their PV implementations. Failed or
malformed descriptions return zero, including `D<16` and invalid Z in the
conditional case. The normalization uses `|Ones(N)|=|N|`, so it preserves
the stated clocks exactly, not just up to a polynomial.

Fact S0 (length-only dependence). `|N| = |N'|  ->  Sim_c(D,N) = Sim_c(D,N')`,
and likewise for `CSim_c`.
Proof: equal lengths give equal `Ones` values by E0; congruence applied to
the defining `Run_c`/`CRun_c` terms gives S0. A PV_1 proof therefore needs
E0's elementary bit-arithmetic proof, not a theorem about U's behavior.

### 0.4 The target sentences

With `m(N) = floor(|N|/2)`:

```text
Inc_c  :=  forall N [ |N| >= 4 ->
             exists X < 2*Pow(N) ( |X| = |N|+1  and
               forall D < Short(N) ( D>=1 -> Sim_c(D,N) != X ) ) ]

CInc_c :=  forall N forall Z [ |N| >= 4 and Z >= 1 ->
             exists X < 2*Pow(N) ( |X| = |N|+1  and
               forall D < Short(N) ( D>=1 -> CSim_c(D,Z,N) != X ) ) ]
```

`|X| = |N|+1` says `str(X)` has length `n`; `1 <= D < 2^(m+1)` says `str(D)`
is a description of length at most `m`; `Sim_c(D,N) != X` says `U(str(D))`
does not halt with output `str(X)` within `n^c` steps. Both sentences are
`forall Sigma^b_2`. Write `Inc_c(N)` and `CInc_c(N,Z)` for the matrices.

For circuits, use the **native** numeric circuit codes underlying the ILW23
sentence, rather than choosing an unrelated gate encoding. Denote its total
PV evaluator by `NativeEval(B,u)` and the PV characteristic predicate for
its circuit quantifier by `NativeCirc(B,k,l)`. These are local names for the
source interface, not claimed names of symbols printed by ILW23. Valid
native circuits have unique input/output arities, and their evaluation on
`u<2^k` is a number below `2^l`, representing the output with width l.
Section 4.4 isolates exactly what is imported and what is proved here.

The raw auxiliary string is `z_C=str(C)`. To supply native circuit number B
to the machine, set `C=Wrap(B)`, so `z_C` is B's canonical binary word and
`|C|=|z_C|+1`. This wrapper includes B=0, whose canonical word is empty.
Define

```text
Circ(C,k,l) := C>=1 and C=Wrap(Val(C)) and NativeCirc(Val(C),k,l).
ell(k)     := 1 if k=0, else 4*k.
Out(X)     := max(2, Top(X)^4).

Eval(C,X):
  if X=0 or not Circ(C,len(X),ell(len(X))), return 0;
  v := NativeEval(Val(C),Val(X));
  if v>=Out(X), return 0;
  return Out(X)+v.
```

This evaluator is deliberately specialized to the required stretch and its
zero-length repair. For positive k, `Out(X)=2^(4k)` when `len(X)=k`; for the
empty input X=1, `Out(X)=2`. Thus its output is the sentinel of exactly the
raw circuit-output bits. All output widths are supported by the **input X**,
so no additional assumption that binary arities supply size resources is
needed. The canonical-wrapper test is for circuit C only: arbitrary leading
zeros in input/output strings must remain valid. Invalid cases return zero.

The local avoidance sentence is

```text
EvalAvoid_4 :=  forall M forall C [ |M| >= 1 and Circ(C, |M|, 4|M|) ->
                  exists Y < 2*Pow(M)^4 ( |Y| = 4|M|+1  and
                    forall X < 2*Pow(M)
                      ( |X| = |M|+1 -> Eval(C,X) != Y ) ) ].
```

This has `forall Sigma^b_2` form. Section 4.4 proves the implication from
this sentinel formulation to the native positive-length Eval sentence.

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

These are universally closed quantifier-free PV matrices, with all terms
defined in Section 0.2. Their truth follows from the displayed bit
constructions; their derivations in PV_1 are still to be supplied.

```text
A1: |N|>=4 -> Short(N)<=A(N) and 2*A(N)=Pow(N).
A2: |N|>=5 -> Short(N)<=H(N) and 2*H(N)=A(N).
A3: |N|>=5 and 1<=D<Short(N)
      -> |H(N)+D|=|N|-1 and H(N)+D<A(N)
         and (H(N)+D) mod Short(N)=D and |2*(H(N)+D)|=|N|.
A4: v<Pow(N) -> |Pow(N)+v|=|N|+1 and (Pow(N)+v)-Pow(N)=v;
    |X|=|N|+1 -> Pow(N)<=X and X<2*Pow(N) and Top(X)=Pow(N).
A5: |Pad4(M)|=4*|M| and Short(Pad4(M))=2*Pow(M)^2
      and Pow(Pad4(M))=Pow(M)^4.
A6: |M|>=1 -> Pow(M)+1<=Pow(M)^4.
```

When proofs below use `n=|N|`, `m=floor(n/2)`, powers `2^n`, `2^(m+1)`,
`2^(n-1)`, and `2^(n-2)` abbreviate respectively `Pow(N)`, `Short(N)`,
`A(N)`, and `H(N)` under their guards. For the Eval proofs, `m=|M|` and
`2^(4m)` abbreviates `Pow(M)^4`. They are not free binary-exponent terms.

## 2. Parameterized Decoders and the APC_1 Forward Direction

### 2.1 Definitions

```text
Dec_c(N, u)     = Sim_c(u, N) - Pow(N)     if 1 <= u < Short(N)
                                          and |Sim_c(u,N)| = |N|+1;
                = 0                        otherwise.

CDec_c(N, Z, u) = CSim_c(u, Z, N) - Pow(N)  if 1 <= u < Short(N), Z >= 1,
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
`PV_1 + dWPHP(Dec_c) proves Inc_c`, modulo A1, A4, C1 and the defining
equations. The parameterized proof does not need S0.

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
`T_APC = T_PV + dWPHP(PV)` the derivation holds for the defined algorithms:
A1, A4, C1 and their defining equations are true universal sentences.

## 3. Unary Decoder and the UAPC_1 Forward Direction

### 3.1 Definition

For each `c >= 1`, define the parameter-free PV function

```text
f_c(u):
  n := |u| + 1;  if n < 5, return 0;
  W := 2*u;                           -- |W|=n, since u is nonzero here
  D := u mod Short(W);  if D = 0, return 0;
  S := Sim_c(D,W);
  if |S| = n+1, return S-Pow(W);  else return 0.
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
`S = Sim_c(D,N) = X`. Equal lengths also give
`Short(2u_D)=Short(N)` and `Pow(2u_D)=Pow(N)` by their definitions, so the
actual modulus and subtraction in f_c agree with those in C2. Since
`|S|=n+1`, its value is `X-2^n`.
Status: true; PV_1: routine given E1, S0, A2, A3.

### 3.3 The finite case n = 4

The chosen pair syntax makes this case simpler than counting: every
description of length at most 2 is malformed, because even a nonempty
one-bit program and an empty payload require 4 description bits. The
bounded runner rejects these descriptions for every c. Use the single
fixed witness `X_4=16=enc(0000)`, independent of c.

Lemma L0_c, universally closed:

```text
|N|=4 and 1<=D<8 -> Sim_c(D,N)=0 and Sim_c(D,N)!=16.
```

Its truth follows from the explicit malformed-description branch; the
same branch gives a PV_1 proof once the runner's defining equations are
installed. No large-clock computations or unknown witness numerals are
required. For a different description syntax, the earlier seven-versus-
sixteen finite-counting argument remains a fallback, not a needed premise.

### 3.4 Theorem F2 (UAPC_1 proves Inc_c, each fixed c)

Claim: `PV_1 + dWPHP'(f_c) proves Inc_c`, modulo E1, S0, A2-A4, C2, L0_c.

Proof. Fix `N`, `n = |N| >= 4`. If `n = 4`, take `X := 16`; L0_c gives
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
depends on the machine contract and algorithm definitions. Below we give
mathematical truth arguments for those definitions, not a machine-checked
implementation or a proof for an arbitrary inefficient universal machine.

### 4.1 Universal lemmas with guards

Each displayed matrix is quantifier-free over the named PV functions and
is universally closed. Once its truth is established for those functions,
its universal closure is an axiom of `T_PV`.

**L0_c** is the explicit malformed-description lemma from Section 3.3.

**L1_c** (= C2) is

```text
forall N,D,X [ |N|>=5 and 1<=D<Short(N) and |X|=|N|+1
               and Sim_c(D,N)=X
               -> H(N)+D<A(N) and f_c(H(N)+D)=X-Pow(N) ].
```

Its proof is C2 with the resource-preserving definition of S0. The guard
means D encodes a short string, not necessarily a well-formed program;
malformed programs cannot satisfy the successful-simulation antecedent.

**Evaluator program and clock for L2.** Fix a nonempty program code E for
the following algorithm. On payload x' and raw auxiliary string z, read
`m=|x'|` and the number B represented by z; check z is the canonical word
for B and `NativeCirc(B,m,ell(m))`; compute
`v=NativeEval(B,val(x'))`; check its output bound and write exactly
`ell(m)` raw output bits, left-padded with zeros. Halt. Invalid cases may
halt with the empty output. In particular E does **not** write a sentinel.
On valid cases, U's output is precisely the string whose sentinel is
`Eval(Wrap(B),enc(x'))`.

Set `M_0=2|E|+2`. The evaluator algorithm is polynomial-time in
`s=m+|z|+1`; output padding costs O(m). Including U's fixed-program
simulation and parsing overhead, choose integers `K>=1, d>=1` so the
runtime on valid cases with `m>=1` is at most `K*s^d`. Fix

```text
c_0 = d + ceil(log_2 K).
```

For `C=Wrap(B)`, `z=z_C=str(C)`, let `r=4m+|C|`. Then
`s=m+|z_C|+1=m+|C|<=r` and `r>=2`, so
`K*s^d <= K*r^d <= r^c_0`. This is exactly the deadline
`(|Pad4(M)|+|C|)^c_0`, not a clock with an extra bit. K, d, E, and c_0
are fixed standard constants depending on the chosen U and native
algorithms; the theorem requires their existence, not a particular numeral
for c_0. A certified concrete implementation would need actual bounds.

Define the total PV function `P(X')` by constructing the sentinel of
`pair(E,str(X'))` for `X'>=1`, and returning 0 at `X'=0`. L2 is

```text
forall M,C,X' [ |M|>=M_0 and Circ(C,|M|,4|M|) and |X'|=|M|+1
                -> 1<=P(X')<Short(Pad4(M))
                   and CSim_{c_0}(P(X'),C,Pad4(M))=Eval(C,X') ].
```

Proof of truth: with `m=|M|`, the pair length is `M_0+m<=2m`.
E's correctness gives exactly the raw output represented by `Eval(C,X')`,
the preceding bound puts the halt within the CSim deadline, and CSim adds
the single sentinel. All width, validity, and clock guards are explicit.
This is an external simulation argument. It is not a PV_1 simulation proof.

**L3 (finite-length repair).** For the fixed `M_0`, R tries the finitely
many `k=1,...,M_0-1`. If `Circ(C,k,4k)` holds, it evaluates all inputs
`X'=2^k+i`, `0<=i<2^k`, and returns the first candidate
`2^(4k)+j`, `0<=j<=2^k`, not among those outputs. If no such valid arity is
found, return 0; totalize any unexpected missing-candidate branch by 0 too.
Every exponent in this algorithm is bounded by the fixed constant `4M_0`.
Thus it runs in polynomial time in `|C|` even for arbitrarily large C.
Native arity uniqueness ensures the chosen k is the one in the guard.

```text
forall M,C,X' [ 1<=|M|<M_0 and Circ(C,|M|,4|M|) and |X'|=|M|+1
                -> |R(C)|=4|M|+1 and Eval(C,X')!=R(C) ].
```

Proof of truth: at most `2^k` evaluated values cannot cover the `2^k+1`
distinct candidates, which are valid 4k-bit strings by A6. This is finite
counting for a fixed constant range of k, not enumeration of all circuits.

E0, E1, S0, A1-A6, the defining equations, and Section 4.4's wrapper and
zero-length lemmas supply the other true universal sentences used below.

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

Together these cases prove EvalAvoid_4 in `T^0_APC + CInc_{c_0}`. The
large-length case uses the added conditional-incompressibility sentence;
the small-length case does not. Only the single exponent c_0 is used.

### 4.4 Theorem T3 (conditional separation)

**Explicit source interface, replacing A-enc.** Use the native symbols of
Section 0.4 consistently in the native sentence

```text
NativeAvoid_4:
  forall M,B [ |M|>=1 and NativeCirc(B,|M|,4|M|)
    -> exists y<Pow(M)^4 forall u<Pow(M), NativeEval(B,u)!=y ].
```

The following universal lemmas express the wrapper, not an assumed
invariance under arbitrary efficient encodings:

```text
W1: Circ(Wrap(B),k,l) <-> NativeCirc(B,k,l).
W2: |M|>=1 and NativeCirc(B,|M|,4|M|) and u<Pow(M)
     -> Eval(Wrap(B),Pow(M)+u)=Pow(M)^4+NativeEval(B,u).
W3: |Y|=4|M|+1 -> Val(Y)<Pow(M)^4 and Y=Pow(M)^4+Val(Y).
```

W1 follows from `Val(Wrap(B))=B`. W2 follows from A4, the local evaluator's
definition, and native evaluation's output-range property. W3 is the
sentinel identity applied at the resource `Pad4(M)`. These are true
universal PV sentences for the specified native interface, so they can be
used in T_PV without claiming PV_1 proofs.

**Wrapper implication in T_PV.** Given a valid native B at length `m=|M|`,
apply local EvalAvoid_4 to `C=Wrap(B)` using W1. For the resulting witness
Y, take `y=Val(Y)`. W3 gives the native output bound. For any `u<Pow(M)`,
take `X=Pow(M)+u`; it is a valid encoded m-bit input. If
`NativeEval(B,u)=y`, W2 and W3 imply `Eval(C,X)=Y`, a contradiction.
Thus `T_PV proves EvalAvoid_4 -> NativeAvoid_4`.

**Zero-length repair.** Under `Circ(C,0,1)`, `Eval(C,1)` is 2 or 3, so
the corrected encoded witness is `Y=5-Eval(C,1)`. The universal matrix

```text
Circ(C,0,1) -> |5-Eval(C,1)|=2 and 5-Eval(C,1)!=Eval(C,1)
```

is true. For a native circuit B, this yields the raw witness
`1-NativeEval(B,0)` by W1 and the evaluator definition. Consequently T_PV
proves that local EvalAvoid_4 implies the full native sentence with
`ell_*(m)=max(1,4m)`, including zero. The old expression `1-Eval(C,1)`
confused a raw bit with a sentinel and is not used. A PV_1 proof of this
interface remains a separate, stronger formalization task.

**Source-binding check still to sign off.** ILW23 Section 4.1, p. 13,
quantifies over exact-arity circuits and uses its own PV evaluator. Its
Section 2.3, p. 8, supplies the length witness; Appendix D, p. 29, explicitly
uses numeric interval representations of strings. Theorem 27's proof,
p. 18, treats circuit-description length as the resource. These support
the native interface used above, but the paper does not give a bit-level
circuit code or name its validity predicate. The remaining import check is
that `NativeCirc` describes exactly that circuit domain, with unique
arities, and that `NativeEval` uses those fixed input/output widths. No
bound `|B|<=m^k` may be introduced. This is a precise source-formalization
obligation, not an extra cryptographic assumption or an arbitrary-coding
equivalence. No separate gate representation needs to be invented here.

Theorem T3 (subject to that source binding). Assume JLS-secure iO exists and
`coNP` is not contained in `i.o.NP/poly`, as in ILW23 Theorem 24. Then

```text
T^0_APC  does not prove  CInc_{c_0},
```

and therefore neither does its subtheory `PV_1 + {Inc_c : c >= 1}`. In
particular `UAPC_1` does not prove `CInc_{c_0}`.

Proof. By Theorem 24 with the constructive stretch `ell_*`, `T^0_APC`
does not prove the full native avoidance sentence. By T2 and the wrapper
implication plus zero-length repair, proving `CInc_{c_0}` would prove that
native sentence. By T1, `PV_1 + {Inc_c}` is contained in `T^0_APC`; so is
UAPC_1. The nonprovability descends to both subtheories.

Status: the logical deduction and explicit wrapper implication are written
out. The truth arguments for L0-L3 use the specified efficient-machine and
native-evaluator contracts. The source binding still needs independent
sign-off; PV_1 derivations and certified concrete implementations have not
been supplied. Do not label this a completed Gate B or an independently
verified new separation. Nothing here has been checked for novelty.

Remark (what T3 does and does not say). It says that ordinary
incompressibility sentences, even all of them together over `PV_1`, do not
yield conditional incompressibility at exponent `c_0`, under ILW23's
hypotheses. It does not say anything about `PV_1` versus `UAPC_1`, and it
does not use or establish any full-schema equivalence. The positive
counterpart in APC_1 is F1, pending its listed PV_1 derivations; the
counterpart over T_APC is established by the true-universal argument.

## 5. Status, Verification, and Handoff

### 5.1 What is fixed, and what is not

- Fixed here: total bit/resource terms; literal bounded Inc/CInc sentences;
  canonical-resource simulation definitions; parameterized and unary
  decoders; the fixed witness 16 at n=4; native/sentinel circuit wrappers;
  E's algorithm and a formula choosing one clock exponent from its runtime
  bound; and R's finite search algorithm.
- Parameterized rather than implemented here: the efficient U and its
  bounded-runner PV symbols, the source's native evaluator/validity symbols,
  and the standard constants describing their implementations. The
  mathematical arguments apply to any fixed realization satisfying the
  explicit contracts. No exact transition table or gate-code implementation
  is claimed to have been checked.
- Still required for Gate B: install the relevant PV defining equations
  and prove the elementary resource/encoding facts there. S0 then follows
  by congruence; it no longer rests on an impossible syntactic restriction.
- Still required for the imported separation: independently sign off the
  source binding in Section 4.4. The wrapper implication itself is explicit.

Choosing a particular numerical value of c_0 is not needed for the theorem
that **some fixed standard exponent** works. It would be needed to identify
one numerically indexed sentence for a particular implemented U. Do not
confuse that implementation task with the existential metatheorem.

### 5.2 PV_1 obligations, by theorem

| Theorem | PV_1 lemmas needed | Expected difficulty |
| --- | --- | --- |
| F1 (`APC_1 proves Inc_c, CInc_c`) | A1, A4, C1, defining equations | Encoding identities and definition unfolding. S0 and simulation correctness are not needed. |
| F2 (`UAPC_1 proves Inc_c`) | E0/S0, A2-A4, C2, L0_c, defining equations | Canonical resource identity, bit arithmetic, and the explicit malformed-description branch. No large finite computations. |
| `PV_1 + CInc_{c_0} proves EvalAvoid_4` | A5, A6, L2, L3 in PV_1 | The substantial additional obligation is proving the fixed-program simulation and clock bound of L2 inside PV_1. L3 has a constant bound on input width, not on circuit size. |
| Local EvalAvoid implies the native sentence in PV_1 | E1, A4-A5, W1-W3, native evaluation contract, zero-length identity | T_PV already permits the true universal identities. Their PV_1 versions must be proved rather than imported from T_PV. |

The notable outcome of Sections 2-3: the forward directions need **no**
universal-simulation correctness lemma, because the decoders are defined
from the same `Sim_c` that appears in the target sentence. The only place
simulation correctness enters is L2, i.e. the reversal.

### 5.3 Ledger update

| Result | Status | Remaining |
| --- | --- | --- |
| T1: `T^0_APC proves Inc_c`, all c | Mathematical derivation with explicit true-universal lemmas for the specified runner | Independent review of the resource terms and defining equations; no machine-checked implementation |
| T2: `T^0_APC + CInc_{c_0} proves EvalAvoid_4` | Mathematical derivation for the efficient-U/native-evaluator contracts; E, clock choice, and finite repair are specified | Review those contracts and L2/L3's truth arguments |
| Local EvalAvoid_4 implies native avoidance in T_PV | Explicit wrapper proof W1-W3 plus corrected zero-length repair | Source-symbol/domain identification, not arbitrary-coding invariance |
| T3: conditional separation | Deduction from T1, T2, the wrapper, and ILW23; source binding still to sign off | Do not yet mark independently verified; novelty unassessed |
| F1: `APC_1 proves Inc_c, CInc_c` | Proof skeleton complete | PV_1 proofs of A1, A4, C1 using actual defining equations |
| F2: `UAPC_1 proves Inc_c` | Proof skeleton complete | PV_1 proofs of E0/S0, A2-A4, C2, L0_c |
| `PV_1 + CInc_{c_0} proves EvalAvoid_4` | Proof to reconstruct internally | L2/L3 and elementary identities in PV_1 |

**Current endpoint:** the earlier errors are repaired and the T_PV-level
arguments have explicit algorithms and interfaces. Step 1 remains partial
under the modified plan's requirement for checked PV_1 forward proofs.

### 5.4 Finite checks performed

The transcript's Python check has been reconstructed in
[check_step1.py](check_step1.py), with additional checks from Astra's review.
Run it from the repository root:

```sh
python3 check_step1.py
```

It uses only the Python standard library. It retains the original seeded
abstract simulation check (417 C1 instances, 412 C2 instances), now through
the canonical resource, and checks the literal bit terms on 4,096 resource
values and 24,532 unary preimage/resource identities. It also checks invalid short
pair descriptions, conditional decoding, the clock-exponent inequality,
and the native/sentinel wrapper on small finite circuit tables. The
zero-length cases remain as regressions: the old raw-bit expression is
rejected and `5-Eval(C,1)` produces the correct encoded complement.

The abstract simulator deliberately exercises more output behaviors than
the actual malformed-program runner; it is not an implementation of U.
The small native tables test the wrapper algebra, not ILW23's circuit
encoding. The clock tests check absorption of a supplied polynomial bound,
not the existence of that bound for an implemented E. The script does not
prove PV_1 derivability, certify U, or discharge the source-binding check.

### 5.5 Corrections from the first review

The review snapshot and executable counterexamples are preserved in git.
This pass replaces the false syntactic length restriction by canonical
resources (Section 0.3), fixes the zero-length sentinel (Section 4.4),
specifies the raw auxiliary string and exact clock absorption (L2), and
replaces A-enc by a native-symbol wrapper with an explicit implication.
L0 now has the constant witness 16 from pair syntax, rather than seven
unspecified computations for every c. The literal PV term table and
bounded quantifiers remove the earlier unrestricted-exponent metanotation.

A bounded independent audit found no blocking mathematical error under
the stated contracts. Its two status-wording findings were corrected:
T2's large-length branch requires the added CInc sentence, and F1 is not
yet a checked APC_1 proof. The audit does not discharge source binding or
the remaining PV_1 obligations. Its expanded finite resource/preimage
checks are included in the saved script, not left only in the transcript.

### 5.6 Suggested next actions

1. Review E0/S0, the literal bit terms, W1-W3, the clock choice, and the
   source binding. Decide whether the paper-level T_PV derivation is
   acceptable for the explicitly specified implementation class.
2. For Gate B, select the concrete PV definitions/basis and discharge the
   elementary F1/F2 obligations. Do not relabel expected proofs as checked
   merely because the T_PV derivations are available.
3. If continuing to PV_1 reversals, formalize L2's fixed-program simulation
   and L3 there. Keep this distinct from importing the negative theorem and
   from any claim of novelty.
