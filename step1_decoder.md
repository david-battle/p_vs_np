# Step 1: Definitions, Decoder Lemmas, and the T^0_APC Route

**Current status (September 5, 2026): outcome 1a accepted at paper level.**
F1/F2 are accepted; the original simulation/overhead task remains incomplete.
T3's circuit-interface obligation is closed in
[step2_conditional_separation.md](step2_conditional_separation.md) (concrete
encoding, (E-a)/(E-b), audited transfer via ILW23 Theorems 25 and 28); the
conditional separation stands under the residual assumptions listed there.
Gate D's first-pass assessment is in [gate_d_novelty.md](gate_d_novelty.md):
known machinery with an explicit incompressibility specialization, exact
formulation unlocated, novelty not established. Sections 6.7-6.8 record the
Step 1 consensus and updated handoff; Section 5.3 is the Step 1 result ledger.

## Work Record

Started 2026-09-05, 20:40 UTC (Fable 5.1, first pass on Step 1, following
[step0_baseline.md](step0_baseline.md) and Astra's three corrections).
Target: fix the one-sorted definitions; prove the forward implications from
the parameterized and unary decoders at the level of explicit lemma
statements; write the guarded universal lemmas L0-L3 and derive the
conditional separation over `T^0_APC`; isolate what remains for the PV_1
versions. Time cap for this pass: 90 minutes. No literature search.

What this note is: a structured proof with every lemma stated explicitly
and its provability status labelled. What it is not: a machine-checked
PV_1 derivation. Section 6 discharges the forward-direction lemmas to the
level of named metatheorems and standard `S^1_2` facts; any remaining
"routine" wording in Sections 0-4 refers to that section.

Astra correction pass, September 5, 2026, started 20:56 UTC: preserve the
size resource, repair sentinel and clock conventions, state literal
universal interfaces, and save all finite checks. Time cap: 60 minutes plus
one bounded audit. The status ledger in Section 5.3 distinguishes the
mathematical derivations from the remaining PV_1 and source-import work.

Finalization pass (Fable 5.1), September 5, 2026, from 21:15 UTC. Target:
review the repaired definitions and L2/W1-W3; discharge the PV_1
obligations of the forward theorems F1 and F2 to the level of named
standard metatheorems plus definition unfolding, isolating exactly what is
not discharged; check the ILW23 interface against the paper's text; record
the Gate B decision. Section 6 holds the result; the ledger in Section 5.3
is updated in place.

Astra concurrence review, September 5, 2026: no blocking error in F1/F2;
accepted outcome 1a at ordinary paper-proof level, not completion of every
original Step 1 task. A targeted basis/conservativity audit confirmed the
same-language transfer and identified compressed arithmetic citations, not
a stronger-theory gap. The following documentation-only handoff records
that review and its recommendation without additional research.

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
standard bit-operation equations are discussed in Section 6.3. The related
identity `|N|=|N'| -> Ones(N)=Ones(N')` will be denoted E0, and its
consequence for the other length-determined terms,

```text
E0': |N|=|N'| -> Pow(N)=Pow(N') and Short(N)=Short(N')
                 and A(N)=A(N') and H(N)=H(N'),
```

will be denoted E0'. Unlike E0, the `Short` clause of E0' is not a pure
congruence: `MSP(N,k)` depends on the bits of N, so E0' needs the length
identity `|MSP(N,k)| = |N|-k` for `k<=|N|` before E0 can be applied to
`Pow(MSP(N,k))`.

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

For circuits, reserve `NativeEval(B,u)` for a total PV evaluator and
`NativeCirc(B,k,l)` for its PV validity/arity predicate. Use the same pair
throughout the simulation and wrapper arguments. These are local interface
names, not claimed names of symbols printed by ILW23. Valid circuits have
unique input/output arities; evaluation on `u<2^k` is below `2^l`, with
output width l. ILW23 does not specify a bit-level code: choosing a concrete
pair and checking its transfer to the source is still required, via
Section 6.5's (E-a)/(E-b). The name "native" alone establishes no binding.

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
constructions; their paper-level PV_1 derivations are recorded in Section
6.3 using standard `S^1_2` arithmetic and the conservativity theorem M1.

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
|N| >= 4  and  Z >= 1  and  1 <= D < 2^(m(N)+1)  and  |X| = |N|+1
   and  CSim_c(D,Z,N) = X
   ->   D < 2^(|N|-1)   and   CDec_c(N,Z,D) = X - 2^|N|.
```

Same statement with `Sim_c`/`Dec_c` and no `Z`. (The hypothesis `Z >= 1`
is available wherever C1 is used; it is also derivable, since `Z = 0`
forces `CSim_c(D,Z,N) = 0 != X`, but stating it keeps C1 a plain
definition-unfolding.)

Proof. `D < 2^(m+1) <= 2^(n-1)` by A1. Under the hypotheses the first branch
of `CDec_c` applies, and its value is `CSim_c(D,Z,N) - 2^|N| = X - 2^n`.
Status: true; PV_1: Section 6.3 (unfold the definition of `CDec_c`, then A1).
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

Status of the theorem: the logical skeleton is complete; the cited lemmas
are discharged in Section 6 at the level described there. Over
`T_APC = T_PV + dWPHP(PV)` the derivation holds for the defined algorithms:
A1, A4, C1 and their defining equations are true universal sentences.
Formally `dWPHP(PV)` takes one parameter `z`; `CDec_c` has the pair
`(N,Z)`, which is packed by a PV pairing function whose projection
identities PV_1 proves.

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
`Short(2u_D)=Short(N)` and `Pow(2u_D)=Pow(N)` by E0', so the
actual modulus and subtraction in f_c agree with those in C2. Since
`|S|=n+1`, its value is `X-2^n`.
Status: true; PV_1: Section 6.3, given E0', S0, A2, A3.

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

Its truth follows from the explicit malformed-description branch; Section
6.2's defining requirement D1a supplies the PV_1 proof. No large-clock
computations or unknown witness numerals are required. For a different
description syntax, the earlier seven-versus-sixteen finite-counting
argument remains a fallback, not a needed premise.

### 3.4 Theorem F2 (UAPC_1 proves Inc_c, each fixed c)

Claim: `PV_1 + dWPHP'(f_c) proves Inc_c`, using E0', S0, A1-A4, C2, L0_c.

Proof. Fix `N`, `n = |N| >= 4`. If `n = 4`, take `X := 16`; L0_c gives
the required `forall D`. If `n >= 5`, instantiate `dWPHP'(f_c)` with
`a = 2^(n-1)`, `b = 1`:

```text
exists v < 2^n  forall u < 2^(n-1)   f_c(u) != v.
```

Set `X := 2^n + v`. If some `D` with `1 <= D < 2^(m+1)` had `Sim_c(D,N) = X`,
then by C2 `u_D < 2^(n-1)` and `f_c(u_D) = v`, contradicting the instance.
So `X` witnesses `Inc_c(N)`.

Status: skeleton complete; the PV_1 lemmas are discharged in Section 6.
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

Proof. Exactly the proof of F2, with E0', S0, A1-A4, L0_c, L1_c now axioms of
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
circuit code or name its validity predicate. Section 6.5 therefore reduces
the remaining import check to a concrete encoding, an efficient coding map,
and a transfer argument for the source theorem, rather than a textual
identification of unknown symbols. No bound `|B|<=m^k` may be introduced.
This is a source-formalization obligation, not an extra cryptographic
assumption or an assumed arbitrary-coding equivalence. A standard circuit
representation suffices as a candidate; no novel representation is needed.

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
native-evaluator contracts. The source binding is reduced in Section 6.5
to the encoding properties (E-a), (E-b), with the concrete choice and
transfer still to sign off. PV_1 derivations of the reversal and certified
concrete implementations have not been supplied.
This is not an independently verified new separation, and nothing here has
been checked for novelty.

Remark (what T3 does and does not say). It says that ordinary
incompressibility sentences, even all of them together over `PV_1`, do not
yield conditional incompressibility at exponent `c_0`, under ILW23's
hypotheses. It does not say anything about `PV_1` versus `UAPC_1`, and it
does not use or establish any full-schema equivalence. The positive
counterpart in APC_1 is F1, accepted at paper level in Section 6.4; the
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
- Done in Section 6 for the forward direction: the PV_1 basis is named,
  the resource/encoding facts are reduced to standard `S^1_2` facts and
  imported by conservativity, and S0 follows by congruence from E0.
- For the imported separation, the source-binding question of Section 4.4
  is reduced in Section 6.5 to encoding properties (E-a), (E-b), under
  our reading of Theorem 24's proof; an encoding satisfying them is still
  to be fixed. The wrapper implication itself is explicit.

Choosing a particular numerical value of c_0 is not needed for the theorem
that **some fixed standard exponent** works. It would be needed to identify
one numerically indexed sentence for a particular implemented U. Do not
confuse that implementation task with the existential metatheorem.

### 5.2 PV_1 obligations, by theorem

| Theorem | PV_1 lemmas needed | Expected difficulty |
| --- | --- | --- |
| F1 (`APC_1 proves Inc_c, CInc_c`) | A1, A4, C1, defining equations | Encoding identities and definition unfolding. S0 and simulation correctness are not needed. |
| F2 (`UAPC_1 proves Inc_c`) | E0/E0'/S0, A1-A4, C2, L0_c, defining equations | Canonical resource identity, bit arithmetic, and the explicit malformed-description branch. No large finite computations. |
| `PV_1 + CInc_{c_0} proves EvalAvoid_4` | A5, A6, L2, L3 in PV_1 | The substantial additional obligation is proving the fixed-program simulation and clock bound of L2 inside PV_1. L3 has a constant bound on input width, not on circuit size. |
| Local EvalAvoid implies the native sentence in PV_1 | E1, A4-A5, W1-W3, native evaluation contract, zero-length identity | T_PV already permits the true universal identities. Their PV_1 versions must be proved rather than imported from T_PV. |

The notable outcome of Sections 2-3: the forward directions need **no**
universal-simulation correctness lemma, because the decoders are defined
from the same `Sim_c` that appears in the target sentence. The only place
simulation correctness enters is L2, i.e. the reversal.

### 5.3 Ledger update

| Result | Status | Remaining |
| --- | --- | --- |
| T1: `T^0_APC proves Inc_c`, all c | Mathematical derivation with explicit true-universal lemmas for the specified runner; resource terms and E0/E0'/S0 re-reviewed in Section 6.1 | No machine-checked implementation |
| T2: `T^0_APC + CInc_{c_0} proves EvalAvoid_4` | Mathematical derivation for the efficient-U/native-evaluator contracts; E, clock choice, and finite repair specified and re-reviewed (Section 6.1) | Nothing further at the T_PV level; PV_1 version is Step 2 |
| Local EvalAvoid_4 implies native avoidance in T_PV | Explicit wrapper proof W1-W3 plus corrected zero-length repair | None at the T_PV level |
| T3: conditional separation | Interface closed in [step2_conditional_separation.md](step2_conditional_separation.md): concrete encoding with (E-a), (E-b); transfer through ILW23 Theorems 25 and 28 directly (the paper's `Eval` and Theorem 24's statement are not used); audited | Residual assumptions in that note's Section 5; [Gate D](gate_d_novelty.md) assesses this as a reconstruction/specialization, novelty unestablished |
| F1: `APC_1 proves Inc_c, CInc_c` | Accepted after concurrence review, relative to M1-M4 and the specified definitions (Sections 6.3-6.4); uses no property of the runners | Paper-level; not machine-checked |
| F2: `UAPC_1 proves Inc_c` | Accepted after concurrence review, relative to M1-M4 and the first clause of D1a; uses E0', S0, A1-A4, C2, L0_c | Paper-level; not machine-checked |
| `PV_1 + CInc_{c_0} proves EvalAvoid_4` | Proof to reconstruct internally | L2/L3 and the required circuit-interface facts in PV_1; L2 is the evaluator-specific instance of D4 (Section 6.6) |

**Current endpoint:** outcome 1a accepted: F1/F2 are established at paper
level under the specified definitions. The original simulation/overhead
task remains incomplete; L2 is its evaluator-specific PV_1 obligation,
not a prerequisite for the `T_PV` route. T3's interface was subsequently
closed in Step 2, and Gate D's first-pass assessment is complete. Section
6.8 points to the current stop-or-extension decision.

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
values and 24,532 unary preimage/resource identities. It also checks
invalid short pair descriptions, conditional decoding, the clock-exponent
inequality, and the native/sentinel wrapper on small finite circuit tables.
The zero-length cases remain as regressions: the old raw-bit expression is
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

A bounded independent audit of that earlier version found no blocking
mathematical error under the stated contracts. Its two status-wording
findings were corrected: T2's large-length branch requires the added CInc
sentence, and F1 was not yet a checked APC_1 proof at that stage. Section
6 now supersedes the latter status. That earlier audit did not discharge
source binding or the PV_1 obligations. Its expanded finite resource/
preimage checks are included in the saved script.

### 5.6 Next actions

The forward-proof review and T3 interface review are complete at paper
level. Gate D's first pass is also complete. Section 6.8 points to the
current stop-or-explicit-extension decision; internal simulation proofs
remain deferred, not an automatic next task.

## 6. Step 1 Finalization

### 6.1 Review of the repaired definitions, L2, and W1-W3

The repaired resource definitions, evaluator clock, and wrapper were
re-derived by hand, independently of the prose in Sections 0-4, with these
results.

- Term table (0.2): every row evaluates as stated, including the edge
  cases `Pow(0)=1`, `Ones(0)=0`, `Top(0)=0`, `Short(0)=2`, `Pad4(0)=0`,
  `Wrap(0)=1`. `Short` at `|N|=1` gives `2=2^(0+1)`, as required.
- E0 and S0 (0.3): `Sim_c(D,N)` is by definition `Run_c(D,Ones(N))`, and
  `Ones(N)=Pow(N)-1=1#N-1`; so S0 is a congruence once E0 is known. This
  is the repair Astra made and it is correct. The proof of C2 additionally
  needs `Short(2u_D)=Short(N)`, which is not a congruence in `N` because
  `MSP(N,k)` reads N's bits. That is the reason for adding E0' in 0.2.
- A1-A6, E1 (1, 0.2): all correct. The boundaries are tight where claimed:
  A1 at `n=4` (`3<=3`), A2 and A3 at `n=5` (`m+1=3<=3`, and the quotient
  `2^(n-2)/2^(m+1)` equals 1, so the `mod` identity has no slack).
- C1 (2.2): the case branch of `CDec_c` requires `Z>=1`, which the earlier
  statement omitted. It is derivable from `CSim_c(D,Z,N)=X!=0`, but it has
  now been added to the hypothesis so C1 is a pure unfolding.
- L2 clock (4.1): with `s=m+|C|`, `r=4m+|C|`, one has `s<=r`, `r>=2`, and
  `K*s^d <= r^ceil(log2 K) * r^d = r^c_0`. The description bound
  `|P(X')|=M_0+m+1<=2m+1` holds exactly when `m>=M_0`, which is L2's guard.
  The deadline of `CSim_{c_0}(P(X'),C,Pad4(M))` is `(|Ones(Pad4(M))|+|C|)^c_0
  =(4m+|C|)^c_0=r^c_0`. Correct.
- W1-W3 and the zero-length repair (4.4): correct. In particular
  `Out(1)=max(2,1)=2`, `Eval(C,1) in {2,3}` under the contract
  `NativeEval(B,0)<2`, and `5-Eval(C,1)` is the other element.
- L0_c (3.3): correct, and simpler than stated there: it follows from the
  malformed branch D1a below without any use of E0 or of clock size.

No mathematical error was found. The two tightenings above are the only
changes to Sections 0-4 made in this pass.

### 6.2 PV_1 basis and the metatheorems used

`PV_1` is Cook's equational theory PV (a function symbol for each
polynomial-time function, introduced by composition and limited recursion
on notation, with its defining equations), taken as a first-order theory
with induction for open formulas, exactly as in Krajicek, *Proof
Complexity* (2019), Chapter 12, and as used by PS21 and ILW23. Open PV
formulas have PV characteristic functions, and definition by cases is
available through `cond`. The derivations below use four standard facts.

The concurrence review checked this presentation against Cook-Thapen,
["The strength of replacement in weak arithmetic"](https://arxiv.org/pdf/cs/0409015),
Section 1, arXiv p. 3 (published in ACM TOCL 7(4), 2006, pp. 749-764).
Their first-order `PV` is the theory called `PV_1` here. In the full PV
language, ordinary open IND is available; the theory also admits a
universal axiomatization. The induction schemes themselves are not
syntactically universal. Do not confuse this with arbitrary
`Sigma^b_1`-IND or silently replace the base by a stronger theory.

- **M1 (conservativity).** `PV_1` is contained in `S^1_2(PV)`, and
  `S^1_2(PV)` is `forall Sigma^b_1(PV)`-conservative over `PV_1` (Buss,
  *Bounded Arithmetic*, 1986, via the witnessing theorem for `S^1_2`). A
  directly checked statement in the same PV language is
  [PS21, Section 2.1, printed p. 7](https://users.ox.ac.uk/~coml0742/papers/stoc-final.pdf#page=7):
  "S^1_2 is forall Sigma^b_1-conservative over PV_1." Every universally
  closed open PV sentence is `forall Sigma^b_1(PV)`. Hence any of the
  identities below that has an ordinary `S^1_2` proof, using BASIC and
  `Sigma^b_1`-LIND, is a `PV_1` theorem. M1 transfers provability, not
  proof size; nothing here needs proof size. It is applied only to the
  open lemmas, not directly to `Inc_c`, `CInc_c`, or `EvalAvoid_4`, which
  are `forall Sigma^b_2`. The PV symbols retain the same definitions on
  both sides; semantic equality of arbitrary implementations is not enough.
- **M2 (unfolding).** For `f(x)=cond(chi(x),s(x),t(x))` with `chi` the
  characteristic function of an open condition `phi`, `PV_1` proves
  `phi(x) -> f(x)=s(x)` and `not phi(x) -> f(x)=t(x)`. "Unfold" below means
  exactly these steps together with the equality axioms.
- **M3 (Cobham).** Every polynomial-time function has a PV symbol. This
  supplies `Run_c`, `CRun_c` (step-by-step simulation of U by limited
  recursion on notation along a term of length `|W|^c`, respectively
  `(|W|+|Z|)^c`, e.g. an iterated smash), the pair parser, `P`, `R`,
  `MSP`, `mod`, floor division, and a pairing function with projections.
  What `PV_1` knows about `Run_c` is its defining equations, and only D1a
  below is used.
- **M4 (closed terms).** `PV_1` proves `t=n` for every closed term `t` and
  the numeral `n` of its value. Used for the finite case split in D1a and
  the closed length/bound facts at `n=4` in Section 6.4.

**D1a (malformed branch; a definitional requirement).** `Run_c` and
`CRun_c` are defined in the form `cond(Malformed(D), 0, ...)` and
`cond(Malformed(D) or Z=0, 0, ...)`, where `Malformed` is the PV pair-syntax
check of 0.3, with `Malformed(0)=1` covering the `D>=1` guard. Since no
valid description has fewer than 4 bits, every `D<16` (string length
`<=3`) is malformed. `PV_1` proves `D<16 -> Malformed(D)=1` by the case
split `D<16 -> D=0 or ... or D=15` (an `S^1_2` triviality, hence `PV_1` by
M1) and M4 on the sixteen closed instances. Therefore

```text
D1a:  D<16 -> Run_c(D,W)=0;     Z=0 -> CRun_c(D,Z,W)=0.
```

F1 uses no property of the runners at all (C1 is pure unfolding, and
`Z>=1` is a hypothesis of `CInc_c`); F2 uses only the first clause of D1a,
through L0_c. The second clause is recorded for completeness and is used
nowhere. In particular no simulation-correctness statement about U enters
the forward direction; this is the point made in 5.2 and it is what makes
the discharge below possible without D4.

### 6.3 Discharge of the open lemmas

Each row reduces the lemma to facts of the following kind, all of which
are `S^1_2` theorems about length-bounded powers of two (Buss 1986,
Chapter 2 bootstrapping; Hajek-Pudlak, Chapter V.3). Here `k`, `j` range
over length terms, so `2^k` denotes a PV term such as `Pow`, `Short`,
`A`, `H`, `Pow(M)^4`:

```text
(P1) |x|=|y| -> x#z=y#z;   x#y=y#x                     (BASIC)
(P2) x>=1 -> 2^(|x|-1) <= x < 2^|x|;    x<2^k <-> |x|<=k
(P3) k<=j <-> 2^k<=2^j;   2^(k+1)=2*2^k;   2^k*2^j=2^(k+j)
(P4) x<2^k and k<=j -> |2^j+x|=j+1 and (2^j+x)-2^j=x
(P5) d<2^k -> (q*2^k+d) mod 2^k = d;   k<=|x| -> |MSP(x,k)|=|x|-k
```

| Lemma | Reduction |
| --- | --- |
| E0 | `Pow(N)=1#N`; P1. |
| E0' | `Pow`, `A`, `H` are functions of `Pow(N)`: E0. For `Short`: P5 gives `|MSP(N,k)|=|N|-k` with `k=|N|-floor(|N|/2)`, so equal `|N|` give equal `|MSP(N,k)|`, then E0 for `Pow(MSP(N,k))`. |
| E1 | First clause: P2 with `Top(S)=2^(|S|-1)` (P3 halving of `Pow`). Second clause: P2 with `k=floor(|N|/2)+1`. Third: P4 with `x=B`, `j=k=|B|`. |
| A1, A2 | P3 with `floor(n/2)+1 <= n-1` for `n>=4`, `<= n-2` for `n>=5`; `2*A(N)=Pow(N)`, `2*H(N)=A(N)` by P3 halving. |
| A3 | P4 with `x=D`, `k=m+1`, `j=n-2` gives the length and the bound; P5 with `q=2^(n-3-m)=Pow(MSP(N,m+3))` gives the `mod` identity; P3 for `|2(H+D)|=n`. |
| A4 | P4 with `j=k=|N|`; converse from P2. |
| A5, A6 | P2/P3 and elementary predecessor arithmetic give `|2^r-1|=r` for the resourced exponent `r=4|M|`, including `r=0` separately; hence `|Pad4(M)|=4|M|`. The `Short` definition and P5/P3 give `Short(Pad4(M))=2^(2m+1)=2*Pow(M)^2`; P3 gives `Pow(Pad4(M))=Pow(M)^4`. Elementary order arithmetic gives `2^m+1<=2^(4m)` for `m>=1`. |
| S0 | E0 and the equality axioms applied to `Run_c(D,Ones(N))`. |
| C1 | M2 on `CDec_c` at `u=D`: the condition `1<=D<Short(N) and Z>=1 and |CSim_c(D,Z,N)|=|N|+1` is literally the hypothesis list with `CSim_c(D,Z,N)=X`; the value is `X-Pow(N)`. `D<A(N)` is A1. Same for `Dec_c`. |
| C2 | A2, A3 give `u_D=H(N)+D` with `|u_D|=n-1`, `u_D<A(N)`, `u_D mod Short(N)=D`, `|2u_D|=n`. M2 on `f_c` at `u_D`: `n'=n>=5`; `W=2u_D`; E0' gives `Short(W)=Short(N)` and `Pow(W)=Pow(N)`, so `D'=D!=0`; S0 gives `Sim_c(D,W)=Sim_c(D,N)=X`; `|X|=n+1` selects the branch returning `X-Pow(N)`. |
| L0_c | `1<=D<8 -> D<16`, D1a, `0!=16`. |

This is a compressed paper-proof reduction table using P1-P5, the named
definitions, and elementary order/floor/predecessor arithmetic, not an
exhaustive formal derivation from the five displayed lines alone. The
concurrence review found no stronger-induction or lost-resource gap.
No universal-simulation correctness or circuit theorem is used here.

### 6.4 Theorems F1 and F2 in PV_1

With the table in place, the proofs written in 2.3 and 3.4 are `PV_1`
derivations: they are first-order reasoning from one instance of the
pigeonhole axiom, the open lemmas C1 (resp. C2, L0_c), A4, A1 (to read
the instance's bound `a(b+1)=2*A(N)` as `Pow(N)`), and the case split
`|N|=4 or |N|>=5` from `|N|>=4`, with `a:=A(N)>0` (P2, `|N|>=1`) and
`b:=|1|=1` as the `Log` witness. The `|N|=4` case of F2 also uses
`|N|=4 -> Pow(N)=16 and Short(N)=8` (P3, P5) and the closed facts
`|16|=5`, `16<32` (M4); `Short(N)=8` passes from `Inc_c`'s bound
`D<Short(N)` to L0_c's hypothesis `D<8`. For F1 the two parameters
`(N,Z)` of `CDec_c` are packed by the M3 pairing function.

```text
F1:  PV_1 + dWPHP(Dec_c)  proves Inc_c;   PV_1 + dWPHP(CDec_c) proves CInc_c.
F2:  PV_1 + dWPHP'(f_c)   proves Inc_c.
```

Status: **derived in PV_1 at paper level**, relative to M1-M4 and the
definitional requirement D1a. "Paper level" means the explicit logical
arguments rest on named metatheorems, standard bit arithmetic as detailed
in Section 6.3, and definition unfolding; it does not mean every elementary
step is expanded into an axiom-by-axiom derivation. Not machine-checked.
Astra's concurrence review accepted F1/F2 on this basis. Consequently
`UAPC_1` proves every `Inc_c` and `APC_1` proves every `Inc_c` and `CInc_c`:
plan outcome **1a**, for each fixed standard `c>=1`.

### 6.5 The ILW23 interface, checked against the text

The ECCC TR23-038 PDF (original March 2023 report) was text-extracted on
September 5, 2026 and the following were confirmed. Printed page numbers.

- p. 8, Section 2.3 and footnote 8: `forall n in Log` abbreviates
  `forall N forall n=|N|`; `T_PV` is the set of true sentences
  `forall x beta` with `beta` quantifier-free in `L(PV)`. Both match the
  conventions of this note.
- p. 13, Section 4.1: `dWPHP_ell(Eval) := forall n in Log forall circuits
  C:{0,1}^n->{0,1}^ell exists y in {0,1}^ell forall x in {0,1}^n
  [Eval(C,x)!=y]`, with `Eval(C,x):=C(x)`.
- p. 16, equation (7) and footnote 14: `dWPHP'(f)` exactly as in 0.5;
  `UAPC_1 := PV_1 + dWPHP'(PV)`.
- p. 17: `T^0_APC := T_PV + dWPHP'(PV)`; Theorem 24 as recorded in Step 0;
  Theorem 25 (= PS21 Theorem 4); Definition 26; statement of Theorem 27.
- p. 18: proof of Theorem 27, which says "circuits encoded by an s-bit
  string" and computes the input length from C; Theorem 28 (AVOID is not
  solvable by polynomial-size circuit families with `O(1)`
  circuit-inversion gates, under the two hypotheses).

**The paper fixes no bit-level circuit encoding and no formal validity
predicate.** So the question in 4.4 ("does `NativeCirc` describe exactly
that circuit domain?") has no textual answer. What the text does give is
the structure of the proof of Theorem 24: Theorem 25 applies to *any*
`forall exists forall` sentence with open `L(PV)` matrix and is
encoding-agnostic; Theorem 27 uses only that the input arity is computable
from the code and that `Eval(C,x)=C(x)` on every valid code, so that the
extracted circuit family solves AVOID on every valid code; Theorem 28 is a
statement about Boolean circuits given by some description, and its
reduction feeds constructed circuits to the AVOID solver *as codes*. So
transferring Theorem 28 to a different encoding needs a polynomial-time
map from standard descriptions into that encoding; existence of codes and
size-relatedness alone do not suffice.

The earlier audit's counterexample illustrates the distinction. Accept
syntactically valid pairs `(G,y)`, with y an l-bit value, and evaluate G
except that an output equal to y has its low bit flipped. Every such code
avoids its stored y, provably in PV_1. For `l>k`, every standard `k->l`
circuit nevertheless has a semantics-preserving code: choose y outside
its range. Existence of that choice does not supply an efficient coding
map. Importantly, validity does not test whether y is outside the range;
that would not be the promised PV syntax check.

Consequently (this is our reading of the proof, not a sentence in the
paper) Theorem 24 holds for any fixed PV pair `(NativeCirc, NativeEval)`
with:

```text
(E-a) there is a PV function code(G) such that for every standard gate
      list G for a circuit {0,1}^k->{0,1}^l, NativeCirc(code(G),k,l) and
      NativeEval(code(G),u) = G(u) for all u<2^k; arities are unique and
      PV-readable from any valid B; |code(G)| is polynomial in |G|;
(E-b) NativeCirc(B,k,l) and u<2^k  ->  NativeEval(B,u) < 2^l.
```

Only the standard-to-native direction of coding is needed. Any standard
gate-list encoding with explicit arities and an l-bit output mask
satisfies both, with `code` the identity. This reduces the "source
binding" item of 4.4 to a specification on our own choice of encoding,
under our reading of the proof of Theorem 24; it is **not** the
arbitrary-coding provability invariance that 4.4 declined to assume,
because the arithmetic side (W1-W3, L2, L3, `EvalAvoid_4`) is stated for
the same fixed pair. The zero-length point stands as in 4.4:
`forall n in Log` includes `N=0`, Theorem 24 needs `n<ell(n)`, so the
stretch used is `ell_*(n)=max(1,4n)` and the zero-length repair is needed.

T3 therefore stands as: under ILW23's hypotheses and our reading of
Theorem 24's proof, for any fixed pair satisfying (E-a), (E-b), `T^0_APC`
does not prove `CInc_{c_0}`, hence neither does `PV_1 + {Inc_c : c>=1}`
nor `UAPC_1`. Its remaining status items are: fix one concrete encoding
satisfying (E-a), (E-b); independent audit of this reading; novelty.

### 6.6 What is not discharged

- **D4 / L2 in PV_1.** The original Step 1 task 4 asks for correctness and
  overhead proofs for fixed PV algorithms in general; it remains
  incomplete. L2 is the evaluator-specific instance, needed for the
  positive reversal `PV_1 + CInc_{c_0} proves EvalAvoid_4`. T2/T3 need
  L2's mathematical truth under the efficient-U contract, but not a PV_1
  proof of it. Its internal proof would formalize U's step relation for E.
  This is deferred work, not the next-context target.
- **L3 in PV_1.** Finite counting over `2^k+1` candidates for the constant
  range `1<=k<M_0`; elementary but not written.
- **W1-W3 and the zero-length identity in PV_1.** Straightforward from E1,
  A4, A5 and (E-b) once the chosen `NativeEval` has its output bound as a
  PV_1 theorem; depends on the encoding fixed under 6.5.
- **Machine checking.** None of the above is machine-checked;
  `check_step1.py` remains a finite sanity check.
- **Novelty.** Gate D's first-pass assessment is complete in
  [gate_d_novelty.md](gate_d_novelty.md); novelty is not established.

### 6.7 Accepted Step 1 outcome

Fable's finalization and Astra's concurrence review converge on this
status, recorded September 5, 2026:

> Step 1 outcome 1a accepted: the parameterized and unary decoder forward
> proofs are complete at ordinary paper-proof level. The internal
> simulation/overhead obligation is explicitly deferred and remains
> incomplete. No completed reversal, separation, or novelty claim is
> included in this acceptance.

For every fixed standard `c>=1`, under the definitions of this note:

```text
UAPC_1 proves Inc_c;
APC_1  proves Inc_c and CInc_c.
```

Gate B's forward-proof deliverable is therefore accepted, not merely
"expected routine". This is not a claim that every original Gate B task
has passed. The proofs apply to fixed realizations of the stated runner
definitions; they do not certify a particular transition table. A
proof-assistant implementation is not a prerequisite for this paper-level
acceptance. No blocking F1/F2 error was found in the concurrence review;
the targeted basis audit confirmed M1-M4 and the resource arithmetic.

Keep the following distinctions when resuming:

- F1 uses the same simulation symbol in the decoder and target; it needs
  no property of the runner. F2 additionally uses normalization through
  `Ones`, E0', and the short-description rejection branch D1a.
- Conservativity transfers the open correctness lemmas only. The
  incompressibility arguments then use first-order logic plus the chosen
  pigeonhole axiom over PV_1; no `forall Sigma^b_2` transfer is claimed.
- The circuit-coding question does not reopen outcome 1a. It belongs to
  T3's import, which remains to sign off. Mathematical truth of L2 is
  required there; an internal PV_1 proof of L2 is not.
- The numerical value of c_0 and a certified concrete U remain unspecified.
  The current route is an existence argument for a fixed standard exponent
  under the efficient-machine contract, not a claim about arbitrary U.

The finite script was rerun during concurrence and passed with the counts
in Section 5.4. It remains a sanity check, not the basis of the acceptance.

### 6.8 Next-context handoff

*Done, September 5, 2026:* items 1-4 below are carried out in
[step2_conditional_separation.md](step2_conditional_separation.md); the
audit, Astra's concurrence corrections, and Fable 5.1's rebuttal review
are recorded there in Section 7; the review cycle is closed. The subsequent
focused novelty check and one bounded source-comparison audit are now in
[gate_d_novelty.md](gate_d_novelty.md). Its Section 5 gives the current
handoff: accept a reconstruction endpoint or deliberately select an
extension. Novelty is not established; L2-in-PV_1 remains deferred.
The original instructions below are retained as an execution record.

**Original transfer target (completed): close the T3 circuit-interface
obligation before attempting L2 inside PV_1.** This superseded the earlier
order "Gate D novelty first, then Gate C internal simulation". The agreed
Step 1 status is now recorded;
do not restart the forward proofs absent a concrete new counterexample.
This handoff adds no new research or completed separation theorem.

Read Sections 6.7, 6.5, and 4 first. The source conventions and exact
external hypotheses are in [step0_baseline.md](step0_baseline.md), Section
4; its older implication ledger is a historical Step 0 snapshot, not the
current proof status. The modified plan remains the scope/outcome guide.
These tracked notes are sufficient to resume; no prior chat or temporary
source extraction is required.

**Bounded attempt:** record the target and a 60-90 minute cap at the start;
allow one bounded independent audit after the write-up. Work in this order:

1. Fix a concrete standard circuit representation, total PV evaluator,
   and validity/arity predicate for `NativeCirc`/`NativeEval`. Specify
   malformed codes and widths, including the zero-input case. There is
   no need to invent a novel encoding or a new universal machine.
2. Establish (E-a)/(E-b) for that choice. Exhibit the efficient map
   `code(G)`, not just the existence of polynomial-size codes. Check its
   arities and semantics against standard circuit evaluation and retain
   the same evaluator in W1-W3, E, L2, L3, and the avoidance sentence.
3. Write the explicit transfer to ILW23's negative result, using the
   Section 6.5 analysis of Theorems 25, 27, and 28 behind Theorem 24.
   Audit resource bounds and quantifiers, not just the informal claim
   that encodings are equivalent. Only a signed-off transfer closes T3.
4. Independently audit the resulting `T_PV` route with the existing
   efficient-U contract. If it passes, consolidate a conditional-separation
   note with the exact ILW23 hypotheses and novelty unassessed. If it
   fails or the cap expires, preserve the strongest checked result and
   identify one precise remaining obligation; do not upgrade the status.

Preserve these constraints during that pass:

- Circuit descriptions have arbitrary length; never add `|B|<=m^k`.
  Keep the length witness M and the resources of Section 0.2 available.
- Auxiliary input is raw `str(C)` with `C=Wrap(B)`. The deadline at
  `N=Pad4(M)` is exactly `(4m+|C|)^c_0`; the sentinel is added only by
  the bounded simulation wrapper, not written by E.
- Retain `M_0=2|E|+2`, the constant-small-length repair L3, and the
  zero-length stretch `ell_*(m)=max(1,4m)` with witness `5-Eval(C,1)`.
- Use JLS-secure iO and `coNP not contained in i.o.NP/poly`, exactly as
  recorded in Step 0. Do not substitute weaker security or reinterpret
  infinitely-often agreement as agreement on isolated inputs.

**Original Gate D target (first pass completed):** a focused novelty check
after the transfer audit, before investing in L2-in-PV_1. Suggested terms are
"conditional Kolmogorov complexity" / "auxiliary input" with "dual weak
pigeonhole", "UAPC", and "parameter-free". A reconstruction of a known
result is an acceptable endpoint. Full-schema equivalences, general
universal-machine formalization, and Liu-Pass remain deferred.

**Verification:** run `python3 check_step1.py` for regression checks and
`git diff --check` for edits. Review the mathematical transfer separately;
the script does not implement U or the source circuit encoding. Record
the new result and audit in this note (or a scoped Step 2 proof note with
a pointer here), update the ledger, and preserve the distinction between
truth in `T_PV`, provability in PV_1, and novelty.
