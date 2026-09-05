"""Finite checks for the Step 2 circuit encoding and solver control flow.

Run: python3 check_step2.py

Implements the Section 2 encoding of step2_conditional_separation.md
(NativeCirc, NativeEval, In, NativeOut), an independent reference evaluator for
gate lists, the Section 0.4 sentinel Eval with the real NativeEval, and
the Section 4.3 solver run against brute-force stand-ins for Theorem 25's
witnessing functions. Standard library only. These are finite sanity
checks; they prove nothing in PV_1 and do not implement ILW23's format.
"""

import random

AND, OR, NOT, ONE = "00", "01", "10", "11"


# --- sentinel conventions (Section 0.1-0.2) ---------------------------------

def enc(bits):
    return (1 << len(bits)) + int(bits or "0", 2)


def str_of(encoded):
    assert encoded >= 1
    return bin(encoded)[3:]


def pow_word(n):
    return 1 << n.bit_length()


def top(s):
    return pow_word(s) // 2


def val(s):
    return s - top(s)


def wrap(b):
    return pow_word(b) + b


def ell(k):
    return 1 if k == 0 else 4 * k


# --- the Section 2 encoding --------------------------------------------------

def bin_w(r, w):
    assert 0 <= r < (1 << w)
    return format(r, "b").zfill(w)


def encode(k, l, gates, outs):
    """gates: list of (op, a, b); outs: list of wire indices."""
    g = len(gates)
    w = max(1, (k + g).bit_length(), l.bit_length())
    p = "1" * w + "0" + "1" * k + "0" + bin_w(l, w) + bin_w(g, w)
    for op, a, b in gates:
        p += op + bin_w(a, w) + bin_w(b, w)
    for o in outs:
        p += bin_w(o, w)
    return p


def parse(p):
    """Return (w, k, l, g, gates, outs) if Valid(p), else None."""
    if not p or p[0] != "1":
        return None                                   # V1: w >= 1
    w = 0
    while w < len(p) and p[w] == "1":
        w += 1
    pos = w + 1                                       # skip the 0
    k = 0
    while pos < len(p) and p[pos] == "1":
        k += 1
        pos += 1
    if pos >= len(p):
        return None                                   # missing 0 after 1^k
    pos += 1
    if pos + 2 * w > len(p):
        return None                                   # V1: fields present
    l = int(p[pos:pos + w], 2)
    g = int(p[pos + w:pos + 2 * w], 2)
    pos += 2 * w
    if len(p) != pos + g * (2 + 2 * w) + l * w:
        return None                                   # V2: exact length
    gates = []
    for j in range(g):
        op = p[pos:pos + 2]
        a = int(p[pos + 2:pos + 2 + w], 2)
        b = int(p[pos + 2 + w:pos + 2 + 2 * w], 2)
        pos += 2 + 2 * w
        if op != ONE and a >= k + j:
            return None                               # V3
        if op in (AND, OR) and b >= k + j:
            return None                               # V3
        gates.append((op, a, b))
    outs = []
    for _ in range(l):
        o = int(p[pos:pos + w], 2)
        pos += w
        if o >= k + g:
            return None                               # V4
        outs.append(o)
    return w, k, l, g, gates, outs


def parsed(B):
    return parse(str_of(B)) if B >= 1 else None


def In(B):
    q = parsed(B)
    return q[1] if q else 0


def NativeOut(B):
    q = parsed(B)
    return q[2] if q else 0


def native_circ(B, k, l):
    return parsed(B) is not None and In(B) == k and NativeOut(B) == l


def native_eval(B, u):
    q = parsed(B)
    if q is None:
        return 0
    _, k, l, g, gates, outs = q
    v = [(u >> i) & 1 for i in range(k)]
    for op, a, b in gates:
        if op == AND:
            v.append(v[a] & v[b])
        elif op == OR:
            v.append(v[a] | v[b])
        elif op == NOT:
            v.append(1 - v[a])
        else:
            v.append(1)
    return sum(v[o] << i for i, o in enumerate(outs))


# --- independent reference semantics on the gate list ------------------------

def reference_eval(k, gates, outs, u):
    wires = {}
    for i in range(k):
        wires[i] = (u // (2 ** i)) % 2
    for j, (op, a, b) in enumerate(gates):
        if op == AND:
            wires[k + j] = 1 if wires[a] == 1 and wires[b] == 1 else 0
        elif op == OR:
            wires[k + j] = 1 if wires[a] == 1 or wires[b] == 1 else 0
        elif op == NOT:
            wires[k + j] = 0 if wires[a] == 1 else 1
        else:
            wires[k + j] = 1
    return sum(wires[o] * (2 ** i) for i, o in enumerate(outs))


def random_circuit(rng, k, l, g):
    gates = []
    for j in range(g):
        op = rng.choice((AND, OR, NOT, ONE))
        if k + j == 0:
            op = ONE
        a = rng.randrange(k + j) if k + j else 0
        b = rng.randrange(k + j) if k + j else 0
        gates.append((op, a, b))
    outs = [rng.randrange(k + g) for _ in range(l)]
    return gates, outs


# --- Section 0.4 Eval with the real NativeEval -------------------------------

def circ(C, k, l):
    return C >= 1 and C == wrap(val(C)) and native_circ(val(C), k, l)


def local_eval(C, X):
    if X == 0:
        return 0
    k = X.bit_length() - 1
    if not circ(C, k, ell(k)):
        return 0
    v = native_eval(val(C), val(X))
    out = max(2, top(X) ** 4)
    return 0 if v >= out else out + v


# --- Section 4.3 solver with stand-in Student functions ----------------------

def solver(n, B, C_eval, O, fs):
    """Run steps 1-3 of the Section 4.3 solver; fs are the f_i stand-ins."""
    if n == 0:
        return 1 - C_eval(0)
    M = (1 << n) - 1
    xs = []
    for f in fs:
        y = f(M, B, xs)
        if y < (1 << (4 * n)):
            x = O(y)
            if C_eval(x) != y:
                return y
            xs.append(x)
        else:
            xs.append(0)
    return None                                       # step 3: unreachable


def main():
    if not __debug__:
        raise SystemExit("run without -O so that assertions are active")
    rng = random.Random(2024)

    # (E-a) with code = identity, (E-b), arities, malformed variants.
    circuits = 0
    evaluations = 0
    rejections = 0
    for k in range(0, 5):
        for l in sorted({ell(k), 0, 1, 3, 4 * k + 2}):
            for g in range(0, 9):
                if l and not (k + g):
                    continue                          # no wire to output
                for _ in range(4):
                    gates, outs = random_circuit(rng, k, l, g)
                    p = encode(k, l, gates, outs)
                    B = enc(p)
                    assert parse(p) is not None, (k, l, g)
                    assert native_circ(B, k, l)
                    assert In(B) == k and NativeOut(B) == l
                    # Arity uniqueness: no other pair is accepted.
                    assert not native_circ(B, k + 1, l)
                    assert not native_circ(B, k, l + 1)
                    circuits += 1
                    for u in range(1 << (k + 1)):     # includes u >= 2^k
                        y = native_eval(B, u)
                        assert y == reference_eval(k, gates, outs, u)
                        assert y < (1 << l)           # (E-b), all u
                        evaluations += 1
                    # Malformed variants of a valid code are rejected.
                    for bad in (
                        "0" + p,                      # w = 0
                        p[:-1] if len(p) > 1 else "",  # truncated
                        p + "0",                      # over-long
                    ):
                        assert parse(bad) is None
                        assert native_eval(enc(bad), 1) == 0 if bad else True
                        rejections += 1
    assert parsed(0) is None and native_eval(0, 5) == 0 and In(0) == NativeOut(0) == 0

    # Forward wire reference and out-of-range output are rejected (V3, V4).
    w = 2
    fwd = "1" * w + "0" + "1" * 1 + "0" + bin_w(1, w) + bin_w(1, w)
    fwd += AND + bin_w(0, w) + bin_w(1, w) + bin_w(1, w)   # gate 0 uses wire 1 = itself
    assert parse(fwd) is None
    oor = "1" * w + "0" + "1" * 1 + "0" + bin_w(1, w) + bin_w(0, w) + bin_w(1, w)
    assert parse(oor) is None                         # output wire 1 with k+g = 1
    rejections += 2

    # Zero-input circuits: constants only, evaluate below 2.
    zero_cases = 0
    for gates, outs in (
        ([(ONE, 0, 0)], [0]),
        ([(ONE, 0, 0), (NOT, 0, 0)], [1]),
        ([(ONE, 0, 0), (NOT, 0, 0), (AND, 0, 1)], [2]),
        ([(ONE, 0, 0), (NOT, 0, 0), (OR, 0, 1)], [2]),
    ):
        B = enc(encode(0, 1, gates, outs))
        assert native_circ(B, 0, 1)
        assert native_eval(B, 0) < 2
        assert native_eval(B, 0) == reference_eval(0, gates, outs, 0)
        # Zero-length identity via the wrapper: Eval(C,1) in {2,3}.
        C = wrap(B)
        e = local_eval(C, 1)
        assert e in (2, 3) and e == 2 + native_eval(B, 0)
        assert (5 - e) in (2, 3) and (5 - e) != e
        zero_cases += 1

    # W1-W3 with the real evaluator at the stretch 4m.
    wrapper_cases = 0
    for m in range(1, 4):
        for _ in range(12):
            g = rng.randrange(0, 10)
            gates, outs = random_circuit(rng, m, 4 * m, g)
            B = enc(encode(m, 4 * m, gates, outs))
            C = wrap(B)
            assert circ(C, m, 4 * m) == native_circ(B, m, 4 * m)   # W1
            M = rng.randrange(1 << (m - 1), 1 << m)
            assert M.bit_length() == m
            PowM = 1 << m
            for u in range(PowM):
                X = PowM + u
                assert X.bit_length() == m + 1
                assert local_eval(C, X) == PowM ** 4 + native_eval(B, u)   # W2
                Y = local_eval(C, X)
                assert Y.bit_length() == 4 * m + 1
                assert val(Y) < PowM ** 4 and Y == PowM ** 4 + val(Y)     # W3
                wrapper_cases += 1
            # Noncanonical wrappers are invalid even when Val recovers B.
            noncanonical = enc("0" + str_of(C))
            assert val(noncanonical) == B and not circ(noncanonical, m, 4 * m)
            assert local_eval(noncanonical, PowM) == 0

    # Section 4.3 solver against pigeonhole stand-ins for f_1..f_k.
    solver_cases = 0
    for n in range(0, 3):
        for _ in range(10):
            g = rng.randrange(0, 8)
            m = ell(n)
            gates, outs = random_circuit(rng, n, m, g)
            B = enc(encode(n, m, gates, outs))
            table = {u: native_eval(B, u) for u in range(1 << n)}

            def C_eval(x, table=table):
                return table[x]

            def O(y, table=table):
                for x, v in table.items():
                    if v == y:
                        return x
                return 0

            # Stand-in 1: constants 0..2^n; the Theorem 25 disjunction
            # holds by pigeonhole (2^n+1 candidates, 2^n inputs).
            fs = [(lambda M, B, xs, c=c: c) for c in range((1 << n) + 1)]
            # Stand-in 2: an oversized first proposal, then the constants.
            fs2 = [lambda M, B, xs, n=n: (1 << (4 * n)) + 7] + fs
            for f_list in (fs, fs2):
                y = solver(n, B, C_eval, O, f_list)
                assert y is not None
                assert 0 <= y < (1 << m)
                assert C_eval(O(y)) != y
                assert y not in table.values()
                solver_cases += 1

    print(f"PASS: {circuits} random valid codes, {evaluations} evaluations "
          "agree with the reference semantics; (E-b) holds for all inputs.")
    print(f"PASS: {rejections} malformed codes rejected (w=0, truncation, "
          "over-length, forward reference, out-of-range output).")
    print(f"PASS: {zero_cases} zero-input circuits; zero-length identity "
          "Eval(C,1) in {2,3} and 5-Eval complement.")
    print(f"PASS: W1-W3 on {wrapper_cases} wrapped evaluations (m=1..3).")
    print(f"PASS: solver control flow on {solver_cases} tiny instances with "
          "pigeonhole stand-ins, including an oversized first proposal.")
    print("Finite checks only; not a PV_1 proof, not Theorem 25's witnessing "
          "functions, not ILW23's circuit format.")


if __name__ == "__main__":
    main()
