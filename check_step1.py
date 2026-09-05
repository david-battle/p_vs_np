"""Reproduce the finite Step 1 checks with the Python standard library.

Run: python3 check_step1.py

The simulation stand-in reconstructs the seeded check in the session
transcript. It is not a universal-machine simulator. These checks neither
prove PV_1 derivability nor verify an implemented evaluator's running time.
Clock checks assume a polynomial bound; toy native circuits test only the
wrapper, not ILW23's encoding. Zero-length cases retain the old error as a
regression while checking the corrected sentinel complement.
"""

import itertools
import random


def enc(bits):
    return (1 << len(bits)) + int(bits or "0", 2)


def str_of(encoded):
    assert encoded >= 1
    return bin(encoded)[3:]


def pow_word(n):
    return 1 << n.bit_length()


def ones(n):
    return pow_word(n) - 1


def top(s):
    return pow_word(s) // 2


def val(s):
    return s - top(s)


def short(n):
    width = n.bit_length()
    return 2 * pow_word(n >> (width - width // 2))


def wrap(b):
    return pow_word(b) + b


def parse_pair(bits):
    program = []
    for position in range(0, len(bits) - 1, 2):
        pair = bits[position:position + 2]
        if pair == "01":
            return ("".join(program), bits[position + 2:]) if program else None
        if pair == "10":
            return None
        program.append(pair[0])
    return None


def sim(description, length_witness):
    return run(description, ones(length_witness))


def run(description, resource):
    """Abstract runner, not U: may succeed even on malformed programs."""
    n = resource.bit_length()
    rng = random.Random(description * 1000 + n)
    if rng.random() < 0.2:
        return 0
    width = n if rng.random() < 0.7 else rng.randint(0, n + 1)
    return enc("".join(rng.choice("01") for _ in range(width)))


def dec(length_witness, description):
    n = length_witness.bit_length()
    if 1 <= description < short(length_witness):
        output = sim(description, length_witness)
        if output.bit_length() == n + 1:
            return output - pow_word(length_witness)
    return 0


def unary(u):
    n = u.bit_length() + 1
    if n < 5:
        return 0
    resource = 2 * u
    description = u % short(resource)
    if description == 0:
        return 0
    output = sim(description, resource)
    if output.bit_length() == n + 1:
        return output - pow_word(resource)
    return 0


def csim(description, auxiliary, length_witness):
    if auxiliary == 0:
        return 0
    # Preserve the canonical N resource while allowing dependence on Z's value.
    return run(description + auxiliary * 100003, ones(length_witness))


def cdec(length_witness, auxiliary, description):
    if auxiliary >= 1 and 1 <= description < short(length_witness):
        output = csim(description, auxiliary, length_witness)
        if output.bit_length() == length_witness.bit_length() + 1:
            return output - pow_word(length_witness)
    return 0


def local_eval(circuit, x, tables):
    """Sentinel wrapper over finite native tables, not actual source circuits."""
    if circuit < 1 or circuit != wrap(val(circuit)) or x < 1:
        return 0
    native = val(circuit)
    if native not in tables:
        return 0
    m, outputs = tables[native]
    if x.bit_length() != m + 1:
        return 0
    bound = max(2, top(x) ** 4)
    v = outputs[val(x)]
    return bound + v if v < bound else 0


def main():
    if not __debug__:
        raise SystemExit("Run without -O: this check uses assertions.")

    encoding_cases = 0
    for m in range(8):
        codes = set()
        for k in range(m + 1):
            for value in range(1 << k):
                bits = format(value, f"0{k}b") if k else ""
                padded = "0" * (m - k) + "1" + bits
                assert int(padded, 2) == enc(bits)
                assert str_of(enc(bits)) == bits
                assert enc(str_of(enc(bits))) == enc(bits)
                assert enc(bits).bit_length() == k + 1
                assert enc(bits) not in codes
                codes.add(enc(bits))
                encoding_cases += 1
        assert codes == set(range(1, 1 << (m + 1)))

    for n in range(4096):
        assert ones(n).bit_length() == n.bit_length()
        assert ones(n) == ones(ones(n))
        assert short(n) == 1 << (n.bit_length() // 2 + 1)
        assert val(wrap(n)) == n
        assert wrap(n).bit_length() == n.bit_length() + 1
        if n:
            assert top(n) <= n < 2 * top(n)
            assert val(n) < top(n)
        for d in range(1, short(n) + 2):
            assert (d < short(n)) == (d.bit_length() <= n.bit_length() // 2 + 1)

    preimage_cases = 0
    for n in range(5, 25):
        resource = (1 << n) - 1
        for d in range(1, short(resource)):
            u = pow_word(resource) // 4 + d
            assert u < pow_word(resource) // 2
            assert (2 * u).bit_length() == resource.bit_length()
            assert short(2 * u) == short(resource)
            assert pow_word(2 * u) == pow_word(resource)
            assert ones(2 * u) == ones(resource)
            assert u % short(2 * u) == d
            preimage_cases += 1

    covered = 0
    unary_covered = 0
    for n in range(4, 15):
        m = n // 2
        assert m + 1 <= n - 1
        assert (m + 1 <= n - 2) == (n >= 5)
        witness = (1 << n) - 1
        same_length_witness = 1 << (n - 1)
        for value in range(1 << n):
            output = (1 << n) + value
            assert output.bit_length() == n + 1
            assert output - (1 << n) == value
        for description in range(1, 1 << (m + 1)):
            output = sim(description, witness)
            assert sim(description, same_length_witness) == output
            if n >= 5:
                u = (1 << (n - 2)) + description
                assert u < (1 << (n - 1))
                assert u.bit_length() == n - 1
                assert (2 * u).bit_length() == n
                assert u % (1 << (m + 1)) == description
            if output.bit_length() == n + 1:
                assert description < (1 << (n - 1))
                assert dec(witness, description) == output - (1 << n)
                covered += 1
                if n >= 5:
                    assert unary(u) == output - (1 << n)
                    unary_covered += 1
        if n == 4:
            outputs = {sim(d, witness) for d in range(1, 8)}
            assert any(16 + value not in outputs for value in range(16))

    for program_length in range(1, 6):
        cutoff = 2 * program_length + 2
        for m in range(1, 40):
            assert (cutoff + m <= 2 * m) == (m >= cutoff)
            assert (1 << m) + 1 <= (1 << (4 * m))
            witness = (1 << m) - 1
            padded = (1 << witness.bit_length()) ** 4 - 1
            assert padded.bit_length() == 4 * m

    assert ((1 << 0) ** 4 - 1).bit_length() == 0

    conditional_covered = 0
    for n in range(4, 11):
        witness = ones(1 << (n - 1))
        for z in range(8):
            for d in range(1, short(witness)):
                output = csim(d, z, witness)
                assert csim(d, z, witness) == csim(d, z, 1 << (n - 1))
                if output.bit_length() == n + 1:
                    assert cdec(witness, z, d) == output - pow_word(witness)
                    conditional_covered += 1
            assert cdec(witness, z, 0) == 0
    assert conditional_covered > 0

    for d in range(1, 16):
        assert parse_pair(str_of(d)) is None
    pair_cases = 0
    for program in ("0", "1", "01", "10", "001", "110"):
        for width in range(5):
            for value in range(1 << width):
                payload = format(value, f"0{width}b") if width else ""
                bits = "".join(bit * 2 for bit in program) + "01" + payload
                assert parse_pair(bits) == (program, payload)
                assert len(bits) == 2 * len(program) + 2 + width
                pair_cases += 1

    clock_cases = 0
    for coefficient in range(1, 33):
        for degree in range(1, 5):
            c0 = degree + (coefficient - 1).bit_length()
            for m in range(1, 6):
                for raw_width in range(11):
                    z = "0" * raw_width
                    c = enc(z)
                    s = m + raw_width + 1
                    r = 4 * m + c.bit_length()
                    assert r == 4 * m + raw_width + 1
                    assert coefficient * s ** degree <= r ** c0
                    clock_cases += 1

    # Exhaust all two-input-value tables at m=1; sample larger widths.
    tables = {0: (0, (0,)), 1: (0, (1,))}
    for outputs in itertools.product(range(16), repeat=2):
        tables[len(tables)] = (1, outputs)
    rng = random.Random(13)
    for m in (2, 3):
        for _ in range(16):
            outputs = tuple(rng.randrange(1 << (4 * m)) for _ in range(1 << m))
            tables[len(tables)] = (m, outputs)
    wrapper_outputs = 0
    for b, (m, outputs) in tables.items():
        c = wrap(b)
        bound = 2 if m == 0 else 1 << (4 * m)
        raw_missing = next(j for j in range((1 << m) + 1) if j not in outputs)
        y = bound + raw_missing
        assert val(y) == raw_missing < bound
        assert y.bit_length() == (1 if m == 0 else 4 * m) + 1
        for u, native_output in enumerate(outputs):
            x = (1 << m) + u
            assert val(x) == u
            assert local_eval(c, x, tables) == bound + native_output
            assert local_eval(c, x, tables) != y
            assert native_output != val(y)
            wrapper_outputs += 1
        # A noncanonical circuit wrapper is invalid, even if Val recovers B.
        noncanonical = enc("0" + str_of(c))
        assert val(noncanonical) == b and noncanonical != wrap(b)
        assert local_eval(noncanonical, 1 << m, tables) == 0
    assert local_eval(0, 1, tables) == local_eval(1, 0, tables) == 0

    print(f"PASS: {encoding_cases} encoding cases (m=0..7).")
    print(f"PASS: C1 on {covered} covered instances (n=4..14).")
    print(f"PASS: C2 on {unary_covered} of those instances (n>=5).")
    print("PASS: literal bit terms on 4096 resource values, including zero.")
    print(f"PASS: {preimage_cases} unary preimage/resource identities (n=5..24).")
    print("PASS: length invariance, bounds, finite avoidance, and Pad4.")
    print(f"PASS: conditional coverage on {conditional_covered} instances.")
    print(
        f"PASS: {pair_cases} pair parses and rejection of all descriptions "
        "shorter than 4 bits."
    )
    print(
        f"PASS: {clock_cases} clock-absorption inequalities "
        "(polynomial bound assumed)."
    )
    print(
        f"PASS: {len(tables)} toy native circuits, "
        f"{wrapper_outputs} wrapped evaluations/avoidance checks."
    )

    # Eval returns a sentinel, not a raw bit. Natural subtraction truncates.
    for output in (2, 3):
        old_witness = max(0, 1 - output)
        corrected_witness = 5 - output
        assert old_witness not in (2, 3)
        assert corrected_witness in (2, 3) and corrected_witness != output
        print(
            f"PASS zero-length regression: Eval={output}; rejected old "
            f"witness {old_witness}; 5-Eval={corrected_witness}."
        )
    print("Finite checks only; not a PV_1 proof or a verification of L2/T3.")


if __name__ == "__main__":
    main()
