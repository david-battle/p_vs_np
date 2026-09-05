"""Reproduce the finite Step 1 checks with the Python standard library.

Run: python3 check_step1.py

The simulation stand-in reconstructs the seeded check in the session
transcript. It is not a universal-machine simulator. These checks neither
prove PV_1 derivability nor verify the evaluator's clock or source encoding.
The zero-length cases explicitly demonstrate an error in the current note.
"""

import random


def enc(bits):
    return (1 << len(bits)) + int(bits or "0", 2)


def str_of(encoded):
    assert encoded >= 1
    return bin(encoded)[3:]


def sim(description, length_witness):
    """Total stand-in: 0 means failure; other values encode output strings."""
    n = length_witness.bit_length()
    rng = random.Random(description * 1000 + n)
    if rng.random() < 0.2:
        return 0
    width = n if rng.random() < 0.7 else rng.randint(0, n + 1)
    return enc("".join(rng.choice("01") for _ in range(width)))


def dec(length_witness, description):
    n = length_witness.bit_length()
    m = n // 2
    if 1 <= description < (1 << (m + 1)):
        output = sim(description, length_witness)
        if output.bit_length() == n + 1:
            return output - (1 << n)
    return 0


def unary(u):
    n = u.bit_length() + 1
    if n < 5:
        return 0
    description = u % (1 << (n // 2 + 1))
    if description == 0:
        return 0
    output = sim(description, 2 * u)
    if output.bit_length() == n + 1:
        return output - (1 << n)
    return 0


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
    print(f"PASS: {encoding_cases} encoding cases (m=0..7).")
    print(f"PASS: C1 on {covered} covered instances (n=4..14).")
    print(f"PASS: C2 on {unary_covered} of those instances (n>=5).")
    print("PASS: length invariance, arithmetic bounds, finite avoidance, and Pad4.")

    # Eval returns a sentinel, not a raw bit. Natural subtraction truncates.
    for output in (2, 3):
        documented_witness = max(0, 1 - output)
        corrected_witness = 5 - output
        assert documented_witness not in (2, 3)
        assert corrected_witness in (2, 3) and corrected_witness != output
        print(
            f"KNOWN NOTE ERROR: Eval={output}; 1-Eval gives "
            f"{documented_witness}, but the encoded complement is "
            f"5-Eval={corrected_witness}."
        )
    print("Finite checks only; not a PV_1 proof or a verification of L2/T3.")


if __name__ == "__main__":
    main()
