from collections import namedtuple
from typing import Any, List, Optional, Tuple
import hashlib
import secrets
import time

#
# The following helper functions were copied from the BIP-340 reference implementation:
# https://github.com/bitcoin/bips/blob/master/bip-0340/reference.py
#

p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

# Points are tuples of X and Y coordinates and the point at infinity is
# represented by the None keyword.
G = (0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798, 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)

Point = Tuple[int, int]

# This implementation can be sped up by storing the midstate after hashing
# tag_hash instead of rehashing it all the time.
def tagged_hash(tag: str, msg: bytes) -> bytes:
    tag_hash = hashlib.sha256(tag.encode()).digest()
    return hashlib.sha256(tag_hash + tag_hash + msg).digest()

def is_infinite(P: Optional[Point]) -> bool:
    return P is None

def x(P: Point) -> int:
    assert not is_infinite(P)
    return P[0]

def y(P: Point) -> int:
    assert not is_infinite(P)
    return P[1]

def point_add(P1: Optional[Point], P2: Optional[Point]) -> Optional[Point]:
    if P1 is None:
        return P2
    if P2 is None:
        return P1
    if (x(P1) == x(P2)) and (y(P1) != y(P2)):
        return None
    if P1 == P2:
        lam = (3 * x(P1) * x(P1) * pow(2 * y(P1), p - 2, p)) % p
    else:
        lam = ((y(P2) - y(P1)) * pow(x(P2) - x(P1), p - 2, p)) % p
    x3 = (lam * lam - x(P1) - x(P2)) % p
    return (x3, (lam * (x(P1) - x3) - y(P1)) % p)

def point_mul(P: Optional[Point], n: int) -> Optional[Point]:
    R = None
    for i in range(256):
        if (n >> i) & 1:
            R = point_add(R, P)
        P = point_add(P, P)
    return R

def bytes_from_int(x: int) -> bytes:
    return x.to_bytes(32, byteorder="big")

def bytes_from_point(P: Point) -> bytes:
    return bytes_from_int(x(P))

def lift_x(b: bytes) -> Optional[Point]:
    x = int_from_bytes(b)
    if x >= p:
        return None
    y_sq = (pow(x, 3, p) + 7) % p
    y = pow(y_sq, (p + 1) // 4, p)
    if pow(y, 2, p) != y_sq:
        return None
    return (x, y if y & 1 == 0 else p-y)

def int_from_bytes(b: bytes) -> int:
    return int.from_bytes(b, byteorder="big")

def has_even_y(P: Point) -> bool:
    assert not is_infinite(P)
    return y(P) % 2 == 0

def schnorr_verify(msg: bytes, pubkey: bytes, sig: bytes) -> bool:
    if len(msg) != 32:
        raise ValueError('The message must be a 32-byte array.')
    if len(pubkey) != 32:
        raise ValueError('The public key must be a 32-byte array.')
    if len(sig) != 64:
        raise ValueError('The signature must be a 64-byte array.')
    P = lift_x(pubkey)
    r = int_from_bytes(sig[0:32])
    s = int_from_bytes(sig[32:64])
    if (P is None) or (r >= p) or (s >= n):
        return False
    e = int_from_bytes(tagged_hash("BIP0340/challenge", sig[0:32] + pubkey + msg)) % n
    R = point_add(point_mul(G, s), point_mul(P, n - e))
    if (R is None) or (not has_even_y(R)) or (x(R) != r):
        return False
    return True

#
# End of helper functions copied from BIP-340 reference implementation.
#

# There are two types of exceptions that can be raised by this implementation:
#   - ValueError for indicating that an input doesn't conform to some function
#     precondition (e.g. an input array is the wrong length, a serialized
#     representation doesn't have the correct format).
#   - InvalidContributionError for indicating that a signer (or the
#     aggregator) is misbehaving in the protocol.
#
# Assertions are used to (1) satisfy the type-checking system, and (2) check for
# inconvenient events that can't happen except with negligible probability (e.g.
# output of a hash function is 0) and can't be manually triggered by any
# signer.

# This exception is raised if a party (signer or nonce aggregator) sends invalid
# values. Actual implementations should not crash when receiving invalid
# contributions. Instead, they should hold the offending party accountable.
class InvalidContributionError(Exception):
    def __init__(self, signer, contrib):
        self.signer = signer
        # contrib is one of "pubkey", "pubnonce", "aggnonce", or "psig".
        self.contrib = contrib

infinity = None

def cbytes(P: Point) -> bytes:
    a = b'\x02' if has_even_y(P) else b'\x03'
    return a + bytes_from_point(P)

def cbytes_extended(P: Optional[Point]) -> bytes:
    if is_infinite(P):
        return (0).to_bytes(33, byteorder='big')
    assert P is not None
    return cbytes(P)

def point_negate(P: Optional[Point]) -> Optional[Point]:
    if P is None:
        return P
    return (x(P), p - y(P))

def cpoint(x: bytes) -> Point:
    P = lift_x(x[1:33])
    if P is None:
        raise ValueError('x is not a valid compressed point.')
    if x[0] == 2:
        return P
    elif x[0] == 3:
        P = point_negate(P)
        assert P is not None
        return P
    else:
        raise ValueError('x is not a valid compressed point.')

def cpoint_extended(x: bytes) -> Optional[Point]:
    if x == (0).to_bytes(33, 'big'):
        return None
    else:
        return cpoint(x)

KeyGenContext = namedtuple('KeyGenContext', ['Q', 'gacc', 'tacc'])

def get_pk(keygen_ctx: KeyGenContext) -> bytes:
    Q, _, _ = keygen_ctx
    return bytes_from_point(Q)

def key_agg(pubkeys: List[bytes]) -> KeyGenContext:
    pk2 = get_second_key(pubkeys)
    u = len(pubkeys)
    Q = infinity
    for i in range(u):
        P_i = lift_x(pubkeys[i])
        if P_i is None:
            raise InvalidContributionError(i, "pubkey")
        a_i = key_agg_coeff_internal(pubkeys, pubkeys[i], pk2)
        Q = point_add(Q, point_mul(P_i, a_i))
    # Q is not the point at infinity except with negligible probability.
    assert(Q is not None)
    gacc = 1
    tacc = 0
    return KeyGenContext(Q, gacc, tacc)

def hash_keys(pubkeys: List[bytes]) -> bytes:
    return tagged_hash('KeyAgg list', b''.join(pubkeys))

def get_second_key(pubkeys: List[bytes]) -> bytes:
    u = len(pubkeys)
    for j in range(1, u):
        if pubkeys[j] != pubkeys[0]:
            return pubkeys[j]
    return bytes_from_int(0)

def key_agg_coeff(pubkeys: List[bytes], pk_: bytes) -> int:
    pk2 = get_second_key(pubkeys)
    return key_agg_coeff_internal(pubkeys, pk_, pk2)

def key_agg_coeff_internal(pubkeys: List[bytes], pk_: bytes, pk2: bytes) -> int:
    L = hash_keys(pubkeys)
    if pk_ == pk2:
        return 1
    return int_from_bytes(tagged_hash('KeyAgg coefficient', L + pk_)) % n

def apply_tweak(keygen_ctx: KeyGenContext, tweak: bytes, is_xonly: bool) -> KeyGenContext:
    if len(tweak) != 32:
        raise ValueError('The tweak must be a 32-byte array.')
    Q, gacc, tacc = keygen_ctx
    if is_xonly and not has_even_y(Q):
        g = n - 1
    else:
        g = 1
    t = int_from_bytes(tweak)
    if t >= n:
        raise ValueError('The tweak must be less than n.')
    Q_ = point_add(point_mul(Q, g), point_mul(G, t))
    if Q_ is None:
        raise ValueError('The result of tweaking cannot be infinity.')
    gacc_ = g * gacc % n
    tacc_ = (t + g * tacc) % n
    return KeyGenContext(Q_, gacc_, tacc_)

def bytes_xor(a: bytes, b: bytes) -> bytes:
    return bytes(x ^ y for x, y in zip(a, b))

def nonce_hash(rand: bytes, aggpk: bytes, i: int, msg_prefixed: bytes, extra_in: bytes) -> int:
    buf = b''
    buf += rand
    buf += len(aggpk).to_bytes(1, 'big')
    buf += aggpk
    buf += msg_prefixed
    buf += len(extra_in).to_bytes(4, 'big')
    buf += extra_in
    buf += i.to_bytes(1, 'big')
    return int_from_bytes(tagged_hash('MuSig/nonce', buf))

def nonce_gen_internal(rand_: bytes, sk: Optional[bytes], aggpk: Optional[bytes], msg: Optional[bytes], extra_in: Optional[bytes]) -> Tuple[bytes, bytes]:
    if sk is not None:
        rand = bytes_xor(sk, tagged_hash('MuSig/aux', rand_))
    else:
        rand = rand_
    if aggpk is None:
        aggpk = b''
    if msg is None:
        msg_prefixed = b'\x00'
    else:
        msg_prefixed = b'\x01'
        msg_prefixed += len(msg).to_bytes(8, 'big')
        msg_prefixed += msg
    if extra_in is None:
        extra_in = b''
    k_1 = nonce_hash(rand, aggpk, 0, msg_prefixed, extra_in)
    k_2 = nonce_hash(rand, aggpk, 1, msg_prefixed, extra_in)
    # k_1 == 0 or k_2 == 0 cannot occur except with negligible probability.
    assert k_1 != 0
    assert k_2 != 0
    R_1_ = point_mul(G, k_1)
    R_2_ = point_mul(G, k_2)
    assert R_1_ is not None
    assert R_2_ is not None
    pubnonce = cbytes(R_1_) + cbytes(R_2_)
    secnonce = bytes_from_int(k_1) + bytes_from_int(k_2)
    return secnonce, pubnonce

def nonce_gen(sk: Optional[bytes], aggpk: Optional[bytes], msg: Optional[bytes], extra_in: Optional[bytes]) -> Tuple[bytes, bytes]:
    if sk is not None and len(sk) != 32:
        raise ValueError('The optional byte array sk must have length 32.')
    if aggpk is not None and len(aggpk) != 32:
        raise ValueError('The optional byte array aggpk must have length 32.')
    rand_ = secrets.token_bytes(32)
    return nonce_gen_internal(rand_, sk, aggpk, msg, extra_in)

def nonce_agg(pubnonces: List[bytes]) -> bytes:
    u = len(pubnonces)
    aggnonce = b''
    for i in (1, 2):
        R_i = infinity
        for j in range(u):
            try:
                R_ij = cpoint(pubnonces[j][(i-1)*33:i*33])
            except ValueError:
                raise InvalidContributionError(j, "pubnonce")
            R_i = point_add(R_i, R_ij)
        aggnonce += cbytes_extended(R_i)
    return aggnonce

SessionContext = namedtuple('SessionContext', ['aggnonce', 'pubkeys', 'tweaks', 'is_xonly', 'msg'])

def key_agg_and_tweak(pubkeys: List[bytes], tweaks: List[bytes], is_xonly: List[bool]):
    if len(tweaks) != len(is_xonly):
        raise ValueError('The `tweaks` and `is_xonly` arrays must have the same length.')
    keygen_ctx = key_agg(pubkeys)
    v = len(tweaks)
    for i in range(v):
        keygen_ctx = apply_tweak(keygen_ctx, tweaks[i], is_xonly[i])
    return keygen_ctx

def get_session_values(session_ctx: SessionContext) -> Tuple[Point, int, int, int, Point, int]:
    (aggnonce, pubkeys, tweaks, is_xonly, msg) = session_ctx
    Q, gacc, tacc = key_agg_and_tweak(pubkeys, tweaks, is_xonly)
    b = int_from_bytes(tagged_hash('MuSig/noncecoef', aggnonce + bytes_from_point(Q) + msg)) % n
    try:
        R_1 = cpoint_extended(aggnonce[0:33])
        R_2 = cpoint_extended(aggnonce[33:66])
    except ValueError:
        # Nonce aggregator sent invalid nonces
        raise InvalidContributionError(None, "aggnonce")
    R_ = point_add(R_1, point_mul(R_2, b))
    R = R_ if not is_infinite(R_) else G
    assert R is not None
    e = int_from_bytes(tagged_hash('BIP0340/challenge', bytes_from_point(R) + bytes_from_point(Q) + msg)) % n
    return (Q, gacc, tacc, b, R, e)

def get_session_key_agg_coeff(session_ctx: SessionContext, P: Point) -> int:
    (_, pubkeys, _, _, _) = session_ctx
    return key_agg_coeff(pubkeys, bytes_from_point(P))

# Callers should overwrite secnonce with zeros after calling sign.
def sign(secnonce: bytes, sk: bytes, session_ctx: SessionContext) -> bytes:
    (Q, gacc, _, b, R, e) = get_session_values(session_ctx)
    k_1_ = int_from_bytes(secnonce[0:32])
    k_2_ = int_from_bytes(secnonce[32:64])
    if not 0 < k_1_ < n:
        raise ValueError('first secnonce value is out of range.')
    if not 0 < k_2_ < n:
        raise ValueError('second secnonce value is out of range.')
    k_1 = k_1_ if has_even_y(R) else n - k_1_
    k_2 = k_2_ if has_even_y(R) else n - k_2_
    d_ = int_from_bytes(sk)
    if not 0 < d_ < n:
        raise ValueError('secret key value is out of range.')
    P = point_mul(G, d_)
    assert P is not None
    a = get_session_key_agg_coeff(session_ctx, P)
    gp = 1 if has_even_y(P) else n - 1
    g = 1 if has_even_y(Q) else n - 1
    d = g * gacc * gp * d_ % n
    sp = (k_1 + b * k_2 + e * a * d) % n
    psig = bytes_from_int(sp)
    Rp_1 = point_mul(G, k_1_)
    Rp_2 = point_mul(G, k_2_)
    assert Rp_1 is not None
    assert Rp_2 is not None
    pubnonce = cbytes(Rp_1) + cbytes(Rp_2)
    # Optional correctness check. The result of signing should pass signature verification.
    assert partial_sig_verify_internal(psig, pubnonce, bytes_from_point(P), session_ctx)
    return psig

def partial_sig_verify(psig: bytes, pubnonces: List[bytes], pubkeys: List[bytes], tweaks: List[bytes], is_xonly: List[bool], msg: bytes, i: int) -> bool:
    if len(pubnonces) != len(pubkeys):
        raise ValueError('The `pubnonces` and `pubkeys` arrays must have the same length.')
    if len(tweaks) != len(is_xonly):
        raise ValueError('The `tweaks` and `is_xonly` arrays must have the same length.')
    aggnonce = nonce_agg(pubnonces)
    session_ctx = SessionContext(aggnonce, pubkeys, tweaks, is_xonly, msg)
    return partial_sig_verify_internal(psig, pubnonces[i], pubkeys[i], session_ctx)

def partial_sig_verify_internal(psig: bytes, pubnonce: bytes, pk: bytes, session_ctx: SessionContext) -> bool:
    (Q, gacc, _, b, R, e) = get_session_values(session_ctx)
    sp = int_from_bytes(psig)
    if sp >= n:
        return False
    Rp_1 = cpoint(pubnonce[0:33])
    Rp_2 = cpoint(pubnonce[33:66])
    Rp_ = point_add(Rp_1, point_mul(Rp_2, b))
    Rp = Rp_ if has_even_y(R) else point_negate(Rp_)
    g = 1 if has_even_y(Q) else n - 1
    g_ = g * gacc % n
    P = point_mul(lift_x(pk), g_)
    if P is None:
        return False
    a = get_session_key_agg_coeff(session_ctx, P)
    return point_mul(G, sp) == point_add(Rp, point_mul(P, e * a % n))

def partial_sig_agg(psigs: List[bytes], session_ctx: SessionContext) -> bytes:
    (Q, _, tacc, _, R, e) = get_session_values(session_ctx)
    s = 0
    u = len(psigs)
    for i in range(u):
        s_i = int_from_bytes(psigs[i])
        if s_i >= n:
            raise InvalidContributionError(i, "psig")
        s = (s + s_i) % n
    g = 1 if has_even_y(Q) else n - 1
    s = (s + e * g * tacc) % n
    return bytes_from_point(R) + bytes_from_int(s)
#
# The following code is only used for testing.
#

import json
import os
import sys

def fromhex_all(l):
    return [bytes.fromhex(l_i) for l_i in l]

# Check that calling `try_fn` raises a `exception`. If `exception` is raised,
# examine it with `except_fn`.
def assertRaises(exception, try_fn, except_fn):
    raised = False
    try:
        try_fn()
    except exception as e:
        raised = True
        assert(except_fn(e))
    except BaseException:
        raise AssertionError("Wrong exception raised in a test.")
    if not raised:
        raise AssertionError("Exception was _not_ raised in a test where it was required.")

def get_error_details(test_case):
    error = test_case["error"]
    if error["type"] == "invalid_contribution":
        exception = InvalidContributionError
        if "contrib" in error:
            except_fn = lambda e: e.signer == error["signer"] and e.contrib == error["contrib"]
        else:
            except_fn = lambda e: e.signer == error["signer"]
    elif error["type"] == "value":
        exception = ValueError
        except_fn = lambda e: str(e) == error["message"]
    else:
        raise RuntimeError(f"Invalid error type: {error['type']}")
    return exception, except_fn

def test_key_agg_vectors():
    with open(os.path.join(sys.path[0], 'key_agg_vectors.json')) as f:
        test_data = json.load(f)

    X = fromhex_all(test_data["pubkeys"])
    T = fromhex_all(test_data["tweaks"])
    valid_test_cases = test_data["valid_test_cases"]
    error_test_cases = test_data["error_test_cases"]

    for test_case in valid_test_cases:
        pubkeys = [X[i] for i in test_case["key_indices"]]
        expected = bytes.fromhex(test_case["expected"])

        assert get_pk(key_agg(pubkeys)) == expected

    for i, test_case in enumerate(error_test_cases):
        exception, except_fn = get_error_details(test_case)

        pubkeys = [X[i] for i in test_case["key_indices"]]
        tweaks = [T[i] for i in test_case["tweak_indices"]]
        is_xonly = test_case["is_xonly"]

        assertRaises(exception, lambda: key_agg_and_tweak(pubkeys, tweaks, is_xonly), except_fn)

def test_nonce_gen_vectors():
    with open(os.path.join(sys.path[0], 'nonce_gen_vectors.json')) as f:
        test_data = json.load(f)

    for test_case in test_data["test_cases"]:
        def get_value(key):
            if test_case[key] is not None:
                return bytes.fromhex(test_case[key])
            else:
                return None

        rand_ = get_value("rand_")
        sk = get_value("sk")
        aggpk = get_value("aggpk")
        msg = get_value("msg")
        extra_in = get_value("extra_in")
        expected = get_value("expected")

        assert nonce_gen_internal(rand_, sk, aggpk, msg, extra_in)[0] == expected

def test_nonce_agg_vectors():
    with open(os.path.join(sys.path[0], 'nonce_agg_vectors.json')) as f:
        test_data = json.load(f)

    pnonce = fromhex_all(test_data["pnonces"])
    valid_test_cases = test_data["valid_test_cases"]
    error_test_cases = test_data["error_test_cases"]

    for test_case in valid_test_cases:
        pubnonces = [pnonce[i] for i in test_case["pnonce_indices"]]
        expected = bytes.fromhex(test_case["expected"])
        assert nonce_agg(pubnonces) == expected

    for i, test_case in enumerate(error_test_cases):
        exception, except_fn = get_error_details(test_case)
        pubnonces = [pnonce[i] for i in test_case["pnonce_indices"]]
        assertRaises(exception, lambda: nonce_agg(pubnonces), except_fn)

def test_sign_verify_vectors():
    with open(os.path.join(sys.path[0], 'sign_verify_vectors.json')) as f:
        test_data = json.load(f)

    sk = bytes.fromhex(test_data["sk"])
    X = fromhex_all(test_data["pubkeys"])
    # The public key corresponding to sk is at index 0
    assert X[0] == bytes_from_point(point_mul(G, int_from_bytes(sk)))

    secnonce = bytes.fromhex(test_data["secnonce"])
    pnonce = fromhex_all(test_data["pnonces"])
    # The public nonce corresponding to secnonce is at index 0
    k1 = int_from_bytes(secnonce[0:32])
    k2 = int_from_bytes(secnonce[32:64])
    assert pnonce[0] == cbytes(point_mul(G, k1)) + cbytes(point_mul(G, k2))

    aggnonces = fromhex_all(test_data["aggnonces"])
    # The aggregate of the first three elements of pnonce is at index 0
    assert(aggnonces[0] == nonce_agg([pnonce[0], pnonce[1], pnonce[2]]))

    msgs = fromhex_all(test_data["msgs"])

    valid_test_cases = test_data["valid_test_cases"]
    sign_error_test_cases = test_data["sign_error_test_cases"]
    verify_fail_test_cases = test_data["verify_fail_test_cases"]
    verify_error_test_cases = test_data["verify_error_test_cases"]

    for test_case in valid_test_cases:
        pubkeys = [X[i] for i in test_case["key_indices"]]
        pubnonces = [pnonce[i] for i in test_case["nonce_indices"]]
        aggnonce = aggnonces[test_case["aggnonce_index"]]
        assert nonce_agg(pubnonces) == aggnonce
        msg = msgs[test_case["msg_index"]]
        signer_index = test_case["signer_index"]
        expected = bytes.fromhex(test_case["expected"])

        session_ctx = SessionContext(aggnonce, pubkeys, [], [], msg)
        assert sign(secnonce, sk, session_ctx) == expected

        # WARNING: An actual implementation should clear the secnonce after use,
        # e.g. by setting secnonce = bytes(64) after usage. Reusing the secnonce, as
        # we do here for testing purposes, can leak the secret key.

        assert partial_sig_verify(expected, pubnonces, pubkeys, [], [], msg, signer_index)

    for i, test_case in enumerate(sign_error_test_cases):
        exception, except_fn = get_error_details(test_case)

        pubkeys = [X[i] for i in test_case["key_indices"]]
        aggnonce = aggnonces[test_case["aggnonce_index"]]
        msg = msgs[test_case["msg_index"]]

        session_ctx = SessionContext(aggnonce, pubkeys, [], [], msg)
        assertRaises(exception, lambda: sign(secnonce, sk, session_ctx), except_fn)

    for test_case in verify_fail_test_cases:
        sig = bytes.fromhex(test_case["sig"])
        pubkeys = [X[i] for i in test_case["key_indices"]]
        pubnonces = [pnonce[i] for i in test_case["nonce_indices"]]
        msg = msgs[test_case["msg_index"]]
        signer_index = test_case["signer_index"]

        assert not partial_sig_verify(sig, pubnonces, pubkeys, [], [], msg, signer_index)

    for i, test_case in enumerate(verify_error_test_cases):
        exception, except_fn = get_error_details(test_case)

        sig = bytes.fromhex(test_case["sig"])
        pubkeys = [X[i] for i in test_case["key_indices"]]
        pubnonces = [pnonce[i] for i in test_case["nonce_indices"]]
        msg = msgs[test_case["msg_index"]]
        signer_index = test_case["signer_index"]

        assertRaises(exception, lambda: partial_sig_verify(sig, pubnonces, pubkeys, [], [], msg, signer_index), except_fn)

def test_tweak_vectors():
    with open(os.path.join(sys.path[0], 'tweak_vectors.json')) as f:
        test_data = json.load(f)

    sk = bytes.fromhex(test_data["sk"])
    X = fromhex_all(test_data["pubkeys"])
    # The public key corresponding to sk is at index 0
    assert X[0] == bytes_from_point(point_mul(G, int_from_bytes(sk)))

    secnonce = bytes.fromhex(test_data["secnonce"])
    pnonce = fromhex_all(test_data["pnonces"])
    # The public nonce corresponding to secnonce is at index 0
    k1 = int_from_bytes(secnonce[0:32])
    k2 = int_from_bytes(secnonce[32:64])
    assert pnonce[0] == cbytes(point_mul(G, k1)) + cbytes(point_mul(G, k2))

    aggnonce = bytes.fromhex(test_data["aggnonce"])
    # The aggnonce is the aggregate of the first three elements of pnonce
    assert(aggnonce == nonce_agg([pnonce[0], pnonce[1], pnonce[2]]))

    tweak = fromhex_all(test_data["tweaks"])
    msg = bytes.fromhex(test_data["msg"])

    valid_test_cases = test_data["valid_test_cases"]
    error_test_cases = test_data["error_test_cases"]

    for test_case in valid_test_cases:
        pubkeys = [X[i] for i in test_case["key_indices"]]
        pubnonces = [pnonce[i] for i in test_case["nonce_indices"]]
        tweaks = [tweak[i] for i in test_case["tweak_indices"]]
        is_xonly = test_case["is_xonly"]
        signer_index = test_case["signer_index"]
        expected = bytes.fromhex(test_case["expected"])

        session_ctx = SessionContext(aggnonce, pubkeys, tweaks, is_xonly, msg)
        assert sign(secnonce, sk, session_ctx) == expected

        # WARNING: An actual implementation should clear the secnonce after use,
        # e.g. by setting secnonce = bytes(64) after usage. Reusing the secnonce, as
        # we do here for testing purposes, can leak the secret key.

        assert partial_sig_verify(expected, pubnonces, pubkeys, tweaks, is_xonly, msg, signer_index)

    for i, test_case in enumerate(error_test_cases):
        exception, except_fn = get_error_details(test_case)

        pubkeys = [X[i] for i in test_case["key_indices"]]
        pubnonces = [pnonce[i] for i in test_case["nonce_indices"]]
        tweaks = [tweak[i] for i in test_case["tweak_indices"]]
        is_xonly = test_case["is_xonly"]
        signer_index = test_case["signer_index"]

        session_ctx = SessionContext(aggnonce, pubkeys, tweaks, is_xonly, msg)
        assertRaises(exception, lambda: sign(secnonce, sk, session_ctx), except_fn)

def test_sig_agg_vectors():
    with open(os.path.join(sys.path[0], 'sig_agg_vectors.json')) as f:
        test_data = json.load(f)

    X = fromhex_all(test_data["pubkeys"])

    # These nonces are only required if the tested API takes the individual
    # nonces and not the aggregate nonce.
    pnonce = fromhex_all(test_data["pnonces"])

    tweak = fromhex_all(test_data["tweaks"])
    psig = fromhex_all(test_data["psigs"])

    msg = bytes.fromhex(test_data["msg"])

    valid_test_cases = test_data["valid_test_cases"]
    error_test_cases = test_data["error_test_cases"]

    for test_case in valid_test_cases:
        pubnonces = [pnonce[i] for i in test_case["nonce_indices"]]
        aggnonce = bytes.fromhex(test_case["aggnonce"])
        assert aggnonce == nonce_agg(pubnonces)

        pubkeys = [X[i] for i in test_case["key_indices"]]
        tweaks = [tweak[i] for i in test_case["tweak_indices"]]
        is_xonly = test_case["is_xonly"]
        psigs = [psig[i] for i in test_case["psig_indices"]]
        expected = bytes.fromhex(test_case["expected"])

        session_ctx = SessionContext(aggnonce, pubkeys, tweaks, is_xonly, msg)
        sig = partial_sig_agg(psigs, session_ctx)
        assert sig == expected
        aggpk = get_pk(key_agg_and_tweak(pubkeys, tweaks, is_xonly))
        assert schnorr_verify(msg, aggpk, sig)

    for i, test_case in enumerate(error_test_cases):
        exception, except_fn = get_error_details(test_case)

        pubnonces = [pnonce[i] for i in test_case["nonce_indices"]]
        aggnonce = nonce_agg(pubnonces)

        pubkeys = [X[i] for i in test_case["key_indices"]]
        tweaks = [tweak[i] for i in test_case["tweak_indices"]]
        is_xonly = test_case["is_xonly"]
        psigs = [psig[i] for i in test_case["psig_indices"]]

        session_ctx = SessionContext(aggnonce, pubkeys, tweaks, is_xonly, msg)
        assertRaises(exception, lambda: partial_sig_agg(psigs, session_ctx), except_fn)

def test_sign_and_verify_random(iters):
    for i in range(iters):
        sk_1 = secrets.token_bytes(32)
        sk_2 = secrets.token_bytes(32)
        pk_1 = bytes_from_point(point_mul(G, int_from_bytes(sk_1)))
        pk_2 = bytes_from_point(point_mul(G, int_from_bytes(sk_2)))
        pubkeys = [pk_1, pk_2]

        # In this example, the message and aggregate pubkey are known
        # before nonce generation, so they can be passed into the nonce
        # generation function as a defense-in-depth measure to protect
        # against nonce reuse.
        #
        # If these values are not known when nonce_gen is called, empty
        # byte arrays can be passed in for the corresponding arguments
        # instead.
        msg = secrets.token_bytes(32)
        v = secrets.randbelow(4)
        tweaks = [secrets.token_bytes(32) for _ in range(v)]
        is_xonly = [secrets.choice([False, True]) for _ in range(v)]
        aggpk = get_pk(key_agg_and_tweak(pubkeys, tweaks, is_xonly))

        # Use a non-repeating counter for extra_in
        secnonce_1, pubnonce_1 = nonce_gen(sk_1, aggpk, msg, i.to_bytes(4, 'big'))

        # Use a clock for extra_in
        t = time.clock_gettime_ns(time.CLOCK_MONOTONIC)
        secnonce_2, pubnonce_2 = nonce_gen(sk_2, aggpk, msg, t.to_bytes(8, 'big'))

        pubnonces = [pubnonce_1, pubnonce_2]
        aggnonce = nonce_agg(pubnonces)

        session_ctx = SessionContext(aggnonce, pubkeys, tweaks, is_xonly, msg)
        psig_1 = sign(secnonce_1, sk_1, session_ctx)
        # Clear the secnonce after use
        secnonce_1 = bytes(64)
        assert partial_sig_verify(psig_1, pubnonces, pubkeys, tweaks, is_xonly, msg, 0)

        # Wrong signer index
        assert not partial_sig_verify(psig_1, pubnonces, pubkeys, tweaks, is_xonly, msg, 1)

        # Wrong message
        assert not partial_sig_verify(psig_1, pubnonces, pubkeys, tweaks, is_xonly, secrets.token_bytes(32), 0)

        psig_2 = sign(secnonce_2, sk_2, session_ctx)
        # Clear the secnonce after use
        secnonce_2 = bytes(64)
        assert partial_sig_verify(psig_2, pubnonces, pubkeys, tweaks, is_xonly, msg, 1)

        sig = partial_sig_agg([psig_1, psig_2], session_ctx)
        assert schnorr_verify(msg, aggpk, sig)

if __name__ == '__main__':
    test_key_agg_vectors()
    test_nonce_gen_vectors()
    test_nonce_agg_vectors()
    test_sign_verify_vectors()
    test_tweak_vectors()
    test_sig_agg_vectors()
    test_sign_and_verify_random(4)
