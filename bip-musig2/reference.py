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

def nonce_hash(rand: bytes, aggpk: bytes, i: int, msg: bytes, extra_in: bytes) -> int:
    buf = b''
    buf += rand
    buf += len(aggpk).to_bytes(1, 'big')
    buf += aggpk
    buf += len(msg).to_bytes(8, 'big')
    buf += msg
    buf += len(extra_in).to_bytes(4, 'big')
    buf += extra_in
    buf += i.to_bytes(1, 'big')
    return int_from_bytes(tagged_hash('MuSig/nonce', buf))

def nonce_gen_internal(rand_: bytes, sk: bytes, aggpk: bytes, msg: bytes, extra_in: bytes) -> Tuple[bytes, bytes]:
    if len(sk) > 0:
        rand = bytes_xor(sk, tagged_hash('MuSig/aux', rand_))
    else:
        rand = rand_
    k_1 = nonce_hash(rand, aggpk, 0, msg, extra_in)
    k_2 = nonce_hash(rand, aggpk, 1, msg, extra_in)
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

def nonce_gen(sk: bytes, aggpk: bytes, msg: bytes, extra_in: bytes) -> Tuple[bytes, bytes]:
    if len(sk) not in (0, 32):
        raise ValueError('The optional byte array sk must have length 0 or 32.')
    if len(aggpk) not in (0, 32):
        raise ValueError('The optional byte array aggpk must have length 0 or 32.')
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
    s = (k_1 + b * k_2 + e * a * d) % n
    psig = bytes_from_int(s)
    R_1_ = point_mul(G, k_1_)
    R_2_ = point_mul(G, k_2_)
    assert R_1_ is not None
    assert R_2_ is not None
    pubnonce = cbytes(R_1_) + cbytes(R_2_)
    # Optional correctness check. The result of signing should pass signature verification.
    assert partial_sig_verify_internal(psig, pubnonce, bytes_from_point(P), session_ctx)
    return psig

def partial_sig_verify(psig: bytes, pubnonces: List[bytes], pubkeys: List[bytes], tweaks: List[bytes], is_xonly: List[bool], msg: bytes, i: int) -> bool:
    aggnonce = nonce_agg(pubnonces)
    session_ctx = SessionContext(aggnonce, pubkeys, tweaks, is_xonly, msg)
    return partial_sig_verify_internal(psig, pubnonces[i], pubkeys[i], session_ctx)

def partial_sig_verify_internal(psig: bytes, pubnonce: bytes, pk_: bytes, session_ctx: SessionContext) -> bool:
    (Q, gacc, _, b, R, e) = get_session_values(session_ctx)
    s = int_from_bytes(psig)
    if s >= n:
        return False
    R_1_ = cpoint(pubnonce[0:33])
    R_2_ = cpoint(pubnonce[33:66])
    R__ = point_add(R_1_, point_mul(R_2_, b))
    R_ = R__ if has_even_y(R) else point_negate(R__)
    g = 1 if has_even_y(Q) else n - 1
    g_ = g * gacc % n
    P = point_mul(lift_x(pk_), g_)
    if P is None:
        return False
    a = get_session_key_agg_coeff(session_ctx, P)
    return point_mul(G, s) == point_add(R_, point_mul(P, e * a % n))

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
# Test vectors were copied from libsecp256k1-zkp's MuSig test file.
# See `musig_test_vectors_keyagg` and `musig_test_vectors_sign` in
# https://github.com/ElementsProject/secp256k1-zkp/blob/master/src/modules/musig/tests_impl.h
#
def fromhex_all(l):
    return [bytes.fromhex(l_i) for l_i in l]

# Check that calling `try_fn` raises a `exception`. If `exception` is raised,
# examine it with `except_fn`.
def assertRaises(exception, try_fn, except_fn):
    try:
        try_fn()
        raise RuntimeError("Exception was _not_ raised in a test where it was required.")
    except exception as e:
        assert(except_fn(e))

def test_key_agg_vectors():
    X = fromhex_all([
        'F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9',
        'DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659',
        '3590A94E768F8E1815C2F24B4D80A8E3149316C3518CE7B7AD338368D038CA66',
    ])

    expected = fromhex_all([
        'E5830140512195D74C8307E39637CBE5FB730EBEAB80EC514CF88A877CEEEE0B',
        'D70CD69A2647F7390973DF48CBFA2CCC407B8B2D60B08C5F1641185C7998A290',
        '81A8B093912C9E481408D09776CEFB48AEB8B65481B6BAAFB3C5810106717BEB',
        '2EB18851887E7BDC5E830E89B19DDBC28078F1FA88AAD0AD01CA06FE4F80210B',
    ])

    # Vector 1
    assert get_pk(key_agg([X[0], X[1], X[2]])) == expected[0]
    # Vector 2
    assert get_pk(key_agg([X[2], X[1], X[0]])) == expected[1]
    # Vector 3
    assert get_pk(key_agg([X[0], X[0], X[0]])) == expected[2]
    # Vector 4
    assert get_pk(key_agg([X[0], X[0], X[1], X[1]])) == expected[3]

    # Vector 5: Invalid public key
    invalid_pk = bytes.fromhex('0000000000000000000000000000000000000000000000000000000000000005')
    assertRaises(InvalidContributionError,
                 lambda: key_agg([X[0], invalid_pk]),
                 lambda e: e.signer == 1 and e.contrib == "pubkey")
    # Vector 6: Public key exceeds field size
    invalid_pk = bytes.fromhex('FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC30')
    assertRaises(InvalidContributionError,
                 lambda: key_agg([X[0], invalid_pk]),
                 lambda e: e.signer == 1 and e.contrib == "pubkey")
    # Vector 7: Tweak is out of range
    invalid_tweak = bytes.fromhex('FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141')
    assertRaises(ValueError,
                 lambda: key_agg_and_tweak([X[0], X[1]], [invalid_tweak], [True]),
                 lambda e: str(e) == 'The tweak must be less than n.')
    # Vector 8: Intermediate tweaking result is point at infinity
    G_ = bytes_from_point(G)
    coeff = bytes_from_int(n - key_agg_coeff([G_], G_))
    assertRaises(ValueError,
                 lambda: key_agg_and_tweak([G_], [coeff], [False]),
                 lambda e: str(e) == 'The result of tweaking cannot be infinity.')

def test_nonce_gen_vectors():
    def fill(i):
        return i.to_bytes(1, byteorder='big') * 32
    rand_ = fill(0)
    msg = fill(1)
    sk = fill(2)
    aggpk = fill(7)
    # This aggpk is a valid public key
    assert(lift_x(aggpk) != None)
    extra_in = fill(8)

    expected = fromhex_all([
        'FDC302CBD26318FF85DE9BB499BCFEB5C54B681A5A2BF1660A3D50A6A97BBCF8' +
        '040577B50C260D6722894B3B6848B68CC74591D7F3BB2F646F69E2609C494DE6',
        'CE2AA822EBBC200ED36829E0DBF5C08CC955DEE9C3CF651DA6D37648A6C5417D' +
        '822BA95D66B455D697BDE2996E4229340A3E60E654E7205994AD4482E3769810',
        '1E5F9CC2BA2716FFD10E72B21043C5C454A7AE956BFB062C8401158DD3F74059' +
        '1AC30C8C020B4BAB07768FAE5FF8EEE20C28EC098B790CD367E8C149BF295860'
    ])

    # Vector 1
    assert nonce_gen_internal(rand_, sk, aggpk, msg, extra_in)[0] == expected[0]
    # Vector 2
    assert nonce_gen_internal(rand_, sk, aggpk, b'', extra_in)[0] == expected[1]
    # Vector 3
    assert nonce_gen_internal(rand_, b'', b'', b'', b'')[0] == expected[2]

def test_nonce_agg_vectors():
    pnonce = fromhex_all([
        '020151C80F435648DF67A22B749CD798CE54E0321D034B92B709B567D60A42E666' +
        '03BA47FBC1834437B3212E89A84D8425E7BF12E0245D98262268EBDCB385D50641',
        '03FF406FFD8ADB9CD29877E4985014F66A59F6CD01C0E88CAA8E5F3166B1F676A6' +
        '0248C264CDD57D3C24D79990B0F865674EB62A0F9018277A95011B41BFC193B833',
    ])
    expected = fromhex_all([
        '035FE1873B4F2967F52FEA4A06AD5A8ECCBE9D0FD73068012C894E2E87CCB5804B' +
        '024725377345BDE0E9C33AF3C43C0A29A9249F2F2956FA8CFEB55C8573D0262DC8'
    ])

    # Vector 1
    assert nonce_agg([pnonce[0], pnonce[1]]) == expected[0]
    # Vector 2: Public nonce from signer 1 is invalid due wrong tag, 0x04, in
    # the first half
    invalid_pnonce = bytes.fromhex(
        '04FF406FFD8ADB9CD29877E4985014F66A59F6CD01C0E88CAA8E5F3166B1F676A6' +
        '0248C264CDD57D3C24D79990B0F865674EB62A0F9018277A95011B41BFC193B833')
    assertRaises(InvalidContributionError,
                 lambda: nonce_agg([pnonce[0], invalid_pnonce]),
                 lambda e: e.signer == 1 and e.contrib == "pubnonce")
    # Vector 3: Public nonce from signer 0 is invalid because the second half
    # does not correspond to an X coordinate
    invalid_pnonce = bytes.fromhex(
        '03FF406FFD8ADB9CD29877E4985014F66A59F6CD01C0E88CAA8E5F3166B1F676A6' +
        '0248C264CDD57D3C24D79990B0F865674EB62A0F9018277A95011B41BFC193B831')
    assertRaises(InvalidContributionError,
                 lambda: nonce_agg([invalid_pnonce, pnonce[1]]),
                 lambda e: e.signer == 0 and e.contrib == "pubnonce")
    # Vector 4: Public nonce from signer 0 is invalid because second half
    # exceeds field size
    invalid_pnonce = bytes.fromhex(
        '03FF406FFD8ADB9CD29877E4985014F66A59F6CD01C0E88CAA8E5F3166B1F676A6' +
        '02FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC30')
    assertRaises(InvalidContributionError,
                 lambda: nonce_agg([invalid_pnonce, pnonce[1]]),
                 lambda e: e.signer == 0 and e.contrib == "pubnonce")
    # Vector 5: Sum of second points encoded in the nonces is point at infinity
    # which is serialized as 33 zero bytes
    neg_G = point_mul(G, n - 1)
    assert nonce_agg([pnonce[0][0:33] + cbytes(G), pnonce[1][0:33] + cbytes(neg_G)]) == expected[0][0:33] + b'\x00'*33

def test_sign_verify_vectors():
    X = fromhex_all([
        'F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9',
        'DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659',
    ])

    secnonce = bytes.fromhex(
        '508B81A611F100A6B2B6B29656590898AF488BCF2E1F55CF22E5CFB84421FE61' +
        'FA27FD49B1D50085B481285E1CA205D55C82CC1B31FF5CD54A489829355901F7')

    # The public nonce corresponding to secnonce is at index 0
    pnonce = fromhex_all([
        '0337C87821AFD50A8644D820A8F3E02E499C931865C2360FB43D0A0D20DAFE07EA' +
        '0287BF891D2A6DEAEBADC909352AA9405D1428C15F4B75F04DAE642A95C2548480',
        '0279BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798' +
        '0279BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798',
        '032DE2662628C90B03F5E720284EB52FF7D71F4284F627B68A853D78C78E1FFE93' +
        '03E4C5524E83FFE1493B9077CF1CA6BEB2090C93D930321071AD40B2F44E599046',
        '0237C87821AFD50A8644D820A8F3E02E499C931865C2360FB43D0A0D20DAFE07EA' +
        '0387BF891D2A6DEAEBADC909352AA9405D1428C15F4B75F04DAE642A95C2548480'
    ])

    aggnonce = bytes.fromhex(
        '028465FCF0BBDBCF443AABCCE533D42B4B5A10966AC09A49655E8C42DAAB8FCD61' +
        '037496A3CC86926D452CAFCFD55D25972CA1675D549310DE296BFF42F72EEEA8C9')
    assert(aggnonce == nonce_agg([pnonce[0], pnonce[1], pnonce[2]]))

    sk  = bytes.fromhex('7FB9E0E687ADA1EEBF7ECFE2F21E73EBDB51A7D450948DFE8D76D7F2D1007671')
    msg = bytes.fromhex('F95466D086770E689964664219266FE5ED215C92AE20BAB5C9D79ADDDDF3C0CF')

    expected = fromhex_all([
        '68537CC5234E505BD14061F8DA9E90C220A181855FD8BDB7F127BB12403B4D3B',
        '2DF67BFFF18E3DE797E13C6475C963048138DAEC5CB20A357CECA7C8424295EA',
        '0D5B651E6DE34A29A12DE7A8B4183B4AE6A7F7FBE15CDCAFA4A3D1BCAABC7517',
        '8D5E0407FB4756EEBCD86264C32D792EE36EEB69E952BBB30B8E41BEBC4D22FA',
        '0167931A502D28A128DDAC1DC2A53296F00DA663CCDDC9673D79020091A3A58A',
    ])

    pk = bytes_from_point(point_mul(G, int_from_bytes(sk)))

    # Vector 1
    session_ctx = SessionContext(aggnonce, [pk, X[0], X[1]], [], [], msg)
    assert sign(secnonce, sk, session_ctx) == expected[0]
    # WARNING: An actual implementation should clear the secnonce after use,
    # e.g. by setting secnonce = bytes(64) after usage. Reusing the secnonce, as
    # we do here for testing purposes, can leak the secret key.

    # Vector 2
    session_ctx = SessionContext(aggnonce, [X[0], pk, X[1]], [], [], msg)
    assert sign(secnonce, sk, session_ctx) == expected[1]

    # Vector 3
    session_ctx = SessionContext(aggnonce, [X[0], X[1], pk], [], [], msg)
    assert sign(secnonce, sk, session_ctx) == expected[2]

    # Vector 4: Both halves of aggregate nonce correspond to point at infinity
    inf_aggnonce = nonce_agg([pnonce[0], pnonce[3]])
    assert(inf_aggnonce == b'\x00'*66)
    session_ctx = SessionContext(inf_aggnonce, [pk, X[0]], [], [], msg)
    assert sign(secnonce, sk, session_ctx) == expected[3]

    # Vector 5: Empty message
    empty_msg = b''
    session_ctx = SessionContext(aggnonce, [pk, X[0], X[1]], [], [], empty_msg)
    assert sign(secnonce, sk, session_ctx) == expected[4]

    # Vector 6: Signer 2 provided an invalid public key
    invalid_pk = bytes.fromhex('0000000000000000000000000000000000000000000000000000000000000007')
    session_ctx = SessionContext(aggnonce, [X[0], pk, invalid_pk], [], [], msg)
    assertRaises(InvalidContributionError,
                 lambda: sign(secnonce, sk, session_ctx),
                 lambda e: e.signer == 2 and e.contrib == "pubkey")

    # Vector 7: Aggregate nonce is invalid due wrong tag, 0x04, in the first
    # half
    invalid_aggnonce = bytes.fromhex(
        '048465FCF0BBDBCF443AABCCE533D42B4B5A10966AC09A49655E8C42DAAB8FCD61' +
        '037496A3CC86926D452CAFCFD55D25972CA1675D549310DE296BFF42F72EEEA8C9')
    session_ctx = SessionContext(invalid_aggnonce, [X[0], X[1], pk], [], [], msg)
    assertRaises(InvalidContributionError,
                 lambda: sign(secnonce, sk, session_ctx),
                 lambda e: e.signer == None and e.contrib == "aggnonce")
    # Vector 8: Aggregate nonce is invalid because the second half does not
    # correspond to an X coordinate
    invalid_aggnonce = bytes.fromhex(
        '028465FCF0BBDBCF443AABCCE533D42B4B5A10966AC09A49655E8C42DAAB8FCD61' +
        '020000000000000000000000000000000000000000000000000000000000000009')
    session_ctx = SessionContext(invalid_aggnonce, [X[0], X[1], pk], [], [], msg)
    assertRaises(InvalidContributionError,
                 lambda: sign(secnonce, sk, session_ctx),
                 lambda e: e.signer == None and e.contrib == "aggnonce")
    # Vector 9: Aggregate nonce is invalid because second half exceeds field
    # size
    invalid_aggnonce = bytes.fromhex(
        '028465FCF0BBDBCF443AABCCE533D42B4B5A10966AC09A49655E8C42DAAB8FCD61' +
        '02FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC30')
    session_ctx = SessionContext(invalid_aggnonce, [X[0], X[1], pk], [], [], msg)
    assertRaises(InvalidContributionError,
                 lambda: sign(secnonce, sk, session_ctx),
                 lambda e: e.signer == None and e.contrib == "aggnonce")

    # Verification test vectors
    # Vector 10
    assert partial_sig_verify(expected[0], [pnonce[0], pnonce[1], pnonce[2]], [pk, X[0], X[1]], [], [], msg, 0)
    # Vector 11
    assert partial_sig_verify(expected[1], [pnonce[1], pnonce[0], pnonce[2]], [X[0], pk, X[1]], [], [], msg, 1)
    # Vector 12
    assert partial_sig_verify(expected[2], [pnonce[1], pnonce[2], pnonce[0]], [X[0], X[1], pk], [], [], msg, 2)

    # Vector 13: Both halves of aggregate nonce correspond to point at infinity
    assert(inf_aggnonce == nonce_agg([pnonce[0], pnonce[3]]))
    assert partial_sig_verify(expected[3], [pnonce[0], pnonce[3]], [pk, X[0]], [], [], msg, 0)

    # Vector 14: Empty message
    assert partial_sig_verify(expected[4], [pnonce[0], pnonce[1], pnonce[2]], [pk, X[0], X[1]], [], [], empty_msg, 0)

    # Vector 15: Wrong signature (which is equal to the negation of valid signature expected[0])
    wrong_sig = bytes.fromhex('97AC833ADCB1AFA42EBF9E0725616F3C9A0D5B614F6FE283CEAAA37A8FFAF406')
    assert not partial_sig_verify(wrong_sig, pnonce, [pk, X[0], X[1]], [], [], msg, 0)
    # Vector 16: Wrong signer
    assert not partial_sig_verify(expected[0], pnonce, [pk, X[0], X[1]], [], [], msg, 1)
    # Vector 17: Signature exceeds group size
    wrong_sig = bytes.fromhex('FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141')
    assert not partial_sig_verify(wrong_sig, pnonce, [pk, X[0], X[1]], [], [], msg, 0)
    # Vector 18: Invalid pubnonce
    invalid_pubnonce = bytes.fromhex('020000000000000000000000000000000000000000000000000000000000000009')
    assertRaises(InvalidContributionError,
                 lambda: partial_sig_verify(expected[0], [invalid_pubnonce, pnonce[1], pnonce[2]], [pk, X[0], X[1]], [], [], msg, 0),
                 lambda e: e.signer == 0 and e.contrib == "pubnonce")
    # Vector 19: Invalid public key
    assertRaises(InvalidContributionError,
                 lambda: partial_sig_verify(expected[0], pnonce, [invalid_pk, X[0], X[1]], [], [], msg, 0),
                 lambda e: e.signer == 0 and e.contrib == "pubkey")

def test_tweak_vectors():
    X = fromhex_all([
        'F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9',
        'DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659',
    ])

    secnonce = bytes.fromhex(
        '508B81A611F100A6B2B6B29656590898AF488BCF2E1F55CF22E5CFB84421FE61' +
        'FA27FD49B1D50085B481285E1CA205D55C82CC1B31FF5CD54A489829355901F7')

    # The public nonce corresponding to secnonce is at index 0
    pnonce = fromhex_all([
        '0337C87821AFD50A8644D820A8F3E02E499C931865C2360FB43D0A0D20DAFE07EA' +
        '0287BF891D2A6DEAEBADC909352AA9405D1428C15F4B75F04DAE642A95C2548480',
        '0279BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798' +
        '0279BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798',
        '032DE2662628C90B03F5E720284EB52FF7D71F4284F627B68A853D78C78E1FFE93' +
        '03E4C5524E83FFE1493B9077CF1CA6BEB2090C93D930321071AD40B2F44E599046'
    ])

    aggnonce = bytes.fromhex(
        '028465FCF0BBDBCF443AABCCE533D42B4B5A10966AC09A49655E8C42DAAB8FCD61' +
        '037496A3CC86926D452CAFCFD55D25972CA1675D549310DE296BFF42F72EEEA8C9')

    sk  = bytes.fromhex('7FB9E0E687ADA1EEBF7ECFE2F21E73EBDB51A7D450948DFE8D76D7F2D1007671')
    msg = bytes.fromhex('F95466D086770E689964664219266FE5ED215C92AE20BAB5C9D79ADDDDF3C0CF')

    tweaks = fromhex_all([
        'E8F791FF9225A2AF0102AFFF4A9A723D9612A682A25EBE79802B263CDFCD83BB',
        'AE2EA797CC0FE72AC5B97B97F3C6957D7E4199A167A58EB08BCAFFDA70AC0455',
        'F52ECBC565B3D8BEA2DFD5B75A4F457E54369809322E4120831626F290FA87E0',
        '1969AD73CC177FA0B4FCED6DF1F7BF9907E665FDE9BA196A74FED0A3CF5AEF9D',
    ])

    expected = fromhex_all([
        '5E24C7496B565DEBC3B9639E6F1304A21597F9603D3AB05B4913641775E1375B',
        '78408DDCAB4813D1394C97D493EF1084195C1D4B52E63ECD7BC5991644E44DDD',
        'C3A829A81480E36EC3AB052964509A94EBF34210403D16B226A6F16EC85B7357',
        '8C4473C6A382BD3C4AD7BE59818DA5ED7CF8CEC4BC21996CFDA08BB4316B8BC7',
    ])

    pk = bytes_from_point(point_mul(G, int_from_bytes(sk)))

    # Vector 1: A single x-only tweak
    session_ctx = SessionContext(aggnonce, [X[0], X[1], pk], tweaks[:1], [True], msg)
    assert sign(secnonce, sk, session_ctx) == expected[0]
    # WARNING: An actual implementation should clear the secnonce after use,
    # e.g. by setting secnonce = bytes(64) after usage. Reusing the secnonce, as
    # we do here for testing purposes, can leak the secret key.
    assert partial_sig_verify(expected[0], [pnonce[1], pnonce[2], pnonce[0]], [X[0], X[1], pk], tweaks[:1], [True], msg, 2)

    # Vector 2: A single plain tweak
    session_ctx = SessionContext(aggnonce, [X[0], X[1], pk], tweaks[:1], [False], msg)
    assert sign(secnonce, sk, session_ctx) == expected[1]
    assert partial_sig_verify(expected[1], [pnonce[1], pnonce[2], pnonce[0]], [X[0], X[1], pk], tweaks[:1], [False], msg, 2)

    # Vector 3: A plain tweak followed by an x-only tweak
    session_ctx = SessionContext(aggnonce, [X[0], X[1], pk], tweaks[:2], [False, True], msg)
    assert sign(secnonce, sk, session_ctx) == expected[2]
    assert partial_sig_verify(expected[2], [pnonce[1], pnonce[2], pnonce[0]], [X[0], X[1], pk], tweaks[:2], [False, True], msg, 2)

    # Vector 4: Four tweaks: x-only, plain, x-only, plain
    session_ctx = SessionContext(aggnonce, [X[0], X[1], pk], tweaks[:4], [True, False, True, False], msg)
    assert sign(secnonce, sk, session_ctx) == expected[3]
    assert partial_sig_verify(expected[3], [pnonce[1], pnonce[2], pnonce[0]], [X[0], X[1], pk], tweaks[:4], [True, False, True, False], msg, 2)

    # Vector 5: Tweak is invalid because it exceeds group size
    invalid_tweak = bytes.fromhex('FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141')
    session_ctx = SessionContext(aggnonce, [X[0], X[1], pk], [invalid_tweak], [False], msg)
    assertRaises(ValueError,
                 lambda: sign(secnonce, sk, session_ctx),
                 lambda e: str(e) == 'The tweak must be less than n.')

def test_sig_agg_vectors():
    X = fromhex_all([
        '487D1B83B41B4CBBD07A111F1BBC7BDC8864CFEF5DBF96E46E51C68399B0BEF6',
        '4795C22501BF534BC478FF619407A7EC9E8D8883646D69BD43A0728944EA802F',
        '0F5BE837F3AB7E7FEFF1FAA44D673C2017206AE836D2C7893CDE4ACB7D55EDEB',
        '0FD453223E444FCA91FB5310990AE8A0C5DAA14D2A4C8944E1C0BC80C30DF682',
    ])

    # These nonces are only required if the tested API takes the individual
    # nonces and not the aggregate nonce.
    pnonce = fromhex_all([
        '0279BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798' +
        '0279BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798',
        '0327EE3C4078B3EE8888C86980C9349B033360C041108412B076D64A199D732247' +
        '0211A8415F0F7044FF94296CD3006D1E0BE7209F1549CF8F96D03C60ACA36DE69C',
        '032D459FC804D89AE5B0352A92B4EAADB5AB2F8F5479C072D9BE4C9887A23CA9E4' +
        '0238A68BF96C2904BBF409527F3D8E1EE2D6A1F6A0F3E68016B3BB575EF22BA2DD',
        '03202ED19F8FF57B795DA93D3DF40DC25EB4BBF5B0CCCD31E71CA2409A8C5575D6' +
        '02B73DFC004F0890B1F3BBF99A42746F02F1B6CB18D16AAD2F8703E779B4688ECA',
        '020663C56E861775F206E0268F5DD517143B6F55374A5C499DB44AD30E342AB81C' +
        '03F33D3F53D7528B3ADA8523C25C86FE4479FC3540CCED28D1D1BE351CF139AE64',
        '0379BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798' +
        '0379BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798'
    ])

    aggnonce = fromhex_all([
        '024FA51009A56F0D6DF737131CE1FBBD833797AF3B4FE6BF0D68F4D49F68B0947E' +
        '0248FB3BB9191F0CFF13806A3A2F1429C23012654FCE4E41F7EC9169EAA6056B21',
        '023B11E63E2460E5E0F1561BB700FEA95B991DD9CA2CBBE92A3960641FA7469F67' +
        '02CA4CD38375FE8BEB857C770807225BFC7D712F42BA896B83FC71138E56409B21',
        '03F98BEAA32B8A38FE3797C4E813DC9CE05ADBE32200035FB37EB0A030B735E9B6' +
        '030E6118EC98EA2BA7A358C2E38E7E13E63681EEB683E067061BF7D52DCF08E615',
        '026491FBCFD47148043A0F7310E62EF898C10F2D0376EE6B232EAAD36F3C2E29E3' +
        '03020CB17D168908E2904DE2EB571CD232CA805A6981D0F86CDBBD2F12BD91F6D0',
        '000000000000000000000000000000000000000000000000000000000000000000' +
        '000000000000000000000000000000000000000000000000000000000000000000',
    ])
    for i, nonce in enumerate(aggnonce):
        assert(nonce == nonce_agg([pnonce[0], pnonce[i+1]]))

    msg = bytes.fromhex('599C67EA410D005B9DA90817CF03ED3B1C868E4DA4EDF00A5880B0082C237869')

    tweaks = fromhex_all([
        "B511DA492182A91B0FFB9A98020D55F260AE86D7ECBD0399C7383D59A5F2AF7C",
        "A815FE049EE3C5AAB66310477FBC8BCCCAC2F3395F59F921C364ACD78A2F48DC",
        "75448A87274B056468B977BE06EB1E9F657577B7320B0A3376EA51FD420D18A8"
    ])
    psig = fromhex_all([
        'E5C1CBD6E7E89FE9EE30D5F3B6D06B9C218846E4A1DEF4EE851410D51ABBD850',
        '9BC470F7F1C9BC848BDF179B0023282FFEF40908E0EF88459784A4355FC86D0C',
        'D5D8A09929BA264B2F5DF15ACA1CF2DEFA47C048DF0C3232E965FFE2F2831B1D',
        'A915197503C1051EA77DC91F01C3A0E60BFD64473BD536CB613F9645BD61C843',
        '99A144D7076A128022134E036B8BDF33811F7EAED9A1E48549B46D8A63D64DC9',
        '716A72A0C1E531EBB4555C8E29FD35C796F4F231C3B039193D7E8D7AEFBDF5F7',
        '06B6DD04BC0F1EF740916730AD7DAC794255B161221719765BDE9686A26633DC',
        'BF6D85D4930062726EBC6EBB184AFD68DBB3FED159C501989690A62600D6FBAB',
    ])

    expected = fromhex_all([
        '4006D4D069F3B51E968762FF8074153E278E5BCD221AABE0743CA001B77E79F5' +
        '81863CCED9B25C6E7A0FED8EB6F393CD65CD7306D385DCF85CC6567DAA4E041B',
        '98BCD40DFD94B47A3DA37D7B78EB6CCE8ABEACA23C3ADE6F4678902410EB35C6' +
        '7EEDBA0E2D7B2B69D6DBBA79CBE093C64B9647A96B98C8C28AD3379BDFAEA21F',
        '3741FEDCCDD7508B58DCB9A780FF5D97452EC8C0448D8C97004EA7175C14F200' +
        '7A54D1DE356EBA6719278436EF111DFA8F1B832368371B9B7A25001709039679',
        'F4B3DA3CF0D0F7CF5C1840593BF1A1A415DA341619AE848F2210696DC8C75125' +
        '40962C84EF7F0CEC491065F2D577213CF10E8A63D153297361B3B172BE27B61F',
    ])

    # Vector 1
    session_ctx = SessionContext(aggnonce[0], [X[0], X[1]], [], [], msg)
    sig = partial_sig_agg([psig[0], psig[1]], session_ctx)
    assert sig == expected[0]
    aggpk = get_pk(key_agg([X[0], X[1]]))
    assert schnorr_verify(msg, aggpk, sig)

    # Vector 2
    session_ctx = SessionContext(aggnonce[1], [X[0], X[2]], [], [], msg)
    sig = partial_sig_agg([psig[2], psig[3]], session_ctx)
    assert sig == expected[1]
    aggpk = get_pk(key_agg([X[0], X[2]]))
    assert schnorr_verify(msg, aggpk, sig)

    # Vector 3
    session_ctx = SessionContext(aggnonce[2], [X[0], X[2]], [tweaks[0]], [False], msg)
    sig = partial_sig_agg([psig[4], psig[5]], session_ctx)
    assert sig == expected[2]
    aggpk = get_pk(key_agg_and_tweak([X[0], X[2]], [tweaks[0]], [False]))
    assert schnorr_verify(msg, aggpk, sig)

    # Vector 4
    session_ctx = SessionContext(aggnonce[3], [X[0], X[3]], tweaks, [True, False, True], msg)
    sig = partial_sig_agg([psig[6], psig[7]], session_ctx)
    assert sig == expected[3]
    aggpk = get_pk(key_agg_and_tweak([X[0], X[3]], tweaks, [True, False, True]))
    assert schnorr_verify(msg, aggpk, sig)

    # Vector 5: Partial signature is invalid because it exceeds group size
    invalid_psig = bytes.fromhex('FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141')
    assertRaises(InvalidContributionError,
                 lambda: partial_sig_agg([psig[7], invalid_psig], session_ctx),
                 lambda e: e.signer == 1)

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
