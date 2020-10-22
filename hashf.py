import hashlib
import random
import time


# mini-version with 32Bit digest for testing
def minihash(text):
    sha = hashlib.sha1(text.encode("UTF-8")).hexdigest()
    return sha[:8]


# mini-version with empty-hash clause to save caching tree-levels
def miniminhash(text):
    if text == '':
        return ''
    sha = hashlib.sha1(text.encode("UTF-8")).hexdigest()
    return sha[:8]


# SHA256 with empty-hash clause to save caching tree-levels
def minhash(text):
    if text == '':
        return ''
    return hashlib.sha256(text.encode("UTF-8")).hexdigest()


def hashadd(hash_function, hash1, hash2):
    return hash_function(hash1 + hash2)


# hash conversion to int
def get_int(inhash):
    if inhash is not '':
        return int(inhash, 16)
    else:
        return 0


# int conversion to hash
def from_int(hashint, length):
    if hashint == 0:
        return ''
    else:
        result = hex(hashint)[2:]
        result = int(length / 4 - len(result)) * '0' + result
        return result


def get_empty_hash_list(hf, bit_length):
    result = []
    tmp = ''
    for _ in range(bit_length):
        tmp = hashadd(hf, tmp, tmp)
        result.append(tmp)
    return result
