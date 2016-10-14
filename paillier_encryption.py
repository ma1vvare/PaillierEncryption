from termcolor import colored
import random
import sys
import math
import M2Crypto
import time


def ipow(a, b, n):
  """calculates a^b%n via binary exponentiation, yielding itermediate
     results as Rabin-Miller requires"""
  A = a = long(a % n)
  yield A
  t = 1L
  while t <= b:
    t <<= 1
  # t = 2**k, and t > b
  t >>= 2

  while t:
    A = (A * A) % n
    if t & b:
      A = (A * a) % n
    yield A
    t >>= 1


def rabin_miller_witness(test, possible):
  """Using Rabin-Miller witness test, will return True if possible is
     definitely not prime (composite), False if it may be prime."""
  return 1 not in ipow(test, possible - 1, possible)

smallprimes = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43,
               47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97)


def default_k(bits):
  return max(40, 2 * bits)


def is_probably_prime(possible, k=None):
  if possible == 1:
    return True
  if k is None:
    k = default_k(possible.bit_length())
  for i in smallprimes:
    if possible == i:
      return True
    if possible % i == 0:
      return False
  for i in xrange(k):
    test = random.randrange(2, possible - 1) | 1
    if rabin_miller_witness(test, possible):
      return False
  return True


def generate_prime(bits, k=None):
  """Will generate an integer of b bits that is probably prime
     (after k trials). Reasonably fast on current hardware for
     values of up to around 512 bits."""
  assert bits >= 8

  if k is None:
    k = default_k(bits)

  while True:
    possible = random.randrange(2 ** (bits - 1) + 1, 2 ** bits) | 1
    if is_probably_prime(possible, k):
      return possible


def invmod(a, p, maxiter=1000000):
  """The multiplicitive inverse of a in the integers modulo p:
       a * b == 1 mod p
     Returns b.
  """
  if a == 0:
    raise ValueError('0 has no inverse mod %d' % p)
  r = a
  d = 1
  for i in xrange(min(p, maxiter)):
    d = ((p // r + 1) * d) % p
    r = (d * a) % p
    if r == 1:
      break
  else:
    raise ValueError('%d has no inverse mod %d' % (a, p))
  return d


def modpow(base, exponent, modulus):
  """Modular exponent:
       c = b ^ e mod m
     Returns c.
  """
  result = 1
  while exponent > 0:
    if exponent & 1 == 1:
      result = (result * base) % modulus
    exponent = exponent >> 1

    base = (base * base) % modulus
  return result


class PrivateKey(object):

  def __init__(self, p, q, n):
    self.l = (p - 1) * (q - 1)
    self.m = invmod(self.l, n)
    print "self.l =", self.l, colored("length of lambda is", 'red'), colored(len(str(self.l)), 'red'), "bits,"
    print "self.m =", self.m, colored("length of miu is", 'red'), colored(len(str(self.m)), 'red'), "bits,"

  def __repr__(self):
    return '<PrivateKey: %s %s>' % (self.l, self.m)


class PublicKey(object):

  @classmethod
  def from_n(cls, n):
    return cls(n)

  def __init__(self, n):
    self.n = n
    self.n_sq = n * n
    self.g = n + 1
    print "self.n =", self.n, colored("length of n is", 'red'), colored(len(str(self.n)), 'red'), "bits,"
    print "self.n_sq =", self.n_sq, colored("length of n_sq is", 'red'), colored(len(str(self.n_sq)), 'red'), "bits,"
    print "self.g =", self.g, colored("length of g is", 'red'), colored(len(str(self.g)), 'red'), "bits,"

  def __repr__(self):
    return '<PublicKey: %s>' % self.n


def generate_keypair(bits):
  p = generate_prime(bits / 2)
  q = generate_prime(bits / 2)
  n = p * q
  return PrivateKey(p, q, n), PublicKey(n)


def computing_random(pub):
  while True:
    random_start = time.time()
    random = generate_prime(long(round(math.log(pub.n, 2))))
    random_stop = time.time()
    if random > 0 and random < pub.n:
      break
  pow_start = time.time()
  x = pow(random, pub.n, pub.n_sq)  # r**N mod N**2
  pow_stop = time.time()

  print 'random =', random
  print "Generate random cost :", colored((random_stop - random_start), 'red'), " s"

  return x


def encrypt(pub, plain, x):
  #(g**m)(r**N) mod N**2
  cipher = (pow(pub.g, plain, pub.n_sq) * x) % pub.n_sq
  print 'cipher =', cipher
  return cipher


def e_add(pub, a, b):
  """Homomorphic attribute"""
  return a * b % pub.n_sq


def decrypt(priv, pub, cipher):
  x = pow(cipher, priv.l, pub.n_sq) - 1
  print "x = ", x
  print "pow_cl_modn_sq = ", pow(cipher, priv.l, pub.n_sq)
  print "pow_cl_modn_sq-1 = ", pow(cipher, priv.l, pub.n_sq) - 1
  plain = ((x // pub.n) * priv.m) % pub.n
  print "x//n = ", x // pub.n
  return plain

print "Generating keypair..."
priv, pub = generate_keypair(128)
x_start = time.time()
rN = computing_random(pub)  # r**N mod N**2
print "rN : ", rN
x_stop = time.time()
print "Computing r**N mod N**2 cost :", colored((x_stop - x_start), 'red'), " s"

x = input("Enter first plaintext : ")
print "x =", x
print colored('Encrypting x...', 'red')
encrypt_start = time.time()
cx = encrypt(pub, x, rN)
encrypt_stop = time.time()
print "cx =", cx, colored("length of cx is", 'red'), colored(len(str(cx)), 'red'), "bits"
print "Encrypting plaintext cost :", colored((encrypt_stop - encrypt_start), 'red'), " s"


y = input("Enter second plaintext : ")
print "y =", y
print colored('Encrypting y...', 'red')
encrypt_start = time.time()
cy = encrypt(pub, y, rN)
encrypt_stop = time.time()
print "cy =", cy, colored("length of cy is", 'red'), colored(len(str(cy)), 'red'), "bits"
print "Encrypting plaintext cost :", colored((encrypt_stop - encrypt_start), 'red'), " s"

print colored('Computing cx + cy...', 'red')
cz = e_add(pub, cx, cy)
print "cz =", cz, colored("length of cz is", 'red'), colored(len(str(cz)), 'red'), "bits"

print colored('Decrypting cz...', 'red')
decrypt_start = time.time()
z = decrypt(priv, pub, cz)

decrypt_stop = time.time()
print "z =", z
print "Decrypting ciphertext cost :", colored((decrypt_stop - decrypt_start), 'red'), " s"


def generate_keypair_as_pem(key_len, exponent):
  def empty_callback():
    pass

  rsa = M2Crypto.RSA.gen_key(key_len, exponent, empty_callback)
  # Get RSA Public Key in PEM format
  buf = M2Crypto.BIO.MemoryBuffer('')
  rsa.save_pub_key_bio(buf)
  public_key = buf.getvalue()

  # Get Private Key in PEM format
  buf = M2Crypto.BIO.MemoryBuffer('')
  rsa.save_key_bio(buf, None)
  private_key = buf.getvalue()  # RSA Private Key

  return (public_key, private_key)
keylen = 1024         # 1024 bits
exponent = 65537
rsa_key_start = time.time()
A_pub_key, A_priv_key = generate_keypair_as_pem(keylen, exponent)
rsa_key_stop = time.time()

print 'A_pub_key =', A_pub_key, len(str(A_pub_key)), 'bits'
print 'A_priv_key =', A_priv_key, len(str(A_priv_key)), 'bits'
print "Creating RSA key cost :", colored((rsa_key_stop - rsa_key_start), 'red'), " s"

# string getBytes
str = 'PeterHsiao'
b = [ord(s) for s in str]
print b
