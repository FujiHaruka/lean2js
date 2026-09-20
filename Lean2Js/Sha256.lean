/-!
# SHA-256

SHA-256, so that a package can carry the digest of every file it ships beside the theorems it ships.

The digest is the plain one `shasum -a 256` prints. A consumer checking that the `index.js` in front of
them is the one the manifest speaks about has neither Lean nor this compiler, so the check has to be one
their own machine already knows how to do.

The three vectors below are FIPS 180-4's own. They are what says the table of constants was copied
correctly: every one of them is wrong the moment a digit is.
-/

namespace Lean2Js.Sha256

/-- The first thirty-two bits of the fractional parts of the cube roots of the first sixty-four primes. -/
private def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The first thirty-two bits of the fractional parts of the square roots of the first eight primes. -/
private def initialState : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

private def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- The message, `0x80`, zeros up to a multiple of the block size less eight, and the length in bits. -/
private def pad (message : ByteArray) : ByteArray := Id.run do
  let bitLength : UInt64 := (message.size * 8).toUInt64
  let mut out := message.push 0x80
  for _ in [0 : (56 + 64 - out.size % 64) % 64] do
    out := out.push 0
  for i in [0:8] do
    out := out.push ((bitLength >>> (((7 - i) * 8).toUInt64)).toUInt8)
  return out

private def block (state : Array UInt32) (m : ByteArray) (base : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := #[]
  for t in [0:16] do
    let o := base + t * 4
    w := w.push ((m[o]!.toUInt32 <<< 24) ||| (m[o + 1]!.toUInt32 <<< 16)
                  ||| (m[o + 2]!.toUInt32 <<< 8) ||| m[o + 3]!.toUInt32)
  for t in [16:64] do
    let x := w[t - 15]!
    let y := w[t - 2]!
    let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
    let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
    w := w.push (w[t - 16]! + s0 + w[t - 7]! + s1)
  let mut a := state[0]!
  let mut b := state[1]!
  let mut c := state[2]!
  let mut d := state[3]!
  let mut e := state[4]!
  let mut f := state[5]!
  let mut g := state[6]!
  let mut h := state[7]!
  for t in [0:64] do
    let s1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let t1 := h + s1 + ch + roundConstants[t]! + w[t]!
    let s0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := s0 + maj
    h := g; g := f; f := e; e := d + t1; d := c; c := b; b := a; a := t1 + t2
  return #[state[0]! + a, state[1]! + b, state[2]! + c, state[3]! + d,
           state[4]! + e, state[5]! + f, state[6]! + g, state[7]! + h]

def hash (message : ByteArray) : ByteArray := Id.run do
  let m := pad message
  let mut state := initialState
  for i in [0 : m.size / 64] do
    state := block state m (i * 64)
  let mut out := ByteArray.empty
  for x in state do
    out := (((out.push (x >>> 24).toUInt8).push (x >>> 16).toUInt8).push (x >>> 8).toUInt8).push x.toUInt8
  return out

private def hexDigits : Array Char :=
  #['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']

def hex (bs : ByteArray) : String := Id.run do
  let mut out := ""
  for i in [0 : bs.size] do
    let b := bs[i]!
    out := (out.push hexDigits[(b >>> 4).toNat]!).push hexDigits[(b &&& 0x0f).toNat]!
  return out

/-- The digest of a file's bytes, spelled the way `shasum -a 256` spells it. -/
def digest (bs : ByteArray) : String := hex (hash bs)

def digestString (s : String) : String := digest s.toUTF8

#guard digestString "" = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard digestString "abc" = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard digestString "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
  = "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"

end Lean2Js.Sha256
