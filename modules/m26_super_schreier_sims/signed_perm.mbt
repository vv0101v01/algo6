///|
/// Module M26 (Part 1) — Signed Permutations & the Hyperoctahedral Group:
/// B_n = Z₂ⁿ ⋊ S_n as permutations of 2n signed points, the even-sign subgroup
/// D_n (index 2, the Z₂ "super" grading), composition/inverse, and generators.

///|
pub(all) suberror SuperGroupError {
  InvalidSignedPerm(String)
  VerificationFailed(String)
}

///|
/// 符號置換 (π, ε)：π ∈ S_n，ε_i ∈ {±1}。
#derive(Eq)
pub(all) struct SignedPerm {
  perm : Array[Int32]
  signs : Array[Int32]
}

///|
pub extend SignedPerm with Eq::{equal, not_equal}

///|
pub fn SignedPerm::identity(n : Int32) -> SignedPerm {
  let p = Array::make(n, 0)
  let s = Array::make(n, 1)
  for i = 0; i < n; i = i + 1 {
    p[i] = i
  }
  { perm: p, signs: s, }
}

///|
pub fn SignedPerm::make(
  perm : Array[Int32],
  signs : Array[Int32],
) -> SignedPerm raise Error {
  let n = perm.length()
  if signs.length() != n {
    raise SuperGroupError::InvalidSignedPerm("length mismatch")
  }
  let seen = Array::make(n, false)
  for v in perm {
    if v < 0 || v >= n || seen[v] {
      raise SuperGroupError::InvalidSignedPerm("not a permutation")
    }
    seen[v] = true
  }
  for s in signs {
    if s != 1 && s != -1 {
      raise SuperGroupError::InvalidSignedPerm("sign not ±1")
    }
  }
  { perm, signs, }
}

///|
/// 嵌入 S_{2n}：點 i = +(i+1)，點 n+i = −(i+1)。
pub fn SignedPerm::to_perm(self : SignedPerm) -> @m23.Perm raise Error {
  let n = self.perm.length()
  let img = Array::make(2 * n, 0)
  for i = 0; i < n; i = i + 1 {
    let pi = self.perm[i]
    if self.signs[i] == 1 {
      img[i] = pi
      img[n + i] = n + pi
    } else {
      img[i] = n + pi
      img[n + i] = pi
    }
  }
  @m23.Perm::make(img)
}

///|
/// compose(self, other) = self ∘ other：π∘σ，sign_i = ε_{σ(i)}·δ_i。
pub fn SignedPerm::compose(
  self : SignedPerm,
  other : SignedPerm,
) -> SignedPerm raise Error {
  let n = self.perm.length()
  if other.perm.length() != n {
    raise SuperGroupError::InvalidSignedPerm("degree mismatch")
  }
  let p = Array::make(n, 0)
  let s = Array::make(n, 1)
  for i = 0; i < n; i = i + 1 {
    p[i] = self.perm[other.perm[i]]
    s[i] = self.signs[other.perm[i]] * other.signs[i]
  }
  { perm: p, signs: s, }
}

///|
pub fn SignedPerm::inv(self : SignedPerm) -> SignedPerm {
  let n = self.perm.length()
  let p = Array::make(n, 0)
  let s = Array::make(n, 1)
  for i = 0; i < n; i = i + 1 {
    p[self.perm[i]] = i
    s[self.perm[i]] = self.signs[i]
  }
  { perm: p, signs: s, }
}

///|
/// Z₂ 超 grading：sign 積 = +1 為偶（D_n），−1 為奇。
pub fn SignedPerm::parity(self : SignedPerm) -> Int32 {
  let mut prod = 1
  for s in self.signs {
    prod = prod * s
  }
  prod
}

///|
/// B_n 生成元：相鄰對換 s_i + 單符號翻轉 t_0。
pub fn hyperoctahedral_generators(n : Int32) -> Array[SignedPerm] raise Error {
  if n < 1 {
    raise SuperGroupError::InvalidSignedPerm("n >= 1")
  }
  let gens : Array[SignedPerm] = []
  for i = 0; i + 1 < n; i = i + 1 {
    let sp = SignedPerm::identity(n)
    sp.perm[i] = i + 1
    sp.perm[i + 1] = i
    gens.push(sp)
  }
  let flip = SignedPerm::identity(n)
  flip.signs[0] = -1
  gens.push(flip)
  gens
}

///|
/// D_n（偶符號子群）生成元：相鄰對換 + 雙符號翻轉（n ≥ 2）。
pub fn even_signed_generators(n : Int32) -> Array[SignedPerm] raise Error {
  if n < 2 {
    raise SuperGroupError::InvalidSignedPerm("D_n needs n >= 2")
  }
  let gens : Array[SignedPerm] = []
  for i = 0; i + 1 < n; i = i + 1 {
    let sp = SignedPerm::identity(n)
    sp.perm[i] = i + 1
    sp.perm[i + 1] = i
    gens.push(sp)
  }
  let flip2 = SignedPerm::identity(n)
  flip2.signs[0] = -1
  flip2.signs[1] = -1
  gens.push(flip2)
  gens
}

///|
/// |B_n| = 2ⁿ·n!。
pub fn hyperoctahedral_order(n : Int32) -> @bigint.BigInt {
  let mut fact = @bigint.BigInt::from_int(1)
  for i = 2; i <= n; i = i + 1 {
    fact = fact * @bigint.BigInt::from_int(i)
  }
  let mut pow2 = @bigint.BigInt::from_int(1)
  for i = 0; i < n; i = i + 1 {
    pow2 = pow2 * @bigint.BigInt::from_int(2)
  }
  pow2 * fact
}
