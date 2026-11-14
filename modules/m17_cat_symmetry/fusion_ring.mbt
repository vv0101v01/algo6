///|
/// Module M17 (Part 1) — Categorical (Non-Invertible) Symmetry: fusion rings
/// N_ij^k with associativity/commutativity/unit/dual certificates, exact
/// quadratic-surd quantum dimensions (Frobenius–Perron ring homomorphisms),
/// and the Verlinde formula N_ij^k = Σ_a w_a λ_i(a)λ_j(a)λ_k(a) verified
/// against Fibonacci (ℚ(√5)) and Ising (ℚ(√2)) modular data.
/// 局部公理（coherence）實例：融合矩陣結合律 N_i N_j = Σ_k N_ij^k N_k。

///|
pub(all) suberror FusionError {
  InvalidFusionData(String)
  InvalidSurd(String)
  VerlindeMismatch(Int32, Int32, Int32)
}

///|
/// 二次根式 a + b√d（d 無平方因子，精確 ℚ(√d) 域）。
#derive(Eq, Debug)
pub(all) struct Surd {
  a : @m20.Rat
  b : @m20.Rat
  d : Int32
}

///|
pub extend Surd with Eq::{equal, not_equal}

///|
pub extend Surd with @debug.Debug::{to_repr}

///|
pub fn Surd::from_rat(a : @m20.Rat, d : Int32) -> Surd {
  { a, b: @m20.Rat::zero(), d, }
}

///|
pub fn Surd::sqrt_d(d : Int32) -> Surd {
  { a: @m20.Rat::zero(), b: @m20.Rat::one(), d, }
}

///|
pub fn Surd::make(a : @m20.Rat, b : @m20.Rat, d : Int32) -> Surd {
  { a, b, d, }
}

///|
pub fn Surd::add(self : Surd, other : Surd) -> Surd raise Error {
  if self.d != other.d {
    raise FusionError::InvalidSurd("radicand mismatch")
  }
  { a: self.a.add(other.a), b: self.b.add(other.b), d: self.d, }
}

///|
pub fn Surd::sub(self : Surd, other : Surd) -> Surd raise Error {
  if self.d != other.d {
    raise FusionError::InvalidSurd("radicand mismatch")
  }
  { a: self.a.sub(other.a), b: self.b.sub(other.b), d: self.d, }
}

///|
pub fn Surd::mul(self : Surd, other : Surd) -> Surd raise Error {
  if self.d != other.d {
    raise FusionError::InvalidSurd("radicand mismatch")
  }
  // (a+b√d)(c+e√d) = (ac + be·d) + (ae + bc)√d
  let dd = @m20.Rat::from_int(self.d)
  let real = self.a.mul(other.a).add(self.b.mul(other.b).mul(dd))
  let rad = self.a.mul(other.b).add(self.b.mul(other.a))
  { a: real, b: rad, d: self.d, }
}

///|
pub fn Surd::inv(self : Surd) -> Surd raise Error {
  // (a+b√d)⁻¹ = (a−b√d)/(a²−b²d)
  let dd = @m20.Rat::from_int(self.d)
  let norm = self.a.mul(self.a).sub(self.b.mul(self.b).mul(dd))
  if norm.is_zero() {
    raise FusionError::InvalidSurd("zero norm")
  }
  { a: self.a.div(norm), b: self.b.neg().div(norm), d: self.d, }
}

///|
pub fn Surd::div(self : Surd, other : Surd) -> Surd raise Error {
  self.mul(other.inv())
}

///|
pub fn Surd::is_zero(self : Surd) -> Bool {
  self.a.is_zero() && self.b.is_zero()
}

///|
/// 融合環：N[i][j][k] = N_ij^k，單位物件 0。
pub(all) struct FusionRing {
  rank : Int32
  coeffs : Array[Int32]
}

///|
pub fn FusionRing::make(
  rank : Int32,
  coeffs : Array[Int32],
) -> FusionRing raise Error {
  if rank < 1 || coeffs.length() != rank * rank * rank {
    raise FusionError::InvalidFusionData("shape")
  }
  for c in coeffs {
    if c < 0 {
      raise FusionError::InvalidFusionData("negative multiplicity")
    }
  }
  let r : FusionRing = { rank, coeffs, }
  // 單位：N_0j^k = δ_jk, N_i0^k = δ_ik
  for j = 0; j < rank; j = j + 1 {
    for k = 0; k < rank; k = k + 1 {
      let expect = if j == k { 1 } else { 0 }
      if r.get(0, j, k) != expect || r.get(j, 0, k) != expect {
        raise FusionError::InvalidFusionData("unit object")
      }
    }
  }
  r
}

///|
pub fn FusionRing::get(
  self : FusionRing,
  i : Int32,
  j : Int32,
  k : Int32,
) -> Int32 {
  self.coeffs[(i * self.rank + j) * self.rank + k]
}

///|
/// 融合矩陣 (N_i)_{j,k} = N_ij^k。結合律證書：N_i N_j = Σ_k N_ij^k N_k。
pub fn FusionRing::associativity_certificate(self : FusionRing) -> Bool {
  for i = 0; i < self.rank; i = i + 1 {
    for j = 0; j < self.rank; j = j + 1 {
      // lhs = N_i · N_j
      for a = 0; a < self.rank; a = a + 1 {
        for b = 0; b < self.rank; b = b + 1 {
          let mut lhs = 0
          for c = 0; c < self.rank; c = c + 1 {
            lhs = lhs + self.get(i, a, c) * self.get(j, c, b)
          }
          let mut rhs = 0
          for k = 0; k < self.rank; k = k + 1 {
            rhs = rhs + self.get(i, j, k) * self.get(k, a, b)
          }
          if lhs != rhs {
            return false
          }
        }
      }
    }
  }
  true
}

///|
pub fn FusionRing::commutativity_certificate(self : FusionRing) -> Bool {
  for i = 0; i < self.rank; i = i + 1 {
    for j = 0; j < self.rank; j = j + 1 {
      for k = 0; k < self.rank; k = k + 1 {
        if self.get(i, j, k) != self.get(j, i, k) {
          return false
        }
      }
    }
  }
  true
}

///|
/// 剛性對偶：每物件 i 有唯一對偶 i* 使 N_{i,i*}^0 = 1 且 N_{i,j}^0 = 0 (j≠i*)。
pub fn FusionRing::duals(self : FusionRing) -> Array[Int32] raise Error {
  let dual : Array[Int32] = []
  for i = 0; i < self.rank; i = i + 1 {
    let mut found = -1
    for j = 0; j < self.rank; j = j + 1 {
      if self.get(i, j, 0) == 1 {
        if found >= 0 {
          raise FusionError::InvalidFusionData("non-unique dual")
        }
        found = j
      } else if self.get(i, j, 0) != 0 {
        raise FusionError::InvalidFusionData("bad unit multiplicity")
      }
    }
    if found < 0 {
      raise FusionError::InvalidFusionData("missing dual")
    }
    dual.push(found)
  }
  dual
}

///|
/// 量子維數同態證書：d_i · d_j = Σ_k N_ij^k d_k（於 ℚ(√d) 精確驗證）。
pub fn quantum_dimension_homomorphism(
  ring : FusionRing,
  dims : Array[Surd],
) -> Bool raise Error {
  if dims.length() != ring.rank {
    return false
  }
  for i = 0; i < ring.rank; i = i + 1 {
    for j = 0; j < ring.rank; j = j + 1 {
      let lhs = dims[i].mul(dims[j])
      let mut rhs = Surd::from_rat(@m20.Rat::zero(), dims[0].d)
      for k = 0; k < ring.rank; k = k + 1 {
        let n = ring.get(i, j, k)
        if n != 0 {
          rhs = rhs.add(dims[k].scale_int(n))
        }
      }
      if lhs != rhs {
        return false
      }
    }
  }
  true
}

///|
pub fn Surd::scale_int(self : Surd, n : Int32) -> Surd raise Error {
  let s = @m20.Rat::from_int(n)
  { a: self.a.mul(s), b: self.b.mul(s), d: self.d, }
}

///|
/// Frobenius–Perron 特徵向量證書：N_i · d = d_i · d（d 為正維數向量）。
pub fn frobenius_perron_eigenvector(
  ring : FusionRing,
  dims : Array[Surd],
) -> Bool raise Error {
  if dims.length() != ring.rank {
    return false
  }
  for i = 0; i < ring.rank; i = i + 1 {
    for j = 0; j < ring.rank; j = j + 1 {
      let mut lhs = Surd::from_rat(@m20.Rat::zero(), dims[0].d)
      for k = 0; k < ring.rank; k = k + 1 {
        let n = ring.get(i, j, k)
        if n != 0 {
          lhs = lhs.add(dims[k].scale_int(n))
        }
      }
      let rhs = dims[i].mul(dims[j])
      if lhs != rhs {
        return false
      }
    }
  }
  true
}

///|
/// Verlinde 公式證書：N_ij^k = Σ_a w_a λ_i(a) λ_j(a) λ_k(a)，
/// 其中 λ_i(a) = S_ia/S_0a，w_a = S_0a²（皆於 ℚ(√d)）。
pub fn verlinde_certificate(
  ring : FusionRing,
  lambda : Array[Array[Surd]],
  weights : Array[Surd],
) -> Bool raise Error {
  if lambda.length() != ring.rank || weights.length() != ring.rank {
    return false
  }
  for i = 0; i < ring.rank; i = i + 1 {
    for j = 0; j < ring.rank; j = j + 1 {
      for k = 0; k < ring.rank; k = k + 1 {
        let mut s = Surd::from_rat(@m20.Rat::zero(), weights[0].d)
        for a = 0; a < ring.rank; a = a + 1 {
          let term = weights[a]
            .mul(lambda[i][a])
            .mul(lambda[j][a])
            .mul(lambda[k][a])
          s = s.add(term)
        }
        let expect = Surd::from_rat(
          @m20.Rat::from_int(ring.get(i, j, k)),
          weights[0].d,
        )
        if s != expect {
          return false
        }
      }
    }
  }
  true
}

///|
fn r(n : Int32, dd : Int32) -> @m20.Rat raise Error {
  // n/dd as Rat
  @m20.Rat::make(@bigint.BigInt::from_int(n), @bigint.BigInt::from_int(dd))
}

///|
/// Fibonacci 融合環：{1, τ}，τ×τ = 1 + τ。
pub fn fibonacci_ring() -> FusionRing raise Error {
  // N[0]=unit rows; N_ττ^1=1, N_ττ^τ=1
  let c = Array::make(8, 0)
  // unit
  c[(0 * 2 + 0) * 2 + 0] = 1
  c[(0 * 2 + 1) * 2 + 1] = 1
  c[(1 * 2 + 0) * 2 + 1] = 1
  // ττ
  c[(1 * 2 + 1) * 2 + 0] = 1
  c[(1 * 2 + 1) * 2 + 1] = 1
  FusionRing::make(2, c)
}

///|
/// Fibonacci 量子維數：d_1 = 1, d_τ = φ = (1+√5)/2。
pub fn fibonacci_dimensions() -> Array[Surd] raise Error {
  [Surd::from_rat(@m20.Rat::one(), 5), Surd::make(r(1, 2), r(1, 2), 5)]
}

///|
/// Fibonacci Verlinde 資料：λ_i(a) = S_ia/S_0a，w_a = S_0a²（ℚ(√5)）。
pub fn fibonacci_verlinde_data() -> (Array[Array[Surd]], Array[Surd]) raise Error {
  let phi = Surd::make(r(1, 2), r(1, 2), 5)
  // λ_1 = (1,1), λ_τ = (φ, −1/φ)
  let inv_phi = phi.inv()
  let lambda = [
    [Surd::from_rat(@m20.Rat::one(), 5), Surd::from_rat(@m20.Rat::one(), 5)],
    [phi, inv_phi.neg_surd()],
  ]
  // w_0 = 1/(2+φ) = (5−√5)/10, w_τ = φ²/(2+φ)
  let two_plus_phi = Surd::from_rat(@m20.Rat::from_int(2), 5).add(phi)
  let w0 = two_plus_phi.inv()
  let w1 = phi.mul(phi).mul(w0)
  (lambda, [w0, w1])
}

///|
pub fn Surd::neg_surd(self : Surd) -> Surd {
  { a: self.a.neg(), b: self.b.neg(), d: self.d, }
}

///|
/// Ising 融合環：{1, ψ, σ}，ψψ=1, ψσ=σ, σσ=1+ψ。
pub fn ising_ring() -> FusionRing raise Error {
  let c = Array::make(27, 0)
  let put = (i : Int32, j : Int32, k : Int32, v : Int32) => {
    c[(i * 3 + j) * 3 + k] = v
  }
  // unit
  put(0, 0, 0, 1)
  put(0, 1, 1, 1)
  put(0, 2, 2, 1)
  put(1, 0, 1, 1)
  put(2, 0, 2, 1)
  // ψψ=1
  put(1, 1, 0, 1)
  // ψσ=σψ=σ
  put(1, 2, 2, 1)
  put(2, 1, 2, 1)
  // σσ=1+ψ
  put(2, 2, 0, 1)
  put(2, 2, 1, 1)
  FusionRing::make(3, c)
}

///|
/// Ising 量子維數：d_1=1, d_ψ=1, d_σ=√2。
pub fn ising_dimensions() -> Array[Surd] {
  [
    Surd::from_rat(@m20.Rat::one(), 2),
    Surd::from_rat(@m20.Rat::one(), 2),
    Surd::sqrt_d(2),
  ]
}

///|
/// Ising Verlinde 資料（ℚ(√2)）：λ_1=(1,1,1), λ_ψ=(1,1,−1), λ_σ=(√2,−√2,0)，
/// w = (1/4, 1/4, 1/2)。
pub fn ising_verlinde_data() -> (Array[Array[Surd]], Array[Surd]) raise Error {
  let s2 = Surd::sqrt_d(2)
  let one = Surd::from_rat(@m20.Rat::one(), 2)
  let lambda = [
    [one, one, one],
    [one, one, one.neg_surd()],
    [s2, s2.neg_surd(), Surd::from_rat(@m20.Rat::zero(), 2)],
  ]
  let weights = [
    Surd::from_rat(r(1, 4), 2),
    Surd::from_rat(r(1, 4), 2),
    Surd::from_rat(r(1, 2), 2),
  ]
  (lambda, weights)
}
