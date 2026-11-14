///|
/// Module M15 (Part 1) — Exact Real-Space Renormalization Group:
/// 1D Ising transfer-matrix decimation as the rational semigroup R_b(t)=t^b
/// (t = tanh K), the diamond hierarchical (Migdal–Kadanoff/Berker–Ostlund)
/// RG map R(t)=2t²/(1+t⁴), Sturm-isolated critical fixed point, and the exact
/// algebraic linearization eigenvalue in ℚ[t]/(t³+t²+t−1).
/// 局部公理（合體結合律）實例：R_b ∘ R_c = R_{bc}（重整化半群律）。

///|
pub(all) suberror RGError {
  InvalidBlockFactor(Int32)
  ZeroPolynomialDivision
  NonSquareFreeSturm
  SingularQuotientElement
  InvalidCouplingDomain
}

///|
fn rat(i : Int32) -> @m20.Rat {
  @m20.Rat::from_int(i)
}

///|
/// 單變元多項式（係數低次→高次，典範修剪）。係數域 ℚ（精確）。
pub(all) struct Poly {
  coeffs : Array[@m20.Rat]
}

///|
pub fn Poly::make(coeffs : Array[@m20.Rat]) -> Poly {
  let c = coeffs.copy()
  while c.length() > 0 && c[c.length() - 1].is_zero() {
    let _ = c.pop()
  }
  { coeffs: c, }
}

///|
pub fn Poly::zero() -> Poly {
  { coeffs: [], }
}

///|
pub fn Poly::one() -> Poly {
  { coeffs: [rat(1)], }
}

///|
pub fn Poly::x() -> Poly {
  { coeffs: [rat(0), rat(1)], }
}

///|
pub fn Poly::constant(c : @m20.Rat) -> Poly {
  Poly::make([c])
}

///|
pub fn Poly::degree(self : Poly) -> Int32 {
  self.coeffs.length() - 1
}

///|
pub fn Poly::is_zero(self : Poly) -> Bool {
  self.coeffs.length() == 0
}

///|
pub fn Poly::coeff(self : Poly, k : Int32) -> @m20.Rat {
  if k < 0 || k >= self.coeffs.length() {
    @m20.Rat::zero()
  } else {
    self.coeffs[k]
  }
}

///|
pub fn Poly::add(self : Poly, other : Poly) -> Poly raise Error {
  let n = if self.coeffs.length() > other.coeffs.length() {
    self.coeffs.length()
  } else {
    other.coeffs.length()
  }
  let c : Array[@m20.Rat] = []
  for i = 0; i < n; i = i + 1 {
    c.push(self.coeff(i).add(other.coeff(i)))
  }
  Poly::make(c)
}

///|
pub fn Poly::sub(self : Poly, other : Poly) -> Poly raise Error {
  let n = if self.coeffs.length() > other.coeffs.length() {
    self.coeffs.length()
  } else {
    other.coeffs.length()
  }
  let c : Array[@m20.Rat] = []
  for i = 0; i < n; i = i + 1 {
    c.push(self.coeff(i).sub(other.coeff(i)))
  }
  Poly::make(c)
}

///|
pub fn Poly::scale(self : Poly, s : @m20.Rat) -> Poly raise Error {
  let c : Array[@m20.Rat] = []
  for v in self.coeffs {
    c.push(v.mul(s))
  }
  Poly::make(c)
}

///|
pub fn Poly::mul(self : Poly, other : Poly) -> Poly raise Error {
  if self.is_zero() || other.is_zero() {
    return Poly::zero()
  }
  let c = Array::make(
    self.coeffs.length() + other.coeffs.length() - 1,
    @m20.Rat::zero(),
  )
  for i = 0; i < self.coeffs.length(); i = i + 1 {
    for j = 0; j < other.coeffs.length(); j = j + 1 {
      c[i + j] = c[i + j].add(self.coeffs[i].mul(other.coeffs[j]))
    }
  }
  Poly::make(c)
}

///|
pub fn Poly::div_mod(self : Poly, other : Poly) -> (Poly, Poly) raise Error {
  if other.is_zero() {
    raise Error::ZeroPolynomialDivision
  }
  let rem = self.coeffs.copy()
  let q = Array::make(
    if self.degree() >= other.degree() {
      self.degree() - other.degree() + 1
    } else {
      0
    },
    @m20.Rat::zero(),
  )
  let lead_inv = other.coeffs[other.coeffs.length() - 1].inv()
  while rem.length() >= other.coeffs.length() && rem.length() > 0 {
    let d = rem.length() - other.coeffs.length()
    let f = rem[rem.length() - 1].mul(lead_inv)
    q[d] = f
    for j = 0; j < other.coeffs.length(); j = j + 1 {
      rem[d + j] = rem[d + j].sub(f.mul(other.coeffs[j]))
    }
    while rem.length() > 0 && rem[rem.length() - 1].is_zero() {
      let _ = rem.pop()
    }
  }
  (Poly::make(q), Poly::make(rem))
}

///|
pub fn Poly::rem(self : Poly, other : Poly) -> Poly raise Error {
  let (_, r) = self.div_mod(other)
  r
}

///|
pub fn Poly::derivative(self : Poly) -> Poly raise Error {
  let c : Array[@m20.Rat] = []
  for i = 1; i < self.coeffs.length(); i = i + 1 {
    c.push(self.coeffs[i].mul(rat(i)))
  }
  Poly::make(c)
}

///|
pub fn Poly::eval(self : Poly, x : @m20.Rat) -> @m20.Rat raise Error {
  // Horner
  let mut acc = @m20.Rat::zero()
  let mut i = self.coeffs.length() - 1
  while i >= 0 {
    acc = acc.mul(x).add(self.coeffs[i])
    i = i - 1
  }
  acc
}

///|
pub fn Poly::monic(self : Poly) -> Poly raise Error {
  if self.is_zero() {
    raise Error::ZeroPolynomialDivision
  }
  self.scale(self.coeffs[self.coeffs.length() - 1].inv())
}

///|
pub fn Poly::gcd(self : Poly, other : Poly) -> Poly raise Error {
  let mut a = self
  let mut b = other
  while !b.is_zero() {
    let r = a.rem(b)
    a = b
    b = r
  }
  if a.is_zero() {
    a
  } else {
    a.monic()
  }
}

///|
pub fn Poly::squarefree_part(self : Poly) -> Poly raise Error {
  if self.is_zero() {
    return self
  }
  let g = self.gcd(self.derivative())
  let (q, _) = self.div_mod(g)
  q
}

///|
/// Sturm 序列：p0=p, p1=p', p_{i+1} = −rem(p_{i−1}, p_i)。
pub fn sturm_sequence(p : Poly) -> Array[Poly] raise Error {
  let sq = p.squarefree_part()
  let seq : Array[Poly] = [sq, sq.derivative()]
  while !seq[seq.length() - 1].is_zero() {
    let n = seq.length()
    let r = seq[n - 2].rem(seq[n - 1])
    if r.is_zero() {
      break
    }
    seq.push(r.scale(rat(-1)))
  }
  seq
}

///|
fn sign_variations(seq : Array[Poly], x : @m20.Rat) -> Int32 raise Error {
  let mut prev = 0
  let mut count = 0
  for p in seq {
    let s = p.eval(x).sign()
    if s == 0 {
      continue
    }
    if prev != 0 && s != prev {
      count = count + 1
    }
    prev = s
  }
  count
}

///|
/// Sturm 定理：開區間 (a,b] 內實根數 = V(a) − V(b)（精確整數）。
pub fn sturm_root_count(
  p : Poly,
  a : @m20.Rat,
  b : @m20.Rat,
) -> Int32 raise Error {
  if a.compare(b) >= 0 {
    raise Error::InvalidCouplingDomain
  }
  let seq = sturm_sequence(p)
  sign_variations(seq, a) - sign_variations(seq, b)
}

///|
/// 1D Ising 轉移矩陣特徵值比 t = tanh K；b-區塊抽取 R_b(t) = t^b（精確有理）。
pub fn decimate_coupling(t : @m20.Rat, b : Int32) -> @m20.Rat raise Error {
  if b < 1 {
    raise Error::InvalidBlockFactor(b)
  }
  let mut acc = @m20.Rat::one()
  for i = 0; i < b; i = i + 1 {
    acc = acc.mul(t)
  }
  acc
}

///|
/// 重整化半群律證書：R_b(R_c(t)) = R_{bc}(t)（合體運算結合律公理之實例）。
pub fn rg_semigroup_certificate(
  t : @m20.Rat,
  b : Int32,
  c : Int32,
) -> Bool raise Error {
  let lhs = decimate_coupling(decimate_coupling(t, c), b)
  let rhs = decimate_coupling(t, b * c)
  lhs == rhs
}

///|
/// 1D Ising 關聯長度 ξ = −1/ln|t| 於抽取下 ξ → ξ/b；臨界指數 ν = 1（t→1 極限）。
/// 回傳 (ν, 抽取後 t)。
pub fn ising_decimation_data(
  t : @m20.Rat,
  b : Int32,
) -> (Int32, @m20.Rat) raise Error {
  if t.sign() < 0 || t.compare(@m20.Rat::one()) > 0 {
    raise Error::InvalidCouplingDomain
  }
  (1, decimate_coupling(t, b))
}

///|
/// 鑽石分級晶格（2 支 × 2 鍵）精確 RG 映射 R(t) = 2t²/(1+t⁴)。
pub fn diamond_rg(t : @m20.Rat) -> @m20.Rat raise Error {
  let t2 = t.mul(t)
  let t4 = t2.mul(t2)
  rat(2).mul(t2).div(rat(1).add(t4))
}

///|
/// 不動點多項式：t = R(t) ⟺ t⁴ − 2t + 1 = (t−1)(t³+t²+t−1)。
pub fn diamond_fixed_point_poly() -> Poly {
  Poly::make([rat(1), rat(-2), rat(0), rat(0), rat(1)])
}

///|
pub fn diamond_critical_poly() -> Poly {
  Poly::make([rat(-1), rat(1), rat(1), rat(1)])
}

///|
/// 臨界不動點存在唯一性證書：t³+t²+t−1 於 (0,1) 恰一實根（Sturm 精確計數），
/// 且 t⁴−2t+1 於 (0,1) 之根數同為 1。
pub fn diamond_critical_isolation() -> (Int32, Int32) raise Error {
  let c1 = sturm_root_count(diamond_critical_poly(), rat(0), rat(1))
  let c2 = sturm_root_count(diamond_fixed_point_poly(), rat(0), rat(1))
  (c1, c2)
}

///|
/// ℚ[t]/(modulus) 元素乘法（modulus 首一）。
fn quotient_mul(a : Poly, b : Poly, modulus : Poly) -> Poly raise Error {
  a.mul(b).rem(modulus)
}

///|
/// 商代數中元素之乘法矩陣（基 1,t,...,t^{d−1}）。
fn quotient_mul_matrix(a : Poly, modulus : Poly) -> @m20.RatMatrix raise Error {
  let d = modulus.degree()
  let m = @m20.RatMatrix::zero(d, d)
  for j = 0; j < d; j = j + 1 {
    let tjc : Array[@m20.Rat] = Array::make(j + 1, @m20.Rat::zero())
    tjc[j] = @m20.Rat::one()
    let tj = Poly::make(tjc)
    let prod = quotient_mul(a, tj, modulus)
    for i = 0; i < d; i = i + 1 {
      m.set(i, j, prod.coeff(i))
    }
  }
  m
}

///|
/// 商代數求逆：解 M_a · x = e_0。
fn quotient_inv(a : Poly, modulus : Poly) -> Poly raise Error {
  let d = modulus.degree()
  let m = quotient_mul_matrix(a, modulus)
  let e0 = Array::make(d, @m20.Rat::zero())
  e0[0] = @m20.Rat::one()
  match m.solve(e0) {
    Inconsistent => raise Error::SingularQuotientElement
    Solution(x, _) => Poly::make(x)
  }
}

///|
/// 代數數之極小多項式：對 λ^0..λ^d 之係數向量求首個線性相關（nullspace）。
pub fn algebraic_minpoly(lambda : Poly, modulus : Poly) -> Poly raise Error {
  let d = modulus.degree()
  let powers : Array[Poly] = [Poly::one()]
  for k = 1; k <= d; k = k + 1 {
    powers.push(quotient_mul(powers[k - 1], lambda, modulus))
  }
  // 找最小 m 使 {λ^0..λ^m} 線性相關
  for mdeg = 1; mdeg <= d; mdeg = mdeg + 1 {
    let mat = @m20.RatMatrix::zero(d, mdeg + 1)
    for j = 0; j <= mdeg; j = j + 1 {
      for i = 0; i < d; i = i + 1 {
        mat.set(i, j, powers[j].coeff(i))
      }
    }
    let ns = mat.nullspace()
    if ns.length() > 0 {
      // 取第一個相關向量，正規化為首一（最高次係數 1）
      let v = ns[0]
      let mut lead = mdeg
      while lead > 0 && v[lead].is_zero() {
        lead = lead - 1
      }
      let c : Array[@m20.Rat] = []
      for i = 0; i <= lead; i = i + 1 {
        c.push(v[i].div(v[lead]))
      }
      return Poly::make(c)
    }
  }
  raise Error::SingularQuotientElement
}

///|
pub(all) struct DiamondCriticalData {
  /// 臨界多項式 t³+t²+t−1
  critical_poly : Poly
  /// (0,1) 內實根數（應為 1）
  roots_in_unit_interval : Int32
  /// 線性化特徵值 λ = R'(t*) 之極小多項式（精確代數數）
  eigenvalue_minpoly : Poly
}

///|
/// 臨界不動點之精確線性化：R'(t) = 4t(1−t⁴)/(1+t⁴)²，於商代數中求值並取極小多項式。
pub fn diamond_critical_linearization() -> DiamondCriticalData raise Error {
  let modulus = diamond_critical_poly()
  let t = Poly::x()
  let t2 = quotient_mul(t, t, modulus)
  let t4 = quotient_mul(t2, t2, modulus)
  // numerator 4t(1−t⁴)
  let one = Poly::one()
  let num = quotient_mul(t.scale(rat(4)), one.sub(t4), modulus)
  // denominator (1+t⁴)²
  let den = quotient_mul(one.add(t4), one.add(t4), modulus)
  let lambda = quotient_mul(num, quotient_inv(den, modulus), modulus)
  let mp = algebraic_minpoly(lambda, modulus)
  let (c1, _) = diamond_critical_isolation()
  {
    critical_poly: modulus,
    roots_in_unit_interval: c1,
    eigenvalue_minpoly: mp,
  }
}
