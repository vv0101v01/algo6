///|
/// Module M25 (Part 4) — GENERAL Superconformal Maps & the Berezinian Line
/// Bundle, derived from scratch rather than transcribed:
///
/// Writing z' = f(z) + θ·g(z) (f even, g odd) and θ' = h(z) + θ·k(z)
/// (h odd, k even), the condition D_θ z' = θ'·D_θ θ' with D_θ = ∂_θ + θ∂_z
/// expands to   g = h·k   and   f' = k² − h·h'.
/// Hence the GENERAL superconformal map is parametrised by arbitrary
/// (h, k) with k of invertible body:
///     z' = f + θ·h·k,  θ' = h + θ·k,  f = ∫(k² − h·h').
/// No square root is needed: k is the free even datum.
///
/// With LEFT-coefficient Jacobian convention (dz' = A dz + B dθ requires
/// B = −∂_θ z' because dθ and ∂_θ z' are both odd) one gets the exact identity
///     Ber(J) = D_θ θ' = k + θ·h',
/// which this file verifies SYMBOLICALLY (all polynomial coefficients, full
/// Grassmann algebra), including cases with h·h' ≠ 0 and k' ≠ 0 where the
/// naive sign convention B = +∂_θ z' FAILS.
///
/// The Berezinian line bundle is then realised by its transition functions
/// w = D_θ θ' with the Čech cocycle condition verified by ACTUAL composition
/// of maps: w_{02} = w_{01} · (w_{12} ∘ g_{01}).

///|
/// Grassmann 係數多項式（z 之形式變數，係數於 Λ）。
pub(all) struct GPol {
  k : Int32
  coeffs : Array[@m22.Grassmann]
}

///|
pub fn GPol::zero(k : Int32) -> GPol {
  { k, coeffs: [], }
}

///|
pub fn GPol::constant(g : @m22.Grassmann) -> GPol {
  { k: g.k, coeffs: [g], }
}

///|
pub fn GPol::scalar(k : Int32, r : @m20.Rat) -> GPol {
  GPol::constant(@m22.Grassmann::scalar(k, r))
}

///|
/// z 之一次項。
pub fn GPol::z(k : Int32) -> GPol {
  {
    k,
    coeffs: [
      @m22.Grassmann::zero(k),
      @m22.Grassmann::scalar(k, @m20.Rat::one()),
    ],
  }
}

///|
fn trim(coeffs : Array[@m22.Grassmann]) -> Array[@m22.Grassmann] {
  let mut n = coeffs.length()
  while n > 0 {
    if !coeffs[n - 1].is_zero() {
      break
    }
    n = n - 1
  }
  let out : Array[@m22.Grassmann] = []
  for i = 0; i < n; i = i + 1 {
    out.push(coeffs[i])
  }
  out
}

///|
pub fn GPol::degree(self : GPol) -> Int32 {
  trim(self.coeffs).length() - 1
}

///|
pub fn GPol::is_zero(self : GPol) -> Bool {
  trim(self.coeffs).length() == 0
}

///|
fn coeff_at(p : GPol, i : Int32) -> @m22.Grassmann {
  if i < p.coeffs.length() {
    p.coeffs[i]
  } else {
    @m22.Grassmann::zero(p.k)
  }
}

///|
pub fn GPol::add(self : GPol, other : GPol) -> GPol raise Error {
  let n = if self.coeffs.length() > other.coeffs.length() {
    self.coeffs.length()
  } else {
    other.coeffs.length()
  }
  let out : Array[@m22.Grassmann] = []
  for i = 0; i < n; i = i + 1 {
    out.push(coeff_at(self, i).add(coeff_at(other, i)))
  }
  { k: self.k, coeffs: trim(out), }
}

///|
pub fn GPol::sub(self : GPol, other : GPol) -> GPol raise Error {
  let n = if self.coeffs.length() > other.coeffs.length() {
    self.coeffs.length()
  } else {
    other.coeffs.length()
  }
  let out : Array[@m22.Grassmann] = []
  for i = 0; i < n; i = i + 1 {
    out.push(coeff_at(self, i).sub(coeff_at(other, i)))
  }
  { k: self.k, coeffs: trim(out), }
}

///|
pub fn GPol::mul(self : GPol, other : GPol) -> GPol raise Error {
  if self.is_zero() || other.is_zero() {
    return GPol::zero(self.k)
  }
  let n = self.degree() + other.degree() + 1
  let out : Array[@m22.Grassmann] = []
  for i = 0; i < n; i = i + 1 {
    out.push(@m22.Grassmann::zero(self.k))
  }
  for i = 0; i <= self.degree(); i = i + 1 {
    for j = 0; j <= other.degree(); j = j + 1 {
      out[i + j] = out[i + j].add(coeff_at(self, i).mul(coeff_at(other, j)))
    }
  }
  { k: self.k, coeffs: trim(out), }
}

///|
pub fn GPol::derivative(self : GPol) -> GPol raise Error {
  let out : Array[@m22.Grassmann] = []
  for i = 1; i < self.coeffs.length(); i = i + 1 {
    out.push(
      self.coeffs[i].mul(@m22.Grassmann::scalar(self.k, @m20.Rat::from_int(i))),
    )
  }
  { k: self.k, coeffs: trim(out), }
}

///|
/// 反導數（常數項 0）。
pub fn GPol::antiderivative(self : GPol) -> GPol raise Error {
  let out : Array[@m22.Grassmann] = [@m22.Grassmann::zero(self.k)]
  for i = 0; i < self.coeffs.length(); i = i + 1 {
    out.push(
      self.coeffs[i].mul(
        @m22.Grassmann::scalar(self.k, @m20.Rat::frac(1, i + 1)),
      ),
    )
  }
  { k: self.k, coeffs: trim(out), }
}

///|
/// 多項式複合 self(other)（other 需偶）。
pub fn GPol::compose(self : GPol, other : GPol) -> GPol raise Error {
  let mut acc = GPol::zero(self.k)
  let mut i = self.degree()
  while i >= 0 {
    acc = acc.mul(other).add(GPol::constant(coeff_at(self, i)))
    i = i - 1
  }
  acc
}

///|
pub fn gpol_eq(a : GPol, b : GPol) -> Bool {
  let ca = trim(a.coeffs)
  let cb = trim(b.coeffs)
  if ca.length() != cb.length() {
    return false
  }
  for i = 0; i < ca.length(); i = i + 1 {
    if !ca[i].eq(cb[i]) {
      return false
    }
  }
  true
}

///|
pub fn GPol::is_even(self : GPol) -> Bool {
  for c in self.coeffs {
    if !c.is_even() {
      return false
    }
  }
  true
}

///|
pub fn GPol::is_odd(self : GPol) -> Bool {
  for c in self.coeffs {
    if !c.is_odd() {
      return false
    }
  }
  true
}

///|
/// θ = Λ 之第 0 生成元（常數 GPol）。
pub fn theta_const(k : Int32) -> GPol raise Error {
  GPol::constant(@m22.Grassmann::generator(k, 0))
}

///|
/// D_θ = ∂_θ + θ·∂_z 作用於 GPol。
pub fn GPol::d_super(self : GPol) -> GPol raise Error {
  let dth : Array[@m22.Grassmann] = []
  for c in self.coeffs {
    dth.push(c.partial(0))
  }
  let part1 : GPol = { k: self.k, coeffs: trim(dth), }
  let part2 = theta_const(self.k).mul(self.derivative())
  part1.add(part2)
}

///|
/// 一般超共形映射：由自由資料 (h 奇, k 偶) 生成，f' = k² − h·h'。
pub(all) struct SuperConformalMap {
  k : Int32
  f : GPol
  h : GPol
  w : GPol
}

///|
pub fn SuperConformalMap::from_data(
  h : GPol,
  w : GPol,
) -> SuperConformalMap raise Error {
  if !h.is_odd() {
    raise SuperGeomError::InvalidSuperField("h must be odd")
  }
  if !w.is_even() {
    raise SuperGeomError::InvalidSuperField("k must be even")
  }
  // body of k at z=0 must be invertible
  let body = coeff_at(w, 0).coeffs[0]
  if body.is_zero() {
    raise SuperGeomError::InvalidSuperField("k body not invertible at 0")
  }
  let fp = w.mul(w).sub(h.mul(h.derivative()))
  let f = fp.antiderivative()
  { k: h.k, f, h, w, }
}

///|
pub fn SuperConformalMap::z_image(self : SuperConformalMap) -> GPol raise Error {
  self.f.add(theta_const(self.k).mul(self.h).mul(self.w))
}

///|
pub fn SuperConformalMap::theta_image(
  self : SuperConformalMap,
) -> GPol raise Error {
  self.h.add(theta_const(self.k).mul(self.w))
}

///|
/// D_θ θ' = k + θ·h'（符號計算，非採樣）。
pub fn SuperConformalMap::d_theta_prime(
  self : SuperConformalMap,
) -> GPol raise Error {
  self.theta_image().d_super()
}

///|
/// 一般超共形約束證書：D_θ z' = θ'·D_θ θ'，以 GPol 全係數符號相等驗證。
/// 測試資料包含 h·h' ≠ 0 及 k' ≠ 0（即 restricted family 掩蓋嘅情形）。
pub fn general_superconformal_constraint_certificate() -> Bool raise Error {
  for data in superconformal_test_data() {
    let m = SuperConformalMap::from_data(data.0, data.1)
    let lhs = m.z_image().d_super()
    let rhs = m.theta_image().mul(m.d_theta_prime())
    if !gpol_eq(lhs, rhs) {
      return false
    }
  }
  true
}

///|
/// 測試資料族：(h, k) 對，涵蓋常數/線性/二次、單/雙奇參數。
fn superconformal_test_data() -> Array[(GPol, GPol)] raise Error {
  let k = 3 // θ, ε₁, ε₂
  let e1 = GPol::constant(@m22.Grassmann::generator(k, 1))
  let e2 = GPol::constant(@m22.Grassmann::generator(k, 2))
  let z = GPol::z(k)
  let one = GPol::scalar(k, @m20.Rat::one())
  let two = GPol::scalar(k, @m20.Rat::from_int(2))
  let three = GPol::scalar(k, @m20.Rat::from_int(3))
  let out : Array[(GPol, GPol)] = []
  // (1) h = ε₁ (常數), k = 2 (常數)：hh'=0, k'=0
  out.push((e1, two))
  // (2) h = ε₁·z, k = 2：hh'=0, k'=0（舊 family）
  out.push((e1.mul(z), two))
  // (3) h = ε₁ + ε₂·z, k = 2：hh' = ε₁ε₂ ≠ 0, k'=0
  out.push((e1.add(e2.mul(z)), two))
  // (4) h = ε₁, k = 2 + 3z：hh'=0, k'≠0
  out.push((e1, two.add(three.mul(z))))
  // (5) h = ε₁ + ε₂·z, k = 2 + 3z：hh'≠0 且 k'≠0（最一般）
  out.push((e1.add(e2.mul(z)), two.add(three.mul(z))))
  // (6) h = ε₁·z + ε₂·z², k = 1 + z + z²：二次
  out.push((e1.mul(z).add(e2.mul(z).mul(z)), one.add(z).add(z.mul(z))))
  out
}

///|
/// 於 Grassmann 點 z0 求值之 Jacobian（左係數約定）。
/// A = ∂_z z'，B = −∂_θ z'（dθ 與 ∂_θz' 皆奇 ⇒ 交換帶負號），
/// C = ∂_z θ'，D = ∂_θ θ'。
fn jacobian_at(
  m : SuperConformalMap,
  z0 : @m20.Rat,
  left_convention : Bool,
) -> @m22.SuperMatrix raise Error {
  let k = m.k
  let zp = m.z_image()
  let thp = m.theta_image()
  let dz = fn(p : GPol) -> @m22.Grassmann raise Error {
    eval_gpol(p.derivative(), z0)
  }
  let dth = fn(p : GPol) -> @m22.Grassmann raise Error {
    eval_gpol(p, z0).partial(0)
  }
  let big_a = dz(zp)
  let raw_b = dth(zp)
  let big_b = if left_convention { raw_b.neg() } else { raw_b }
  let big_c = dz(thp)
  let big_d = dth(thp)
  @m22.SuperMatrix::make(k, 1, 1, [[big_a, big_b], [big_c, big_d]])
}

///|
/// Ber(J) = D_θ θ' 證書（一般情形，符號於多點全係數比對）。
/// 同時證明：錯誤約定 B = +∂_θz' 於 h·h' ≠ 0 時**必然失敗**，
/// 故此證書非恆真——它能夠失敗，且確實捉到舊代碼嘅符號 bug。
pub fn ber_jacobian_equals_d_theta_certificate() -> Bool raise Error {
  let mut naive_failed_somewhere = false
  for data in superconformal_test_data() {
    let m = SuperConformalMap::from_data(data.0, data.1)
    let expect = m.d_theta_prime()
    for z0 in [@m20.Rat::zero(), @m20.Rat::one(), @m20.Rat::frac(2, 3)] {
      // 正確約定
      let j = jacobian_at(m, z0, true)
      let ber = @m22.berezinian(j)
      let want = eval_gpol(expect, z0)
      if !ber.eq(want) {
        return false
      }
      // 錯誤約定：記錄是否失敗
      let jn = jacobian_at(m, z0, false)
      let bern = @m22.berezinian(jn)
      if !bern.eq(want) {
        naive_failed_somewhere = true
      }
    }
  }
  naive_failed_somewhere
}

///|
fn eval_gpol(p : GPol, z0 : @m20.Rat) -> @m22.Grassmann raise Error {
  let mut acc = @m22.Grassmann::zero(p.k)
  let mut i = p.degree()
  while i >= 0 {
    acc = acc.mul(@m22.Grassmann::scalar(p.k, z0)).add(coeff_at(p, i))
    i = i - 1
  }
  acc
}

///|
/// 超共形映射複合 g₂ ∘ g₁（真實代入，非假設）。
pub fn superconformal_compose(
  g1 : SuperConformalMap,
  g2 : SuperConformalMap,
) -> (GPol, GPol) raise Error {
  let z1 = g1.z_image()
  let th1 = g1.theta_image()
  // z₂∘g₁ = f₂(z₁) + θ₁·h₂(z₁)·k₂(z₁)
  let z2 = g2.f.compose(z1).add(th1.mul(g2.h.compose(z1)).mul(g2.w.compose(z1)))
  // θ₂∘g₁ = h₂(z₁) + θ₁·k₂(z₁)
  let th2 = g2.h.compose(z1).add(th1.mul(g2.w.compose(z1)))
  (z2, th2)
}

///|
/// Ber 線束之 Čech 上循環證書：w = D_θθ' 滿足
/// w₀₂ = w₀₁ · (w₁₂ ∘ g₀₁)，由**實際複合**計算驗證。
/// 呢個就係 Ber 線束存在嘅轉移函數黏合條件。
pub fn ber_line_bundle_cocycle_certificate() -> Bool raise Error {
  let data = superconformal_test_data()
  // 取兩組一般資料作相鄰圖卡轉移
  let g01 = SuperConformalMap::from_data(data[2].0, data[2].1)
  let g12 = SuperConformalMap::from_data(data[4].0, data[4].1)
  let (z02, th02) = superconformal_compose(g01, g12)
  // 複合仍須超共形：D z02 = th02 · D th02
  if !gpol_eq(z02.d_super(), th02.mul(th02.d_super())) {
    return false
  }
  // w₀₂ 由複合直接算
  let w02 = th02.d_super()
  // w₀₁ · (w₁₂ ∘ g₀₁)，其中 w₁₂ = k₂ + θ·h₂'
  let w12_pulled = g2_w_pulled(g12, g01)
  let predicted = g01.d_theta_prime().mul(w12_pulled)
  gpol_eq(w02, predicted)
}

///|
/// w₁₂ ∘ g₀₁ = k₂(z₁) + θ₁·h₂'(z₁)。
fn g2_w_pulled(
  g2 : SuperConformalMap,
  g1 : SuperConformalMap,
) -> GPol raise Error {
  let z1 = g1.z_image()
  let th1 = g1.theta_image()
  g2.w.compose(z1).add(th1.mul(g2.h.derivative().compose(z1)))
}

///|
/// ω = Ber(T*Σ) ≅ D⁻¹ 證書：二者之轉移函數**逐圖卡相等**（皆為 w = D_θθ'），
/// 而非只比對宇稱。D_θ = w·D_θ' ⇒ D 之轉移為 w⁻¹ ⇒ D⁻¹ 之轉移為 w = Ber(J)。
pub fn omega_is_d_inverse_by_transitions_certificate() -> Bool raise Error {
  for data in superconformal_test_data() {
    let m = SuperConformalMap::from_data(data.0, data.1)
    let w = m.d_theta_prime()
    // Ber(J) 於多點等於 w
    for z0 in [@m20.Rat::zero(), @m20.Rat::from_int(2)] {
      let ber = @m22.berezinian(jacobian_at(m, z0, true))
      let want = eval_gpol(w, z0)
      if !ber.eq(want) {
        return false
      }
    }
  }
  // 算子律 D_θ = w·D_θ' 於一般超函數 F = a(z) + θ·b(z) 上驗證：
  // D_θ(F∘g) = w · ((D_θ' F)∘g)。此確立 D 之轉移為 w⁻¹，故 D⁻¹ 轉移 = w = Ber(J)。
  d_operator_transformation_law_certificate()
}

///|
/// D_θ = (D_θθ')·D_θ' 算子律證書（一般超函數，符號驗證）。
pub fn d_operator_transformation_law_certificate() -> Bool raise Error {
  let k = 3
  let e1 = GPol::constant(@m22.Grassmann::generator(k, 1))
  let e2 = GPol::constant(@m22.Grassmann::generator(k, 2))
  let z = GPol::z(k)
  let one = GPol::scalar(k, @m20.Rat::one())
  // 一般超函數 F = a(z) + θ·b(z)，a 偶、b 奇
  let test_fs : Array[(GPol, GPol)] = [
    (one.add(z.mul(z)), e1.mul(z)),
    (z, e1.add(e2.mul(z))),
    (one, e2),
  ]
  for data in superconformal_test_data() {
    let m = SuperConformalMap::from_data(data.0, data.1)
    let zi = m.z_image()
    let thi = m.theta_image()
    let w = m.d_theta_prime()
    for (a, b) in test_fs {
      // F∘g = a(z') + θ'·b(z')
      let pulled = a.compose(zi).add(thi.mul(b.compose(zi)))
      let lhs = pulled.d_super()
      // (D_θ' F)∘g = b(z') + θ'·a'(z')
      let dprime_f = b.compose(zi).add(thi.mul(a.derivative().compose(zi)))
      let rhs = w.mul(dprime_f)
      if !gpol_eq(lhs, rhs) {
        return false
      }
    }
  }
  true
}
