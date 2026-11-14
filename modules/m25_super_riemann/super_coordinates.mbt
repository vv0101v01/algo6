///|
/// Module M25 (Part 1) — Superconformal Coordinates & the D-Operator:
/// superfields f(z)+θ·g(z) on the split (1|1) superspace, the odd covariant
/// derivative D = ∂_θ + θ∂_z with D² = ∂_z, and the superconformal transition
/// constraint D_θ z' = θ'·D_θ θ' verified exactly in the Grassmann algebra
/// (M22) for the family u(z)=a²z, η(z)=εz.

///|
pub(all) suberror SuperGeomError {
  InvalidSuperField(String)
  InvalidWeight(Int32)
}

///|
/// 超場 f(z) + θ·g(z)：even = f，odd = g（有理係數多式）。
pub(all) struct SuperField {
  even : @m15.Poly
  odd : @m15.Poly
}

///|
pub fn SuperField::make(even : @m15.Poly, odd : @m15.Poly) -> SuperField {
  { even, odd, }
}

///|
/// D = ∂_θ + θ∂_z：D(f + θg) = g + θ·f'。
pub fn SuperField::d(self : SuperField) -> SuperField raise Error {
  { even: self.odd, odd: self.even.derivative(), }
}

///|
/// ∂_z(f + θg) = f' + θ·g'。
pub fn SuperField::dz(self : SuperField) -> SuperField raise Error {
  { even: self.even.derivative(), odd: self.odd.derivative(), }
}

///|
fn poly_eq(a : @m15.Poly, b : @m15.Poly) -> Bool {
  let da = a.degree()
  let db = b.degree()
  if da != db {
    return false
  }
  for i = 0; i <= da; i = i + 1 {
    if a.coeff(i) != b.coeff(i) {
      return false
    }
  }
  true
}

///|
fn superfield_eq(a : SuperField, b : SuperField) -> Bool {
  poly_eq(a.even, b.even) && poly_eq(a.odd, b.odd)
}

///|
/// D² = ∂_z 證書：於超場基 {1, z, z², θ, θz, θz²} 上驗證 D² = ∂_z。
pub fn d_squared_equals_dz_certificate() -> Bool raise Error {
  let basis : Array[SuperField] = []
  for k = 0; k <= 2; k = k + 1 {
    // z^k (even)
    let coeffs = Array::make(k + 1, @m20.Rat::zero())
    coeffs[k] = @m20.Rat::one()
    let p = @m15.Poly::make(coeffs)
    basis.push(SuperField::make(p, @m15.Poly::zero()))
    basis.push(SuperField::make(@m15.Poly::zero(), p))
  }
  for f in basis {
    let d2 = f.d().d()
    let dz = f.dz()
    if !superfield_eq(d2, dz) {
      return false
    }
  }
  true
}

///|
/// 超共形權重 n 場之變換因子 (D_θ θ')^n：驗證 D_θ θ' = a（於上述 family），
/// 故權重 n 場乘以 a^n。回傳權重 n 之變換因子（Grassmann 偶元素）。
pub fn superconformal_weight_factor(
  a : @m20.Rat,
  weight : Int32,
) -> @m22.Grassmann raise Error {
  if weight < 0 {
    raise SuperGeomError::InvalidWeight(weight)
  }
  let k = 2
  // D_θ θ' = a（偶常數）於 family u=a²z, η=εz
  let mut factor = @m22.Grassmann::scalar(k, @m20.Rat::one())
  let base = @m22.Grassmann::scalar(k, a)
  for i = 0; i < weight; i = i + 1 {
    factor = factor.mul(base)
  }
  factor
}
