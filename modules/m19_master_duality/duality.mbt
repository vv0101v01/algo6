///|
/// Module M19 (Part 2) — Dualities: exact rational LP strong-duality /
/// complementary-slackness certificates, Markov process duality functions
/// (W H = H Vᵀ), and Kramers–Wannier involution t* = (1−t)/(1+t) with self-dual
/// critical polynomial t² + 2t − 1 (t_c = √2 − 1).  KW duality is the
/// non-invertible Ising categorical symmetry (bridges M15 RG and M17).
/// 局部公理（伽羅瓦對應）之最佳化實例：原始—對偶弱對偶夾擠。

///|
pub(all) suberror DualityError {
  InvalidLP(String)
  InvalidDuality(String)
}

///|
pub(all) struct LPDualityCertificate {
  primal_feasible : Bool
  dual_feasible : Bool
  /// 強對偶：cᵀx = bᵀy
  strong_duality : Bool
  /// 互補鬆弛：x_j(Aᵀy−c)_j = 0 且 y_i(b−Ax)_i = 0
  complementary_slackness : Bool
  objective : @m20.Rat
}

///|
/// 原始 max cᵀx s.t. Ax ≤ b, x ≥ 0；對偶 min bᵀy s.t. Aᵀy ≥ c, y ≥ 0。
/// 給定可行 x,y 且目標相等 ⟹ 两者皆最優（弱對偶夾擠 cᵀx ≤ yᵀAx ≤ bᵀy）。
pub fn lp_duality_certificate(
  a : @m20.RatMatrix,
  b : Array[@m20.Rat],
  c : Array[@m20.Rat],
  x : Array[@m20.Rat],
  y : Array[@m20.Rat],
) -> LPDualityCertificate raise Error {
  let m = a.rows
  let n = a.cols
  if b.length() != m || c.length() != n || x.length() != n || y.length() != m {
    raise DualityError::InvalidLP("shape")
  }
  let ax = a.mul_vec(x)
  let aty = a.transpose().mul_vec(y)
  let mut primal_ok = true
  let mut dual_ok = true
  let mut cs_ok = true
  for i = 0; i < m; i = i + 1 {
    if y[i].sign() < 0 {
      dual_ok = false
    }
    let slack = b[i].sub(ax[i])
    if slack.sign() < 0 {
      primal_ok = false
    }
    // y_i (b − Ax)_i = 0
    if !y[i].mul(slack).is_zero() {
      cs_ok = false
    }
  }
  for j = 0; j < n; j = j + 1 {
    if x[j].sign() < 0 {
      primal_ok = false
    }
    let surplus = aty[j].sub(c[j])
    if surplus.sign() < 0 {
      dual_ok = false
    }
    // x_j (Aᵀy − c)_j = 0
    if !x[j].mul(surplus).is_zero() {
      cs_ok = false
    }
  }
  let mut obj_p = @m20.Rat::zero()
  for j = 0; j < n; j = j + 1 {
    obj_p = obj_p.add(c[j].mul(x[j]))
  }
  let mut obj_d = @m20.Rat::zero()
  for i = 0; i < m; i = i + 1 {
    obj_d = obj_d.add(b[i].mul(y[i]))
  }
  {
    primal_feasible: primal_ok,
    dual_feasible: dual_ok,
    strong_duality: obj_p == obj_d,
    complementary_slackness: cs_ok,
    objective: obj_p,
  }
}

///|
/// Markov 對偶證書：W H = H Vᵀ，即 Σ_x' W(x,x')H(x',y) = Σ_y' H(x,y')V(y,y')。
pub fn markov_duality_certificate(
  w : @m20.RatMatrix,
  v : @m20.RatMatrix,
  h : @m20.RatMatrix,
) -> Bool raise Error {
  if w.cols != h.rows || h.cols != v.rows {
    raise DualityError::InvalidDuality("shape")
  }
  let lhs = w.mul(h)
  let rhs = h.mul(v.transpose())
  for i = 0; i < lhs.data.length(); i = i + 1 {
    if lhs.data[i] != rhs.data[i] {
      return false
    }
  }
  true
}

///|
/// Kramers–Wannier 對偶 t* = (1−t)/(1+t)（t = tanh K）。
pub fn kw_dual(t : @m20.Rat) -> @m20.Rat raise Error {
  let denom = @m20.Rat::one().add(t)
  if denom.is_zero() {
    raise DualityError::InvalidDuality("KW singular at t=-1")
  }
  @m20.Rat::one().sub(t).div(denom)
}

///|
/// KW 對合證書：t** = t（對任意 t ≠ ±1）。
pub fn kw_involution_certificate(t : @m20.Rat) -> Bool raise Error {
  let d1 = kw_dual(t)
  let d2 = kw_dual(d1)
  d2 == t
}

///|
/// 自對偶臨界多項式：t = t* ⟺ t² + 2t − 1 = 0（正根 t_c = √2 − 1）。
/// 回傳多項式係數 [−1, 2, 1]（低次→高次）。
pub fn kw_self_dual_poly() -> Array[Int32] {
  [-1, 2, 1]
}

///|
/// 自對偶條件證書：t² + 2t − 1 之判別式 = 8，正根為 √2−1（於 ℚ(√2)）。
/// 此處驗證臨界多項式與 KW 不動點方程 t(1+t) = 1−t 之代數等價。
pub fn kw_self_dual_equation_certificate(t : @m20.Rat) -> Bool raise Error {
  // t = kw_dual(t) ⟺ t(1+t) = 1−t ⟺ t²+2t−1 = 0
  let lhs = t.mul(@m20.Rat::one().add(t))
  let rhs = @m20.Rat::one().sub(t)
  let poly = t.mul(t).add(t.mul(@m20.Rat::from_int(2))).sub(@m20.Rat::one())
  (lhs == rhs) == poly.is_zero()
}
