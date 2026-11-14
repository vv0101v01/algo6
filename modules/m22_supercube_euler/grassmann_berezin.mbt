///|
/// Module M22 (Part 2) — Grassmann Algebra & Berezinian: Λ(θ_1..θ_k) over ℚ
/// with signed wedge product, even/odd parity, nilpotent-series inversion of
/// even elements, and the superdeterminant Ber([[A,B],[C,D]]) =
/// det(A − B D⁻¹ C)·det(D)⁻¹ with A,D even and B,C odd.  Multiplicativity
/// Ber(XY) = Ber(X)Ber(Y) is verified exactly (it FAILS for commuting odd
/// entries — the supercommutative structure is essential).

///|
pub(all) suberror SuperError {
  InvalidSuperMatrix(String)
  InvalidGenerator(Int32)
  NonInvertibleBody
}

///|
/// Grassmann 代數元素：coeffs[S] = 子集 S（位元遮罩）之係數，維度 2^k。
pub(all) struct Grassmann {
  k : Int32
  coeffs : Array[@m20.Rat]
}

///|
pub fn Grassmann::zero(k : Int32) -> Grassmann {
  { k, coeffs: Array::make(1 << k, @m20.Rat::zero()), }
}

///|
pub fn Grassmann::scalar(k : Int32, c : @m20.Rat) -> Grassmann {
  let g = Grassmann::zero(k)
  g.coeffs[0] = c
  g
}

///|
pub fn Grassmann::generator(k : Int32, i : Int32) -> Grassmann raise Error {
  if i < 0 || i >= k {
    raise SuperError::InvalidGenerator(i)
  }
  let g = Grassmann::zero(k)
  g.coeffs[1 << i] = @m20.Rat::one()
  g
}

///|
pub fn Grassmann::add(
  self : Grassmann,
  other : Grassmann,
) -> Grassmann raise Error {
  if self.k != other.k {
    raise SuperError::InvalidSuperMatrix("Grassmann generator count mismatch")
  }
  let out = Grassmann::zero(self.k)
  for i = 0; i < self.coeffs.length(); i = i + 1 {
    out.coeffs[i] = self.coeffs[i].add(other.coeffs[i])
  }
  out
}

///|
pub fn Grassmann::sub(
  self : Grassmann,
  other : Grassmann,
) -> Grassmann raise Error {
  if self.k != other.k {
    raise SuperError::InvalidSuperMatrix("Grassmann generator count mismatch")
  }
  let out = Grassmann::zero(self.k)
  for i = 0; i < self.coeffs.length(); i = i + 1 {
    out.coeffs[i] = self.coeffs[i].sub(other.coeffs[i])
  }
  out
}

///|
pub fn Grassmann::neg(self : Grassmann) -> Grassmann {
  let out = Grassmann::zero(self.k)
  for i = 0; i < self.coeffs.length(); i = i + 1 {
    out.coeffs[i] = self.coeffs[i].neg()
  }
  out
}

///|
fn popcount(x : Int32) -> Int32 {
  let mut c = 0
  let mut v = x
  while v != 0 {
    c = c + (v & 1)
    v = v >> 1
  }
  c
}

///|
/// wedge 符號：θ_T ∧ θ_U = (−1)^{#{i∈T, j∈U, i>j}} θ_{T∪U}（T,U 不相交）。
fn wedge_sign(t : Int32, u : Int32) -> Int32 {
  // 對 t 中每個生成元 i，數 u 中比 i 細嘅生成元個數。
  // 用最低位元逐步剝離，唔再硬編生成元上限（舊版 i<16 喺 k≥17 時漏算）。
  let mut inv = 0
  let mut bits = t
  while bits != 0 {
    let low = bits & bits.neg()
    inv = inv + popcount(u & (low - 1))
    bits = bits ^ low
  }
  if inv % 2 == 0 {
    1
  } else {
    -1
  }
}

///|
pub fn Grassmann::mul(
  self : Grassmann,
  other : Grassmann,
) -> Grassmann raise Error {
  if self.k != other.k {
    raise SuperError::InvalidSuperMatrix("Grassmann generator count mismatch")
  }
  let out = Grassmann::zero(self.k)
  for t = 0; t < self.coeffs.length(); t = t + 1 {
    if self.coeffs[t].is_zero() {
      continue
    }
    for u = 0; u < other.coeffs.length(); u = u + 1 {
      if other.coeffs[u].is_zero() || (t & u) != 0 {
        continue
      }
      let s = t | u
      let sign = wedge_sign(t, u)
      let term = self.coeffs[t]
        .mul(other.coeffs[u])
        .mul(@m20.Rat::from_int(sign))
      out.coeffs[s] = out.coeffs[s].add(term)
    }
  }
  out
}

///|
/// 奇導數 ∂/∂θ_i：∂_i(θ_S) = (−1)^{#{j∈S : j<i}} θ_{S\{i}}（i∉S 時為 0）。
pub fn Grassmann::partial(self : Grassmann, i : Int32) -> Grassmann raise Error {
  if i < 0 || i >= self.k {
    raise SuperError::InvalidGenerator(i)
  }
  let out = Grassmann::zero(self.k)
  let bit = 1 << i
  for s = 0; s < self.coeffs.length(); s = s + 1 {
    if (s & bit) == 0 || self.coeffs[s].is_zero() {
      continue
    }
    let lower = s & (bit - 1)
    let sign = if popcount(lower) % 2 == 0 {
      @m20.Rat::one()
    } else {
      @m20.Rat::from_int(-1)
    }
    let t = s ^ bit
    out.coeffs[t] = out.coeffs[t].add(self.coeffs[s].mul(sign))
  }
  out
}

///|
/// Grassmann 元素相等（全係數）。
pub fn Grassmann::eq(self : Grassmann, other : Grassmann) -> Bool {
  if self.k != other.k {
    return false
  }
  for i = 0; i < self.coeffs.length(); i = i + 1 {
    if self.coeffs[i] != other.coeffs[i] {
      return false
    }
  }
  true
}

///|
pub fn Grassmann::is_zero(self : Grassmann) -> Bool {
  for c in self.coeffs {
    if !c.is_zero() {
      return false
    }
  }
  true
}

///|
pub fn Grassmann::is_even(self : Grassmann) -> Bool {
  for s = 0; s < self.coeffs.length(); s = s + 1 {
    if !self.coeffs[s].is_zero() && popcount(s) % 2 != 0 {
      return false
    }
  }
  true
}

///|
pub fn Grassmann::is_odd(self : Grassmann) -> Bool {
  for s = 0; s < self.coeffs.length(); s = s + 1 {
    if !self.coeffs[s].is_zero() && popcount(s) % 2 != 1 {
      return false
    }
  }
  true
}

///|
/// 偶元素求逆（body ≠ 0）：a = body·(1+n)，a⁻¹ = body⁻¹ Σ (−n)^j（冪零級數）。
pub fn Grassmann::inv_even(self : Grassmann) -> Grassmann raise Error {
  let body = self.coeffs[0]
  if body.is_zero() {
    raise SuperError::NonInvertibleBody
  }
  let body_inv = body.inv()
  // n = (a − body)/body
  let nil = Grassmann::zero(self.k)
  for s = 1; s < self.coeffs.length(); s = s + 1 {
    nil.coeffs[s] = self.coeffs[s].mul(body_inv)
  }
  // sum = 1 − n + n² − ...
  let mut sum = Grassmann::scalar(self.k, @m20.Rat::one())
  let mut term = Grassmann::scalar(self.k, @m20.Rat::one())
  let mut j = 1
  while j <= self.k + 1 {
    term = term.mul(nil).neg()
    if term.is_zero() {
      break
    }
    sum = sum.add(term)
    j = j + 1
  }
  // multiply by body_inv
  let out = Grassmann::zero(self.k)
  for s = 0; s < self.coeffs.length(); s = s + 1 {
    out.coeffs[s] = sum.coeffs[s].mul(body_inv)
  }
  out
}

///|
/// 超矩陣 [[A,B],[C,D]]：A p×p 偶、D q×q 偶、B p×q 奇、C q×p 奇。
pub(all) struct SuperMatrix {
  k : Int32
  p : Int32
  q : Int32
  entries : Array[Array[Grassmann]]
}

///|
pub fn SuperMatrix::make(
  k : Int32,
  p : Int32,
  q : Int32,
  entries : Array[Array[Grassmann]],
) -> SuperMatrix raise Error {
  let n = p + q
  if entries.length() != n {
    raise SuperError::InvalidSuperMatrix("rows")
  }
  for i = 0; i < n; i = i + 1 {
    if entries[i].length() != n {
      raise SuperError::InvalidSuperMatrix("cols")
    }
    for j = 0; j < n; j = j + 1 {
      let even_block = (i < p && j < p) || (i >= p && j >= p)
      if even_block && !entries[i][j].is_even() {
        raise SuperError::InvalidSuperMatrix("even block has odd entry")
      }
      if !even_block && !entries[i][j].is_odd() {
        raise SuperError::InvalidSuperMatrix("odd block has even entry")
      }
    }
  }
  { k, p, q, entries, }
}

///|
/// 偶方陣行列式（Leibniz 公式，Λ_0 交換）。
fn det_even(m : Array[Array[Grassmann]], k : Int32) -> Grassmann raise Error {
  let n = m.length()
  if n == 0 {
    return Grassmann::scalar(k, @m20.Rat::one())
  }
  // permutations via recursion
  let mut acc = Grassmann::zero(k)
  let perm = Array::make(n, 0)
  let used = Array::make(n, false)
  fn rec(pos : Int32, sign : Int32) -> Unit raise Error {
    if pos == n {
      let mut prod = Grassmann::scalar(k, @m20.Rat::from_int(sign))
      for i = 0; i < n; i = i + 1 {
        prod = prod.mul(m[i][perm[i]])
      }
      acc = acc.add(prod)
      return
    }
    for v = 0; v < n; v = v + 1 {
      if used[v] {
        continue
      }
      used[v] = true
      perm[pos] = v
      // sign flips by number of used values < v ... use inversion parity of perm prefix
      let mut inv = 0
      for i = 0; i < pos; i = i + 1 {
        if perm[i] > v {
          inv = inv + 1
        }
      }
      let ns = if inv % 2 == 0 { sign } else { -sign }
      rec(pos + 1, ns)
      used[v] = false
    }
  }
  rec(0, 1)
  acc
}

///|
/// Berezinian Ber(X) = det(A − B D⁻¹ C) · det(D)⁻¹。
pub fn berezinian(x : SuperMatrix) -> Grassmann raise Error {
  let p = x.p
  let q = x.q
  // D block
  let d : Array[Array[Grassmann]] = []
  for i = 0; i < q; i = i + 1 {
    let row : Array[Grassmann] = []
    for j = 0; j < q; j = j + 1 {
      row.push(x.entries[p + i][p + j])
    }
    d.push(row)
  }
  let det_d = det_even(d, x.k)
  let det_d_inv = det_d.inv_even()
  // D⁻¹ via adjugate for small q (use solve over even ring via nilpotent inverse)
  let d_inv = mat_even_inverse(d, x.k)
  // A − B D⁻¹ C
  let schur : Array[Array[Grassmann]] = []
  for i = 0; i < p; i = i + 1 {
    let row : Array[Grassmann] = []
    for j = 0; j < p; j = j + 1 {
      let mut s = x.entries[i][j]
      for a = 0; a < q; a = a + 1 {
        for b = 0; b < q; b = b + 1 {
          // B[i,a] D⁻¹[a,b] C[b,j]
          let t = x.entries[i][p + a].mul(d_inv[a][b]).mul(x.entries[p + b][j])
          s = s.sub(t)
        }
      }
      row.push(s)
    }
    schur.push(row)
  }
  let det_schur = det_even(schur, x.k)
  det_schur.mul(det_d_inv)
}

///|
/// 偶矩陣逆（高斯消元於 Λ_0，主元 body 可逆）。
fn mat_even_inverse(
  m : Array[Array[Grassmann]],
  k : Int32,
) -> Array[Array[Grassmann]] raise Error {
  let n = m.length()
  // augment [m | I]
  let aug : Array[Array[Grassmann]] = []
  for i = 0; i < n; i = i + 1 {
    let row : Array[Grassmann] = []
    for j = 0; j < n; j = j + 1 {
      row.push(m[i][j])
    }
    for j = 0; j < n; j = j + 1 {
      row.push(
        if i == j {
          Grassmann::scalar(k, @m20.Rat::one())
        } else {
          Grassmann::zero(k)
        },
      )
    }
    aug.push(row)
  }
  for c = 0; c < n; c = c + 1 {
    // pivot
    let piv_inv = aug[c][c].inv_even()
    for j = 0; j < 2 * n; j = j + 1 {
      aug[c][j] = aug[c][j].mul(piv_inv)
    }
    for i = 0; i < n; i = i + 1 {
      if i == c {
        continue
      }
      let f = aug[i][c]
      for j = 0; j < 2 * n; j = j + 1 {
        aug[i][j] = aug[i][j].sub(f.mul(aug[c][j]))
      }
    }
  }
  let inv : Array[Array[Grassmann]] = []
  for i = 0; i < n; i = i + 1 {
    let row : Array[Grassmann] = []
    for j = 0; j < n; j = j + 1 {
      row.push(aug[i][n + j])
    }
    inv.push(row)
  }
  inv
}

///|
pub fn supermatrix_mul(
  x : SuperMatrix,
  y : SuperMatrix,
) -> SuperMatrix raise Error {
  let n = x.p + x.q
  let entries : Array[Array[Grassmann]] = []
  for i = 0; i < n; i = i + 1 {
    let row : Array[Grassmann] = []
    for j = 0; j < n; j = j + 1 {
      let mut s = Grassmann::zero(x.k)
      for t = 0; t < n; t = t + 1 {
        s = s.add(x.entries[i][t].mul(y.entries[t][j]))
      }
      row.push(s)
    }
    entries.push(row)
  }
  SuperMatrix::make(x.k, x.p, x.q, entries)
}

///|
/// Berezinian 乘法性證書：Ber(XY) = Ber(X)·Ber(Y)（精確 Grassmann 相等）。
pub fn berezinian_multiplicative(
  x : SuperMatrix,
  y : SuperMatrix,
) -> Bool raise Error {
  let xy = supermatrix_mul(x, y)
  let lhs = berezinian(xy)
  let rhs = berezinian(x).mul(berezinian(y))
  for i = 0; i < lhs.coeffs.length(); i = i + 1 {
    if lhs.coeffs[i] != rhs.coeffs[i] {
      return false
    }
  }
  true
}

///|
/// 超矩陣相等（同 k,p,q 且全 Grassmann 係數相等）。
pub fn SuperMatrix::eq(self : SuperMatrix, other : SuperMatrix) -> Bool {
  if self.k != other.k || self.p != other.p || self.q != other.q {
    return false
  }
  let n = self.p + self.q
  for i = 0; i < n; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      if !self.entries[i][j].eq(other.entries[i][j]) {
        return false
      }
    }
  }
  true
}
