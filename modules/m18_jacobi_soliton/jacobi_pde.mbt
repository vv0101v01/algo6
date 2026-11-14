///|
/// Module M18 (Part 1) — Exact Multivariate PDE Calculus & the Jacobi-Bundle
/// Identity: sparse ℚ[x_1..x_n] polynomials, Jacobi structures (Λ, E) with
/// bracket {f,g} = Λ(df,dg) + f·E(g) − g·E(f), the Schouten–Nijenhuis structure
/// equations [Λ,Λ] = 2E∧Λ and [E,Λ] = 0, and a convention-free direct Jacobi
/// identity certificate on a monomial spanning set.  Bi-Hamiltonian
/// compatibility bridges to the Hirota soliton calculus in Part 2.

///|
pub(all) suberror JacobiError {
  InvalidStructure(String)
  NotAntisymmetric
  JacobiViolation
}

///|
fn mono_cmp(a : Array[Int32], b : Array[Int32]) -> Int32 {
  let n = if a.length() < b.length() { a.length() } else { b.length() }
  for i = 0; i < n; i = i + 1 {
    if a[i] != b[i] {
      return if a[i] < b[i] { -1 } else { 1 }
    }
  }
  if a.length() == b.length() {
    0
  } else if a.length() < b.length() {
    -1
  } else {
    1
  }
}

///|
fn mono_eq(a : Array[Int32], b : Array[Int32]) -> Bool {
  mono_cmp(a, b) == 0
}

///|
/// 稀疏多項式：terms 依單項式字典序排序、同類合併、無零係數（典範唯一形）。
pub(all) struct MPoly {
  nvars : Int32
  terms : Array[(Array[Int32], @m20.Rat)]
}

///|
fn normalize(
  nvars : Int32,
  raw : Array[(Array[Int32], @m20.Rat)],
) -> MPoly raise Error {
  // insertion sort by monomial
  let a = raw.copy()
  for i = 1; i < a.length(); i = i + 1 {
    let x = a[i]
    let mut j = i
    while j > 0 && mono_cmp(a[j - 1].0, x.0) > 0 {
      a[j] = a[j - 1]
      j = j - 1
    }
    a[j] = x
  }
  let out : Array[(Array[Int32], @m20.Rat)] = []
  for t in a {
    let (m, c) = t
    if c.is_zero() {
      continue
    }
    if out.length() > 0 && mono_eq(out[out.length() - 1].0, m) {
      let (pm, pc) = out[out.length() - 1]
      out[out.length() - 1] = (pm, pc.add(c))
    } else {
      out.push((m, c))
    }
  }
  // drop newly-zeroed
  let normed : Array[(Array[Int32], @m20.Rat)] = []
  for t in out {
    if !t.1.is_zero() {
      normed.push(t)
    }
  }
  { nvars, terms: normed, }
}

///|
pub fn MPoly::zero(nvars : Int32) -> MPoly {
  { nvars, terms: [], }
}

///|
pub fn MPoly::constant(nvars : Int32, c : @m20.Rat) -> MPoly raise Error {
  normalize(nvars, [(Array::make(nvars, 0), c)])
}

///|
pub fn MPoly::coord(nvars : Int32, i : Int32) -> MPoly raise Error {
  let e = Array::make(nvars, 0)
  e[i] = 1
  normalize(nvars, [(e, @m20.Rat::one())])
}

///|
pub fn MPoly::is_zero(self : MPoly) -> Bool {
  self.terms.length() == 0
}

///|
pub fn MPoly::add(self : MPoly, other : MPoly) -> MPoly raise Error {
  let raw = self.terms.copy()
  for t in other.terms {
    raw.push(t)
  }
  normalize(self.nvars, raw)
}

///|
pub fn MPoly::neg(self : MPoly) -> MPoly raise Error {
  let raw : Array[(Array[Int32], @m20.Rat)] = []
  for t in self.terms {
    raw.push((t.0, t.1.neg()))
  }
  normalize(self.nvars, raw)
}

///|
pub fn MPoly::sub(self : MPoly, other : MPoly) -> MPoly raise Error {
  self.add(other.neg())
}

///|
pub fn MPoly::scale(self : MPoly, s : @m20.Rat) -> MPoly raise Error {
  let raw : Array[(Array[Int32], @m20.Rat)] = []
  for t in self.terms {
    raw.push((t.0, t.1.mul(s)))
  }
  normalize(self.nvars, raw)
}

///|
pub fn MPoly::mul(self : MPoly, other : MPoly) -> MPoly raise Error {
  let raw : Array[(Array[Int32], @m20.Rat)] = []
  for ta in self.terms {
    for tb in other.terms {
      let e = Array::make(self.nvars, 0)
      for i = 0; i < self.nvars; i = i + 1 {
        e[i] = ta.0[i] + tb.0[i]
      }
      raw.push((e, ta.1.mul(tb.1)))
    }
  }
  normalize(self.nvars, raw)
}

///|
pub fn MPoly::partial(self : MPoly, i : Int32) -> MPoly raise Error {
  let raw : Array[(Array[Int32], @m20.Rat)] = []
  for t in self.terms {
    let (e, c) = t
    if e[i] > 0 {
      let ne = e.copy()
      ne[i] = ne[i] - 1
      raw.push((ne, c.mul(@m20.Rat::from_int(e[i]))))
    }
  }
  normalize(self.nvars, raw)
}

///|
pub fn MPoly::eq_poly(self : MPoly, other : MPoly) -> Bool {
  if self.terms.length() != other.terms.length() {
    return false
  }
  for i = 0; i < self.terms.length(); i = i + 1 {
    if !mono_eq(self.terms[i].0, other.terms[i].0) ||
      self.terms[i].1 != other.terms[i].1 {
      return false
    }
  }
  true
}

///|
/// 雅可比結構 (Λ, E)：Λ 反對稱雙向量場、E 向量場（係數多項式）。
pub(all) struct JacobiStructure {
  nvars : Int32
  lambda : Array[Array[MPoly]]
  e : Array[MPoly]
}

///|
pub fn JacobiStructure::make(
  nvars : Int32,
  lambda : Array[Array[MPoly]],
  e : Array[MPoly],
) -> JacobiStructure raise Error {
  if lambda.length() != nvars || e.length() != nvars {
    raise JacobiError::InvalidStructure("shape")
  }
  for i = 0; i < nvars; i = i + 1 {
    if lambda[i].length() != nvars {
      raise JacobiError::InvalidStructure("row shape")
    }
    for j = 0; j < nvars; j = j + 1 {
      // antisymmetry Λ^{ij} = −Λ^{ji}
      if !lambda[i][j].eq_poly(lambda[j][i].neg()) {
        raise JacobiError::NotAntisymmetric
      }
    }
  }
  { nvars, lambda, e, }
}

///|
/// E(g) = Σ_i E^i ∂_i g。
pub fn JacobiStructure::e_apply(
  self : JacobiStructure,
  g : MPoly,
) -> MPoly raise Error {
  let mut acc = MPoly::zero(self.nvars)
  for i = 0; i < self.nvars; i = i + 1 {
    acc = acc.add(self.e[i].mul(g.partial(i)))
  }
  acc
}

///|
/// 雅可比括號 {f,g} = Σ_{ij} Λ^{ij} ∂_i f ∂_j g + f·E(g) − g·E(f)。
pub fn JacobiStructure::bracket(
  self : JacobiStructure,
  f : MPoly,
  g : MPoly,
) -> MPoly raise Error {
  let mut acc = MPoly::zero(self.nvars)
  for i = 0; i < self.nvars; i = i + 1 {
    for j = 0; j < self.nvars; j = j + 1 {
      if !self.lambda[i][j].is_zero() {
        acc = acc.add(self.lambda[i][j].mul(f.partial(i)).mul(g.partial(j)))
      }
    }
  }
  acc = acc.add(f.mul(self.e_apply(g)))
  acc = acc.sub(g.mul(self.e_apply(f)))
  acc
}

///|
/// 直接雅可比恆等式證書（無約定依賴）：對單項式 spanning set（次數 ≤ 2 含常數）
/// 之全部三元組驗證 {f,{g,h}} + {g,{h,f}} + {h,{f,g}} = 0。
pub fn JacobiStructure::jacobi_identity_certificate(
  self : JacobiStructure,
) -> Bool raise Error {
  let basis = monomial_basis(self.nvars, 2)
  for f in basis {
    for g in basis {
      for h in basis {
        let t1 = self.bracket(f, self.bracket(g, h))
        let t2 = self.bracket(g, self.bracket(h, f))
        let t3 = self.bracket(h, self.bracket(f, g))
        let s = t1.add(t2).add(t3)
        if !s.is_zero() {
          return false
        }
      }
    }
  }
  true
}

///|
/// 次數 ≤ deg 之全部單項式（含常數 1）。
pub fn monomial_basis(nvars : Int32, deg : Int32) -> Array[MPoly] raise Error {
  let out : Array[MPoly] = []
  let exps = Array::make(nvars, 0)
  fn rec(pos : Int32, remaining : Int32) -> Unit raise Error {
    if pos == nvars {
      out.push(normalize(nvars, [(exps.copy(), @m20.Rat::one())]))
      return
    }
    for e = 0; e <= remaining; e = e + 1 {
      exps[pos] = e
      rec(pos + 1, remaining - e)
    }
    exps[pos] = 0
  }
  rec(0, deg)
  out
}

///|
/// Schouten 自括號 [Λ,Λ]^{ijk} = Σ_l (Λ^{il}∂_l Λ^{jk} + Λ^{jl}∂_l Λ^{ki} + Λ^{kl}∂_l Λ^{ij})。
pub fn JacobiStructure::schouten_self(
  self : JacobiStructure,
  i : Int32,
  j : Int32,
  k : Int32,
) -> MPoly raise Error {
  let mut acc = MPoly::zero(self.nvars)
  for l = 0; l < self.nvars; l = l + 1 {
    let t1 = self.lambda[i][l].mul(self.lambda[j][k].partial(l))
    let t2 = self.lambda[j][l].mul(self.lambda[k][i].partial(l))
    let t3 = self.lambda[k][l].mul(self.lambda[i][j].partial(l))
    acc = acc.add(t1).add(t2).add(t3)
  }
  acc
}

///|
/// (E∧Λ)^{ijk} = E^i Λ^{jk} + E^j Λ^{ki} + E^k Λ^{ij}。
pub fn JacobiStructure::e_wedge_lambda(
  self : JacobiStructure,
  i : Int32,
  j : Int32,
  k : Int32,
) -> MPoly raise Error {
  self.e[i]
  .mul(self.lambda[j][k])
  .add(self.e[j].mul(self.lambda[k][i]))
  .add(self.e[k].mul(self.lambda[i][j]))
}

///|
/// [E,Λ]^{ij} = Σ_l (E^l ∂_l Λ^{ij} − Λ^{il} ∂_l E^j − Λ^{lj} ∂_l E^i)（L_E Λ）。
pub fn JacobiStructure::lie_derivative_lambda(
  self : JacobiStructure,
  i : Int32,
  j : Int32,
) -> MPoly raise Error {
  let mut acc = MPoly::zero(self.nvars)
  for l = 0; l < self.nvars; l = l + 1 {
    let t1 = self.e[l].mul(self.lambda[i][j].partial(l))
    let t2 = self.lambda[i][l].mul(self.e[j].partial(l))
    let t3 = self.lambda[l][j].mul(self.e[i].partial(l))
    acc = acc.add(t1).sub(t2).sub(t3)
  }
  acc
}

///|
/// 結構方程證書：[Λ,Λ] = 2E∧Λ 且 [E,Λ] = 0（逐分量多項式恆等式）。
pub fn JacobiStructure::structure_equations_certificate(
  self : JacobiStructure,
) -> Bool raise Error {
  for i = 0; i < self.nvars; i = i + 1 {
    for j = i + 1; j < self.nvars; j = j + 1 {
      if !self.lie_derivative_lambda(i, j).is_zero() {
        return false
      }
      for k = j + 1; k < self.nvars; k = k + 1 {
        // 約定 {f,g}=Λ(df,dg)+fE(g)−gE(f) 下結構方程為 [Λ,Λ] = −2E∧Λ，
        // 即 schouten_self = −(E∧Λ)（與直接雅可比證書一致）。
        let lhs = self.schouten_self(i, j, k)
        let rhs = self.e_wedge_lambda(i, j, k)
        if !lhs.eq_poly(rhs.neg()) {
          return false
        }
      }
    }
  }
  true
}

///|
/// so(3) Lie–Poisson：Λ^{ij} = ε^{ijk} x_k，E = 0。
pub fn so3_lie_poisson() -> JacobiStructure raise Error {
  let n = 3
  let x = MPoly::coord(n, 0)
  let y = MPoly::coord(n, 1)
  let z = MPoly::coord(n, 2)
  let zero = MPoly::zero(n)
  let lam : Array[Array[MPoly]] = [
    [zero, z, y.neg()],
    [z.neg(), zero, x],
    [y, x.neg(), zero],
  ]
  JacobiStructure::make(n, lam, [zero, zero, zero])
}

///|
/// 平凡非泊松雅可比結構：Λ = 0，E = ∂_x（括號 {f,g} = f ∂_x g − g ∂_x f）。
pub fn trivial_jacobi() -> JacobiStructure raise Error {
  let n = 2
  let zero = MPoly::zero(n)
  let lam : Array[Array[MPoly]] = [[zero, zero], [zero, zero]]
  JacobiStructure::make(n, lam, [MPoly::constant(n, @m20.Rat::one()), zero])
}

///|
/// ℝ³ 切觸結構 η = dz − y dx 之雅可比結構：Λ = (∂_x + y∂_z)∧∂_y，E = ∂_z。
pub fn contact_jacobi() -> JacobiStructure raise Error {
  let n = 3
  let zero = MPoly::zero(n)
  let one = MPoly::constant(n, @m20.Rat::one())
  let y = MPoly::coord(n, 1)
  // Λ^{xy}=1, Λ^{yz}=−y, Λ^{xz}=0
  let lam : Array[Array[MPoly]] = [
    [zero, one, zero],
    [one.neg(), zero, y.neg()],
    [zero, y, zero],
  ]
  JacobiStructure::make(n, lam, [zero, zero, one])
}

///|
/// 雙哈密頓相容性：π1, π2（皆 E=0 泊松）相容 iff π1+π2 仍泊松（[π1,π2]=0）。
pub fn bihamiltonian_compatible(
  p1 : JacobiStructure,
  p2 : JacobiStructure,
) -> Bool raise Error {
  if p1.nvars != p2.nvars {
    return false
  }
  let sum : Array[Array[MPoly]] = []
  for i = 0; i < p1.nvars; i = i + 1 {
    let row : Array[MPoly] = []
    for j = 0; j < p1.nvars; j = j + 1 {
      row.push(p1.lambda[i][j].add(p2.lambda[i][j]))
    }
    sum.push(row)
  }
  let zero : Array[MPoly] = []
  for i = 0; i < p1.nvars; i = i + 1 {
    zero.push(MPoly::zero(p1.nvars))
  }
  let combined = JacobiStructure::make(p1.nvars, sum, zero)
  combined.jacobi_identity_certificate()
}
