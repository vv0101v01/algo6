///|
/// Module M21 (Part 1) — Exact Linear Symplectic Algebra over ℚ: nondegenerate
/// skew forms, Darboux normal form via symplectic Gram–Schmidt, recursive
/// Pfaffian (Pf² = det), Hamiltonian (sp) membership, symplectic complements and
/// coisotropic (Marsden–Weinstein) reduction dimensions.

///|
pub(all) suberror SymplecticError {
  NotSkewSymmetric
  DegenerateForm
  OddDimension(Int32)
  NotCoisotropic
}

///|
pub(all) struct SymplecticForm {
  dim : Int32
  omega : @m20.RatMatrix
}

///|
pub fn SymplecticForm::make(
  omega : @m20.RatMatrix,
) -> SymplecticForm raise Error {
  let n = omega.rows
  if n != omega.cols || n % 2 != 0 {
    raise SymplecticError::OddDimension(n)
  }
  for i = 0; i < n; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      if omega.get(i, j) != omega.get(j, i).neg() {
        raise SymplecticError::NotSkewSymmetric
      }
    }
  }
  if omega.det().is_zero() {
    raise SymplecticError::DegenerateForm
  }
  { dim: n, omega, }
}

///|
/// 標準辛形式 J（交錯 Darboux 序 e_0,f_0,e_1,f_1,...）：J[2i,2i+1]=1, J[2i+1,2i]=−1。
pub fn standard_symplectic(n : Int32) -> SymplecticForm raise Error {
  let d = 2 * n
  let j = @m20.RatMatrix::zero(d, d)
  for i = 0; i < n; i = i + 1 {
    j.set(2 * i, 2 * i + 1, @m20.Rat::one())
    j.set(2 * i + 1, 2 * i, @m20.Rat::from_int(-1))
  }
  SymplecticForm::make(j)
}

///|
fn sym_pair(
  omega : @m20.RatMatrix,
  u : Array[@m20.Rat],
  v : Array[@m20.Rat],
) -> @m20.Rat raise Error {
  let wv = omega.mul_vec(v)
  let mut acc = @m20.Rat::zero()
  for i = 0; i < u.length(); i = i + 1 {
    acc = acc.add(u[i].mul(wv[i]))
  }
  acc
}

///|
fn vec_scale(v : Array[@m20.Rat], s : @m20.Rat) -> Array[@m20.Rat] raise Error {
  let out : Array[@m20.Rat] = []
  for x in v {
    out.push(x.mul(s))
  }
  out
}

///|
/// Darboux 基（辛 Gram–Schmidt）：回傳變換矩陣 T（行向量為新基），Tᵀ ω T = J。
pub fn darboux_basis(form : SymplecticForm) -> @m20.RatMatrix raise Error {
  let d = form.dim
  let mut remaining : Array[Array[@m20.Rat]] = []
  for i = 0; i < d; i = i + 1 {
    let e = Array::make(d, @m20.Rat::zero())
    e[i] = @m20.Rat::one()
    remaining.push(e)
  }
  let basis : Array[Array[@m20.Rat]] = []
  while remaining.length() > 0 {
    let e = remaining[0]
    // find f with ω(e,f) ≠ 0
    let mut fidx = -1
    let mut pairing = @m20.Rat::zero()
    for j = 1; j < remaining.length(); j = j + 1 {
      let p = sym_pair(form.omega, e, remaining[j])
      if !p.is_zero() {
        fidx = j
        pairing = p
        break
      }
    }
    if fidx < 0 {
      raise SymplecticError::DegenerateForm
    }
    let f = vec_scale(remaining[fidx], pairing.inv())
    basis.push(e)
    basis.push(f)
    let new_remaining : Array[Array[@m20.Rat]] = []
    for j = 1; j < remaining.length(); j = j + 1 {
      if j == fidx {
        continue
      }
      let v = remaining[j]
      // v' = v − ω(v,f) e + ω(v,e) f
      let avf = sym_pair(form.omega, v, f)
      let ave = sym_pair(form.omega, v, e)
      let vp : Array[@m20.Rat] = []
      for i = 0; i < d; i = i + 1 {
        vp.push(v[i].sub(avf.mul(e[i])).add(ave.mul(f[i])))
      }
      let mut nonzero = false
      for x in vp {
        if !x.is_zero() {
          nonzero = true
        }
      }
      if nonzero {
        new_remaining.push(vp)
      }
    }
    remaining = new_remaining
  }
  let t = @m20.RatMatrix::zero(d, d)
  for j = 0; j < d; j = j + 1 {
    for i = 0; i < d; i = i + 1 {
      t.set(i, j, basis[j][i])
    }
  }
  t
}

///|
/// Darboux 證書：Tᵀ ω T = J。
pub fn darboux_certificate(
  form : SymplecticForm,
  t : @m20.RatMatrix,
) -> Bool raise Error {
  let j = standard_symplectic(form.dim / 2)
  let got = t.transpose().mul(form.omega).mul(t)
  for i = 0; i < got.data.length(); i = i + 1 {
    if got.data[i] != j.omega.data[i] {
      return false
    }
  }
  true
}

///|
/// 遞迴 Pfaffian：Pf(A) = Σ_{j≥1} (−1)^{j+1} A[0][j] Pf(A 去掉 0,j 行列)。
pub fn pfaffian(m : @m20.RatMatrix) -> @m20.Rat raise Error {
  let n = m.rows
  if n != m.cols {
    raise SymplecticError::OddDimension(n)
  }
  if n == 0 {
    return @m20.Rat::one()
  }
  if n % 2 != 0 {
    return @m20.Rat::zero()
  }
  let mut acc = @m20.Rat::zero()
  for j = 1; j < n; j = j + 1 {
    let minor = @m20.RatMatrix::zero(n - 2, n - 2)
    let mut ri = 0
    for i = 0; i < n; i = i + 1 {
      if i == 0 || i == j {
        continue
      }
      let mut ci = 0
      for k = 0; k < n; k = k + 1 {
        if k == 0 || k == j {
          continue
        }
        minor.set(ri, ci, m.get(i, k))
        ci = ci + 1
      }
      ri = ri + 1
    }
    let sign = if j % 2 == 1 { @m20.Rat::one() } else { @m20.Rat::from_int(-1) }
    acc = acc.add(sign.mul(m.get(0, j)).mul(pfaffian(minor)))
  }
  acc
}

///|
/// Pfaffian 證書：Pf(ω)² = det(ω)。
pub fn pfaffian_certificate(form : SymplecticForm) -> Bool raise Error {
  let pf = pfaffian(form.omega)
  pf.mul(pf) == form.omega.det()
}

///|
/// 哈密頓矩陣（sp 成員）：Hᵀ ω + ω H = 0。
pub fn is_hamiltonian(
  form : SymplecticForm,
  h : @m20.RatMatrix,
) -> Bool raise Error {
  let lhs = h.transpose().mul(form.omega).add(form.omega.mul(h))
  for v in lhs.data {
    if !v.is_zero() {
      return false
    }
  }
  true
}

///|
/// 辛補 W^ω = ker(Wᵀ ω)（W 之行張成子空間）。
pub fn symplectic_complement(
  form : SymplecticForm,
  w : @m20.RatMatrix,
) -> Array[Array[@m20.Rat]] raise Error {
  let m = w.transpose().mul(form.omega)
  m.nullspace()
}

///|
/// 餘迷向（coisotropic）判定：C^ω ⊆ C（每個 C^ω 基向量屬於 span C）。
pub fn is_coisotropic(
  form : SymplecticForm,
  c : @m20.RatMatrix,
) -> Bool raise Error {
  let comp = symplectic_complement(form, c)
  for v in comp {
    match c.solve(v) {
      Inconsistent => return false
      Solution(_, _) => ()
    }
  }
  true
}

///|
/// 辛約化維數：dim(C/C^ω) = 2·dim C − dim V（餘迷向時非負偶數）。
pub fn reduced_dimension(
  form : SymplecticForm,
  c : @m20.RatMatrix,
) -> Int32 raise Error {
  if !is_coisotropic(form, c) {
    raise SymplecticError::NotCoisotropic
  }
  2 * c.cols - form.dim
}
