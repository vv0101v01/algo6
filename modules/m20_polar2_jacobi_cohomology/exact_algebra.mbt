///|
/// Module M20 (Part 1) — Exact Algebra Hub: BigInt-backed Rational Field `Rat`,
/// Gauss-Jordan elimination, nullspace / affine solution sets, integer Smith
/// Normal Form with full invariant-factor divisibility chain, and finitely
/// generated abelian-group homology invariants.
///
/// 全域公理（唯一性證明無關）實例：RREF 與 Smith 標準形之唯一性——任何合法
/// 消元路徑所得之典範形唯一，故其唯一性證書與路徑（證明）無關。

///|
pub(all) suberror AlgebraError {
  ZeroDenominator
  MatrixShapeMismatch(Int32, Int32, Int32, Int32)
  MatrixDataLength(Int32, Int32)
  NonSquareDeterminant(Int32, Int32)
  IndexOutOfBounds(Int32, Int32)
  InconsistentDimensions(String)
}

///|
/// 精確有理數：num / den，恆有 den > 0 且 gcd(|num|, den) = 1（典範唯一形）。
#derive(Eq, Hash, Debug)
pub(all) struct Rat {
  num : @bigint.BigInt
  den : @bigint.BigInt
}

///|
pub extend Rat with Eq::{equal, not_equal}

///|
pub extend Rat with Hash::{hash, hash_combine}

///|
pub extend Rat with @debug.Debug::{to_repr}

///|
fn z(i : Int32) -> @bigint.BigInt {
  @bigint.BigInt::from_int(i)
}

///|
fn zabs(a : @bigint.BigInt) -> @bigint.BigInt {
  if a.compare_int(0) < 0 {
    a.neg()
  } else {
    a
  }
}

///|
fn zgcd(a : @bigint.BigInt, b : @bigint.BigInt) -> @bigint.BigInt {
  let mut x = zabs(a)
  let mut y = zabs(b)
  while y.compare_int(0) != 0 {
    let r = x.mod(y)
    x = y
    y = r
  }
  x
}

///|
pub fn Rat::make(
  num : @bigint.BigInt,
  den : @bigint.BigInt,
) -> Rat raise AlgebraError {
  if den.compare_int(0) == 0 {
    raise AlgebraError::ZeroDenominator
  }
  let mut n = num
  let mut d = den
  if d.compare_int(0) < 0 {
    n = n.neg()
    d = d.neg()
  }
  let g = zgcd(n, d)
  if g.compare_int(1) != 0 {
    n = n.div(g)
    d = d.div(g)
  }
  { num: n, den: d, }
}

///|
pub fn Rat::from_int(i : Int32) -> Rat {
  { num: z(i), den: z(1), }
}

///|
pub fn Rat::frac(n : Int32, d : Int32) -> Rat raise AlgebraError {
  Rat::make(z(n), z(d))
}

///|
pub fn Rat::zero() -> Rat {
  Rat::from_int(0)
}

///|
pub fn Rat::one() -> Rat {
  Rat::from_int(1)
}

///|
pub fn Rat::is_zero(self : Rat) -> Bool {
  self.num.compare_int(0) == 0
}

///|
pub fn Rat::sign(self : Rat) -> Int32 {
  self.num.compare_int(0)
}

///|
pub fn Rat::neg(self : Rat) -> Rat {
  { num: self.num.neg(), den: self.den, }
}

///|
pub fn Rat::inv(self : Rat) -> Rat raise AlgebraError {
  Rat::make(self.den, self.num)
}

///|
pub fn Rat::add(self : Rat, other : Rat) -> Rat raise AlgebraError {
  Rat::make(self.num * other.den + other.num * self.den, self.den * other.den)
}

///|
pub fn Rat::sub(self : Rat, other : Rat) -> Rat raise AlgebraError {
  Rat::make(self.num * other.den - other.num * self.den, self.den * other.den)
}

///|
pub fn Rat::mul(self : Rat, other : Rat) -> Rat raise AlgebraError {
  Rat::make(self.num * other.num, self.den * other.den)
}

///|
pub fn Rat::div(self : Rat, other : Rat) -> Rat raise AlgebraError {
  Rat::make(self.num * other.den, self.den * other.num)
}

///|
pub fn Rat::compare(self : Rat, other : Rat) -> Int32 {
  (self.num * other.den).compare(other.num * self.den)
}

///|
pub impl Show for Rat with fn output(self, logger) {
  logger.write_string(self.num.to_string())
  if self.den.compare_int(1) != 0 {
    logger.write_string("/")
    logger.write_string(self.den.to_string())
  }
}

///|
pub extend Rat with Show::{to_string, output}

///|
/// 有理矩陣（列主序）。所有消元皆精確，無浮點誤差。
pub(all) struct RatMatrix {
  rows : Int32
  cols : Int32
  data : Array[Rat]
}

///|
pub fn RatMatrix::make(
  rows : Int32,
  cols : Int32,
  data : Array[Rat],
) -> RatMatrix raise AlgebraError {
  if rows < 0 || cols < 0 || data.length() != rows * cols {
    raise AlgebraError::MatrixDataLength(data.length(), rows * cols)
  }
  { rows, cols, data, }
}

///|
pub fn RatMatrix::zero(
  rows : Int32,
  cols : Int32,
) -> RatMatrix raise AlgebraError {
  RatMatrix::make(rows, cols, Array::make(rows * cols, Rat::zero()))
}

///|
pub fn RatMatrix::identity(n : Int32) -> RatMatrix raise AlgebraError {
  let m = RatMatrix::zero(n, n)
  for i = 0; i < n; i = i + 1 {
    m.data[i * n + i] = Rat::one()
  }
  m
}

///|
pub fn RatMatrix::get(
  self : RatMatrix,
  i : Int32,
  j : Int32,
) -> Rat raise AlgebraError {
  if i < 0 || i >= self.rows || j < 0 || j >= self.cols {
    raise AlgebraError::IndexOutOfBounds(i, j)
  }
  self.data[i * self.cols + j]
}

///|
pub fn RatMatrix::set(
  self : RatMatrix,
  i : Int32,
  j : Int32,
  v : Rat,
) -> Unit raise AlgebraError {
  if i < 0 || i >= self.rows || j < 0 || j >= self.cols {
    raise AlgebraError::IndexOutOfBounds(i, j)
  }
  self.data[i * self.cols + j] = v
}

///|
pub fn RatMatrix::copy(self : RatMatrix) -> RatMatrix {
  { rows: self.rows, cols: self.cols, data: self.data.copy(), }
}

///|
fn swap_rows(m : RatMatrix, a : Int32, b : Int32) -> Unit {
  if a == b {
    return
  }
  for j = 0; j < m.cols; j = j + 1 {
    let t = m.data[a * m.cols + j]
    m.data[a * m.cols + j] = m.data[b * m.cols + j]
    m.data[b * m.cols + j] = t
  }
}

///|
/// RREF 典範形（唯一性證明無關公理之演算法實例）。
pub(all) struct RRef {
  matrix : RatMatrix
  rank : Int32
  pivots : Array[Int32]
}

///|
pub fn RatMatrix::rref(self : RatMatrix) -> RRef raise AlgebraError {
  let m = self.copy()
  let pivots : Array[Int32] = []
  let mut r = 0
  for c = 0; c < m.cols && r < m.rows; c = c + 1 {
    let mut p = -1
    for i = r; i < m.rows; i = i + 1 {
      if !m.data[i * m.cols + c].is_zero() {
        p = i
        break
      }
    }
    if p < 0 {
      continue
    }
    swap_rows(m, r, p)
    let inv = m.data[r * m.cols + c].inv()
    for j = 0; j < m.cols; j = j + 1 {
      m.data[r * m.cols + j] = m.data[r * m.cols + j].mul(inv)
    }
    for i = 0; i < m.rows; i = i + 1 {
      if i == r {
        continue
      }
      let f = m.data[i * m.cols + c]
      if f.is_zero() {
        continue
      }
      for j = 0; j < m.cols; j = j + 1 {
        m.data[i * m.cols + j] = m.data[i * m.cols + j].sub(
          f.mul(m.data[r * m.cols + j]),
        )
      }
    }
    pivots.push(c)
    r = r + 1
  }
  { matrix: m, rank: r, pivots, }
}

///|
pub fn RatMatrix::rank(self : RatMatrix) -> Int32 raise AlgebraError {
  self.rref().rank
}

///|
pub fn RatMatrix::nullspace(
  self : RatMatrix,
) -> Array[Array[Rat]] raise AlgebraError {
  let rr = self.rref()
  let free : Array[Int32] = []
  for c = 0; c < self.cols; c = c + 1 {
    if !rr.pivots.contains(c) {
      free.push(c)
    }
  }
  let basis : Array[Array[Rat]] = []
  for f in free {
    let v = Array::make(self.cols, Rat::zero())
    v[f] = Rat::one()
    for k = 0; k < rr.pivots.length(); k = k + 1 {
      v[rr.pivots[k]] = rr.matrix.get(k, f).neg()
    }
    basis.push(v)
  }
  basis
}

///|
pub(all) enum LinearSolution {
  Inconsistent
  Solution(Array[Rat], Array[Array[Rat]])
}

///|
pub fn RatMatrix::solve(
  self : RatMatrix,
  b : Array[Rat],
) -> LinearSolution raise AlgebraError {
  if b.length() != self.rows {
    raise AlgebraError::MatrixShapeMismatch(self.rows, self.cols, b.length(), 1)
  }
  let aug = RatMatrix::zero(self.rows, self.cols + 1)
  for i = 0; i < self.rows; i = i + 1 {
    for j = 0; j < self.cols; j = j + 1 {
      aug.set(i, j, self.get(i, j))
    }
    aug.set(i, self.cols, b[i])
  }
  let rr = aug.rref()
  for k = 0; k < rr.pivots.length(); k = k + 1 {
    if rr.pivots[k] == self.cols {
      return Inconsistent
    }
  }
  let x = Array::make(self.cols, Rat::zero())
  for k = 0; k < rr.pivots.length(); k = k + 1 {
    x[rr.pivots[k]] = rr.matrix.get(k, self.cols)
  }
  Solution(x, self.nullspace())
}

///|
pub fn RatMatrix::det(self : RatMatrix) -> Rat raise AlgebraError {
  if self.rows != self.cols {
    raise AlgebraError::NonSquareDeterminant(self.rows, self.cols)
  }
  let m = self.copy()
  let mut acc = Rat::one()
  for c = 0; c < m.cols; c = c + 1 {
    let mut p = -1
    for i = c; i < m.rows; i = i + 1 {
      if !m.data[i * m.cols + c].is_zero() {
        p = i
        break
      }
    }
    if p < 0 {
      return Rat::zero()
    }
    if p != c {
      swap_rows(m, c, p)
      acc = acc.neg()
    }
    let pv = m.data[c * m.cols + c]
    acc = acc.mul(pv)
    let inv = pv.inv()
    for i = c + 1; i < m.rows; i = i + 1 {
      let f = m.data[i * m.cols + c].mul(inv)
      if f.is_zero() {
        continue
      }
      for j = c; j < m.cols; j = j + 1 {
        m.data[i * m.cols + j] = m.data[i * m.cols + j].sub(
          f.mul(m.data[c * m.cols + j]),
        )
      }
    }
  }
  acc
}

///|
pub fn RatMatrix::mul_vec(
  self : RatMatrix,
  v : Array[Rat],
) -> Array[Rat] raise AlgebraError {
  if v.length() != self.cols {
    raise AlgebraError::MatrixShapeMismatch(self.rows, self.cols, v.length(), 1)
  }
  let out = Array::make(self.rows, Rat::zero())
  for i = 0; i < self.rows; i = i + 1 {
    let mut s = Rat::zero()
    for j = 0; j < self.cols; j = j + 1 {
      s = s.add(self.get(i, j).mul(v[j]))
    }
    out[i] = s
  }
  out
}

///|
pub fn RatMatrix::mul(
  self : RatMatrix,
  other : RatMatrix,
) -> RatMatrix raise AlgebraError {
  if self.cols != other.rows {
    raise AlgebraError::MatrixShapeMismatch(
      self.rows,
      self.cols,
      other.rows,
      other.cols,
    )
  }
  let out = RatMatrix::zero(self.rows, other.cols)
  for i = 0; i < self.rows; i = i + 1 {
    for j = 0; j < other.cols; j = j + 1 {
      let mut s = Rat::zero()
      for k = 0; k < self.cols; k = k + 1 {
        s = s.add(self.get(i, k).mul(other.get(k, j)))
      }
      out.set(i, j, s)
    }
  }
  out
}

///|
pub fn RatMatrix::scale(
  self : RatMatrix,
  s : Rat,
) -> RatMatrix raise AlgebraError {
  let out = RatMatrix::zero(self.rows, self.cols)
  for i = 0; i < self.data.length(); i = i + 1 {
    out.data[i] = self.data[i].mul(s)
  }
  out
}

///|
pub fn RatMatrix::add(
  self : RatMatrix,
  other : RatMatrix,
) -> RatMatrix raise AlgebraError {
  if self.rows != other.rows || self.cols != other.cols {
    raise AlgebraError::MatrixShapeMismatch(
      self.rows,
      self.cols,
      other.rows,
      other.cols,
    )
  }
  let out = RatMatrix::zero(self.rows, self.cols)
  for i = 0; i < self.data.length(); i = i + 1 {
    out.data[i] = self.data[i].add(other.data[i])
  }
  out
}

///|
pub fn RatMatrix::sub(
  self : RatMatrix,
  other : RatMatrix,
) -> RatMatrix raise AlgebraError {
  if self.rows != other.rows || self.cols != other.cols {
    raise AlgebraError::MatrixShapeMismatch(
      self.rows,
      self.cols,
      other.rows,
      other.cols,
    )
  }
  let out = RatMatrix::zero(self.rows, self.cols)
  for i = 0; i < self.data.length(); i = i + 1 {
    out.data[i] = self.data[i].sub(other.data[i])
  }
  out
}

///|
pub fn RatMatrix::transpose(self : RatMatrix) -> RatMatrix raise AlgebraError {
  let out = RatMatrix::zero(self.cols, self.rows)
  for i = 0; i < self.rows; i = i + 1 {
    for j = 0; j < self.cols; j = j + 1 {
      out.set(j, i, self.get(i, j))
    }
  }
  out
}

///|
pub fn RatMatrix::from_ints(
  rows : Int32,
  cols : Int32,
  data : Array[Int32],
) -> RatMatrix raise AlgebraError {
  if data.length() != rows * cols {
    raise AlgebraError::MatrixDataLength(data.length(), rows * cols)
  }
  let rs : Array[Rat] = []
  for v in data {
    rs.push(Rat::from_int(v))
  }
  RatMatrix::make(rows, cols, rs)
}

///|
/// 整數矩陣（BigInt 係數，無溢位）。Smith 標準形之載體。
pub(all) struct IntMatrix {
  rows : Int32
  cols : Int32
  data : Array[@bigint.BigInt]
}

///|
pub fn IntMatrix::make(
  rows : Int32,
  cols : Int32,
  data : Array[@bigint.BigInt],
) -> IntMatrix raise AlgebraError {
  if rows < 0 || cols < 0 || data.length() != rows * cols {
    raise AlgebraError::MatrixDataLength(data.length(), rows * cols)
  }
  { rows, cols, data, }
}

///|
pub fn IntMatrix::from_ints(
  rows : Int32,
  cols : Int32,
  data : Array[Int32],
) -> IntMatrix raise AlgebraError {
  if data.length() != rows * cols {
    raise AlgebraError::MatrixDataLength(data.length(), rows * cols)
  }
  let zs : Array[@bigint.BigInt] = []
  for v in data {
    zs.push(z(v))
  }
  IntMatrix::make(rows, cols, zs)
}

///|
pub fn IntMatrix::zero(
  rows : Int32,
  cols : Int32,
) -> IntMatrix raise AlgebraError {
  IntMatrix::make(rows, cols, Array::make(rows * cols, z(0)))
}

///|
pub fn IntMatrix::get(
  self : IntMatrix,
  i : Int32,
  j : Int32,
) -> @bigint.BigInt raise AlgebraError {
  if i < 0 || i >= self.rows || j < 0 || j >= self.cols {
    raise AlgebraError::IndexOutOfBounds(i, j)
  }
  self.data[i * self.cols + j]
}

///|
pub fn IntMatrix::set(
  self : IntMatrix,
  i : Int32,
  j : Int32,
  v : @bigint.BigInt,
) -> Unit raise AlgebraError {
  if i < 0 || i >= self.rows || j < 0 || j >= self.cols {
    raise AlgebraError::IndexOutOfBounds(i, j)
  }
  self.data[i * self.cols + j] = v
}

///|
pub fn IntMatrix::to_rat(self : IntMatrix) -> RatMatrix raise AlgebraError {
  let rs : Array[Rat] = []
  for v in self.data {
    rs.push(Rat::make(v, z(1)))
  }
  RatMatrix::make(self.rows, self.cols, rs)
}

///|
fn im_swap_rows(m : IntMatrix, a : Int32, b : Int32) -> Unit {
  if a == b {
    return
  }
  for j = 0; j < m.cols; j = j + 1 {
    let t = m.data[a * m.cols + j]
    m.data[a * m.cols + j] = m.data[b * m.cols + j]
    m.data[b * m.cols + j] = t
  }
}

///|
fn im_swap_cols(m : IntMatrix, a : Int32, b : Int32) -> Unit {
  if a == b {
    return
  }
  for i = 0; i < m.rows; i = i + 1 {
    let t = m.data[i * m.cols + a]
    m.data[i * m.cols + a] = m.data[i * m.cols + b]
    m.data[i * m.cols + b] = t
  }
}

///|
/// 歐幾里得除法：a = q*p + r，0 <= r < |p|。
fn euclid_div(
  a : @bigint.BigInt,
  p : @bigint.BigInt,
) -> (@bigint.BigInt, @bigint.BigInt) {
  let mut q = a.div(p)
  let mut r = a.sub(q.mul(p))
  if r.compare_int(0) < 0 {
    let ap = zabs(p)
    r = r.add(ap)
    if p.compare_int(0) > 0 {
      q = q.sub(z(1))
    } else {
      q = q.add(z(1))
    }
  }
  (q, r)
}

///|
pub(all) struct SmithForm {
  factors : Array[@bigint.BigInt]
  rank : Int32
}

///|
/// Smith 標準形：diag(d1,...,dr,0,...)，d1 | d2 | ... | dr，di > 0。
/// 演算法：最小非零元主元 + 行列歐幾里得消元 + 整除性修補；BigInt 保證無溢位。
/// 複雜度：多項式（每輪主元絕對值嚴格遞減，總輪數受輸入位元長度約束）。
pub fn IntMatrix::smith_normal_form(self : IntMatrix) -> SmithForm {
  let m : IntMatrix = {
    rows: self.rows,
    cols: self.cols,
    data: self.data.copy(),
  }
  let lim = if m.rows < m.cols { m.rows } else { m.cols }
  let factors : Array[@bigint.BigInt] = []
  let mut k = 0
  while k < lim {
    // 1) 找子矩陣 (k.., k..) 中最小非零絕對值元並搬到 (k,k)。
    let mut bi = -1
    let mut bj = -1
    let mut best : @bigint.BigInt = z(0)
    for i = k; i < m.rows; i = i + 1 {
      for j = k; j < m.cols; j = j + 1 {
        let v = m.data[i * m.cols + j]
        if v.compare_int(0) != 0 {
          let av = zabs(v)
          if bi < 0 || av.compare(best) < 0 {
            bi = i
            bj = j
            best = av
          }
        }
      }
    }
    if bi < 0 {
      break
    }
    im_swap_rows(m, k, bi)
    im_swap_cols(m, k, bj)
    // 2) 行列歐幾里得消元，直到第 k 行/列除主元外全零。
    let mut changed = true
    while changed {
      changed = false
      for i = k + 1; i < m.rows; i = i + 1 {
        let a = m.data[i * m.cols + k]
        if a.compare_int(0) == 0 {
          continue
        }
        let (q, r) = euclid_div(a, m.data[k * m.cols + k])
        for j = k; j < m.cols; j = j + 1 {
          m.data[i * m.cols + j] = m.data[i * m.cols + j].sub(
            q.mul(m.data[k * m.cols + j]),
          )
        }
        if r.compare_int(0) != 0 {
          im_swap_rows(m, k, i)
          changed = true
        }
      }
      for j = k + 1; j < m.cols; j = j + 1 {
        let a = m.data[k * m.cols + j]
        if a.compare_int(0) == 0 {
          continue
        }
        let (q, r) = euclid_div(a, m.data[k * m.cols + k])
        for i = k; i < m.rows; i = i + 1 {
          m.data[i * m.cols + j] = m.data[i * m.cols + j].sub(
            q.mul(m.data[i * m.cols + k]),
          )
        }
        if r.compare_int(0) != 0 {
          im_swap_cols(m, k, j)
          changed = true
        }
      }
      // 3) 整除性修補：主元須整除子矩陣所有元；否則把違規行加到第 k 行再消。
      let pv = m.data[k * m.cols + k]
      let mut fixed = false
      for i = k + 1; i < m.rows && !fixed; i = i + 1 {
        for j = k + 1; j < m.cols && !fixed; j = j + 1 {
          let v = m.data[i * m.cols + j]
          let (_, r) = euclid_div(v, pv)
          if r.compare_int(0) != 0 {
            for jj = k; jj < m.cols; jj = jj + 1 {
              m.data[k * m.cols + jj] = m.data[k * m.cols + jj].add(
                m.data[i * m.cols + jj],
              )
            }
            changed = true
            fixed = true
          }
        }
      }
    }
    // 正規化主元為正（整列變號）。
    if m.data[k * m.cols + k].compare_int(0) < 0 {
      for j = k; j < m.cols; j = j + 1 {
        m.data[k * m.cols + j] = m.data[k * m.cols + j].neg()
      }
    }
    factors.push(m.data[k * m.cols + k])
    k = k + 1
  }
  { factors, rank: factors.length(), }
}

///|
pub(all) struct AbelianGroup {
  free_rank : Int32
  torsion : Array[@bigint.BigInt]
}

///|
/// H_k = ker ∂_k / im ∂_{k+1} 之有限生成阿貝爾群不變量：
/// free_rank = dim C_k − rank ∂_k − rank ∂_{k+1}；撓率 = ∂_{k+1} 之 >1 不變因子。
pub fn homology_invariants(
  partial_k : IntMatrix,
  partial_k1 : IntMatrix,
  dim_ck : Int32,
) -> AbelianGroup raise AlgebraError {
  if partial_k.cols != dim_ck || partial_k1.rows != dim_ck {
    raise AlgebraError::InconsistentDimensions("homology chain dimensions")
  }
  let rk = partial_k.to_rat().rank()
  let rk1 = partial_k1.to_rat().rank()
  let sf = partial_k1.smith_normal_form()
  let torsion : Array[@bigint.BigInt] = []
  for f in sf.factors {
    if f.compare_int(1) > 0 {
      torsion.push(f)
    }
  }
  { free_rank: dim_ck - rk - rk1, torsion, }
}
