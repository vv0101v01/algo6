///|
/// Module M21 (Part 2) — Spectral Sequences of Filtered & Double Complexes:
/// the cohomological spectral sequence E_r^{p,q} = Z_r^{p,q}/B_r^{p,q} computed
/// page-by-page by exact subspace linear algebra (Z_r = F^p ∩ D¹F^{p+r},
/// B_r = Z_{r-1}^{p+1,q-1} + (D F^{p-r+1} ∩ F^p)), with convergence certificate
/// Σ_p E_∞^{p,n-p} = dim H^n.  Double complexes filter by column; a symplectic
/// tower (Λ^• V_p^*, d_v=0) gives an E_2-degenerate spectral sequence.

///|
pub(all) suberror SpectralError {
  InvalidComplex(String)
  NotFiltered
}

///|
/// 子空間以行向量基矩陣表示（ambient × k）。
fn subspace_reduce(cols : @m20.RatMatrix) -> @m20.RatMatrix raise Error {
  // 取行空間之獨立行：對轉置做 rref，主元行即獨立行
  let rr = cols.transpose().rref()
  let basis : Array[Array[@m20.Rat]] = []
  for k = 0; k < rr.pivots.length(); k = k + 1 {
    let row : Array[@m20.Rat] = []
    for j = 0; j < cols.rows; j = j + 1 {
      row.push(rr.matrix.get(k, j))
    }
    basis.push(row)
  }
  let out = @m20.RatMatrix::zero(cols.rows, basis.length())
  for j = 0; j < basis.length(); j = j + 1 {
    for i = 0; i < cols.rows; i = i + 1 {
      out.set(i, j, basis[j][i])
    }
  }
  out
}

///|
fn subspace_sum(
  a : @m20.RatMatrix,
  b : @m20.RatMatrix,
) -> @m20.RatMatrix raise Error {
  let cat = @m20.RatMatrix::zero(a.rows, a.cols + b.cols)
  for j = 0; j < a.cols; j = j + 1 {
    for i = 0; i < a.rows; i = i + 1 {
      cat.set(i, j, a.get(i, j))
    }
  }
  for j = 0; j < b.cols; j = j + 1 {
    for i = 0; i < b.rows; i = i + 1 {
      cat.set(i, a.cols + j, b.get(i, j))
    }
  }
  subspace_reduce(cat)
}

///|
/// 子空間交集 A ∩ B：nullspace([A | −B]) 之前 dim A 分量經 A 映射。
fn subspace_intersection(
  a : @m20.RatMatrix,
  b : @m20.RatMatrix,
) -> @m20.RatMatrix raise Error {
  let cat = @m20.RatMatrix::zero(a.rows, a.cols + b.cols)
  for j = 0; j < a.cols; j = j + 1 {
    for i = 0; i < a.rows; i = i + 1 {
      cat.set(i, j, a.get(i, j))
    }
  }
  for j = 0; j < b.cols; j = j + 1 {
    for i = 0; i < b.rows; i = i + 1 {
      cat.set(i, a.cols + j, b.get(i, j).neg())
    }
  }
  let ns = cat.nullspace()
  let imgs : Array[Array[@m20.Rat]] = []
  for v in ns {
    let coeff : Array[@m20.Rat] = []
    for j = 0; j < a.cols; j = j + 1 {
      coeff.push(v[j])
    }
    imgs.push(a.mul_vec(coeff))
  }
  let m = @m20.RatMatrix::zero(a.rows, imgs.length())
  for j = 0; j < imgs.length(); j = j + 1 {
    for i = 0; i < a.rows; i = i + 1 {
      m.set(i, j, imgs[j][i])
    }
  }
  subspace_reduce(m)
}

///|
/// 過濾複形：C^n 維度、每基元過濾度、D_n : C^n → C^{n+1}（D 升過濾）。
pub(all) struct FilteredComplex {
  degree_dims : Array[Int32]
  filtration : Array[Array[Int32]]
  diff : Array[@m20.RatMatrix]
}

///|
pub fn FilteredComplex::make(
  degree_dims : Array[Int32],
  filtration : Array[Array[Int32]],
  diff : Array[@m20.RatMatrix],
) -> FilteredComplex raise Error {
  let nd = degree_dims.length()
  if nd < 1 || filtration.length() != nd || diff.length() != nd - 1 {
    raise SpectralError::InvalidComplex("shape")
  }
  for n = 0; n < nd; n = n + 1 {
    if filtration[n].length() != degree_dims[n] {
      raise SpectralError::InvalidComplex("filtration length")
    }
  }
  for n = 0; n < diff.length(); n = n + 1 {
    if diff[n].rows != degree_dims[n + 1] || diff[n].cols != degree_dims[n] {
      raise SpectralError::InvalidComplex("diff shape")
    }
    // filtered: D raises filtration
    for i = 0; i < diff[n].rows; i = i + 1 {
      for j = 0; j < diff[n].cols; j = j + 1 {
        if !diff[n].get(i, j).is_zero() &&
          filtration[n + 1][i] < filtration[n][j] {
          raise SpectralError::NotFiltered
        }
      }
    }
    // D² = 0
    if n + 1 < diff.length() {
      let sq = diff[n + 1].mul(diff[n])
      for v in sq.data {
        if !v.is_zero() {
          raise SpectralError::InvalidComplex("D² ≠ 0")
        }
      }
    }
  }
  { degree_dims, filtration, diff, }
}

///|
/// F^p C^n 之標準基（過濾度 ≥ p 之基元）。
fn filtration_subspace(
  cx : FilteredComplex,
  n : Int32,
  p : Int32,
) -> @m20.RatMatrix raise Error {
  if n < 0 || n >= cx.degree_dims.length() {
    return @m20.RatMatrix::zero(0, 0)
  }
  let dim = cx.degree_dims[n]
  let idx : Array[Int32] = []
  for i = 0; i < dim; i = i + 1 {
    if cx.filtration[n][i] >= p {
      idx.push(i)
    }
  }
  let m = @m20.RatMatrix::zero(dim, idx.length())
  for j = 0; j < idx.length(); j = j + 1 {
    m.set(idx[j], j, @m20.Rat::one())
  }
  m
}

///|
/// Z_r^{p,q} = {x ∈ F^p C^n : Dx ∈ F^{p+r} C^{n+1}}（n = p+q）。
fn z_space(
  cx : FilteredComplex,
  p : Int32,
  q : Int32,
  r : Int32,
) -> @m20.RatMatrix raise Error {
  let n = p + q
  if n < 0 || n >= cx.degree_dims.length() {
    return @m20.RatMatrix::zero(0, 0)
  }
  let fp = filtration_subspace(cx, n, p)
  if fp.cols == 0 {
    return fp
  }
  if n + 1 >= cx.degree_dims.length() {
    // D = 0 beyond top → Z_r = F^p
    return fp
  }
  let d = cx.diff[n]
  // rows of C^{n+1} with filtration < p+r must vanish on Dx
  let bad_rows : Array[Int32] = []
  for i = 0; i < cx.degree_dims[n + 1]; i = i + 1 {
    if cx.filtration[n + 1][i] < p + r {
      bad_rows.push(i)
    }
  }
  if bad_rows.length() == 0 {
    return fp
  }
  // build R·D·fp where R selects bad_rows
  let rdfp = @m20.RatMatrix::zero(bad_rows.length(), fp.cols)
  for j = 0; j < fp.cols; j = j + 1 {
    let v = column_of(fp, j)
    let dv = d.mul_vec(v)
    for bi = 0; bi < bad_rows.length(); bi = bi + 1 {
      rdfp.set(bi, j, dv[bad_rows[bi]])
    }
  }
  let ns = rdfp.nullspace()
  let out = @m20.RatMatrix::zero(cx.degree_dims[n], ns.length())
  for j = 0; j < ns.length(); j = j + 1 {
    let v = fp.mul_vec(ns[j])
    for i = 0; i < cx.degree_dims[n]; i = i + 1 {
      out.set(i, j, v[i])
    }
  }
  subspace_reduce(out)
}

///|
fn column_of(m : @m20.RatMatrix, j : Int32) -> Array[@m20.Rat] raise Error {
  let v : Array[@m20.Rat] = []
  for i = 0; i < m.rows; i = i + 1 {
    v.push(m.get(i, j))
  }
  v
}

///|
/// B_r^{p,q} = Z_{r-1}^{p+1,q-1} + (D(F^{p-r+1} C^{n-1}) ∩ F^p C^n)。
fn b_space(
  cx : FilteredComplex,
  p : Int32,
  q : Int32,
  r : Int32,
) -> @m20.RatMatrix raise Error {
  let n = p + q
  if n < 0 || n >= cx.degree_dims.length() {
    return @m20.RatMatrix::zero(0, 0)
  }
  let z_prev = z_space(cx, p + 1, q - 1, r - 1)
  let fp = filtration_subspace(cx, n, p)
  let img_part = if n - 1 < 0 {
    @m20.RatMatrix::zero(cx.degree_dims[n], 0)
  } else {
    let fsrc = filtration_subspace(cx, n - 1, p - r + 1)
    let d = cx.diff[n - 1]
    let img = d.mul(fsrc)
    subspace_intersection(img, fp)
  }
  subspace_sum(z_prev, img_part)
}

///|
/// B_r^{p,q} 之子空間基（pub 包裝，供高階微分顯式矩陣求解模 B_r 坐標）。
pub fn b_r_basis(
  cx : FilteredComplex,
  p : Int32,
  q : Int32,
  r : Int32,
) -> @m20.RatMatrix raise Error {
  b_space(cx, p, q, r)
}

///|
/// E_r^{p,q} = Z_r^{p,q}/B_r^{p,q} 之一組代表元（C^{p+q} 中行向量），
/// 以增量秩選取 Z_r 中模 B_r 獨立之欄。供高階微分 d_r 顯式矩陣使用。
pub fn e_r_representatives(
  cx : FilteredComplex,
  p : Int32,
  q : Int32,
  r : Int32,
) -> @m20.RatMatrix raise Error {
  let n = p + q
  let z = z_space(cx, p, q, r)
  let b = b_space(cx, p, q, r)
  if n < 0 || n >= cx.degree_dims.length() {
    return @m20.RatMatrix::zero(0, 0)
  }
  let mut cur = b
  let mut cur_rank = cur.rank()
  let reps : Array[Int32] = []
  for j = 0; j < z.cols; j = j + 1 {
    let aug = @m20.RatMatrix::zero(n_dim(cx, n), cur.cols + 1)
    for c = 0; c < cur.cols; c = c + 1 {
      for i = 0; i < aug.rows; i = i + 1 {
        aug.set(i, c, cur.get(i, c))
      }
    }
    for i = 0; i < aug.rows; i = i + 1 {
      aug.set(i, cur.cols, z.get(i, j))
    }
    let rk = aug.rank()
    if rk > cur_rank {
      reps.push(j)
      cur = aug
      cur_rank = rk
    }
  }
  let out = @m20.RatMatrix::zero(n_dim(cx, n), reps.length())
  for j = 0; j < reps.length(); j = j + 1 {
    for i = 0; i < out.rows; i = i + 1 {
      out.set(i, j, z.get(i, reps[j]))
    }
  }
  out
}

///|
fn n_dim(cx : FilteredComplex, n : Int32) -> Int32 {
  if n < 0 || n >= cx.degree_dims.length() {
    0
  } else {
    cx.degree_dims[n]
  }
}

///|
pub(all) struct SpectralPage {
  r : Int32
  /// dims[p][q] = dim E_r^{p,q}（以 Map 鍵 "p,q" 儲存非零項）
  dims : Map[String, Int32]
  total_dim : Int32
}

///|
pub fn filtration_range(cx : FilteredComplex) -> (Int32, Int32) {
  let mut lo = 0
  let mut hi = 0
  let mut first = true
  for row in cx.filtration {
    for f in row {
      if first {
        lo = f
        hi = f
        first = false
      } else {
        if f < lo {
          lo = f
        }
        if f > hi {
          hi = f
        }
      }
    }
  }
  (lo, hi)
}

///|
/// 計算第 r 頁 E_r^{p,q} 維度。
pub fn spectral_page(
  cx : FilteredComplex,
  r : Int32,
) -> SpectralPage raise Error {
  if r < 1 {
    raise SpectralError::InvalidComplex("page r >= 1")
  }
  let (lo, hi) = filtration_range(cx)
  let dims : Map[String, Int32] = Map([])
  let mut total = 0
  for p = lo; p <= hi; p = p + 1 {
    for q = 0; q < cx.degree_dims.length(); q = q + 1 {
      let n = p + q
      if n < 0 || n >= cx.degree_dims.length() {
        continue
      }
      let z = z_space(cx, p, q, r)
      let b = b_space(cx, p, q, r)
      let d = z.cols - b.cols
      if d > 0 {
        dims[p.to_string() + "," + q.to_string()] = d
        total = total + d
      }
    }
  }
  { r, dims, total_dim: total, }
}

///|
/// 總上同調 dim H^n = dim ker D_n − rank D_{n-1}。
pub fn total_cohomology_dims(cx : FilteredComplex) -> Array[Int32] raise Error {
  let out : Array[Int32] = []
  for n = 0; n < cx.degree_dims.length(); n = n + 1 {
    let ker_dim = if n < cx.diff.length() {
      cx.degree_dims[n] - cx.diff[n].rank()
    } else {
      cx.degree_dims[n]
    }
    let im_rank = if n > 0 { cx.diff[n - 1].rank() } else { 0 }
    out.push(ker_dim - im_rank)
  }
  out
}

///|
pub(all) struct SpectralSequenceResult {
  pages : Array[SpectralPage]
  /// 收斂穩定頁 r_∞
  stable_page : Int32
  /// Σ_p E_∞^{p,n-p} = dim H^n
  converged : Bool
}

///|
/// 計算譜序列直到穩定，並驗證收斂於總上同調之 associated graded。
pub fn spectral_sequence(
  cx : FilteredComplex,
) -> SpectralSequenceResult raise Error {
  let h_total = total_cohomology_dims(cx)
  let pages : Array[SpectralPage] = []
  let max_r = cx.degree_dims.length() +
    filtration_range(cx).1 -
    filtration_range(cx).0 +
    2
  // 計算所有頁至 max_r（其後 d_r 必零）。total_dim 非遞增，
  // 首次達到最終 total_dim 之頁即為穩定頁（不可用相鄰頁相等做早停：
  // d_1=0 而 d_2≠0 時相鄰頁 total 相等但尚未穩定）。
  for r = 1; r <= max_r; r = r + 1 {
    pages.push(spectral_page(cx, r))
  }
  let last = pages[pages.length() - 1]
  let mut stable = max_r
  for i = 0; i < pages.length(); i = i + 1 {
    if pages[i].total_dim == last.total_dim {
      stable = i + 1
      break
    }
  }
  // convergence: E_∞ graded sums equal total cohomology
  let mut converged = true
  for n = 0; n < h_total.length(); n = n + 1 {
    let mut graded = 0
    for p = filtration_range(cx).0; p <= filtration_range(cx).1; p = p + 1 {
      let q = n - p
      if q < 0 {
        continue
      }
      let dval = match last.dims.get(p.to_string() + "," + q.to_string()) {
        Some(d) => d
        None => 0
      }
      graded = graded + dval
    }
    if graded != h_total[n] {
      converged = false
    }
  }
  { pages, stable_page: stable, converged, }
}

///|
/// 雙複形 (C^{p,q}, d_v, d_h)，d_v: (p,q)→(p,q+1)，d_h: (p,q)→(p+1,q)，
/// d_v²=d_h²=0，d_v d_h + d_h d_v = 0。
pub(all) struct DoubleComplex {
  /// dims[p][q]
  dims : Array[Array[Int32]]
  /// dv[p][q] : C^{p,q} → C^{p,q+1}
  dv : Array[Array[@m20.RatMatrix]]
  /// dh[p][q] : C^{p,q} → C^{p+1,q}
  dh : Array[Array[@m20.RatMatrix]]
}

///|
pub fn DoubleComplex::make(
  dims : Array[Array[Int32]],
  dv : Array[Array[@m20.RatMatrix]],
  dh : Array[Array[@m20.RatMatrix]],
) -> DoubleComplex raise Error {
  let np = dims.length()
  for p = 0; p < np; p = p + 1 {
    let nq = dims[p].length()
    if dv[p].length() != nq || dh[p].length() != nq {
      raise SpectralError::InvalidComplex("double complex shape")
    }
    for q = 0; q < nq; q = q + 1 {
      let vdim = if q + 1 < nq { dims[p][q + 1] } else { 0 }
      let hdim = if p + 1 < np && q < dims[p + 1].length() {
        dims[p + 1][q]
      } else {
        0
      }
      if dv[p][q].rows != vdim ||
        dv[p][q].cols != dims[p][q] ||
        dh[p][q].rows != hdim ||
        dh[p][q].cols != dims[p][q] {
        raise SpectralError::InvalidComplex("double diff shape")
      }
    }
  }
  { dims, dv, dh, }
}

///|
/// 雙複形 → 過濾總複形（按行 p 過濾，D = d_h + (−1)^p d_v）。
pub fn DoubleComplex::to_filtered_total(
  self : DoubleComplex,
) -> FilteredComplex raise Error {
  let np = self.dims.length()
  let mut max_n = 0
  for p = 0; p < np; p = p + 1 {
    for q = 0; q < self.dims[p].length(); q = q + 1 {
      if p + q > max_n {
        max_n = p + q
      }
    }
  }
  let nd = max_n + 1
  // layout: degree n basis = concat over p of C^{p,n-p}
  let degree_dims = Array::make(nd, 0)
  let offsets : Array[Array[Int32]] = [] // offsets[n][p]
  for n = 0; n < nd; n = n + 1 {
    let row : Array[Int32] = []
    let mut off = 0
    for p = 0; p < np; p = p + 1 {
      row.push(off)
      let q = n - p
      if q >= 0 && q < self.dims[p].length() {
        off = off + self.dims[p][q]
      }
    }
    offsets.push(row)
    degree_dims[n] = off
  }
  let filtration : Array[Array[Int32]] = []
  for n = 0; n < nd; n = n + 1 {
    let row : Array[Int32] = []
    for p = 0; p < np; p = p + 1 {
      let q = n - p
      if q >= 0 && q < self.dims[p].length() {
        for i = 0; i < self.dims[p][q]; i = i + 1 {
          row.push(p)
        }
      }
    }
    filtration.push(row)
  }
  let diff : Array[@m20.RatMatrix] = []
  for n = 0; n + 1 < nd; n = n + 1 {
    let d = @m20.RatMatrix::zero(degree_dims[n + 1], degree_dims[n])
    for p = 0; p < np; p = p + 1 {
      let q = n - p
      if q < 0 || q >= self.dims[p].length() {
        continue
      }
      let src_off = offsets[n][p]
      // d_h : C^{p,q} → C^{p+1,q} (degree n+1)
      if p + 1 < np && q < self.dims[p + 1].length() {
        let dst_off = offsets[n + 1][p + 1]
        let dh = self.dh[p][q]
        for i = 0; i < dh.rows; i = i + 1 {
          for j = 0; j < dh.cols; j = j + 1 {
            d.set(dst_off + i, src_off + j, dh.get(i, j))
          }
        }
      }
      // (-1)^p d_v : C^{p,q} → C^{p,q+1} (degree n+1)
      if q + 1 < self.dims[p].length() {
        let dst_off = offsets[n + 1][p]
        let dv = self.dv[p][q]
        let sign = if p % 2 == 0 {
          @m20.Rat::one()
        } else {
          @m20.Rat::from_int(-1)
        }
        for i = 0; i < dv.rows; i = i + 1 {
          for j = 0; j < dv.cols; j = j + 1 {
            d.set(dst_off + i, src_off + j, sign.mul(dv.get(i, j)))
          }
        }
      }
    }
    diff.push(d)
  }
  FilteredComplex::make(degree_dims, filtration, diff)
}

///|
/// 辛塔譜序列 E_2-退化證書：d_v = 0 之雙複形（辛序列結構之 Λ^• 模型），
/// 其譜序列於 E_2 退化（高階微分皆零），且收斂。
pub fn symplectic_tower_e2_degenerate(dc : DoubleComplex) -> Bool raise Error {
  // verify dv = 0
  for p = 0; p < dc.dv.length(); p = p + 1 {
    for q = 0; q < dc.dv[p].length(); q = q + 1 {
      for v in dc.dv[p][q].data {
        if !v.is_zero() {
          return false
        }
      }
    }
  }
  let cx = dc.to_filtered_total()
  let ss = spectral_sequence(cx)
  if !ss.converged {
    return false
  }
  // E_2 = E_∞ (degenerate): page 2 total equals stable total
  if ss.pages.length() < 2 {
    return ss.converged
  }
  ss.pages[1].total_dim == ss.pages[ss.pages.length() - 1].total_dim
}
