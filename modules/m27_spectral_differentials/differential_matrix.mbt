///|
/// Module M27 — Explicit Higher Differentials of Spectral Sequences:
/// d_r^{p,q} : E_r^{p,q} → E_r^{p+r,q−r+1}, [z] ↦ [Dz], constructed as an
/// exact rational matrix by expressing Dz in E_r representatives modulo B_r.
/// Certificates: d_r² = 0 and E_{r+1} = H(E_r, d_r) (the fundamental theorem
/// of spectral sequences), verified bidegree-by-bidegree against M21's pages.

///|
pub(all) suberror DifferentialError {
  InvalidPage(Int32)
  InconsistentLift(String)
}

///|
pub(all) struct DifferentialMatrix {
  r : Int32
  p : Int32
  q : Int32
  /// rows = dim E_r^{p+r,q−r+1}, cols = dim E_r^{p,q}
  matrix : @m20.RatMatrix
  source_dim : Int32
  target_dim : Int32
}

///|
/// 顯式 d_r^{p,q} 矩陣。
pub fn spectral_differential(
  cx : @m21.FilteredComplex,
  p : Int32,
  q : Int32,
  r : Int32,
) -> DifferentialMatrix raise Error {
  if r < 1 {
    raise DifferentialError::InvalidPage(r)
  }
  let n = p + q
  let tp = p + r
  let tq = q - r + 1
  let src = @m21.e_r_representatives(cx, p, q, r)
  let tgt = @m21.e_r_representatives(cx, tp, tq, r)
  let sdim = src.cols
  let tdim = tgt.cols
  let mat = @m20.RatMatrix::zero(tdim, sdim)
  if sdim == 0 || tdim == 0 {
    return { r, p, q, matrix: mat, source_dim: sdim, target_dim: tdim, }
  }
  let tb = @m21.b_r_basis(cx, tp, tq, r)
  // augmented [tgt | tb] in C^{n+1}
  let ambient = if n + 1 < cx.degree_dims.length() {
    cx.degree_dims[n + 1]
  } else {
    0
  }
  let aug = @m20.RatMatrix::zero(ambient, tdim + tb.cols)
  for j = 0; j < tdim; j = j + 1 {
    for i = 0; i < ambient; i = i + 1 {
      aug.set(i, j, tgt.get(i, j))
    }
  }
  for j = 0; j < tb.cols; j = j + 1 {
    for i = 0; i < ambient; i = i + 1 {
      aug.set(i, tdim + j, tb.get(i, j))
    }
  }
  for j = 0; j < sdim; j = j + 1 {
    // x = src column j ∈ C^n
    let x : Array[@m20.Rat] = []
    for i = 0; i < src.rows; i = i + 1 {
      x.push(src.get(i, j))
    }
    // Dx ∈ C^{n+1}
    let dx : Array[@m20.Rat] = if n < cx.diff.length() {
      cx.diff[n].mul_vec(x)
    } else {
      Array::make(ambient, @m20.Rat::zero())
    }
    let sol = aug.solve(dx)
    match sol {
      @m20.LinearSolution::Solution(coords, _) =>
        for i = 0; i < tdim; i = i + 1 {
          mat.set(i, j, coords[i])
        }
      @m20.LinearSolution::Inconsistent =>
        raise DifferentialError::InconsistentLift("Dz not in Z_r target")
    }
  }
  { r, p, q, matrix: mat, source_dim: sdim, target_dim: tdim, }
}

///|
/// d_r² = 0 證書：對每個 (p,q)，d_r^{p+r,q−r+1} ∘ d_r^{p,q} = 0。
pub fn d_r_squared_zero_certificate(
  cx : @m21.FilteredComplex,
  r : Int32,
) -> Bool raise Error {
  let (lo, hi) = @m21.filtration_range(cx)
  for p = lo; p <= hi; p = p + 1 {
    for q = 0; q < cx.degree_dims.length(); q = q + 1 {
      let n = p + q
      if n < 0 || n >= cx.degree_dims.length() {
        continue
      }
      let d1 = spectral_differential(cx, p, q, r)
      if d1.source_dim == 0 || d1.target_dim == 0 {
        continue
      }
      let d2 = spectral_differential(cx, p + r, q - r + 1, r)
      if d2.target_dim == 0 {
        continue
      }
      let prod = d2.matrix.mul(d1.matrix)
      for v in prod.data {
        if !v.is_zero() {
          return false
        }
      }
    }
  }
  true
}

///|
/// E_{r+1} = H(E_r, d_r) 證書：對每個 (p,q)，
/// dim E_{r+1}^{p,q} = nullity(d_r out) − rank(d_r in)，與 M21 第 r+1 頁一致。
pub fn next_page_is_homology_certificate(
  cx : @m21.FilteredComplex,
  r : Int32,
) -> Bool raise Error {
  let (lo, hi) = @m21.filtration_range(cx)
  let next = @m21.spectral_page(cx, r + 1)
  for p = lo; p <= hi; p = p + 1 {
    for q = 0; q < cx.degree_dims.length(); q = q + 1 {
      let n = p + q
      if n < 0 || n >= cx.degree_dims.length() {
        continue
      }
      let out = spectral_differential(cx, p, q, r)
      let nullity = out.source_dim - out.matrix.rank()
      let incoming = spectral_differential(cx, p - r, q + r - 1, r)
      let im_rank = incoming.matrix.rank()
      let predicted = nullity - im_rank
      let actual = match next.dims.get(p.to_string() + "," + q.to_string()) {
        Some(d) => d
        None => 0
      }
      if predicted != actual {
        return false
      }
    }
  }
  true
}

///|
/// 高階微分總證書：d_r²=0 且 E_{r+1}=H(E_r,d_r)。
pub fn explicit_differential_certificate(
  cx : @m21.FilteredComplex,
  r : Int32,
) -> Bool raise Error {
  d_r_squared_zero_certificate(cx, r) &&
  next_page_is_homology_certificate(cx, r)
}

///|
/// 收集第 r 頁所有非零 d_r 矩陣（層級關係：頁 r → r+1）。
pub fn differential_page(
  cx : @m21.FilteredComplex,
  r : Int32,
) -> Array[DifferentialMatrix] raise Error {
  let (lo, hi) = @m21.filtration_range(cx)
  let out : Array[DifferentialMatrix] = []
  for p = lo; p <= hi; p = p + 1 {
    for q = 0; q < cx.degree_dims.length(); q = q + 1 {
      let n = p + q
      if n < 0 || n >= cx.degree_dims.length() {
        continue
      }
      let d = spectral_differential(cx, p, q, r)
      if d.source_dim > 0 && d.target_dim > 0 {
        out.push(d)
      }
    }
  }
  out
}
