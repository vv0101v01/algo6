///|
/// Module M20 (Part 2) — Polar Čech Cohomology & the 2-Abelian Chain-Homotopy
/// Calculus: finite covers → nerves → coboundary matrices → Smith cohomology;
/// ℤ/2-polarity as diagonal chain isomorphism; chain maps, chain homotopies and
/// the induced-map-on-homology functor (the 2-morphism layer of the 2-abelian
/// category of complexes).

///|
fn sorted_unique(vs : Array[Int32]) -> Array[Int32] {
  let a = vs.copy()
  // insertion sort (small simplex cardinalities)
  for i = 1; i < a.length(); i = i + 1 {
    let x = a[i]
    let mut j = i
    while j > 0 && a[j - 1] > x {
      a[j] = a[j - 1]
      j = j - 1
    }
    a[j] = x
  }
  let out : Array[Int32] = []
  for v in a {
    if out.length() == 0 || out[out.length() - 1] != v {
      out.push(v)
    }
  }
  out
}

///|
fn simplex_key(s : Array[Int32]) -> String {
  let mut k = ""
  for v in s {
    k = k + v.to_string() + ","
  }
  k
}

///|
/// 抽象單純複形：simplices[k] = 全部 k-單體（頂點遞增排序）。
pub(all) struct SimplicialComplex {
  simplices : Array[Array[Array[Int32]]]
}

///|
fn add_simplex_with_faces(
  store : Array[Array[Array[Int32]]],
  seen : Map[String, Bool],
  s : Array[Int32],
) -> Unit {
  let key = simplex_key(s)
  if seen.contains(key) {
    return
  }
  seen[key] = true
  let d = s.length() - 1
  while store.length() <= d {
    store.push([])
  }
  store[d].push(s)
  for i = 0; i < s.length(); i = i + 1 {
    let face : Array[Int32] = []
    for j = 0; j < s.length(); j = j + 1 {
      if j != i {
        face.push(s[j])
      }
    }
    if face.length() > 0 {
      add_simplex_with_faces(store, seen, face)
    }
  }
}

///|
pub fn SimplicialComplex::from_facets(
  facets : Array[Array[Int32]],
) -> SimplicialComplex raise AlgebraError {
  let store : Array[Array[Array[Int32]]] = [[]]
  let seen : Map[String, Bool] = Map([])
  for f in facets {
    let s = sorted_unique(f)
    if s.length() == 0 {
      raise AlgebraError::InconsistentDimensions("empty facet")
    }
    add_simplex_with_faces(store, seen, s)
  }
  { simplices: store, }
}

///|
/// 覆蓋 {U_i} 之 nerve：S 為單體 iff ∩_{i∈S} U_i ≠ ∅。
/// 實作：對每點 x，包含 x 之覆蓋索引集之所有子集皆為單體（聯集即 nerve）。
pub fn nerve_of_cover(
  cover : Array[Array[Int32]],
) -> SimplicialComplex raise AlgebraError {
  let mut max_pt = -1
  for u in cover {
    for x in u {
      if x < 0 {
        raise AlgebraError::InconsistentDimensions("negative point label")
      }
      if x > max_pt {
        max_pt = x
      }
    }
  }
  let store : Array[Array[Array[Int32]]] = [[]]
  let seen : Map[String, Bool] = Map([])
  for x = 0; x <= max_pt; x = x + 1 {
    let idx : Array[Int32] = []
    for i = 0; i < cover.length(); i = i + 1 {
      if cover[i].contains(x) {
        idx.push(i)
      }
    }
    let n = idx.length()
    if n == 0 {
      continue
    }
    // enumerate all nonempty subsets of idx
    for mask = 1; mask < 1 << n; mask = mask + 1 {
      let s : Array[Int32] = []
      for b = 0; b < n; b = b + 1 {
        if ((mask >> b) & 1) == 1 {
          s.push(idx[b])
        }
      }
      add_simplex_with_faces(store, seen, s)
    }
  }
  if store[0].length() == 0 {
    raise AlgebraError::InconsistentDimensions("empty cover nerve")
  }
  { simplices: store, }
}

///|
fn simplex_index(
  cx : SimplicialComplex,
  dim : Int32,
  s : Array[Int32],
) -> Int32 raise AlgebraError {
  if dim < 0 || dim >= cx.simplices.length() {
    raise AlgebraError::IndexOutOfBounds(dim, cx.simplices.length())
  }
  let key = simplex_key(s)
  for i = 0; i < cx.simplices[dim].length(); i = i + 1 {
    if simplex_key(cx.simplices[dim][i]) == key {
      return i
    }
  }
  raise AlgebraError::InconsistentDimensions("simplex not in complex")
}

///|
/// ∂_k : C_k → C_{k-1}，(∂σ)_i = (-1)^i σ 去掉第 i 頂點。k=0 回傳 0×n0。
pub fn boundary_matrix(
  cx : SimplicialComplex,
  k : Int32,
) -> IntMatrix raise AlgebraError {
  if k < 0 || k >= cx.simplices.length() {
    raise AlgebraError::IndexOutOfBounds(k, cx.simplices.length())
  }
  let nk = cx.simplices[k].length()
  if k == 0 {
    return IntMatrix::zero(0, nk)
  }
  let nk1 = cx.simplices[k - 1].length()
  let m = IntMatrix::zero(nk1, nk)
  for col = 0; col < nk; col = col + 1 {
    let s = cx.simplices[k][col]
    for i = 0; i < s.length(); i = i + 1 {
      let face : Array[Int32] = []
      for j = 0; j < s.length(); j = j + 1 {
        if j != i {
          face.push(s[j])
        }
      }
      let row = simplex_index(cx, k - 1, face)
      let sign = if i % 2 == 0 { 1 } else { -1 }
      m.data[row * nk + col] = z(sign)
    }
  }
  m
}

///|
/// δ^k = (∂_{k+1})^T : C^k → C^{k+1}。
pub fn coboundary_matrix(
  cx : SimplicialComplex,
  k : Int32,
) -> IntMatrix raise AlgebraError {
  if k + 1 >= cx.simplices.length() {
    let nk = if k < cx.simplices.length() {
      cx.simplices[k].length()
    } else {
      0
    }
    return IntMatrix::zero(0, nk)
  }
  rat_to_int_unchecked(boundary_matrix(cx, k + 1).to_rat().transpose())
}

///|
fn rat_to_int_unchecked(m : RatMatrix) -> IntMatrix raise AlgebraError {
  let out = IntMatrix::zero(m.rows, m.cols)
  for idx = 0; idx < m.data.length(); idx = idx + 1 {
    if m.data[idx].den.compare_int(1) != 0 {
      raise AlgebraError::InconsistentDimensions("non-integral coboundary")
    }
    out.data[idx] = m.data[idx].num
  }
  out
}

///|
/// Čech 上同調 H^k = ker δ^k / im δ^{k-1}（常值 ℤ 係數）。
pub fn cech_cohomology(
  cx : SimplicialComplex,
  k : Int32,
) -> AbelianGroup raise AlgebraError {
  if k < 0 || k >= cx.simplices.length() {
    raise AlgebraError::IndexOutOfBounds(k, cx.simplices.length())
  }
  let nk = cx.simplices[k].length()
  let dk = coboundary_matrix(cx, k)
  let dk1 = if k == 0 {
    IntMatrix::zero(nk, 0)
  } else {
    coboundary_matrix(cx, k - 1)
  }
  homology_invariants(dk, dk1, nk)
}

///|
/// 極性（polarity）：每胞腔賦 ±1；∂^pol_k = D_{k-1} ∂_k D_k 為鏈同構共軛，
/// 故 ∂^pol² = 0 且上同調不變（極性翻轉定理）。
pub fn polar_boundary_matrix(
  cx : SimplicialComplex,
  k : Int32,
  signs : Array[Array[Int32]],
) -> IntMatrix raise AlgebraError {
  if signs.length() != cx.simplices.length() {
    raise AlgebraError::InconsistentDimensions("polarity per dimension")
  }
  for d = 0; d < signs.length(); d = d + 1 {
    if signs[d].length() != cx.simplices[d].length() {
      raise AlgebraError::InconsistentDimensions("polarity per cell")
    }
    for s in signs[d] {
      if s != 1 && s != -1 {
        raise AlgebraError::InconsistentDimensions("polarity must be ±1")
      }
    }
  }
  let b = boundary_matrix(cx, k)
  if k == 0 {
    return b
  }
  let out = IntMatrix::zero(b.rows, b.cols)
  for i = 0; i < b.rows; i = i + 1 {
    for j = 0; j < b.cols; j = j + 1 {
      let s = z(signs[k - 1][i] * signs[k][j])
      out.data[i * b.cols + j] = b.get(i, j).mul(s)
    }
  }
  out
}

///|
pub(all) struct ChainComplex {
  dims : Array[Int32]
  /// partials[k] = ∂_{k+1} : C_{k+1} → C_k
  partials : Array[IntMatrix]
}

///|
pub fn ChainComplex::make(
  dims : Array[Int32],
  partials : Array[IntMatrix],
) -> ChainComplex raise AlgebraError {
  if dims.length() == 0 || partials.length() != dims.length() - 1 {
    raise AlgebraError::InconsistentDimensions("chain complex shape")
  }
  for k = 0; k < partials.length(); k = k + 1 {
    if partials[k].rows != dims[k] || partials[k].cols != dims[k + 1] {
      raise AlgebraError::InconsistentDimensions("boundary shape")
    }
  }
  for k = 1; k < partials.length(); k = k + 1 {
    let prod = partials[k - 1].to_rat().mul(partials[k].to_rat())
    for v in prod.data {
      if !v.is_zero() {
        raise AlgebraError::InconsistentDimensions("∂² ≠ 0")
      }
    }
  }
  { dims, partials, }
}

///|
pub fn ChainComplex::homology(
  self : ChainComplex,
  k : Int32,
) -> AbelianGroup raise AlgebraError {
  if k < 0 || k >= self.dims.length() {
    raise AlgebraError::IndexOutOfBounds(k, self.dims.length())
  }
  let pk = if k == 0 {
    IntMatrix::zero(0, self.dims[0])
  } else {
    self.partials[k - 1]
  }
  let pk1 = if k == self.dims.length() - 1 {
    IntMatrix::zero(self.dims[k], 0)
  } else {
    self.partials[k]
  }
  homology_invariants(pk, pk1, self.dims[k])
}

///|
pub(all) struct ChainMap {
  mats : Array[IntMatrix]
}

///|
pub fn is_chain_map(
  src : ChainComplex,
  dst : ChainComplex,
  f : ChainMap,
) -> Bool raise AlgebraError {
  if src.dims.length() != dst.dims.length() ||
    f.mats.length() != src.dims.length() {
    return false
  }
  for k = 0; k < src.dims.length(); k = k + 1 {
    if f.mats[k].rows != dst.dims[k] || f.mats[k].cols != src.dims[k] {
      return false
    }
  }
  for k = 0; k < src.partials.length(); k = k + 1 {
    // ∂^D_{k+1} ∘ f_{k+1} = f_k ∘ ∂^C_{k+1}
    let lhs = dst.partials[k].to_rat().mul(f.mats[k + 1].to_rat())
    let rhs = f.mats[k].to_rat().mul(src.partials[k].to_rat())
    for i = 0; i < lhs.data.length(); i = i + 1 {
      if lhs.data[i] != rhs.data[i] {
        return false
      }
    }
  }
  true
}

///|
pub(all) struct ChainHomotopy {
  /// mats[k] = h_k : C_k → D_{k+1}（頂層為 0 矩陣）
  mats : Array[IntMatrix]
}

///|
/// 2-阿貝爾 2-態射驗證：f − g = ∂^D h + h ∂^C（逐次）。
pub fn is_chain_homotopy(
  src : ChainComplex,
  dst : ChainComplex,
  f : ChainMap,
  g : ChainMap,
  h : ChainHomotopy,
) -> Bool raise AlgebraError {
  if !is_chain_map(src, dst, f) || !is_chain_map(src, dst, g) {
    return false
  }
  if h.mats.length() != src.dims.length() {
    return false
  }
  for k = 0; k < src.dims.length(); k = k + 1 {
    let top = if k + 1 < dst.dims.length() { dst.dims[k + 1] } else { 0 }
    if h.mats[k].rows != top || h.mats[k].cols != src.dims[k] {
      return false
    }
  }
  for k = 0; k < src.dims.length(); k = k + 1 {
    // dh 項：∂^D_{k+1} h_k
    let dh = if k < dst.partials.length() {
      dst.partials[k].to_rat().mul(h.mats[k].to_rat())
    } else {
      RatMatrix::zero(dst.dims[k], src.dims[k])
    }
    // hd 項：h_{k-1} ∂^C_k
    let hd = if k > 0 {
      h.mats[k - 1].to_rat().mul(src.partials[k - 1].to_rat())
    } else {
      RatMatrix::zero(dst.dims[k], src.dims[k])
    }
    for i = 0; i < dst.dims[k]; i = i + 1 {
      for j = 0; j < src.dims[k]; j = j + 1 {
        let lhs = bigint_to_rat(f.mats[k].get(i, j)).sub(
          bigint_to_rat(g.mats[k].get(i, j)),
        )
        let rhs = dh.get(i, j).add(hd.get(i, j))
        if lhs != rhs {
          return false
        }
      }
    }
  }
  true
}

///|
fn bigint_to_rat(v : @bigint.BigInt) -> Rat raise AlgebraError {
  Rat::make(v, z(1))
}

///|
/// H_k 之 ℚ-代表元基：ker ∂_k 中模 im ∂_{k+1} 線性獨立之向量。
pub fn homology_representatives(
  cx : ChainComplex,
  k : Int32,
) -> Array[Array[Rat]] raise AlgebraError {
  if k < 0 || k >= cx.dims.length() {
    raise AlgebraError::IndexOutOfBounds(k, cx.dims.length())
  }
  let ker : Array[Array[Rat]] = if k == 0 {
    let id = RatMatrix::identity(cx.dims[0])
    let cols : Array[Array[Rat]] = []
    for j = 0; j < cx.dims[0]; j = j + 1 {
      let v : Array[Rat] = []
      for i = 0; i < cx.dims[0]; i = i + 1 {
        v.push(id.get(i, j))
      }
      cols.push(v)
    }
    cols
  } else {
    cx.partials[k - 1].to_rat().nullspace()
  }
  let im_cols : Array[Array[Rat]] = if k < cx.partials.length() {
    let m = cx.partials[k].to_rat()
    let cols : Array[Array[Rat]] = []
    for j = 0; j < m.cols; j = j + 1 {
      let v : Array[Rat] = []
      for i = 0; i < m.rows; i = i + 1 {
        v.push(m.get(i, j))
      }
      cols.push(v)
    }
    cols
  } else {
    []
  }
  // greedily select ker vectors independent modulo im
  let mut basis = im_cols.copy()
  let mut cur_rank = 0
  if basis.length() > 0 {
    cur_rank = columns_matrix(basis, cx.dims[k]).rank()
  }
  let reps : Array[Array[Rat]] = []
  for v in ker {
    let trial = basis.copy()
    trial.push(v)
    let r = columns_matrix(trial, cx.dims[k]).rank()
    if r > cur_rank {
      cur_rank = r
      basis = trial
      reps.push(v)
    }
  }
  reps
}

///|
fn columns_matrix(
  cols : Array[Array[Rat]],
  rows : Int32,
) -> RatMatrix raise AlgebraError {
  let m = RatMatrix::zero(rows, cols.length())
  for j = 0; j < cols.length(); j = j + 1 {
    for i = 0; i < rows; i = i + 1 {
      m.set(i, j, cols[j][i])
    }
  }
  m
}

///|
/// 鏈映射誘導之 H_k(ℚ) 映射矩陣（對代表元基）。
pub fn induced_homology_map(
  src : ChainComplex,
  dst : ChainComplex,
  f : ChainMap,
  k : Int32,
) -> RatMatrix raise AlgebraError {
  if !is_chain_map(src, dst, f) {
    raise AlgebraError::InconsistentDimensions("not a chain map")
  }
  let srep = homology_representatives(src, k)
  let trep = homology_representatives(dst, k)
  let tim : Array[Array[Rat]] = if k < dst.partials.length() {
    let m = dst.partials[k].to_rat()
    let cols : Array[Array[Rat]] = []
    for j = 0; j < m.cols; j = j + 1 {
      let v : Array[Rat] = []
      for i = 0; i < m.rows; i = i + 1 {
        v.push(m.get(i, j))
      }
      cols.push(v)
    }
    cols
  } else {
    []
  }
  let aug_cols = trep.copy()
  for c in tim {
    aug_cols.push(c)
  }
  let aug = columns_matrix(aug_cols, dst.dims[k])
  let out = RatMatrix::zero(trep.length(), srep.length())
  for j = 0; j < srep.length(); j = j + 1 {
    let w = f.mats[k].to_rat().mul_vec(srep[j])
    match aug.solve(w) {
      Inconsistent =>
        raise AlgebraError::InconsistentDimensions(
          "chain map does not preserve cycles",
        )
      Solution(coeff, _) =>
        for i = 0; i < trep.length(); i = i + 1 {
          out.set(i, j, coeff[i])
        }
    }
  }
  out
}

///|
/// 2-阿貝爾同倫不變性證書：f ≃ g ⟹ H_k(f) = H_k(g)（精確矩陣相等）。
pub fn homotopy_invariance_certificate(
  src : ChainComplex,
  dst : ChainComplex,
  f : ChainMap,
  g : ChainMap,
  h : ChainHomotopy,
  k : Int32,
) -> Bool raise AlgebraError {
  if !is_chain_homotopy(src, dst, f, g, h) {
    return false
  }
  let mf = induced_homology_map(src, dst, f, k)
  let mg = induced_homology_map(src, dst, g, k)
  for i = 0; i < mf.data.length(); i = i + 1 {
    if mf.data[i] != mg.data[i] {
      return false
    }
  }
  true
}
