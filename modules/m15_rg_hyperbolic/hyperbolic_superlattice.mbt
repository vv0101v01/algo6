///|
/// Module M15 (Part 2) — Hyperbolic Stacked Superlattices: {p,q} curvature
/// trichotomy, the Möbius–Kantor generalized Petersen graph G(8,3) as the
/// 16-vertex {8,3} Bolza quotient, Cartesian-product stacking with the exact
/// resultant spectral theorem charpoly(G□H) = Res_y(p_G(y), p_H(x−y)),
/// Gromov 4-point δ-hyperbolicity, and Schur-complement layer decimation
/// (Feshbach projection) linking RG coarse-graining to the superlattice resolvent.

///|
pub(all) suberror LatticeError {
  InvalidTessellation(Int32, Int32)
  GraphIndex(Int32, Int32)
  EmptyGraph
  SingularResolvent
}

///|
/// {p,q} 鑲嵌每頂點角虧 / π = 2 − q(p−2)/p = (2p − pq + 2q)/p。
/// >0 球面、=0 歐氏、<0 雙曲；雙曲等價於 (p−2)(q−2) > 4。
pub fn tessellation_curvature(p : Int32, q : Int32) -> @m20.Rat raise Error {
  if p < 3 || q < 3 {
    raise LatticeError::InvalidTessellation(p, q)
  }
  @m20.Rat::make(
    @bigint.BigInt::from_int(2 * p - p * q + 2 * q),
    @bigint.BigInt::from_int(p),
  )
}

///|
#derive(Eq)
pub(all) enum Geometry {
  Spherical
  Euclidean
  Hyperbolic
}

///|
pub extend Geometry with Eq::{equal, not_equal}

///|
pub fn classify_tessellation(p : Int32, q : Int32) -> Geometry raise Error {
  let c = tessellation_curvature(p, q)
  if c.sign() > 0 {
    Spherical
  } else if c.sign() == 0 {
    Euclidean
  } else {
    Hyperbolic
  }
}

///|
/// 每面 Euler 示性數密度 χ/F = (2p − pq + 2q)/(2q)。
pub fn euler_density_per_face(p : Int32, q : Int32) -> @m20.Rat raise Error {
  if p < 3 || q < 3 {
    raise LatticeError::InvalidTessellation(p, q)
  }
  @m20.Rat::make(
    @bigint.BigInt::from_int(2 * p - p * q + 2 * q),
    @bigint.BigInt::from_int(2 * q),
  )
}

///|
pub(all) struct Graph {
  n : Int32
  adj : Array[Array[Int32]]
}

///|
pub fn Graph::make(
  n : Int32,
  edges : Array[(Int32, Int32)],
) -> Graph raise Error {
  if n <= 0 {
    raise LatticeError::EmptyGraph
  }
  let adj : Array[Array[Int32]] = Array::make(n, [])
  for i = 0; i < n; i = i + 1 {
    adj[i] = []
  }
  for e in edges {
    let (u, v) = e
    if u < 0 || u >= n || v < 0 || v >= n {
      raise LatticeError::GraphIndex(u, v)
    }
    adj[u].push(v)
    adj[v].push(u)
  }
  { n, adj, }
}

///|
/// 廣義 Petersen 圖 G(n,k)：外圈 u_i、內星 v_i；u_i~u_{i+1}, u_i~v_i, v_i~v_{i+k}。
/// G(8,3) = Möbius–Kantor 圖（16 頂點、3-正則、圍長 6，{8,3} Bolza 虧格 2 商骨架）。
pub fn generalized_petersen(n : Int32, k : Int32) -> Graph raise Error {
  if n < 3 || k < 1 || k >= n {
    raise LatticeError::InvalidTessellation(n, k)
  }
  let edges : Array[(Int32, Int32)] = []
  for i = 0; i < n; i = i + 1 {
    edges.push((i, (i + 1) % n))
    edges.push((i, n + i))
    edges.push((n + i, n + (i + k) % n))
  }
  Graph::make(2 * n, edges)
}

///|
pub fn mobius_kantor_bolza() -> Graph raise Error {
  generalized_petersen(8, 3)
}

///|
pub fn path_graph(l : Int32) -> Graph raise Error {
  let edges : Array[(Int32, Int32)] = []
  for i = 0; i + 1 < l; i = i + 1 {
    edges.push((i, i + 1))
  }
  Graph::make(l, edges)
}

///|
pub fn cycle_graph(l : Int32) -> Graph raise Error {
  if l < 3 {
    raise LatticeError::InvalidTessellation(l, 3)
  }
  let edges : Array[(Int32, Int32)] = []
  for i = 0; i < l; i = i + 1 {
    edges.push((i, (i + 1) % l))
  }
  Graph::make(l, edges)
}

///|
/// 笛卡兒積 G□H（堆疊超晶格）：(u,v)~(u',v') iff u=u'且v~v' 或 v=v'且u~u'。
pub fn cartesian_product(g : Graph, h : Graph) -> Graph raise Error {
  let edges : Array[(Int32, Int32)] = []
  let id = (u : Int32, v : Int32) => u * h.n + v
  for u = 0; u < g.n; u = u + 1 {
    for w in g.adj[u] {
      if u < w {
        for v = 0; v < h.n; v = v + 1 {
          edges.push((id(u, v), id(w, v)))
        }
      }
    }
  }
  for v = 0; v < h.n; v = v + 1 {
    for w in h.adj[v] {
      if v < w {
        for u = 0; u < g.n; u = u + 1 {
          edges.push((id(u, v), id(u, w)))
        }
      }
    }
  }
  Graph::make(g.n * h.n, edges)
}

///|
pub fn adjacency_rat(g : Graph) -> @m20.RatMatrix raise Error {
  let m = @m20.RatMatrix::zero(g.n, g.n)
  for u = 0; u < g.n; u = u + 1 {
    for v in g.adj[u] {
      m.set(u, v, @m20.Rat::one())
    }
  }
  m
}

///|
/// Faddeev–LeVerrier 特徵多項式 det(λI−A)（係數低次→高次，精確 ℚ）。
pub fn characteristic_poly(g : Graph) -> Poly raise Error {
  let a = adjacency_rat(g)
  let n = g.n
  let mut m = @m20.RatMatrix::zero(n, n)
  let cs : Array[@m20.Rat] = Array::make(n + 1, @m20.Rat::zero())
  cs[n] = @m20.Rat::one()
  for k = 1; k <= n; k = k + 1 {
    if k == 1 {
      m = @m20.RatMatrix::identity(n)
    } else {
      // M_k = A M_{k-1} + c_{k-1} I
      let am = a.mul(m)
      for i = 0; i < n; i = i + 1 {
        am.set(i, i, am.get(i, i).add(cs[n - k + 1]))
      }
      m = am
    }
    // c_k = −tr(A M_k)/k
    let am = a.mul(m)
    let mut tr = @m20.Rat::zero()
    for i = 0; i < n; i = i + 1 {
      tr = tr.add(am.get(i, i))
    }
    cs[n - k] = tr.div(@m20.Rat::from_int(k)).neg()
  }
  Poly::make(cs)
}

///|
/// Sylvester 結式 Res(f,g)（ℚ 係數，det of Sylvester matrix）。
pub fn resultant(f : Poly, g : Poly) -> @m20.Rat raise Error {
  let m = f.degree()
  let n = g.degree()
  if m < 0 || n < 0 {
    return @m20.Rat::zero()
  }
  if m == 0 {
    // Res(const, g) = const^{deg g}
    let mut acc = @m20.Rat::one()
    for i = 0; i < n; i = i + 1 {
      acc = acc.mul(f.coeff(0))
    }
    return acc
  }
  if n == 0 {
    let mut acc = @m20.Rat::one()
    for i = 0; i < m; i = i + 1 {
      acc = acc.mul(g.coeff(0))
    }
    return acc
  }
  let sz = m + n
  let s = @m20.RatMatrix::zero(sz, sz)
  for i = 0; i < n; i = i + 1 {
    for j = 0; j <= m; j = j + 1 {
      s.set(i, i + j, f.coeff(m - j))
    }
  }
  for i = 0; i < m; i = i + 1 {
    for j = 0; j <= n; j = j + 1 {
      s.set(n + i, i + j, g.coeff(n - j))
    }
  }
  s.det()
}

///|
/// g(x−y) 視為 y 之多項式（固定 x，二項式展開）。
fn shifted_poly(g : Poly, x : @m20.Rat) -> Poly raise Error {
  let acc : Array[@m20.Rat] = Array::make(g.degree() + 1, @m20.Rat::zero())
  for k = 0; k <= g.degree(); k = k + 1 {
    // (x−y)^k = Σ_{j=0}^k C(k,j) x^{k−j} (−1)^j y^j
    let mut binom = @m20.Rat::one()
    for j = 0; j <= k; j = j + 1 {
      let mut xp = @m20.Rat::one()
      for t = 0; t < k - j; t = t + 1 {
        xp = xp.mul(x)
      }
      let sign = if j % 2 == 0 {
        @m20.Rat::one()
      } else {
        @m20.Rat::from_int(-1)
      }
      acc[j] = acc[j].add(g.coeff(k).mul(binom).mul(xp).mul(sign))
      // binom(k, j+1) = binom(k,j)*(k−j)/(j+1)
      binom = binom
        .mul(@m20.Rat::from_int(k - j))
        .div(@m20.Rat::from_int(j + 1))
    }
  }
  Poly::make(acc)
}

///|
/// 堆疊譜定理：charpoly(G□H)(x) = Res_y(p_G(y), p_H(x−y))。
/// 演算法：於 x=0..mn 取樣結式，Vandermonde 精確插值（次數 mn）。
pub fn stacked_charpoly(g : Graph, h : Graph) -> Poly raise Error {
  let pg = characteristic_poly(g)
  let ph = characteristic_poly(h)
  let deg = pg.degree() * ph.degree()
  let samples : Array[@m20.Rat] = []
  for x = 0; x <= deg; x = x + 1 {
    let shifted = shifted_poly(ph, @m20.Rat::from_int(x))
    samples.push(resultant(pg, shifted))
  }
  // Vandermonde 插值：Σ c_i x^i = samples[x]
  let v = @m20.RatMatrix::zero(deg + 1, deg + 1)
  for x = 0; x <= deg; x = x + 1 {
    let mut p = @m20.Rat::one()
    for i = 0; i <= deg; i = i + 1 {
      v.set(x, i, p)
      p = p.mul(@m20.Rat::from_int(x))
    }
  }
  match v.solve(samples) {
    Inconsistent => raise LatticeError::SingularResolvent
    Solution(c, _) => Poly::make(c)
  }
}

///|
/// BFS 全對最短路（無權圖）。
pub fn all_pairs_distance(g : Graph) -> Array[Array[Int32]] {
  let dist : Array[Array[Int32]] = []
  for s = 0; s < g.n; s = s + 1 {
    let d = Array::make(g.n, -1)
    d[s] = 0
    let queue : Array[Int32] = [s]
    let mut head = 0
    while head < queue.length() {
      let u = queue[head]
      head = head + 1
      for w in g.adj[u] {
        if d[w] < 0 {
          d[w] = d[u] + 1
          queue.push(w)
        }
      }
    }
    dist.push(d)
  }
  dist
}

///|
/// Gromov 四點條件 δ：max over (a,b,c,d) of
/// (d(a,b)+d(c,d) − max(d(a,c)+d(b,d), d(a,d)+d(b,c)))/2。精確半整數。
pub fn gromov_delta(g : Graph) -> @m20.Rat raise Error {
  let d = all_pairs_distance(g)
  let mut best = 0
  for a = 0; a < g.n; a = a + 1 {
    for b = a + 1; b < g.n; b = b + 1 {
      for c = b + 1; c < g.n; c = c + 1 {
        for e = c + 1; e < g.n; e = e + 1 {
          let s1 = d[a][b] + d[c][e]
          let s2 = d[a][c] + d[b][e]
          let s3 = d[a][e] + d[b][c]
          let mx = if s2 > s3 { s2 } else { s3 }
          let diff = s1 - mx
          if diff > best {
            best = diff
          }
        }
      }
    }
  }
  @m20.Rat::make(@bigint.BigInt::from_int(best), @bigint.BigInt::from_int(2))
}

///|
fn rat_inverse(m : @m20.RatMatrix) -> @m20.RatMatrix raise Error {
  let n = m.rows
  if n != m.cols {
    raise LatticeError::SingularResolvent
  }
  let inv = @m20.RatMatrix::zero(n, n)
  for j = 0; j < n; j = j + 1 {
    let e = Array::make(n, @m20.Rat::zero())
    e[j] = @m20.Rat::one()
    match m.solve(e) {
      Inconsistent => raise LatticeError::SingularResolvent
      Solution(x, _) =>
        for i = 0; i < n; i = i + 1 {
          inv.set(i, j, x[i])
        }
    }
  }
  inv
}

///|
pub(all) struct LayerDecimation {
  effective_adjacency : @m20.RatMatrix
  ///  resolvent 恆等式證書：(E−A_full)⁻¹|_1 = (E−A_eff)⁻¹
  feshbach_verified : Bool
}

///|
/// Schur 補層抽取（Feshbach 投影）：雙層 [[A,tI],[tI,A]] 於能量 E 抽掉第二層，
/// A_eff = A + t²(E·I−A)⁻¹；驗證保留層 Green 函數恆等式。
pub fn decimate_bilayer(
  a : @m20.RatMatrix,
  t : @m20.Rat,
  energy : @m20.Rat,
) -> LayerDecimation raise Error {
  let n = a.rows
  if n != a.cols {
    raise LatticeError::SingularResolvent
  }
  let ei_minus_a = @m20.RatMatrix::zero(n, n)
  for i = 0; i < n; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      let v = a.get(i, j).neg()
      ei_minus_a.set(i, j, if i == j { v.add(energy) } else { v })
    }
  }
  let resolvent = rat_inverse(ei_minus_a)
  let t2 = t.mul(t)
  let a_eff = @m20.RatMatrix::zero(n, n)
  for i = 0; i < n; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      a_eff.set(i, j, a.get(i, j).add(t2.mul(resolvent.get(i, j))))
    }
  }
  // full 2n×2n resolvent 之 (1,1) 塊
  let full = @m20.RatMatrix::zero(2 * n, 2 * n)
  for i = 0; i < n; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      let v = a.get(i, j).neg()
      full.set(i, j, if i == j { v.add(energy) } else { v })
      full.set(n + i, n + j, if i == j { v.add(energy) } else { v })
      let coup = if i == j { t.neg() } else { @m20.Rat::zero() }
      full.set(i, n + j, coup)
      full.set(n + i, j, coup)
    }
  }
  let full_inv = rat_inverse(full)
  let eff_inv = @m20.RatMatrix::zero(n, n)
  for i = 0; i < n; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      let v = a_eff.get(i, j).neg()
      eff_inv.set(i, j, if i == j { v.add(energy) } else { v })
    }
  }
  let eff_resolvent = rat_inverse(eff_inv)
  let mut ok = true
  for i = 0; i < n; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      if full_inv.get(i, j) != eff_resolvent.get(i, j) {
        ok = false
      }
    }
  }
  { effective_adjacency: a_eff, feshbach_verified: ok, }
}
