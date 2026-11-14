///|
/// Module M16 (Part 1) — Finite Geometric Spaces: integer metric spaces with
/// geodesic betweenness, combinatorial Gauss–Bonnet (Descartes angular defect)
/// on regular-faced polyhedra, and graph U(1) connections with gauge-invariant
/// cycle holonomy.  The holonomy of a connection on a geometric space is the
/// discrete Berry phase; Part 2 lifts this to the Brillouin-zone torus.

///|
pub(all) suberror GeoError {
  InvalidMetric(String)
  InvalidPolyhedron(String)
  InvalidConnection(String)
}

///|
pub(all) struct FiniteMetric {
  n : Int32
  dist : Array[Array[Int32]]
}

///|
pub fn FiniteMetric::make(
  n : Int32,
  dist : Array[Array[Int32]],
) -> FiniteMetric raise Error {
  if n <= 0 || dist.length() != n {
    raise GeoError::InvalidMetric("shape")
  }
  for i = 0; i < n; i = i + 1 {
    if dist[i].length() != n || dist[i][i] != 0 {
      raise GeoError::InvalidMetric("diagonal")
    }
    for j = 0; j < n; j = j + 1 {
      if dist[i][j] < 0 || dist[i][j] != dist[j][i] {
        raise GeoError::InvalidMetric("symmetry/positivity")
      }
    }
  }
  for i = 0; i < n; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      for k = 0; k < n; k = k + 1 {
        if dist[i][k] > dist[i][j] + dist[j][k] {
          raise GeoError::InvalidMetric("triangle inequality")
        }
      }
    }
  }
  { n, dist, }
}

///|
/// 測地中間性：b 在 a→c 測地線上 iff d(a,c) = d(a,b)+d(b,c)。
pub fn FiniteMetric::is_between(
  self : FiniteMetric,
  a : Int32,
  b : Int32,
  c : Int32,
) -> Bool {
  self.dist[a][c] == self.dist[a][b] + self.dist[b][c]
}

///|
pub(all) struct Polyhedron {
  vertices : Int32
  faces : Array[Array[Int32]]
}

///|
pub(all) struct GaussBonnetCertificate {
  euler_char : Int32
  /// 每頂點角虧（π 單位，精確有理）
  defects : Array[@m20.Rat]
  /// Σ defects = 2χ（Descartes–Gauss–Bonnet）
  gauss_bonnet_holds : Bool
}

///|
/// 正則面多面體之組合 Gauss–Bonnet：正 k 邊形內角 (k−2)/k·π，
/// 頂點角虧 = 2 − Σ_{面∋v}(k−2)/k；Σ 角虧 = 2V−2E+2F = 2χ。
pub fn gauss_bonnet(poly : Polyhedron) -> GaussBonnetCertificate raise Error {
  let v = poly.vertices
  if v <= 0 || poly.faces.length() == 0 {
    raise GeoError::InvalidPolyhedron("empty")
  }
  let defects : Array[@m20.Rat] = Array::make(v, @m20.Rat::from_int(2))
  let edge_count : Map[String, Int32] = Map([])
  for f in poly.faces {
    let k = f.length()
    if k < 3 {
      raise GeoError::InvalidPolyhedron("face size < 3")
    }
    let angle = @m20.Rat::make(
      @bigint.BigInt::from_int(k - 2),
      @bigint.BigInt::from_int(k),
    )
    for i = 0; i < k; i = i + 1 {
      let vert = f[i]
      if vert < 0 || vert >= v {
        raise GeoError::InvalidPolyhedron("vertex index")
      }
      defects[vert] = defects[vert].sub(angle)
      let a = f[i]
      let b = f[(i + 1) % k]
      let key = if a < b {
        a.to_string() + "-" + b.to_string()
      } else {
        b.to_string() + "-" + a.to_string()
      }
      edge_count[key] = match edge_count.get(key) {
        Some(c) => c + 1
        None => 1
      }
    }
  }
  let mut total_face_edges = 0
  for f in poly.faces {
    total_face_edges = total_face_edges + f.length()
  }
  for kv in edge_count {
    let (_, c) = kv
    if c != 2 {
      raise GeoError::InvalidPolyhedron("edge not shared by exactly 2 faces")
    }
  }
  let e = total_face_edges / 2
  let f = poly.faces.length()
  let chi = v - e + f
  let mut total = @m20.Rat::zero()
  for d in defects {
    total = total.add(d)
  }
  {
    euler_char: chi,
    defects,
    gauss_bonnet_holds: total == @m20.Rat::from_int(2 * chi),
  }
}

///|
pub fn tetrahedron() -> Polyhedron {
  { vertices: 4, faces: [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]], }
}

///|
pub fn cube() -> Polyhedron {
  {
    vertices: 8,
    faces: [
      [0, 1, 2, 3],
      [4, 5, 6, 7],
      [0, 1, 5, 4],
      [1, 2, 6, 5],
      [2, 3, 7, 6],
      [3, 0, 4, 7],
    ],
  }
}

///|
pub fn octahedron() -> Polyhedron {
  {
    vertices: 6,
    faces: [
      [0, 2, 4],
      [0, 4, 3],
      [0, 3, 5],
      [0, 5, 2],
      [1, 2, 5],
      [1, 5, 3],
      [1, 3, 4],
      [1, 4, 2],
    ],
  }
}

///|
pub fn icosahedron() -> Polyhedron {
  {
    vertices: 12,
    faces: [
      [0, 1, 2],
      [0, 2, 3],
      [0, 3, 4],
      [0, 4, 5],
      [0, 5, 1],
      [1, 6, 2],
      [2, 6, 7],
      [2, 7, 3],
      [3, 7, 8],
      [3, 8, 4],
      [4, 8, 9],
      [4, 9, 5],
      [5, 9, 10],
      [5, 10, 1],
      [1, 10, 6],
      [11, 6, 7],
      [11, 7, 8],
      [11, 8, 9],
      [11, 9, 10],
      [11, 10, 6],
    ],
  }
}

///|
/// 圖上 U(1) 聯絡（Z_n 格點規範）：每有向邊賦相位 link ∈ Z_n。
pub(all) struct GraphU1 {
  n : Int32
  modulus : Int32
  edges : Array[(Int32, Int32)]
  link : Array[Int32]
}

///|
pub fn GraphU1::make(
  n : Int32,
  modulus : Int32,
  edges : Array[(Int32, Int32)],
  link : Array[Int32],
) -> GraphU1 raise Error {
  if n <= 0 || modulus < 2 || link.length() != edges.length() {
    raise GeoError::InvalidConnection("shape")
  }
  let lk : Array[Int32] = []
  for i = 0; i < edges.length(); i = i + 1 {
    let (u, v) = edges[i]
    if u < 0 || u >= n || v < 0 || v >= n {
      raise GeoError::InvalidConnection("edge index")
    }
    lk.push((link[i] % modulus + modulus) % modulus)
  }
  { n, modulus, edges, link: lk, }
}

///|
fn mod_n(a : Int32, n : Int32) -> Int32 {
  (a % n + n) % n
}

///|
/// 沿閉合路徑（頂點序列，首尾相連）之 Wilson 圈 holonomy = Σ 有向 link (mod n)。
pub fn GraphU1::cycle_holonomy(
  self : GraphU1,
  cycle : Array[Int32],
) -> Int32 raise Error {
  if cycle.length() < 2 {
    raise GeoError::InvalidConnection("cycle too short")
  }
  let mut acc = 0
  for i = 0; i < cycle.length(); i = i + 1 {
    let u = cycle[i]
    let v = cycle[(i + 1) % cycle.length()]
    // find edge (u,v) or (v,u)
    let mut found = false
    for e = 0; e < self.edges.length(); e = e + 1 {
      let (a, b) = self.edges[e]
      if a == u && b == v {
        acc = acc + self.link[e]
        found = true
        break
      } else if a == v && b == u {
        acc = acc - self.link[e]
        found = true
        break
      }
    }
    if !found {
      raise GeoError::InvalidConnection("cycle edge missing")
    }
  }
  mod_n(acc, self.modulus)
}

///|
/// 規範變換 g : V → Z_n：link(u,v) → link + g(v) − g(u)。閉圈 holonomy 不變。
pub fn GraphU1::gauge_transform(
  self : GraphU1,
  g : Array[Int32],
) -> GraphU1 raise Error {
  if g.length() != self.n {
    raise GeoError::InvalidConnection("gauge shape")
  }
  let lk : Array[Int32] = []
  for e = 0; e < self.edges.length(); e = e + 1 {
    let (u, v) = self.edges[e]
    lk.push(mod_n(self.link[e] + g[v] - g[u], self.modulus))
  }
  { n: self.n, modulus: self.modulus, edges: self.edges, link: lk, }
}

///|
pub fn holonomy_gauge_invariance_certificate(
  conn : GraphU1,
  cycle : Array[Int32],
  g : Array[Int32],
) -> Bool raise Error {
  let h1 = conn.cycle_holonomy(cycle)
  let h2 = conn.gauge_transform(g).cycle_holonomy(cycle)
  h1 == h2
}
