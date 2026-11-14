///|
/// Module M25 (Part 5) — Ribbon / Fat Graphs (權重樹圖之真實內容):
/// a ribbon graph is a graph TOGETHER WITH a cyclic order of half-edges
/// (darts) at each vertex.  With α the fixed-point-free involution pairing
/// darts into edges and σ the vertex rotation, the faces are the cycles of
/// φ = σ∘α, and the genus of the ambient surface follows from
///     V − E + F = 2 − 2g.
/// This is genuinely finer than an abstract graph: the SAME abstract graph
/// with different cyclic orders yields DIFFERENT genus (verified below).
/// Vertex genus weights then give the total arithmetic genus
///     g_total = Σ g_v + g(ribbon),
/// and the supermoduli dimension separates NS and Ramond punctures:
///     (3g−3+n_NS+n_R | 2g−2+n_NS+n_R/2).

///|
/// Ribbon 圖：vertices[v] = 該頂點之 dart 循環序；num_edges = E。
/// dart 2i 與 2i+1 配對成第 i 條邊。
pub(all) struct RibbonGraph {
  vertices : Array[Array[Int32]]
  num_edges : Int32
}

///|
pub fn RibbonGraph::make(
  vertices : Array[Array[Int32]],
  num_edges : Int32,
) -> RibbonGraph raise Error {
  let nd = 2 * num_edges
  let seen = Array::make(nd, false)
  for cyc in vertices {
    for d in cyc {
      if d < 0 || d >= nd || seen[d] {
        raise SuperGeomError::InvalidSuperField("dart index / repetition")
      }
      seen[d] = true
    }
  }
  for s in seen {
    if !s {
      raise SuperGeomError::InvalidSuperField("dart not assigned to a vertex")
    }
  }
  { vertices, num_edges, }
}

///|
/// α：dart 對合（2i ↔ 2i+1）。
fn alpha_dart(d : Int32) -> Int32 {
  if d % 2 == 0 {
    d + 1
  } else {
    d - 1
  }
}

///|
/// σ：頂點旋轉（循環序之下一個）。
pub fn RibbonGraph::sigma(self : RibbonGraph) -> Array[Int32] {
  let nd = 2 * self.num_edges
  let s = Array::make(nd, 0)
  for cyc in self.vertices {
    for i = 0; i < cyc.length(); i = i + 1 {
      s[cyc[i]] = cyc[(i + 1) % cyc.length()]
    }
  }
  s
}

///|
/// 面 = φ = σ∘α 之循環。
pub fn RibbonGraph::faces(self : RibbonGraph) -> Array[Array[Int32]] {
  let nd = 2 * self.num_edges
  let s = self.sigma()
  let seen = Array::make(nd, false)
  let out : Array[Array[Int32]] = []
  for start = 0; start < nd; start = start + 1 {
    if seen[start] {
      continue
    }
    let cyc : Array[Int32] = []
    let mut d = start
    while !seen[d] {
      seen[d] = true
      cyc.push(d)
      d = s[alpha_dart(d)]
    }
    out.push(cyc)
  }
  out
}

///|
pub fn RibbonGraph::face_count(self : RibbonGraph) -> Int32 {
  self.faces().length()
}

///|
/// Euler 特徵 V − E + F。
pub fn RibbonGraph::euler_characteristic(self : RibbonGraph) -> Int32 {
  self.vertices.length() - self.num_edges + self.face_count()
}

///|
/// Ribbon genus g = (2 − V + E − F)/2（需連通）。
pub fn RibbonGraph::genus(self : RibbonGraph) -> Int32 raise Error {
  let chi = self.euler_characteristic()
  if (2 - chi) % 2 != 0 {
    raise SuperGeomError::InvalidSuperField("non-orientable / disconnected")
  }
  (2 - chi) / 2
}

///|
/// Ribbon 圖證書：同一抽象圖、不同循環序 ⇒ 不同 genus。
/// 單頂點兩自環（V=1,E=2）：序 [0,2,1,3] 給 g=1；序 [0,1,2,3] 給 g=0。
pub fn ribbon_genus_certificate() -> Bool raise Error {
  // 樹：V=2, E=1, F=1 → g=0
  let tree = RibbonGraph::make([[0], [1]], 1)
  if tree.face_count() != 1 || tree.genus() != 0 {
    return false
  }
  // 單頂點兩自環，交錯序 → 環面 g=1, F=1
  let torus = RibbonGraph::make([[0, 2, 1, 3]], 2)
  if torus.face_count() != 1 || torus.genus() != 1 {
    return false
  }
  // 同一抽象圖，非交錯序 → 平面 g=0, F=3
  let plane = RibbonGraph::make([[0, 1, 2, 3]], 2)
  if plane.face_count() != 3 || plane.genus() != 0 {
    return false
  }
  // 兩者抽象圖相同（同 V,E）但 genus 不同 ⇒ ribbon 結構真係有內容
  if torus.vertices.length() != plane.vertices.length() {
    return false
  }
  if torus.num_edges != plane.num_edges {
    return false
  }
  torus.genus() != plane.genus()
}

///|
/// 帶 genus 權重之 ribbon 圖總 genus：g_total = Σ g_v + g(ribbon)。
pub fn weighted_ribbon_genus(
  rb : RibbonGraph,
  genus_weights : Array[Int32],
) -> Int32 raise Error {
  if genus_weights.length() != rb.vertices.length() {
    raise SuperGeomError::InvalidSuperField("weight count")
  }
  let mut s = 0
  for g in genus_weights {
    if g < 0 {
      raise SuperGeomError::InvalidSuperField("negative weight")
    }
    s = s + g
  }
  s + rb.genus()
}

///|
/// 超模空間維度（正確分離 NS / Ramond）：
/// (3g−3+n_NS+n_R | 2g−2+n_NS+n_R/2)，要求 n_R 偶。
pub fn supermoduli_dimension_ns_ramond(
  g : Int32,
  n_ns : Int32,
  n_r : Int32,
) -> (Int32, Int32) raise Error {
  if g < 0 || n_ns < 0 || n_r < 0 {
    raise SuperGeomError::InvalidSuperField("negative input")
  }
  if n_r % 2 != 0 {
    raise SuperGeomError::InvalidSuperField("Ramond count must be even")
  }
  (3 * g - 3 + n_ns + n_r, 2 * g - 2 + n_ns + n_r / 2)
}

///|
/// 權重 ribbon + NS/Ramond 維度證書。
pub fn weighted_ribbon_supermoduli_certificate() -> Bool raise Error {
  let torus = RibbonGraph::make([[0, 2, 1, 3]], 2)
  // 單頂點權重 2 + ribbon genus 1 → g_total = 3
  if weighted_ribbon_genus(torus, [2]) != 3 {
    return false
  }
  // 閉合 g=3 → (6|4)
  let (e0, o0) = supermoduli_dimension_ns_ramond(3, 0, 0)
  if e0 != 6 || o0 != 4 {
    return false
  }
  // g=2, 2 NS, 2 Ramond → (3·2−3+2+2 | 2·2−2+2+1) = (7|5)
  let (e1, o1) = supermoduli_dimension_ns_ramond(2, 2, 2)
  if e1 != 7 || o1 != 5 {
    return false
  }
  // 純 NS：g=2, 3 NS → (6|5)
  let (e2, o2) = supermoduli_dimension_ns_ramond(2, 3, 0)
  if e2 != 6 || o2 != 5 {
    return false
  }
  // 純 Ramond：g=2, 4 R → (7|4)
  let (e3, o3) = supermoduli_dimension_ns_ramond(2, 0, 4)
  e3 == 7 && o3 == 4
}
