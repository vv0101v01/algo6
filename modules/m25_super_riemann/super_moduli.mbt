///|
/// Module M25 (Part 3) — Closed Superspace, Supermoduli & Weighted Dual Graphs:
/// the supermoduli dimension (3g−3+n | 2g−2+n) of a stable super curve,
/// weighted dual graphs with genus formula g = Σ g_v + b₁(Γ), vertex stability
/// 2g_v−2+n_v > 0, and Berezinian line-bundle gluing coherence via the actual
/// Čech cocycle w₀₂ = w₀₁·(w₁₂∘g₀₁) (Part 4). NS/Ramond dimensions delegate to
/// supermoduli_dimension_ns_ramond as the single source of truth.

///|
/// 權重對偶圖：頂點帶 genus 權重 g_v 與 NS 標記數 marks[v]，邊為節點。
pub(all) struct WeightedDualGraph {
  genus_weights : Array[Int32]
  marks : Array[Int32]
  edges : Array[(Int32, Int32)]
}

///|
pub fn WeightedDualGraph::make(
  genus_weights : Array[Int32],
  marks : Array[Int32],
  edges : Array[(Int32, Int32)],
) -> WeightedDualGraph raise Error {
  let v = genus_weights.length()
  if marks.length() != v {
    raise SuperGeomError::InvalidSuperField("marks length")
  }
  for g in genus_weights {
    if g < 0 {
      raise SuperGeomError::InvalidSuperField("negative genus weight")
    }
  }
  for (a, b) in edges {
    if a < 0 || a >= v || b < 0 || b >= v {
      raise SuperGeomError::InvalidSuperField("edge index")
    }
  }
  { genus_weights, marks, edges, }
}

///|
/// 連通分量數（並查集）。
fn graph_components(g : WeightedDualGraph) -> Int32 {
  let v = g.genus_weights.length()
  let parent = Array::make(v, 0)
  for i = 0; i < v; i = i + 1 {
    parent[i] = i
  }
  fn find(x : Int32) -> Int32 {
    let mut r = x
    while parent[r] != r {
      r = parent[r]
    }
    r
  }
  for (a, b) in g.edges {
    let ra = find(a)
    let rb = find(b)
    if ra != rb {
      parent[ra] = rb
    }
  }
  let mut count = 0
  for i = 0; i < v; i = i + 1 {
    if find(i) == i {
      count = count + 1
    }
  }
  count
}

///|
/// 第一 Betti 數 b₁ = E − V + components。
pub fn WeightedDualGraph::first_betti(self : WeightedDualGraph) -> Int32 {
  self.edges.length() - self.genus_weights.length() + graph_components(self)
}

///|
/// 總 genus g = Σ g_v + b₁(Γ)。
pub fn WeightedDualGraph::total_genus(self : WeightedDualGraph) -> Int32 {
  let mut s = 0
  for g in self.genus_weights {
    s = s + g
  }
  s + self.first_betti()
}

///|
/// 頂點穩定性：2g_v − 2 + n_v > 0，n_v = 邊價 + marks[v]。
pub fn WeightedDualGraph::is_stable(self : WeightedDualGraph) -> Bool {
  let v = self.genus_weights.length()
  let valence = Array::make(v, 0)
  for (a, b) in self.edges {
    valence[a] = valence[a] + 1
    valence[b] = valence[b] + 1
  }
  for i = 0; i < v; i = i + 1 {
    let n_v = valence[i] + self.marks[i]
    if 2 * self.genus_weights[i] - 2 + n_v <= 0 {
      return false
    }
  }
  true
}

///|
/// 超模空間維度 (even|odd) = (3g−3+n | 2g−2+n)，n = Σ marks（NS 穿孔）。
pub fn WeightedDualGraph::supermoduli_dimension(
  self : WeightedDualGraph,
) -> (Int32, Int32) raise Error {
  self.supermoduli_dimension_with_ramond(0)
}

///|
/// 帶 Ramond 穿孔之超模維度；marks 視為 NS 穿孔數。
/// 委派至 `supermoduli_dimension_ns_ramond` 作單一真相來源，
/// 避免兩處硬寫算式而 Ramond 項不一致。
pub fn WeightedDualGraph::supermoduli_dimension_with_ramond(
  self : WeightedDualGraph,
  n_r : Int32,
) -> (Int32, Int32) raise Error {
  let g = self.total_genus()
  let mut n = 0
  for m in self.marks {
    n = n + m
  }
  supermoduli_dimension_ns_ramond(g, n, n_r)
}

///|
/// 閉合超空間（n=0, g≥2）之超模空間維度 (3g−3 | 2g−2)。
pub fn closed_supermoduli_dimension(g : Int32) -> (Int32, Int32) raise Error {
  if g < 2 {
    raise SuperGeomError::InvalidSuperField("closed supermoduli needs g >= 2")
  }
  supermoduli_dimension_ns_ramond(g, 0, 0)
}

///|
/// 權重對偶圖 genus 公式證書：構造已知 genus 之穩定圖驗證 g=Σg_v+b₁。
pub fn weighted_graph_genus_certificate() -> Bool raise Error {
  // 單一頂點 g=3，無邊無標記：g=3, b1=0
  let g3 = WeightedDualGraph::make([3], [0], [])
  if g3.total_genus() != 3 || g3.first_betti() != 0 || !g3.is_stable() {
    return false
  }
  // 兩頂點 g=1,g=2，三條邊（b1=3−2+1=2）：g=1+2+2=5
  let g5 = WeightedDualGraph::make([1, 2], [0, 0], [(0, 1), (0, 1), (0, 1)])
  if g5.total_genus() != 5 || g5.first_betti() != 2 {
    return false
  }
  // 啞鈴圖：兩 g=1 頂點各帶一自環 + 一 connecting 邊 → b1=3−2+1=2, g=1+1+2=4
  let dumbbell = WeightedDualGraph::make([1, 1], [0, 0], [
    (0, 0),
    (1, 1),
    (0, 1),
  ])
  if dumbbell.total_genus() != 4 || dumbbell.first_betti() != 2 {
    return false
  }
  // 不穩定圖：g=0 單頂點無標記 → 2·0−2+0=−2 ≤ 0
  let unstable = WeightedDualGraph::make([0], [0], [])
  if unstable.is_stable() {
    return false
  }
  // g=0 帶 3 標記 → 穩定（2·0−2+3=1>0）
  let stable0 = WeightedDualGraph::make([0], [3], [])
  if !stable0.is_stable() {
    return false
  }
  true
}

///|
/// 超模空間維度證書：閉合 g=2 → (3|2)，g=3 → (6|4)；帶 n 穿孔之穩定圖一致。
pub fn supermoduli_dimension_certificate() -> Bool raise Error {
  let (e2, o2) = closed_supermoduli_dimension(2)
  if e2 != 3 || o2 != 2 {
    return false
  }
  let (e3, o3) = closed_supermoduli_dimension(3)
  if e3 != 6 || o3 != 4 {
    return false
  }
  let g3 = WeightedDualGraph::make([3], [0], [])
  let (eg, og) = g3.supermoduli_dimension()
  if eg != 6 || og != 4 {
    return false
  }
  // g=2 帶 2 NS 穿孔 → (3·2−3+2 | 2·2−2+2) = (5|4)
  let g2n2 = WeightedDualGraph::make([2], [2], [])
  let (e2n, o2n) = g2n2.supermoduli_dimension()
  e2n == 5 && o2n == 4
}

///|
/// Berezinian 線束黏合連貫性證書：由**實際複合**超共形映射驗證
/// Čech 上循環 w₀₂ = w₀₁·(w₁₂∘g₀₁)（見 Part 4）。
/// 舊版以人手揀定 factors [2,3,1/6] 令積=1，屬恆真檢查，已移除。
pub fn berezinian_gluing_coherence_certificate() -> Bool raise Error {
  ber_line_bundle_cocycle_certificate() &&
  omega_is_d_inverse_by_transitions_certificate()
}
