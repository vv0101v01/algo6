///|
/// Module M28 — Super Fusion Bridges (結合・橋接・嵌入・聯動・層級):
/// B1 superconformal Berezinian exact sequence ↔ spectral-sequence convergence
///    (M25 ↔ M21/M27): exactness ↔ E_∞ = 0, Ber parity ↔ superdimension.
/// B2 hyperoctahedral parity grading ↔ Schreier–Sims obstruction orbits
///    (M26 ↔ M23): B_n/D_n index 2 parallels S_n/A_n index 2.
/// B3 weighted dual-graph genus ↔ spectral-page hierarchy (M25 ↔ M21/M27):
///    g = Σ g_v + b₁(Γ) parallels Σ_p E_∞^{p,n−p} = dim H^n.
/// B4 superconformal weight ↔ d_r bidegree shift (M25 ↔ M27): both Z-graded.

///|
pub(all) suberror SuperFusionError {
  FusionMismatch(String)
}

///|
/// B1：超共形 Berezinian 正合序列 ↔ 譜序列收斂。
/// 正合序列 0→D→T→D²→0 之「正合」對應無環過濾複形之 E_∞=0；
/// Ber 宇稱（奇）對應超模空間超維度之奇偶。
pub fn superconformal_ber_spectral_bridge() -> Bool raise Error {
  if !@m25.srs_exact_sequence_certificate() {
    return false
  }
  // 無環過濾複形 C^0(f0) --1--> C^1(f1)，譜序列收斂至 E_∞=0
  let d = @m20.RatMatrix::from_ints(1, 1, [1])
  let cx = @m21.FilteredComplex::make([1, 1], [[0], [1]], [d])
  let ss = @m21.spectral_sequence(cx)
  if !ss.converged {
    return false
  }
  if ss.pages[ss.pages.length() - 1].total_dim != 0 {
    return false
  }
  // 高階微分證書一致
  if !@m27.explicit_differential_certificate(cx, 1) {
    return false
  }
  // 超模空間超維度 (3g−3)−(2g−2) = g−1（g=3 → 2）
  let (e, o) = @m25.closed_supermoduli_dimension(3)
  e - o == 2
}

///|
/// B2：超八面體 parity grading ↔ 阻撓軌道。B_n/D_n 指數 2 ↔ S_n/A_n 指數 2。
pub fn parity_obstruction_super_bridge(n : Int32) -> Bool raise Error {
  if n < 3 {
    raise SuperFusionError::FusionMismatch("n >= 3")
  }
  if !@m26.super_grading_certificate(n) {
    return false
  }
  if !@m23.parity_obstruction_certificate(n) {
    return false
  }
  // B_n/D_n 指數 2 已由 super_grading_certificate 真實計算兩群階數驗證；
  // 呢度只獨立驗證 S_n/A_n 指數 2（唔再用 bn/2*2==bn 恆真式）。
  let sn = @m23.schreier_sims(n, @m23.symmetric_generators(n))
  let an = @m23.schreier_sims(n, @m23.alternating_generators(n))
  an.order * @bigint.BigInt::from_int(2) == sn.order
}

///|
/// B3：權重對偶圖 genus ↔ 譜序列頁層級。g=Σg_v+b₁ ↔ Σ_p E_∞=dim H。
pub fn weighted_graph_spectral_hierarchy_bridge() -> Bool raise Error {
  if !@m25.weighted_graph_genus_certificate() {
    return false
  }
  // 非零 d_2 之過濾複形：C^0(f0)--0-->C^1(f0)--1-->C^2(f2)
  let d0 = @m20.RatMatrix::from_ints(1, 1, [0])
  let d1 = @m20.RatMatrix::from_ints(1, 1, [1])
  let cx = @m21.FilteredComplex::make([1, 1, 1], [[0], [0], [2]], [d0, d1])
  let ss = @m21.spectral_sequence(cx)
  if !ss.converged {
    return false
  }
  // 頁 total_dim 非遞增（層級關係）
  for i = 1; i < ss.pages.length(); i = i + 1 {
    if ss.pages[i].total_dim > ss.pages[i - 1].total_dim {
      return false
    }
  }
  // 高階微分 d_2 顯式矩陣非零且 E_3=H(E_2,d_2)
  if !@m27.explicit_differential_certificate(cx, 2) {
    return false
  }
  let dr2 = @m27.spectral_differential(cx, 0, 1, 2)
  dr2.matrix.get(0, 0) == @m20.Rat::one()
}

///|
/// B4：超共形權重 ↔ d_r 雙次數移位。權重因子 a^m·a^n=a^{m+n} ↔
/// d_r 移位 (r,1−r) 之複合可加。
pub fn superconformal_weight_dr_shift_bridge() -> Bool raise Error {
  let a = @m20.Rat::from_int(2)
  let w2 = @m25.superconformal_weight_factor(a, 2)
  let w3 = @m25.superconformal_weight_factor(a, 3)
  let w5 = @m25.superconformal_weight_factor(a, 5)
  let prod = w2.mul(w3)
  if prod.coeffs[0] != w5.coeffs[0] {
    return false
  }
  if prod.coeffs[0] != @m20.Rat::from_int(32) {
    return false
  }
  // d_r 移位 (r,1−r) 之**真實驗證**：顯式矩陣之目標維度必須等於
  // E_r^{p+r,q−r+1} 之維度（由 M21 代表元獨立算出）。
  // 舊版 `dp+dp != 2*r` 屬恆真，已移除。
  let d0 = @m20.RatMatrix::from_ints(1, 1, [0])
  let d1 = @m20.RatMatrix::from_ints(1, 1, [1])
  let cx = @m21.FilteredComplex::make([1, 1, 1], [[0], [0], [2]], [d0, d1])
  let mut checked = 0
  for r = 1; r <= 3; r = r + 1 {
    for p = 0; p <= 2; p = p + 1 {
      for q = 0; q <= 2; q = q + 1 {
        if p + q >= 3 {
          continue
        }
        let dr = @m27.spectral_differential(cx, p, q, r)
        let target = @m21.e_r_representatives(cx, p + r, q - r + 1, r)
        if dr.target_dim != target.cols {
          return false
        }
        let source = @m21.e_r_representatives(cx, p, q, r)
        if dr.source_dim != source.cols {
          return false
        }
        checked = checked + 1
      }
    }
  }
  checked > 0
}

///|
/// 總超融合證書：四條橋同時成立。
pub fn unified_super_fusion_certificate() -> Bool raise Error {
  if !superconformal_ber_spectral_bridge() {
    return false
  }
  if !weighted_graph_spectral_hierarchy_bridge() {
    return false
  }
  if !superconformal_weight_dr_shift_bridge() {
    return false
  }
  parity_obstruction_super_bridge(3)
}
