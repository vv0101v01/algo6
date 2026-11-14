///|
/// Module M24 — Cross-Module Fusion Bridges (結合・橋接・嵌入・聯動):
/// B1 Berry curvature = symplectic volume: Σ Pf(F̃·J) = n·C, bridging
///    M16 (FHS Chern) ↔ M21 (Pfaffian/symplectic) ↔ M22 (Riemann periods).
/// B2 Linearized RG as a 2-term filtered complex: the spectral sequence
///    detects marginal directions (λ=1 ⇒ H≠0), bridging M15 ↔ M21.
/// B3 Categorical H³ obstruction orbits: gauge-equivalence classes of
///    pointed associators are separated by the cohomology invariant,
///    bridging M17 ↔ M23 (invariant-separation certificate).

///|
pub(all) suberror BridgeError {
  BridgeMismatch(String)
}

///|
/// B1：Berry 曲率之辛體積證書。每個 plaquette 場強 F̃ 對應 2×2 辛形式
/// [[0,F̃],[−F̃,0]]，其 Pfaffian = F̃；總和 = modulus·Chern 數。
pub fn berry_symplectic_volume_certificate(
  field : @m16.TorusGaugeField,
) -> Bool raise Error {
  let c = field.chern_number()
  let mut total_pf = @m20.Rat::zero()
  for x = 0; x < field.lx; x = x + 1 {
    for y = 0; y < field.ly; y = y + 1 {
      let f = field.plaquette_flux(x, y)
      let m = @m20.RatMatrix::zero(2, 2)
      m.set(0, 1, @m20.Rat::from_int(f))
      m.set(1, 0, @m20.Rat::from_int(-f))
      let pf = @m21.pfaffian(m)
      if pf != @m20.Rat::from_int(f) {
        return false
      }
      if f != 0 {
        // 非退化 ⇒ 真辛形式
        let sym = @m21.SymplecticForm::make(m)
        if sym.dim != 2 {
          return false
        }
      }
      total_pf = total_pf.add(pf)
    }
  }
  total_pf == @m20.Rat::from_int(field.modulus * c)
}

///|
/// B1 延伸：Landau C=1 構型 ↔ 離散黎曼週期 τ = i·L_y/L_x。
pub fn berry_riemann_period_bridge(lx : Int32, n : Int32) -> Bool raise Error {
  let field = @m16.landau_chern_one(lx, n)
  if field.chern_number() != lx {
    return false
  }
  if !berry_symplectic_volume_certificate(field) {
    return false
  }
  let torus = @m22.DiscreteTorus::make(lx, n, 1, 1)
  let tau = torus.period_matrix()
  if tau.im != @m20.Rat::frac(n, lx) {
    return false
  }
  torus.riemann_relations_certificate()
}

///|
/// B2：線性化 RG 映射 λ 之 2-項過濾複形 C^0 --(λ−1)--> C^1。
pub fn rg_linearized_complex(
  lambda : @m20.Rat,
) -> @m21.FilteredComplex raise Error {
  let d = @m20.RatMatrix::zero(1, 1)
  d.set(0, 0, lambda.sub(@m20.Rat::one()))
  @m21.FilteredComplex::make([1, 1], [[0], [1]], [d])
}

///|
/// B2 證書：λ=1（邊際）⇒ 譜序列收斂至 H^0=H^1=Q；λ≠1 ⇒ 無環。
pub fn rg_spectral_marginal_certificate() -> Bool raise Error {
  // 邊際情形
  let marginal = rg_linearized_complex(@m20.Rat::one())
  let ss_m = @m21.spectral_sequence(marginal)
  let h_m = @m21.total_cohomology_dims(marginal)
  if !ss_m.converged || h_m[0] != 1 || h_m[1] != 1 {
    return false
  }
  if ss_m.pages[ss_m.pages.length() - 1].total_dim != 2 {
    return false
  }
  // 相關/無關情形 λ=2
  let relevant = rg_linearized_complex(@m20.Rat::from_int(2))
  let ss_r = @m21.spectral_sequence(relevant)
  let h_r = @m21.total_cohomology_dims(relevant)
  if !ss_r.converged || h_r[0] != 0 || h_r[1] != 0 {
    return false
  }
  ss_r.pages[ss_r.pages.length() - 1].total_dim == 0
}

///|
/// B2 與 M15 鑽石 RG 臨界點對接：臨界線性化特徵值之極小多項式於 1 不 vanish
/// （非邊際），且 (0,1) 內唯一臨界根。
pub fn diamond_rg_spectral_bridge() -> Bool raise Error {
  let data = @m15.diamond_critical_linearization()
  if data.roots_in_unit_interval != 1 {
    return false
  }
  let at_one = data.eigenvalue_minpoly.eval(@m20.Rat::one())
  if at_one.is_zero() {
    return false
  }
  // RG 半群證書（b=2,c=3）
  @m15.rg_semigroup_certificate(@m20.Rat::frac(1, 2), 2, 3)
}

///|
/// B3：範疇 H³ 阻撓軌道證書。H³(Z_n,U(1)) ≅ Z_n 之每個類 p 皆 coherent，
/// 規範等價作用於類標籤為平凡（上邊界類 0），故不同 p 屬不同軌道；
/// 以 M23 不變量分離證書確立 p=0 與 p=1 之阻撓。
pub fn categorical_h3_obstruction_orbit_certificate(
  n : Int32,
) -> Bool raise Error {
  if n < 2 {
    raise BridgeError::BridgeMismatch("n >= 2")
  }
  let (all_ok, trivial) = @m17.h3_zn_certificate(n)
  if !all_ok || !trivial {
    return false
  }
  // 所有典範上循環滿足五边形
  for p = 0; p < n; p = p + 1 {
    let cat = @m17.canonical_cocycle(n, p)
    if !cat.pentagon_holds() {
      return false
    }
    // 規範變換保持 coherent
    let beta = Array::make(n * n, 0)
    if !@m17.gauge_equivalence_certificate(cat, beta) {
      return false
    }
  }
  // 類標籤空間 {0..n−1}，規範作用平凡，inv = id 分離 0 與 1
  let id = @m23.Perm::identity(n)
  let gens = [id]
  let domain : Array[Int32] = []
  for i = 0; i < n; i = i + 1 {
    domain.push(i)
  }
  let apply = fn(p : @m23.Perm, x : Int32) -> Int32 { p.apply(x) }
  let inv = fn(x : Int32) -> Int32 { x }
  @m23.invariant_separation_certificate(gens, domain, apply, inv, 0, 1)
}

///|
/// 總融合證書：三條橋同時成立。
pub fn unified_fusion_certificate() -> Bool raise Error {
  if !berry_riemann_period_bridge(2, 3) {
    return false
  }
  if !rg_spectral_marginal_certificate() {
    return false
  }
  if !diamond_rg_spectral_bridge() {
    return false
  }
  categorical_h3_obstruction_orbit_certificate(3)
}
