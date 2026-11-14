///|
/// Module M26 (Part 3) — What "superizing Schreier–Sims" actually means,
/// and WHERE the naive port COLLIDES.
///
/// Honest scope statement: Parts 1–2 above implement Schreier–Sims for the
/// SIGNED permutation group B_n = Z₂ⁿ ⋊ S_n.  That is a classical input to
/// Schreier–Sims (GAP/Magma handle it routinely); a Z₂ SIGN is not a Z₂
/// GRADING.  It is not a supergroup algorithm.
///
/// The genuine obstruction: Schreier–Sims rests on finite cardinality,
///     |G| = |orbit| · |G_base|,
/// with finite orbits and finite transversals.  For an actual supergroup
/// over a Grassmann algebra this fails at the root: an odd unipotent
///     g = [[1, θ], [0, 1]],  g^n = [[1, nθ], [0, 1]]
/// generates an INFINITE cyclic group while its body is the identity
/// (order 1).  So "order" is not an integer invariant and orbit counting
/// cannot even start.  This is demonstrated computationally below.
///
/// What survives is a TWO-LAYER structure:
///   layer 0 (body / reduced group): an ordinary group — Schreier–Sims applies;
///   layer 1 (odd / nilpotent directions): a MODULE over the body group —
///            linear algebra (rank/dimension), not counting;
/// glued by the conjugation action (semidirect product).  Size is measured by
/// dim GL(p|q) = (p²+q² | 2pq) rather than by |G|.

///|
/// 奇冪么元 g = [[1,θ],[0,1]]。
fn odd_unipotent(k : Int32) -> @m22.SuperMatrix raise Error {
  let one = @m22.Grassmann::scalar(k, @m20.Rat::one())
  let zero = @m22.Grassmann::zero(k)
  let th = @m22.Grassmann::generator(k, 0)
  @m22.SuperMatrix::make(k, 1, 1, [[one, th], [zero, one]])
}

///|
/// 相撞證書：奇冪么元之冪 g¹..g⁶ 兩兩相異（無限循環群），
/// 但每個 g^n 之 body 皆為單位矩陣（階 1）。
/// ⇒ 有限計數 |G|=|orbit|·|G_base| 喺真正超群上唔成立。
pub fn supergroup_counting_collision_certificate() -> Bool raise Error {
  let k = 1
  let g = odd_unipotent(k)
  let powers : Array[@m22.SuperMatrix] = []
  let mut cur = g
  for n = 1; n <= 6; n = n + 1 {
    powers.push(cur)
    // body（常數項）必須係單位矩陣
    if cur.entries[0][0].coeffs[0] != @m20.Rat::one() {
      return false
    }
    if cur.entries[1][1].coeffs[0] != @m20.Rat::one() {
      return false
    }
    if !cur.entries[0][1].coeffs[0].is_zero() {
      return false
    }
    // B 塊應為 n·θ
    if cur.entries[0][1].coeffs[1] != @m20.Rat::from_int(n) {
      return false
    }
    cur = @m22.supermatrix_mul(cur, g)
  }
  // 兩兩相異 ⇒ 無限階，與 body 階 1 矛盾於有限計數
  for i = 0; i < powers.length(); i = i + 1 {
    for j = i + 1; j < powers.length(); j = j + 1 {
      if @m22.SuperMatrix::eq(powers[i], powers[j]) {
        return false
      }
    }
  }
  true
}

///|
/// GL(p|q) 之超維數 (p²+q² | 2pq)——用維度取代階數。
pub fn supergroup_dimension(p : Int32, q : Int32) -> (Int32, Int32) {
  (p * p + q * q, 2 * p * q)
}

///|
/// 偶對角元 diag(a,d)。
fn even_diag(
  a : @m20.Rat,
  d : @m20.Rat,
  k : Int32,
) -> @m22.SuperMatrix raise Error {
  @m22.SuperMatrix::make(k, 1, 1, [
    [@m22.Grassmann::scalar(k, a), @m22.Grassmann::zero(k)],
    [@m22.Grassmann::zero(k), @m22.Grassmann::scalar(k, d)],
  ])
}

///|
/// 奇元素 X = [[0,x],[0,0]]。
fn odd_upper(x : @m22.Grassmann) -> @m22.SuperMatrix raise Error {
  let k = x.k
  @m22.SuperMatrix::make(k, 1, 1, [
    [@m22.Grassmann::zero(k), x],
    [@m22.Grassmann::zero(k), @m22.Grassmann::zero(k)],
  ])
}

///|
/// 共軛作用 conj(g, X) = g X g⁻¹（g 偶對角）。
fn conj_by_diag(
  a : @m20.Rat,
  d : @m20.Rat,
  x : @m22.Grassmann,
) -> @m22.SuperMatrix raise Error {
  let k = x.k
  let g = even_diag(a, d, k)
  let gi = even_diag(a.inv(), d.inv(), k)
  let gx = @m22.supermatrix_mul(g, odd_upper(x))
  @m22.supermatrix_mul(gx, gi)
}

///|
/// 兩層結構證書：
/// (i) body 層共軛作用於 odd 層為線性特徵 a/d；
/// (ii) 對 X 可加（模公理）；
/// (iii) 對 g 乘法相容（作用公理）；
/// (iv) 超維數 dim GL(1|1) = (2|2)，以維度而非階數度量。
pub fn body_odd_module_certificate() -> Bool raise Error {
  let k = 2
  let th1 = @m22.Grassmann::generator(k, 0)
  let th2 = @m22.Grassmann::generator(k, 1)
  let a = @m20.Rat::from_int(3)
  let d = @m20.Rat::from_int(2)
  // (i) conj(diag(3,2), θ₁) = (3/2)·θ₁
  let c1 = conj_by_diag(a, d, th1)
  if c1.entries[0][1].coeffs[1] != @m20.Rat::frac(3, 2) {
    return false
  }
  // (ii) 可加性
  let sum = th1.add(th2)
  let csum = conj_by_diag(a, d, sum)
  let c2 = conj_by_diag(a, d, th2)
  for i = 0; i < csum.entries[0][1].coeffs.length(); i = i + 1 {
    let expect = c1.entries[0][1].coeffs[i].add(c2.entries[0][1].coeffs[i])
    if csum.entries[0][1].coeffs[i] != expect {
      return false
    }
  }
  // (iii) 作用公理：conj(g₁g₂, X) = conj(g₁, conj(g₂, X))
  let a2 = @m20.Rat::from_int(5)
  let d2 = @m20.Rat::from_int(7)
  let lhs = conj_by_diag(a.mul(a2), d.mul(d2), th1)
  let inner = conj_by_diag(a2, d2, th1)
  let rhs = conj_by_diag(a, d, inner.entries[0][1])
  if !@m22.SuperMatrix::eq(lhs, rhs) {
    return false
  }
  // (iv) 超維數
  let (ev, od) = supergroup_dimension(1, 1)
  ev == 2 && od == 2
}

///|
/// 層級關係證書：body 層可用 Schreier–Sims（有限），odd 層用模維度（線性），
/// 兩層以共軛黏合。以 B_n 作 body 層示例，odd 層以 GL(1|1) 之 2 維奇方向。
pub fn super_two_layer_hierarchy_certificate(n : Int32) -> Bool raise Error {
  if n < 2 {
    raise SuperGroupError::InvalidSignedPerm("n >= 2")
  }
  // body 層：有限群，Schreier–Sims 適用且已驗證
  let body = las_vegas_schreier_sims(
    2 * n,
    signed_generators_to_perm(hyperoctahedral_generators(n)),
    seed=23UL,
  )
  if !body.verified {
    return false
  }
  if body.chain.order != hyperoctahedral_order(n) {
    return false
  }
  // odd 層：模，維度而非階數
  if !body_odd_module_certificate() {
    return false
  }
  // 相撞仍然成立：整體唔能用單一整數階數描述
  supergroup_counting_collision_certificate()
}
