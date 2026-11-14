///|
/// Module M20 (Part 3) — Jacobi Structure-Sheaf Gluing: finite covers with
/// restriction matrices, the sheaf locality/gluing equalizer certificate, and
/// sheaves of local Lie (Kirillov/Jacobi trivial-line-bundle) algebras whose
/// brackets commute with restriction.  This is the finite-dimensional gluing
/// layer of the polar-2-abelian-Jacobi-sheaf cohomology programme; the PDE
/// Jacobi-bundle identity itself lives in M18 and bridges here via M24.

///|
/// 有限覆蓋預層：補丁 U_i 之截面空間維度、兩兩交集與限制映射。
pub(all) struct FiniteCoverSheaf {
  patch_dims : Array[Int32]
  inter_i : Array[Int32]
  inter_j : Array[Int32]
  inter_dims : Array[Int32]
  /// res_from_i[t] : F(U_i) → F(U_i∩U_j)，res_from_j[t] : F(U_j) → F(U_i∩U_j)
  res_from_i : Array[RatMatrix]
  res_from_j : Array[RatMatrix]
}

///|
pub fn FiniteCoverSheaf::make(
  patch_dims : Array[Int32],
  inter_i : Array[Int32],
  inter_j : Array[Int32],
  inter_dims : Array[Int32],
  res_from_i : Array[RatMatrix],
  res_from_j : Array[RatMatrix],
) -> FiniteCoverSheaf raise AlgebraError {
  let t = inter_i.length()
  if inter_j.length() != t ||
    inter_dims.length() != t ||
    res_from_i.length() != t ||
    res_from_j.length() != t {
    raise AlgebraError::InconsistentDimensions("intersection arrays")
  }
  for k = 0; k < t; k = k + 1 {
    let i = inter_i[k]
    let j = inter_j[k]
    if i < 0 ||
      j < 0 ||
      i >= patch_dims.length() ||
      j >= patch_dims.length() ||
      i >= j {
      raise AlgebraError::InconsistentDimensions("intersection pair order")
    }
    if res_from_i[k].rows != inter_dims[k] ||
      res_from_i[k].cols != patch_dims[i] ||
      res_from_j[k].rows != inter_dims[k] ||
      res_from_j[k].cols != patch_dims[j] {
      raise AlgebraError::InconsistentDimensions("restriction shape")
    }
  }
  { patch_dims, inter_i, inter_j, inter_dims, res_from_i, res_from_j, }
}

///|
/// Čech δ^0 : ⊕F(U_i) → ⊕F(U_i∩U_j)，(δs)_ij = res_i s_i − res_j s_j。
pub fn FiniteCoverSheaf::cech_delta0(
  self : FiniteCoverSheaf,
) -> RatMatrix raise AlgebraError {
  let mut total_patch = 0
  let offsets : Array[Int32] = []
  for d in self.patch_dims {
    offsets.push(total_patch)
    total_patch = total_patch + d
  }
  let mut total_inter = 0
  let ioff : Array[Int32] = []
  for d in self.inter_dims {
    ioff.push(total_inter)
    total_inter = total_inter + d
  }
  let m = RatMatrix::zero(total_inter, total_patch)
  for t = 0; t < self.inter_i.length(); t = t + 1 {
    let oi = offsets[self.inter_i[t]]
    let oj = offsets[self.inter_j[t]]
    let ot = ioff[t]
    for r = 0; r < self.inter_dims[t]; r = r + 1 {
      for c = 0; c < self.patch_dims[self.inter_i[t]]; c = c + 1 {
        m.set(ot + r, oi + c, self.res_from_i[t].get(r, c))
      }
      for c = 0; c < self.patch_dims[self.inter_j[t]]; c = c + 1 {
        let v = self.res_from_j[t].get(r, c)
        m.set(ot + r, oj + c, v.neg())
      }
    }
  }
  m
}

///|
pub(all) struct SheafCertificate {
  /// 局部性：F(X) → ⊕F(U_i) 單射（rank = global_dim）
  locality : Bool
  /// 黏合：im(res) = ker δ^0（compatible families 恰為全域截面）
  gluing : Bool
  h0_dim : Int32
  global_dim : Int32
}

///|
/// 層公理證書：給定全域截面空間與限制映射 res_i : F(X) → F(U_i)，
/// 驗證 (1) 局部性（單射）與 (2) 黏合（像 = 相容族核）。
pub fn FiniteCoverSheaf::sheaf_certificate(
  self : FiniteCoverSheaf,
  global_dim : Int32,
  res_from_global : Array[RatMatrix],
) -> SheafCertificate raise AlgebraError {
  if res_from_global.length() != self.patch_dims.length() {
    raise AlgebraError::InconsistentDimensions("global restriction count")
  }
  let mut total_patch = 0
  for i = 0; i < self.patch_dims.length(); i = i + 1 {
    if res_from_global[i].rows != self.patch_dims[i] ||
      res_from_global[i].cols != global_dim {
      raise AlgebraError::InconsistentDimensions("global restriction shape")
    }
    total_patch = total_patch + self.patch_dims[i]
  }
  let r = RatMatrix::zero(total_patch, global_dim)
  let mut off = 0
  for i = 0; i < self.patch_dims.length(); i = i + 1 {
    for rr = 0; rr < self.patch_dims[i]; rr = rr + 1 {
      for c = 0; c < global_dim; c = c + 1 {
        r.set(off + rr, c, res_from_global[i].get(rr, c))
      }
    }
    off = off + self.patch_dims[i]
  }
  let delta = self.cech_delta0()
  let h0 = delta.nullspace().length()
  let r_rank = r.rank()
  let locality = r_rank == global_dim
  // gluing: δ∘res = 0 且 rank(res) = dim ker δ
  let comp = delta.mul(r)
  let mut annihilated = true
  for v in comp.data {
    if !v.is_zero() {
      annihilated = false
    }
  }
  { locality, gluing: annihilated && r_rank == h0, h0_dim: h0, global_dim, }
}

///|
/// 局部 Lie（Kirillov 局部李代數 / 平凡線叢 Jacobi）括號：結構常數 c[a][b][k]。
pub(all) struct LocalBracket {
  dim : Int32
  constants : Array[Rat]
}

///|
pub fn LocalBracket::make(
  dim : Int32,
  constants : Array[Rat],
) -> LocalBracket raise AlgebraError {
  if constants.length() != dim * dim * dim {
    raise AlgebraError::MatrixDataLength(constants.length(), dim * dim * dim)
  }
  { dim, constants, }
}

///|
pub fn LocalBracket::get(
  self : LocalBracket,
  a : Int32,
  b : Int32,
  k : Int32,
) -> Rat raise AlgebraError {
  if a < 0 || a >= self.dim || b < 0 || b >= self.dim || k < 0 || k >= self.dim {
    raise AlgebraError::IndexOutOfBounds(a, b)
  }
  self.constants[(a * self.dim + b) * self.dim + k]
}

///|
/// 反對稱 + 雅可比恆等式 Σ_l c[a][b][l]c[l][k][m] + cyclic = 0（精確驗證）。
pub fn LocalBracket::jacobi_identity_holds(
  self : LocalBracket,
) -> Bool raise AlgebraError {
  for a = 0; a < self.dim; a = a + 1 {
    for b = 0; b < self.dim; b = b + 1 {
      for k = 0; k < self.dim; k = k + 1 {
        if self.get(a, b, k) != self.get(b, a, k).neg() {
          return false
        }
      }
    }
  }
  for a = 0; a < self.dim; a = a + 1 {
    for b = 0; b < self.dim; b = b + 1 {
      for k = 0; k < self.dim; k = k + 1 {
        for m = 0; m < self.dim; m = m + 1 {
          let mut s = Rat::zero()
          for l = 0; l < self.dim; l = l + 1 {
            let t1 = self.get(a, b, l).mul(self.get(l, k, m))
            let t2 = self.get(b, k, l).mul(self.get(l, a, m))
            let t3 = self.get(k, a, l).mul(self.get(l, b, m))
            s = s.add(t1).add(t2).add(t3)
          }
          if !s.is_zero() {
            return false
          }
        }
      }
    }
  }
  true
}

///|
/// 括號與限制映射相容：R([e_a,e_b]) = [R e_a, R e_b]（對全部基配對）。
pub fn bracket_restriction_compatible(
  src : LocalBracket,
  dst : LocalBracket,
  restriction : RatMatrix,
) -> Bool raise AlgebraError {
  if restriction.rows != dst.dim || restriction.cols != src.dim {
    return false
  }
  for a = 0; a < src.dim; a = a + 1 {
    for b = 0; b < src.dim; b = b + 1 {
      // lhs = R([e_a,e_b])
      let br : Array[Rat] = []
      for k = 0; k < src.dim; k = k + 1 {
        br.push(src.get(a, b, k))
      }
      let lhs = restriction.mul_vec(br)
      // rhs = [R e_a, R e_b]
      let ra : Array[Rat] = []
      let rb : Array[Rat] = []
      for r = 0; r < dst.dim; r = r + 1 {
        ra.push(restriction.get(r, a))
        rb.push(restriction.get(r, b))
      }
      for m = 0; m < dst.dim; m = m + 1 {
        let mut s = Rat::zero()
        for u = 0; u < dst.dim; u = u + 1 {
          for v = 0; v < dst.dim; v = v + 1 {
            s = s.add(ra[u].mul(rb[v]).mul(dst.get(u, v, m)))
          }
        }
        if lhs[m] != s {
          return false
        }
      }
    }
  }
  true
}

///|
pub(all) struct JacobiSheafCertificate {
  sheaf : SheafCertificate
  local_jacobi : Bool
  restriction_bracket : Bool
}

///|
/// 雅可比結構層總證書：層公理 + 每補丁/交集局部雅可比恆等式 + 限制括號相容。
pub fn jacobi_sheaf_certificate(
  sheaf : FiniteCoverSheaf,
  global_dim : Int32,
  res_from_global : Array[RatMatrix],
  patch_brackets : Array[LocalBracket],
  inter_brackets : Array[LocalBracket],
) -> JacobiSheafCertificate raise AlgebraError {
  if patch_brackets.length() != sheaf.patch_dims.length() ||
    inter_brackets.length() != sheaf.inter_i.length() {
    raise AlgebraError::InconsistentDimensions("bracket counts")
  }
  let sc = sheaf.sheaf_certificate(global_dim, res_from_global)
  let mut local_ok = true
  for i = 0; i < patch_brackets.length(); i = i + 1 {
    if patch_brackets[i].dim != sheaf.patch_dims[i] ||
      !patch_brackets[i].jacobi_identity_holds() {
      local_ok = false
    }
  }
  for t = 0; t < inter_brackets.length(); t = t + 1 {
    if inter_brackets[t].dim != sheaf.inter_dims[t] ||
      !inter_brackets[t].jacobi_identity_holds() {
      local_ok = false
    }
  }
  let mut res_ok = true
  for t = 0; t < sheaf.inter_i.length(); t = t + 1 {
    let i = sheaf.inter_i[t]
    let j = sheaf.inter_j[t]
    if !bracket_restriction_compatible(
        patch_brackets[i],
        inter_brackets[t],
        sheaf.res_from_i[t],
      ) ||
      !bracket_restriction_compatible(
        patch_brackets[j],
        inter_brackets[t],
        sheaf.res_from_j[t],
      ) {
      res_ok = false
    }
  }
  { sheaf: sc, local_jacobi: local_ok, restriction_bracket: res_ok, }
}
