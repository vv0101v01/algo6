///|
/// Module M25 (Part 2) — Super Cotangent Bundle, Even/Odd Blocks & the
/// Berezinian Line Bundle: ranks of the exact sequence 0→D→TΣ→D²→0
/// ((0|1)→(1|1)→(1|0)) and Ber parity. The GENERAL superconformal Jacobian
/// (left-coefficient convention B=−∂_θz') and Ber(J)=D_θθ' are verified
/// symbolically in Part 4 (superconformal_atlas.mbt); the narrow affine-family
/// Jacobian certificates were removed as dead code.

///|
/// 超向量空間秩 (even|odd)。
#derive(Eq)
pub(all) struct SuperRank {
  even : Int32
  odd : Int32
}

///|
pub extend SuperRank with Eq::{equal, not_equal}

///|
pub fn SuperRank::add(self : SuperRank, other : SuperRank) -> SuperRank {
  { even: self.even + other.even, odd: self.odd + other.odd, }
}

///|
/// Ber(V) 之宇稱 = odd rank mod 2（偶線束 1|0 或奇線束 0|1）。
pub fn ber_parity(r : SuperRank) -> Int32 {
  r.odd % 2
}

///|
/// 超切叢正合序列 0 → D → TΣ → D² → 0 之秩。
pub fn srs_exact_sequence_ranks() -> (SuperRank, SuperRank, SuperRank) {
  let d : SuperRank = { even: 0, odd: 1, } // D  rank 0|1
  let t : SuperRank = { even: 1, odd: 1, } // TΣ rank 1|1
  let d2 : SuperRank = { even: 1, odd: 0, } // D² rank 1|0
  (d, t, d2)
}

///|
/// 正合序列證書：秩可加 T = D + D²，且 Ber(T) = Ber(D)⊗Ber(D²)（宇稱相加）。
pub fn srs_exact_sequence_certificate() -> Bool raise Error {
  let (d, t, d2) = srs_exact_sequence_ranks()
  if d.add(d2) != t {
    return false
  }
  // 唔再用「宇稱相等」做恆真結尾；改為真實算子律：
  // D²=∂_z 於超場基上成立，且 D_θ = w·D_θ' 於一般超函數上成立，
  // 由此確立 D 之轉移為 w⁻¹、D⁻¹ 轉移為 w=Ber(J)。
  d_squared_equals_dz_certificate() &&
  d_operator_transformation_law_certificate()
}

///|
/// 註：原本嘅窄版 `superconformal_jacobian` / `jacobian_berezinian_certificate`
/// / `omega_equals_d_inverse_certificate` 已於健檢中移除——佢只覆蓋
/// u=a²z, η=εz 一個仿射 family，且掩蓋咗 B 塊符號錯誤。
/// 一般情形之正確版本見 superconformal_atlas.mbt：
/// `ber_jacobian_equals_d_theta_certificate`、
/// `omega_is_d_inverse_by_transitions_certificate`。
