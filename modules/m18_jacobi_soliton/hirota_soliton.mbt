///|
/// Module M18 (Part 2) — Hirota Bilinear Soliton Calculus: the KdV N-soliton
/// τ-function τ = Σ_{μ∈{0,1}^N} exp(Σ μ_i η_i + Σ_{i<j} μ_iμ_j A_ij) with
/// η_i = k_i x − k_i³ t and e^{A_ij} = ((k_i−k_j)/(k_i+k_j))², and exact
/// verification of the bilinear equation (D_x D_t + D_x⁴) τ·τ = 0 by grouping
/// exponential monomials.  D_x^m D_t^n exp(η_a)·exp(η_b) =
/// (K_a−K_b)^m (Ω_a−Ω_b)^n exp((K_a+K_b)x + (Ω_a+Ω_b)t).

///|
pub(all) suberror SolitonError {
  InvalidWaveNumber(Int32)
  ResonantDenominator
}

///|
/// 指數單項式 coeff · exp(k·x + omega·t)。
#derive(Eq, Debug)
pub(all) struct ExpTerm {
  coeff : @m20.Rat
  k : @m20.Rat
  omega : @m20.Rat
}

///|
pub extend ExpTerm with Eq::{equal, not_equal}

///|
pub extend ExpTerm with @debug.Debug::{to_repr}

///|
pub(all) struct TauFunction {
  terms : Array[ExpTerm]
}

///|
/// KdV N-孤子 τ 函數（色散 ω_i = −k_i³，精確有理係數）。
pub fn kdv_tau(ks : Array[@m20.Rat]) -> TauFunction raise Error {
  let n = ks.length()
  if n < 1 {
    raise SolitonError::InvalidWaveNumber(n)
  }
  let omegas : Array[@m20.Rat] = []
  for k in ks {
    omegas.push(k.mul(k).mul(k).neg())
  }
  let terms : Array[ExpTerm] = []
  for mask = 0; mask < 1 << n; mask = mask + 1 {
    let mut kk = @m20.Rat::zero()
    let mut oo = @m20.Rat::zero()
    let mut coeff = @m20.Rat::one()
    for i = 0; i < n; i = i + 1 {
      if ((mask >> i) & 1) == 1 {
        kk = kk.add(ks[i])
        oo = oo.add(omegas[i])
      }
    }
    for i = 0; i < n; i = i + 1 {
      if ((mask >> i) & 1) == 0 {
        continue
      }
      for j = i + 1; j < n; j = j + 1 {
        if ((mask >> j) & 1) == 0 {
          continue
        }
        let denom = ks[i].add(ks[j])
        if denom.is_zero() {
          raise SolitonError::ResonantDenominator
        }
        let ratio = ks[i].sub(ks[j]).div(denom)
        coeff = coeff.mul(ratio).mul(ratio)
      }
    }
    terms.push({ coeff, k: kk, omega: oo, })
  }
  { terms, }
}

///|
pub(all) struct BilinearGroup {
  k_total : @m20.Rat
  omega_total : @m20.Rat
  mut residual : @m20.Rat
}

///|
/// (D_x D_t + D_x⁴) τ·τ 依指數單項式 (K_a+K_b, Ω_a+Ω_b) 分組之殘差。
/// 每組殘差 = Σ coeff_a coeff_b [(K_a−K_b)(Ω_a−Ω_b) + (K_a−K_b)⁴]。
pub fn hirota_bilinear_residual(
  tau : TauFunction,
) -> Array[BilinearGroup] raise Error {
  let groups : Array[BilinearGroup] = []
  for a in tau.terms {
    for b in tau.terms {
      let dk = a.k.sub(b.k)
      let do_ = a.omega.sub(b.omega)
      let dk2 = dk.mul(dk)
      let factor = dk.mul(do_).add(dk2.mul(dk2))
      let contrib = a.coeff.mul(b.coeff).mul(factor)
      if contrib.is_zero() {
        continue
      }
      let ks = a.k.add(b.k)
      let os = a.omega.add(b.omega)
      let mut found = false
      for g in groups {
        if g.k_total == ks && g.omega_total == os {
          g.residual = g.residual.add(contrib)
          found = true
          break
        }
      }
      if !found {
        groups.push({ k_total: ks, omega_total: os, residual: contrib, })
      }
    }
  }
  groups
}

///|
/// KdV 雙線性方程驗證證書：所有分組殘差為零。
pub fn kdv_bilinear_verified(tau : TauFunction) -> Bool raise Error {
  let groups = hirota_bilinear_residual(tau)
  for g in groups {
    if !g.residual.is_zero() {
      return false
    }
  }
  true
}

///|
/// 雙孤子交互作用相移 e^{A_12} = ((k_1−k_2)/(k_1+k_2))²（精確有理）。
pub fn soliton_phase_shift(
  k1 : @m20.Rat,
  k2 : @m20.Rat,
) -> @m20.Rat raise Error {
  let denom = k1.add(k2)
  if denom.is_zero() {
    raise SolitonError::ResonantDenominator
  }
  let ratio = k1.sub(k2).div(denom)
  ratio.mul(ratio)
}

///|
/// 孤子數目與 τ 項數關係證書：N-孤子 τ 恰有 2^N 個指數項。
pub fn tau_term_count_certificate(n : Int32) -> Bool raise Error {
  if n < 1 || n > 6 {
    raise SolitonError::InvalidWaveNumber(n)
  }
  let ks : Array[@m20.Rat] = []
  for i = 0; i < n; i = i + 1 {
    ks.push(@m20.Rat::from_int(i + 1))
  }
  let tau = kdv_tau(ks)
  tau.terms.length() == 1 << n
}
