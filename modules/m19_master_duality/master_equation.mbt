///|
/// Module M19 (Part 1) — Master Equations: continuous-time Markov generators
/// (row-sum-zero rate matrices), exact rational stationary nullspaces, detailed
/// balance, the H-theorem entropy-production sign certificate, and Lindblad
/// quantum channels verified completely-positive (Choi PSD via all principal
/// minors) and trace-preserving over ℚ.

///|
pub(all) suberror MasterError {
  InvalidGenerator(String)
  ReducibleChain(Int32)
  InvalidChannel(String)
}

///|
/// CTMC 生成元 W：W[i][j] = i→j 速率 (i≠j ≥ 0)，對角 = −Σ_{j≠i} W[i][j]（列和 0）。
pub(all) struct MarkovGenerator {
  n : Int32
  rates : @m20.RatMatrix
}

///|
pub fn MarkovGenerator::from_offdiag(
  rates : @m20.RatMatrix,
) -> MarkovGenerator raise Error {
  let n = rates.rows
  if n != rates.cols || n < 1 {
    raise MasterError::InvalidGenerator("shape")
  }
  let w = @m20.RatMatrix::zero(n, n)
  for i = 0; i < n; i = i + 1 {
    let mut outflow = @m20.Rat::zero()
    for j = 0; j < n; j = j + 1 {
      if i == j {
        continue
      }
      let r = rates.get(i, j)
      if r.sign() < 0 {
        raise MasterError::InvalidGenerator("negative rate")
      }
      w.set(i, j, r)
      outflow = outflow.add(r)
    }
    w.set(i, i, outflow.neg())
  }
  { n, rates: w, }
}

///|
/// 平穩分佈 π：π W = 0，Σ π = 1（不可約鏈唯一，精確有理）。
pub fn MarkovGenerator::stationary(
  self : MarkovGenerator,
) -> Array[@m20.Rat] raise Error {
  let wt = self.rates.transpose()
  let ns = wt.nullspace()
  if ns.length() != 1 {
    raise MasterError::ReducibleChain(ns.length())
  }
  let v = ns[0]
  let mut total = @m20.Rat::zero()
  for x in v {
    total = total.add(x)
  }
  if total.is_zero() {
    raise MasterError::ReducibleChain(0)
  }
  let pi : Array[@m20.Rat] = []
  for x in v {
    pi.push(x.div(total))
  }
  pi
}

///|
/// 細緻平衡（可逆性）：π_i W_ij = π_j W_ji 對全部 i,j。
pub fn MarkovGenerator::detailed_balance(
  self : MarkovGenerator,
  pi : Array[@m20.Rat],
) -> Bool raise Error {
  if pi.length() != self.n {
    return false
  }
  for i = 0; i < self.n; i = i + 1 {
    for j = 0; j < self.n; j = j + 1 {
      let lhs = pi[i].mul(self.rates.get(i, j))
      let rhs = pi[j].mul(self.rates.get(j, i))
      if lhs != rhs {
        return false
      }
    }
  }
  true
}

///|
pub(all) struct EntropyProductionCertificate {
  /// H-定理：σ = Σ_{i<j} (J_ij − J_ji) ln(J_ij/J_ji) ≥ 0（每項 ≥ 0，ln 單調）
  nonnegative : Bool
  /// σ = 0 iff 細緻平衡（全部通量對稱）
  zero : Bool
  irreversible_pairs : Int32
}

///|
/// 熵產生率符號證書：通量 J_ij = π_i W_ij。每對 (i,j) 之貢獻
/// (J_ij − J_ji)·ln(J_ij/J_ji) ≥ 0（因 ln 單調，差與對數差同號）。
/// 零熵產生等價於 J_ij = J_ji（細緻平衡），以精確有理通量驗證。
pub fn MarkovGenerator::entropy_production(
  self : MarkovGenerator,
  pi : Array[@m20.Rat],
) -> EntropyProductionCertificate raise Error {
  let mut irreversible = 0
  let mut all_symmetric = true
  for i = 0; i < self.n; i = i + 1 {
    for j = i + 1; j < self.n; j = j + 1 {
      let jij = pi[i].mul(self.rates.get(i, j))
      let jji = pi[j].mul(self.rates.get(j, i))
      if jij != jji {
        irreversible = irreversible + 1
        all_symmetric = false
      }
    }
  }
  // 每對貢獻 (a−b)ln(a/b) ≥ 0 由 ln 單調性保證（a,b ≥ 0）；此為 H-定理之代數證明結構。
  { nonnegative: true, zero: all_symmetric, irreversible_pairs: irreversible, }
}

///|
/// 實 Kraus 量子通道 Φ(ρ) = Σ_k K_k ρ K_k^T（有理係數）。
pub(all) struct KrausChannel {
  dim : Int32
  kraus : Array[@m20.RatMatrix]
}

///|
pub fn KrausChannel::make(
  dim : Int32,
  kraus : Array[@m20.RatMatrix],
) -> KrausChannel raise Error {
  if dim < 1 || kraus.length() == 0 {
    raise MasterError::InvalidChannel("shape")
  }
  for k in kraus {
    if k.rows != dim || k.cols != dim {
      raise MasterError::InvalidChannel("kraus shape")
    }
  }
  { dim, kraus, }
}

///|
/// Choi 矩陣 J(Φ) = Σ_{ij} Φ(E_ij) ⊗ E_ij（dim² × dim²）。
pub fn KrausChannel::choi(self : KrausChannel) -> @m20.RatMatrix raise Error {
  let d = self.dim
  let choi = @m20.RatMatrix::zero(d * d, d * d)
  for i = 0; i < d; i = i + 1 {
    for j = 0; j < d; j = j + 1 {
      // Φ(E_ij) = Σ_k K_k E_ij K_k^T；(E_ij)_{ab} = δ_ai δ_bj
      // Φ(E_ij)_{ac} = Σ_k K_k[a,i] K_k[c,j]
      for a = 0; a < d; a = a + 1 {
        for c = 0; c < d; c = c + 1 {
          let mut v = @m20.Rat::zero()
          for k in self.kraus {
            v = v.add(k.get(a, i).mul(k.get(c, j)))
          }
          // ⊗ E_ij：Choi 塊 (a,c) 之 (i,j) 位置 → row a*d+i, col c*d+j
          choi.set(a * d + i, c * d + j, v)
        }
      }
    }
  }
  choi
}

///|
/// 對稱矩陣 PSD 判定（Sylvester 準則：全部主子式 ≥ 0，精確有理）。
pub fn is_psd_principal_minors(m : @m20.RatMatrix) -> Bool raise Error {
  let n = m.rows
  if n != m.cols {
    return false
  }
  // symmetry
  for i = 0; i < n; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      if m.get(i, j) != m.get(j, i) {
        return false
      }
    }
  }
  for mask = 1; mask < 1 << n; mask = mask + 1 {
    let idx : Array[Int32] = []
    for b = 0; b < n; b = b + 1 {
      if ((mask >> b) & 1) == 1 {
        idx.push(b)
      }
    }
    let k = idx.length()
    let sub = @m20.RatMatrix::zero(k, k)
    for a = 0; a < k; a = a + 1 {
      for b = 0; b < k; b = b + 1 {
        sub.set(a, b, m.get(idx[a], idx[b]))
      }
    }
    if sub.det().sign() < 0 {
      return false
    }
  }
  true
}

///|
/// 完全正性證書：Choi 矩陣 PSD（Choi 定理）。
pub fn KrausChannel::completely_positive(
  self : KrausChannel,
) -> Bool raise Error {
  is_psd_principal_minors(self.choi())
}

///|
/// 保跡證書：Σ_k K_k^T K_k = I。
pub fn KrausChannel::trace_preserving(self : KrausChannel) -> Bool raise Error {
  let d = self.dim
  let acc = @m20.RatMatrix::zero(d, d)
  for k in self.kraus {
    let kt = k.transpose()
    let prod = kt.mul(k)
    for i = 0; i < d; i = i + 1 {
      for j = 0; j < d; j = j + 1 {
        acc.set(i, j, acc.get(i, j).add(prod.get(i, j)))
      }
    }
  }
  let id = @m20.RatMatrix::identity(d)
  for i = 0; i < d * d; i = i + 1 {
    if acc.data[i] != id.data[i] {
      return false
    }
  }
  true
}

///|
/// 全振幅阻尼通道（γ=1）：K0 = |0⟩⟨0|, K1 = |0⟩⟨1|（有理 CPTP）。
pub fn amplitude_damping_full() -> KrausChannel raise Error {
  let k0 = @m20.RatMatrix::from_ints(2, 2, [1, 0, 0, 0])
  let k1 = @m20.RatMatrix::from_ints(2, 2, [0, 1, 0, 0])
  KrausChannel::make(2, [k0, k1])
}
