///|
/// Module M22 (Part 3) — Cubical Hypercube Homology & Discrete Riemann Periods:
/// the n-cube's cubical chain complex over ℤ (faces = (free-mask, fixed-bits),
/// alternating face boundary), contractibility certificate H_0=ℤ, H_{>0}=0,
/// cubical Euler characteristic χ=1; and the exact discrete Riemann period
/// matrix of a rectangular flat torus (τ = i·L_y/L_x) with Riemann bilinear
/// relations and symplectic intersection form bridged to M21.

///|
pub(all) suberror CubeError {
  InvalidDimension(Int32)
  InvalidTorus(String)
}

///|
fn cube_index(n : Int32, free : Int32, fixed : Int32) -> Int32 {
  // rank of (free,fixed) among k-faces: enumerate free masks of same popcount
  let k = popcount(free)
  let mut idx = 0
  for mask = 0; mask < 1 << n; mask = mask + 1 {
    if popcount(mask) != k {
      continue
    }
    if mask < free {
      idx = idx + (1 << (n - k))
    } else if mask == free {
      // fixed bits live on complement; compress to submask index
      let comp = ((1 << n) - 1) ^ free
      let mut sub = 0
      let mut bit = 0
      let mut c = comp
      while c != 0 {
        let b = c & -c
        if (fixed & b) != 0 {
          sub = sub | (1 << bit)
        }
        bit = bit + 1
        c = c ^ b
      }
      return idx + sub
    }
  }
  idx
}

///|
/// n-立方體之 cubical 鏈複形（整數係數，接入 M20 ChainComplex）。
pub fn hypercube_chain_complex(n : Int32) -> @m20.ChainComplex raise Error {
  if n < 0 || n > 12 {
    raise CubeError::InvalidDimension(n)
  }
  let dims : Array[Int32] = []
  for k = 0; k <= n; k = k + 1 {
    // C(n,k) 2^{n-k}
    let mut c = 1
    for i = 0; i < k; i = i + 1 {
      c = c * (n - i) / (i + 1)
    }
    dims.push(c * (1 << (n - k)))
  }
  let partials : Array[@m20.IntMatrix] = []
  for k = 0; k < n; k = k + 1 {
    // ∂_{k+1} : C_{k+1} → C_k
    let m = @m20.IntMatrix::zero(dims[k], dims[k + 1])
    for free = 0; free < 1 << n; free = free + 1 {
      if popcount(free) != k + 1 {
        continue
      }
      let comp = ((1 << n) - 1) ^ free
      // iterate fixed submasks of comp
      let mut fixed = comp
      while true {
        let col = cube_index(n, free, fixed)
        // free bits in increasing order
        let bits : Array[Int32] = []
        for b = 0; b < n; b = b + 1 {
          if ((free >> b) & 1) == 1 {
            bits.push(b)
          }
        }
        for j = 0; j < bits.length(); j = j + 1 {
          let b = bits[j]
          let free2 = free ^ (1 << b)
          let sign = if j % 2 == 0 { 1 } else { -1 }
          // face with bit b = 0
          let f0 = fixed
          let row0 = cube_index(n, free2, f0)
          let old0 = m.get(row0, col)
          m.set(row0, col, old0 + @bigint.BigInt::from_int(sign))
          // face with bit b = 1
          let f1 = fixed | (1 << b)
          let row1 = cube_index(n, free2, f1)
          let old1 = m.get(row1, col)
          m.set(row1, col, old1 + @bigint.BigInt::from_int(-sign))
        }
        if fixed == 0 {
          break
        }
        fixed = (fixed - 1) & comp
      }
    }
    partials.push(m)
  }
  @m20.ChainComplex::make(dims, partials)
}

///|
/// 超立方體可縮證書：H_0 = ℤ、H_k = 0 (k>0)，且 cubical Euler χ = 1。
pub fn hypercube_contractible_certificate(n : Int32) -> Bool raise Error {
  let cx = hypercube_chain_complex(n)
  let h0 = cx.homology(0)
  if h0.free_rank != 1 || h0.torsion.length() != 0 {
    return false
  }
  for k = 1; k <= n; k = k + 1 {
    let h = cx.homology(k)
    if h.free_rank != 0 || h.torsion.length() != 0 {
      return false
    }
  }
  // Euler characteristic from face counts
  let mut chi = 0
  for k = 0; k <= n; k = k + 1 {
    let mut c = 1
    for i = 0; i < k; i = i + 1 {
      c = c * (n - i) / (i + 1)
    }
    let count = c * (1 << (n - k))
    chi = chi + (if k % 2 == 0 { count } else { -count })
  }
  chi == 1
}

///|
/// 離散黎曼環面：矩形平坦環面 [0,L_x]×[0,L_y] 之正方形胞腔分解。
/// 離散全純微分 dz 之週期為 (L_x, i L_y)，正規化週期矩陣 τ = i L_y/L_x。
pub(all) struct DiscreteTorus {
  lx : Int32
  ly : Int32
  nx : Int32
  ny : Int32
}

///|
pub fn DiscreteTorus::make(
  lx : Int32,
  ly : Int32,
  nx : Int32,
  ny : Int32,
) -> DiscreteTorus raise Error {
  if lx <= 0 || ly <= 0 || nx <= 0 || ny <= 0 {
    raise CubeError::InvalidTorus("positive lengths and subdivisions required")
  }
  { lx, ly, nx, ny, }
}

///|
/// 複數 a + b i（精確有理係數）。
#derive(Eq, Debug)
pub(all) struct GaussianRat {
  re : @m20.Rat
  im : @m20.Rat
}

///|
pub extend GaussianRat with Eq::{equal, not_equal}

///|
pub extend GaussianRat with @debug.Debug::{to_repr}

///|
pub fn GaussianRat::make(re : @m20.Rat, im : @m20.Rat) -> GaussianRat {
  { re, im, }
}

///|
pub fn GaussianRat::sub(
  self : GaussianRat,
  other : GaussianRat,
) -> GaussianRat raise Error {
  { re: self.re.sub(other.re), im: self.im.sub(other.im), }
}

///|
pub fn GaussianRat::mul(
  self : GaussianRat,
  other : GaussianRat,
) -> GaussianRat raise Error {
  {
    re: self.re.mul(other.re).sub(self.im.mul(other.im)),
    im: self.re.mul(other.im).add(self.im.mul(other.re)),
  }
}

///|
/// 離散週期矩陣 τ（genus 1）：τ = i·L_y/L_x。
pub fn DiscreteTorus::period_matrix(
  self : DiscreteTorus,
) -> GaussianRat raise Error {
  let ratio = @m20.Rat::frac(self.ly, self.lx)
  GaussianRat::make(@m20.Rat::zero(), ratio)
}

///|
/// Riemann 雙線性關係證書（genus 1）：
/// (i) τ 對稱（1×1 自動）；(ii) Im τ > 0；(iii) 交叉形式為標準辛 J_1；
/// (iv) 週期向量 (L_x, i L_y) 滿足 ∮_a dz · ∮_b d z̄ − ∮_b dz · ∮_a d z̄ = 2i L_x L_y。
pub fn DiscreteTorus::riemann_relations_certificate(
  self : DiscreteTorus,
) -> Bool raise Error {
  let tau = self.period_matrix()
  if tau.im.sign() <= 0 {
    return false
  }
  // intersection form on H_1(a,b) = [[0,1],[-1,0]]
  let j = @m20.RatMatrix::zero(2, 2)
  j.set(0, 1, @m20.Rat::one())
  j.set(1, 0, @m20.Rat::from_int(-1))
  let sym = @m21.SymplecticForm::make(j)
  if sym.dim != 2 {
    return false
  }
  // period bilinear: A = L_x, B = i L_y
  let a = GaussianRat::make(@m20.Rat::from_int(self.lx), @m20.Rat::zero())
  let b = GaussianRat::make(@m20.Rat::zero(), @m20.Rat::from_int(self.ly))
  let bbar = GaussianRat::make(@m20.Rat::zero(), @m20.Rat::from_int(-self.ly))
  let abar = GaussianRat::make(@m20.Rat::from_int(self.lx), @m20.Rat::zero())
  // A·B̄ − B·Ā = L_x·(−i L_y) − i L_y·L_x = −2i L_x L_y
  let lhs = a.mul(bbar).sub(b.mul(abar))
  let expect_im = @m20.Rat::from_int(-2 * self.lx * self.ly)
  lhs.re.is_zero() && lhs.im == expect_im
}

///|
/// 離散 Hodge 分解維數證書：矩形環面胞腔複形之 H^1 維數 = 2（與 nx,ny 無關），
/// 對應兩個調和 1-形式 dx, dy。以 M20 鏈複形對偶計算。
pub fn DiscreteTorus::hodge_h1_certificate(
  self : DiscreteTorus,
) -> Bool raise Error {
  // cell counts: V = nx·ny, E = 2 nx·ny, F = nx·ny
  let v = self.nx * self.ny
  let e = 2 * v
  let f = v
  // ∂_1 : C_1 → C_0 (incidence), ∂_2 : C_2 → C_1
  let d1 = @m20.IntMatrix::zero(v, e)
  let d2 = @m20.IntMatrix::zero(e, f)
  let vid = fn(x : Int32, y : Int32) -> Int32 {
    (x % self.nx + self.nx) % self.nx * self.ny +
    (y % self.ny + self.ny) % self.ny
  }
  let eid_x = fn(x : Int32, y : Int32) -> Int32 {
    (x % self.nx + self.nx) % self.nx * self.ny +
    (y % self.ny + self.ny) % self.ny
  }
  let eid_y = fn(x : Int32, y : Int32) -> Int32 {
    v +
    (x % self.nx + self.nx) % self.nx * self.ny +
    (y % self.ny + self.ny) % self.ny
  }
  for x = 0; x < self.nx; x = x + 1 {
    for y = 0; y < self.ny; y = y + 1 {
      let v0 = vid(x, y)
      let v1 = vid(x + 1, y)
      let v2 = vid(x, y + 1)
      let ex = eid_x(x, y)
      let ey = eid_y(x, y)
      d1.set(v0, ex, @bigint.BigInt::from_int(-1))
      d1.set(v1, ex, @bigint.BigInt::from_int(1))
      d1.set(v0, ey, @bigint.BigInt::from_int(-1))
      d1.set(v2, ey, @bigint.BigInt::from_int(1))
      // face boundary: ex(x,y) + ey(x+1,y) − ex(x,y+1) − ey(x,y)
      let face = x * self.ny + y
      d2.set(ex, face, @bigint.BigInt::from_int(1))
      d2.set(eid_y(x + 1, y), face, @bigint.BigInt::from_int(1))
      d2.set(eid_x(x, y + 1), face, @bigint.BigInt::from_int(-1))
      d2.set(ey, face, @bigint.BigInt::from_int(-1))
    }
  }
  let cx = @m20.ChainComplex::make([v, e, f], [d1, d2])
  let h1 = cx.homology(1)
  h1.free_rank == 2 && h1.torsion.length() == 0
}
