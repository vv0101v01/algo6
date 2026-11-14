///|
/// Module M22 (Part 1) — Euler's Four-Square Identity & Composition Algebras:
/// integer quaternions and Cayley–Dickson octonions with N(pq)=N(p)N(q)
/// proved by complete polarization on basis vectors (not sampling); a
/// sedenion zero divisor exhibiting the Hurwitz 1/2/4/8 boundary; and the
/// Q₈ conjugation action on the cube (image V₄, kernel {±1}).

///|
/// 完全極化證書引擎：給定一組基向量、雙線性乘法與對稱雙線型 dot，
/// 驗證 ⟨e_i e_k, e_j e_l⟩ + ⟨e_i e_l, e_j e_k⟩ = 2·dot(e_i,e_j)·dot(e_k,e_l)
/// 對所有 i,j,k,l 成立。若 dot 為標準內積且基為標準正交基，右式即 2δ_ijδ_kl，
/// 由雙線性／二次型極化，此蘊含一般 N(pq)=N(p)N(q)。
fn[T] polarization_certificate(
  basis : Array[T],
  mul : (T, T) -> T,
  dot : (T, T) -> @bigint.BigInt,
) -> Bool {
  let n = basis.length()
  let prod : Array[Array[T]] = []
  for i = 0; i < n; i = i + 1 {
    let row : Array[T] = []
    for k = 0; k < n; k = k + 1 {
      row.push(mul(basis[i], basis[k]))
    }
    prod.push(row)
  }
  let gram : Array[Array[@bigint.BigInt]] = []
  for i = 0; i < n; i = i + 1 {
    let row : Array[@bigint.BigInt] = []
    for j = 0; j < n; j = j + 1 {
      row.push(dot(basis[i], basis[j]))
    }
    gram.push(row)
  }
  for i = 0; i < n; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      for k = 0; k < n; k = k + 1 {
        for l = 0; l < n; l = l + 1 {
          let lhs = dot(prod[i][k], prod[j][l]) + dot(prod[i][l], prod[j][k])
          let rhs = gram[i][j] * gram[k][l] * @bigint.BigInt::from_int(2)
          if lhs != rhs {
            return false
          }
        }
      }
    }
  }
  true
}

///|
/// 整數四元數 a + b i + c j + d k。
#derive(Eq, Debug)
pub(all) struct Quat {
  a : @bigint.BigInt
  b : @bigint.BigInt
  c : @bigint.BigInt
  d : @bigint.BigInt
}

///|
pub extend Quat with Eq::{equal, not_equal}

///|
pub extend Quat with @debug.Debug::{to_repr}

///|
pub fn Quat::make(a : Int32, b : Int32, c : Int32, d : Int32) -> Quat {
  {
    a: @bigint.BigInt::from_int(a),
    b: @bigint.BigInt::from_int(b),
    c: @bigint.BigInt::from_int(c),
    d: @bigint.BigInt::from_int(d),
  }
}

///|
pub fn Quat::mul(self : Quat, other : Quat) -> Quat {
  // Hamilton: i²=j²=k²=ijk=−1
  {
    a: self.a * other.a - self.b * other.b - self.c * other.c - self.d * other.d,
    b: self.a * other.b + self.b * other.a + self.c * other.d - self.d * other.c,
    c: self.a * other.c - self.b * other.d + self.c * other.a + self.d * other.b,
    d: self.a * other.d + self.b * other.c - self.c * other.b + self.d * other.a,
  }
}

///|
pub fn Quat::conj(self : Quat) -> Quat {
  { a: self.a, b: self.b.neg(), c: self.c.neg(), d: self.d.neg(), }
}

///|
/// 範數 N = a²+b²+c²+d²（歐拉四平方和）。
pub fn Quat::norm(self : Quat) -> @bigint.BigInt {
  self.a * self.a + self.b * self.b + self.c * self.c + self.d * self.d
}

///|
fn quat_dot(a : Quat, b : Quat) -> @bigint.BigInt {
  a.a * b.a + a.b * b.b + a.c * b.c + a.d * b.d
}

///|
/// 歐拉四平方恆等式 N(pq)=N(p)N(q)：對四元數標準基作完全極化證明。
/// 只需 4⁴=256 個基向量恆等式（取代舊 3⁸=6561 點網格），由雙線性即蘊含一般情形。
pub fn euler_four_square_certificate() -> Bool {
  let basis = [
    Quat::make(1, 0, 0, 0),
    Quat::make(0, 1, 0, 0),
    Quat::make(0, 0, 1, 0),
    Quat::make(0, 0, 0, 1),
  ]
  polarization_certificate(basis, Quat::mul, quat_dot)
}

///|
/// Q₈ = {±1, ±i, ±j, ±k} 之乘法表（索引 0..7 = 1,−1,i,−i,j,−j,k,−k）。
pub fn q8_table() -> Array[Array[Int32]] {
  let elems = [
    Quat::make(1, 0, 0, 0),
    Quat::make(-1, 0, 0, 0),
    Quat::make(0, 1, 0, 0),
    Quat::make(0, -1, 0, 0),
    Quat::make(0, 0, 1, 0),
    Quat::make(0, 0, -1, 0),
    Quat::make(0, 0, 0, 1),
    Quat::make(0, 0, 0, -1),
  ]
  let table : Array[Array[Int32]] = []
  for x in elems {
    let row : Array[Int32] = []
    for y in elems {
      let prod = x.mul(y)
      let mut idx = -1
      for k = 0; k < 8; k = k + 1 {
        if elems[k] == prod {
          idx = k
          break
        }
      }
      row.push(idx)
    }
    table.push(row)
  }
  table
}

///|
fn bi_small(z : @bigint.BigInt) -> Int32 {
  if z.compare_int(0) == 0 {
    0
  } else if z.compare_int(1) == 0 {
    1
  } else if z.compare_int(-1) == 0 {
    -1
  } else {
    99
  }
}

///|
/// q 對純虛四元數之共軛作用矩陣（3×3，行 = 影像分量）。
/// q ∈ Q₈ ⇒ N(q)=1 ⇒ q⁻¹ = q̄。
fn q8_conj_matrix(q : Quat) -> Array[Array[Int32]] {
  let units = [
    Quat::make(0, 1, 0, 0),
    Quat::make(0, 0, 1, 0),
    Quat::make(0, 0, 0, 1),
  ]
  let cols : Array[Array[Int32]] = []
  for v in units {
    let r = q.mul(v).mul(q.conj())
    cols.push([bi_small(r.b), bi_small(r.c), bi_small(r.d)])
  }
  // 轉成矩陣：M[row][col]
  let m : Array[Array[Int32]] = []
  for row = 0; row < 3; row = row + 1 {
    m.push([cols[0][row], cols[1][row], cols[2][row]])
  }
  m
}

///|
fn mat3_mul_vec(m : Array[Array[Int32]], v : Array[Int32]) -> Array[Int32] {
  let out = Array::make(3, 0)
  for i = 0; i < 3; i = i + 1 {
    let mut acc = 0
    for j = 0; j < 3; j = j + 1 {
      acc = acc + m[i][j] * v[j]
    }
    out[i] = acc
  }
  out
}

///|
fn mat3_mul(
  a : Array[Array[Int32]],
  b : Array[Array[Int32]],
) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for i = 0; i < 3; i = i + 1 {
    let row = Array::make(3, 0)
    for j = 0; j < 3; j = j + 1 {
      let mut acc = 0
      for k = 0; k < 3; k = k + 1 {
        acc = acc + a[i][k] * b[k][j]
      }
      row[j] = acc
    }
    out.push(row)
  }
  out
}

///|
fn mat3_det(m : Array[Array[Int32]]) -> Int32 {
  m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1]) -
  m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0]) +
  m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0])
}

///|
fn mat3_eq(a : Array[Array[Int32]], b : Array[Array[Int32]]) -> Bool {
  for i = 0; i < 3; i = i + 1 {
    for j = 0; j < 3; j = j + 1 {
      if a[i][j] != b[i][j] {
        return false
      }
    }
  }
  true
}

///|
/// Q₈ ↔ 立方體之**真實共軛作用**證書（取代先前任意符號雙射）：
/// (i) 每個 q ∈ Q₈ 之共軛作用為帶符號置換矩陣、det=+1（真旋轉）；
/// (ii) 同態：conj(q₁q₂) = conj(q₁)·conj(q₂)；
/// (iii) 像恰為 4 個（Klein 四元群 V₄，繞座標軸 180° 旋轉），核恰為 {±1}；
/// (iv) 作用於立方體頂點 {±1}³ 保持 Hamming 鄰接（立方體圖自同構）。
pub fn q8_cube_correspondence() -> Bool {
  let elems = [
    Quat::make(1, 0, 0, 0),
    Quat::make(-1, 0, 0, 0),
    Quat::make(0, 1, 0, 0),
    Quat::make(0, -1, 0, 0),
    Quat::make(0, 0, 1, 0),
    Quat::make(0, 0, -1, 0),
    Quat::make(0, 0, 0, 1),
    Quat::make(0, 0, 0, -1),
  ]
  let mats : Array[Array[Array[Int32]]] = []
  for q in elems {
    let m = q8_conj_matrix(q)
    // (i) 帶符號置換 + det +1
    for r in m {
      let mut nz = 0
      for v in r {
        if v != 0 {
          nz = nz + 1
          if v != 1 && v != -1 {
            return false
          }
        }
      }
      if nz != 1 {
        return false
      }
    }
    if mat3_det(m) != 1 {
      return false
    }
    mats.push(m)
  }
  // (ii) 同態
  let table = q8_table()
  for a = 0; a < 8; a = a + 1 {
    for b = 0; b < 8; b = b + 1 {
      if !mat3_eq(mats[table[a][b]], mat3_mul(mats[a], mats[b])) {
        return false
      }
    }
  }
  // (iii) 像大小 4、核 {±1}
  let id3 = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
  let image : Array[Array[Array[Int32]]] = []
  let kernel : Array[Int32] = []
  for i = 0; i < 8; i = i + 1 {
    if mat3_eq(mats[i], id3) {
      kernel.push(i)
    }
    let mut found = false
    for im in image {
      if mat3_eq(im, mats[i]) {
        found = true
      }
    }
    if !found {
      image.push(mats[i])
    }
  }
  if image.length() != 4 || kernel.length() != 2 {
    return false
  }
  if kernel[0] != 0 || kernel[1] != 1 {
    return false
  }
  // (iv) 立方體頂點鄰接保持
  let verts : Array[Array[Int32]] = []
  for mask = 0; mask < 8; mask = mask + 1 {
    let v = Array::make(3, 0)
    for b = 0; b < 3; b = b + 1 {
      v[b] = if ((mask >> b) & 1) == 1 { 1 } else { -1 }
    }
    verts.push(v)
  }
  for m in image {
    let imgs : Array[Array[Int32]] = []
    for v in verts {
      imgs.push(mat3_mul_vec(m, v))
    }
    for a = 0; a < 8; a = a + 1 {
      for b = a + 1; b < 8; b = b + 1 {
        let mut d0 = 0
        let mut d1 = 0
        for t = 0; t < 3; t = t + 1 {
          if verts[a][t] != verts[b][t] {
            d0 = d0 + 1
          }
          if imgs[a][t] != imgs[b][t] {
            d1 = d1 + 1
          }
        }
        if d0 != d1 {
          return false
        }
      }
    }
  }
  true
}

///|
/// 八元數（Cayley–Dickson）：x + y·ℓ，x,y 四元數。
#derive(Eq, Debug)
pub(all) struct Octonion {
  x : Quat
  y : Quat
}

///|
pub extend Octonion with Eq::{equal, not_equal}

///|
pub extend Octonion with @debug.Debug::{to_repr}

///|
pub fn Octonion::mul(self : Octonion, other : Octonion) -> Octonion {
  // (x+yℓ)(z+wℓ) = (xz − w̄ y) + (w x + y z̄)ℓ
  let xz = self.x.mul(other.x)
  let wbar_y = other.y.conj().mul(self.y)
  let wx = other.y.mul(self.x)
  let yzbar = self.y.mul(other.x.conj())
  {
    x: {
      a: xz.a - wbar_y.a,
      b: xz.b - wbar_y.b,
      c: xz.c - wbar_y.c,
      d: xz.d - wbar_y.d,
    },
    y: {
      a: wx.a + yzbar.a,
      b: wx.b + yzbar.b,
      c: wx.c + yzbar.c,
      d: wx.d + yzbar.d,
    },
  }
}

///|
pub fn Octonion::norm(self : Octonion) -> @bigint.BigInt {
  self.x.norm() + self.y.norm()
}

///|
/// 八元數基向量 e_i。
fn oct_basis(i : Int32) -> Octonion {
  let c = Array::make(8, 0)
  c[i] = 1
  Octonion::from_ints(c)
}

///|
/// 標準內積（八個分量逐項相乘求和）。
fn oct_dot(a : Octonion, b : Octonion) -> @bigint.BigInt {
  a.x.a * b.x.a +
  a.x.b * b.x.b +
  a.x.c * b.x.c +
  a.x.d * b.x.d +
  a.y.a * b.y.a +
  a.y.b * b.y.b +
  a.y.c * b.y.c +
  a.y.d * b.y.d
}

///|
/// 八平方恆等式 N(pq)=N(p)N(q)：對八元數標準基作完全極化證明（非採樣）。
/// 全部 8⁴=4096 個基向量恆等式成立，由雙線性／二次型極化即蘊含一般 p,q。
pub fn octonion_eight_square_certificate() -> Bool {
  let basis : Array[Octonion] = []
  for i = 0; i < 8; i = i + 1 {
    basis.push(oct_basis(i))
  }
  polarization_certificate(basis, Octonion::mul, oct_dot)
}

///|
pub fn Octonion::from_ints(c : Array[Int32]) -> Octonion {
  {
    x: Quat::make(c[0], c[1], c[2], c[3]),
    y: Quat::make(c[4], c[5], c[6], c[7]),
  }
}

///|
/// 十六元數（sedenion，Cayley–Dickson 再一層）：x + y·m，x,y 八元數。
pub(all) struct Sedenion {
  x : Octonion
  y : Octonion
}

///|
pub fn Sedenion::mul(self : Sedenion, other : Sedenion) -> Sedenion {
  // Cayley–Dickson: (x+y m)(z+w m) = (xz − w̄ y) + (w x + y z̄) m
  let xz = self.x.mul(other.x)
  let wbar_y = oct_conj(other.y).mul(self.y)
  let wx = other.y.mul(self.x)
  let yzbar = self.y.mul(oct_conj(other.x))
  { x: oct_sub(xz, wbar_y), y: oct_add(wx, yzbar), }
}

///|
fn oct_conj(o : Octonion) -> Octonion {
  {
    x: o.x.conj(),
    y: { a: o.y.a.neg(), b: o.y.b.neg(), c: o.y.c.neg(), d: o.y.d.neg(), },
  }
}

///|
fn oct_sub(a : Octonion, b : Octonion) -> Octonion {
  {
    x: {
      a: a.x.a - b.x.a,
      b: a.x.b - b.x.b,
      c: a.x.c - b.x.c,
      d: a.x.d - b.x.d,
    },
    y: {
      a: a.y.a - b.y.a,
      b: a.y.b - b.y.b,
      c: a.y.c - b.y.c,
      d: a.y.d - b.y.d,
    },
  }
}

///|
fn oct_add(a : Octonion, b : Octonion) -> Octonion {
  {
    x: {
      a: a.x.a + b.x.a,
      b: a.x.b + b.x.b,
      c: a.x.c + b.x.c,
      d: a.x.d + b.x.d,
    },
    y: {
      a: a.y.a + b.y.a,
      b: a.y.b + b.y.b,
      c: a.y.c + b.y.c,
      d: a.y.d + b.y.d,
    },
  }
}

///|
pub fn Sedenion::norm(self : Sedenion) -> @bigint.BigInt {
  self.x.norm() + self.y.norm()
}

///|
pub fn Sedenion::is_zero(self : Sedenion) -> Bool {
  self.norm().compare_int(0) == 0
}

///|
/// Hurwitz 邊界證書：sedenion 有零因子 a,b ≠ 0 但 a·b = 0，
/// 故 16 平方無乘法範數恆等式（Hurwitz 1/2/4/8 定理之計算見證）。
/// 經典零因子：(e_3 + e_10)(e_6 − e_15) = 0（依 Cayley–Dickson 基索引）。
pub fn sedenion_zero_divisor_certificate() -> Bool {
  // 以基向量構造並搜尋一对零因子（確定性枚舉小支撑）
  let basis : Array[Sedenion] = []
  for i = 0; i < 16; i = i + 1 {
    let c = Array::make(16, 0)
    c[i] = 1
    basis.push(sedenion_from_ints(c))
  }
  // 嘗試 (e_i + e_j)(e_k − e_l) 形式之零因子
  for i = 0; i < 16; i = i + 1 {
    for j = i + 1; j < 16; j = j + 1 {
      let a = sed_add(basis[i], basis[j])
      for k = 0; k < 16; k = k + 1 {
        for l = 0; l < 16; l = l + 1 {
          if k == l {
            continue
          }
          let b = sed_sub(basis[k], basis[l])
          let prod = a.mul(b)
          if prod.is_zero() && !a.is_zero() && !b.is_zero() {
            return true
          }
        }
      }
    }
  }
  false
}

///|
fn sed_add(a : Sedenion, b : Sedenion) -> Sedenion {
  { x: oct_add(a.x, b.x), y: oct_add(a.y, b.y), }
}

///|
fn sed_sub(a : Sedenion, b : Sedenion) -> Sedenion {
  { x: oct_sub(a.x, b.x), y: oct_sub(a.y, b.y), }
}

///|
pub fn sedenion_from_ints(c : Array[Int32]) -> Sedenion {
  {
    x: Octonion::from_ints([c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7]]),
    y: Octonion::from_ints([
      c[8],
      c[9],
      c[10],
      c[11],
      c[12],
      c[13],
      c[14],
      c[15],
    ]),
  }
}
