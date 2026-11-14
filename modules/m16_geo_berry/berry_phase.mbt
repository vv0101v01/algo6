///|
/// Module M16 (Part 2) — Discrete Berry Phase à la Fukui–Hatsugai–Suzuki:
/// U(1) link variables on the Brillouin-zone torus valued in Z_n, principal-
/// branch plaquette field strength, the manifestly gauge-invariant integer
/// Chern number C = (1/n) Σ F̃, and the 1D Zak Wilson loop.  All arithmetic is
/// exact modular integer arithmetic — no floating point, no gauge fixing.

///|
pub(all) struct TorusGaugeField {
  lx : Int32
  ly : Int32
  modulus : Int32
  /// ux[x*ly+y]：+x 方向 link；uy[x*ly+y]：+y 方向 link
  ux : Array[Int32]
  uy : Array[Int32]
}

///|
pub fn TorusGaugeField::make(
  lx : Int32,
  ly : Int32,
  modulus : Int32,
  ux : Array[Int32],
  uy : Array[Int32],
) -> TorusGaugeField raise Error {
  if lx < 1 ||
    ly < 1 ||
    modulus < 2 ||
    ux.length() != lx * ly ||
    uy.length() != lx * ly {
    raise GeoError::InvalidConnection("torus gauge shape")
  }
  let nx : Array[Int32] = []
  let ny : Array[Int32] = []
  for i = 0; i < ux.length(); i = i + 1 {
    nx.push(mod_n(ux[i], modulus))
    ny.push(mod_n(uy[i], modulus))
  }
  { lx, ly, modulus, ux: nx, uy: ny, }
}

///|
/// 主分支 plaquette 場強 F̃(x,y) ∈ (−n/2, n/2]：
/// F = ux(x,y) + uy(x+1,y) − ux(x,y+1) − uy(x,y) (mod n)，再取主分支。
pub fn TorusGaugeField::plaquette_flux(
  self : TorusGaugeField,
  x : Int32,
  y : Int32,
) -> Int32 raise Error {
  if x < 0 || x >= self.lx || y < 0 || y >= self.ly {
    raise GeoError::InvalidConnection("plaquette index")
  }
  let xp = (x + 1) % self.lx
  let yp = (y + 1) % self.ly
  let raw = self.ux[x * self.ly + y] +
    self.uy[xp * self.ly + y] -
    self.ux[x * self.ly + yp] -
    self.uy[x * self.ly + y]
  let r = mod_n(raw, self.modulus)
  if 2 * r > self.modulus {
    r - self.modulus
  } else {
    r
  }
}

///|
/// FHS 陳數 C = (1/n) Σ_{x,y} F̃(x,y)。因 Σ F ≡ 0 (mod n)（望遠鏡消去），
/// C 必為整數；規範變換下逐 plaquette 不變，故 C 規範不變。
pub fn TorusGaugeField::chern_number(
  self : TorusGaugeField,
) -> Int32 raise Error {
  let mut total = 0
  for x = 0; x < self.lx; x = x + 1 {
    for y = 0; y < self.ly; y = y + 1 {
      total = total + self.plaquette_flux(x, y)
    }
  }
  if total % self.modulus != 0 {
    raise GeoError::InvalidConnection("Chern sum not divisible by n")
  }
  total / self.modulus
}

///|
/// 規範變換 g(x,y)：ux → ux + g(x+1,y) − g(x,y)，uy → uy + g(x,y+1) − g(x,y)。
pub fn TorusGaugeField::gauge_transform(
  self : TorusGaugeField,
  g : Array[Int32],
) -> TorusGaugeField raise Error {
  if g.length() != self.lx * self.ly {
    raise GeoError::InvalidConnection("gauge shape")
  }
  let nx : Array[Int32] = []
  let ny : Array[Int32] = []
  for x = 0; x < self.lx; x = x + 1 {
    for y = 0; y < self.ly; y = y + 1 {
      let xp = (x + 1) % self.lx
      let yp = (y + 1) % self.ly
      nx.push(
        mod_n(
          self.ux[x * self.ly + y] + g[xp * self.ly + y] - g[x * self.ly + y],
          self.modulus,
        ),
      )
      ny.push(
        mod_n(
          self.uy[x * self.ly + y] + g[x * self.ly + yp] - g[x * self.ly + y],
          self.modulus,
        ),
      )
    }
  }
  { lx: self.lx, ly: self.ly, modulus: self.modulus, ux: nx, uy: ny, }
}

///|
pub fn chern_gauge_invariance_certificate(
  field : TorusGaugeField,
  g : Array[Int32],
) -> Bool raise Error {
  field.chern_number() == field.gauge_transform(g).chern_number()
}

///|
/// Landau 規範 C=+1 構型：ux(x,y) = (n−y) mod n，uy = 0（ly = n）。
pub fn landau_chern_one(lx : Int32, n : Int32) -> TorusGaugeField raise Error {
  let ux : Array[Int32] = []
  let uy : Array[Int32] = []
  for x = 0; x < lx; x = x + 1 {
    for y = 0; y < n; y = y + 1 {
      ux.push(mod_n(n - y, n))
      uy.push(0)
    }
  }
  TorusGaugeField::make(lx, n, n, ux, uy)
}

///|
/// 1D Zak 相位（Brillouin 圈 Wilson 迴路）：Σ_x ux(x,0) mod n。
pub fn zak_phase(field : TorusGaugeField) -> Int32 raise Error {
  if field.ly != 1 {
    raise GeoError::InvalidConnection("Zak phase requires ly=1")
  }
  let mut acc = 0
  for x = 0; x < field.lx; x = x + 1 {
    acc = acc + field.ux[x]
  }
  mod_n(acc, field.modulus)
}

///|
/// Zak 相位之 Z₂ 量子化判據：反演對稱使 Wilson 圈 W → −W，故 2W ≡ 0 (mod n)，
/// 即 W ∈ {0, n/2}。回傳 (是否量子化, Zak 值)；此為精確模算術判定，無浮點。
pub fn zak_z2_quantized(field : TorusGaugeField) -> (Bool, Int32) raise Error {
  let z = zak_phase(field)
  (mod_n(2 * z, field.modulus) == 0, z)
}
