///|
/// Module M17 (Part 2) — Pointed Fusion Categories Vec_{Z_n}^ω and Pentagon
/// Coherence: the associator ω : G³ → U(1) (phases in Z_m) must satisfy the
/// 3-cocycle pentagon; gauge transformations shift ω by a 2-coboundary, and
/// δ² = 0 guarantees every coboundary is coherent.  The canonical family
/// ω_p(a,b,c) = p·a·⌊(b+c)/n⌋ (mod n) realizes H³(Z_n, U(1)) ≅ Z_n.
/// 局部公理（軸向交換與 coherence）之範疇實例。

///|
pub(all) struct PointedCategory {
  n : Int32
  modulus : Int32
  /// omega[(a*n+b)*n+c] ∈ Z_modulus
  omega : Array[Int32]
}

///|
fn zm(a : Int32, m : Int32) -> Int32 {
  (a % m + m) % m
}

///|
pub fn PointedCategory::make(
  n : Int32,
  modulus : Int32,
  omega : Array[Int32],
) -> PointedCategory raise Error {
  if n < 1 || modulus < 2 || omega.length() != n * n * n {
    raise FusionError::InvalidFusionData("pointed shape")
  }
  let om : Array[Int32] = []
  for v in omega {
    om.push(zm(v, modulus))
  }
  { n, modulus, omega: om, }
}

///|
pub fn PointedCategory::get(
  self : PointedCategory,
  a : Int32,
  b : Int32,
  c : Int32,
) -> Int32 {
  self.omega[(a * self.n + b) * self.n + c]
}

///|
/// 五边形（3-上循環）條件：對全部 a,b,c,d ∈ Z_n，
/// ω(b,c,d) − ω(a+b,c,d) + ω(a,b+c,d) − ω(a,b,c+d) + ω(a,b,c) ≡ 0 (mod m)。
pub fn PointedCategory::pentagon_holds(self : PointedCategory) -> Bool {
  let n = self.n
  let m = self.modulus
  for a = 0; a < n; a = a + 1 {
    for b = 0; b < n; b = b + 1 {
      for c = 0; c < n; c = c + 1 {
        for d = 0; d < n; d = d + 1 {
          let ab = (a + b) % n
          let bc = (b + c) % n
          let cd = (c + d) % n
          let v = self.get(b, c, d) -
            self.get(ab, c, d) +
            self.get(a, bc, d) -
            self.get(a, b, cd) +
            self.get(a, b, c)
          if zm(v, m) != 0 {
            return false
          }
        }
      }
    }
  }
  true
}

///|
/// 典範 3-上循環 ω_p(a,b,c) = p·a·⌊(b+c)/n⌋ (mod n)，代表 H³(Z_n,U(1)) 之類 p。
pub fn canonical_cocycle(n : Int32, p : Int32) -> PointedCategory raise Error {
  let om : Array[Int32] = []
  for a = 0; a < n; a = a + 1 {
    for b = 0; b < n; b = b + 1 {
      for c = 0; c < n; c = c + 1 {
        om.push(zm(p * a * ((b + c) / n), n))
      }
    }
  }
  PointedCategory::make(n, n, om)
}

///|
/// 2-上邊界 dβ(a,b,c) = β(b,c) − β(a+b,c) + β(a,b+c) − β(a,b)（β : G² → Z_m，
/// 平凡作用之非齊次群上同調微分）。此式保證 d² = 0。
pub fn coboundary(
  n : Int32,
  modulus : Int32,
  beta : Array[Int32],
) -> Array[Int32] raise Error {
  if beta.length() != n * n {
    raise FusionError::InvalidFusionData("beta shape")
  }
  let bget = (x : Int32, y : Int32) => beta[x * n + y]
  let om : Array[Int32] = []
  for a = 0; a < n; a = a + 1 {
    for b = 0; b < n; b = b + 1 {
      for c = 0; c < n; c = c + 1 {
        let ab = (a + b) % n
        let bc = (b + c) % n
        om.push(
          zm(bget(b, c) - bget(ab, c) + bget(a, bc) - bget(a, b), modulus),
        )
      }
    }
  }
  om
}

///|
/// δ² = 0 證書：任意 2-上鏈 β 之上邊界 δβ 必滿足五边形（上邊界皆上循環）。
pub fn coboundary_coherence_certificate(
  n : Int32,
  modulus : Int32,
  beta : Array[Int32],
) -> Bool raise Error {
  let om = coboundary(n, modulus, beta)
  let cat = PointedCategory::make(n, modulus, om)
  cat.pentagon_holds()
}

///|
/// 規範等價證書：ω 與 ω + δβ 同滿足五边形（範疇等價由 2-上鏈給出）。
pub fn gauge_equivalence_certificate(
  cat : PointedCategory,
  beta : Array[Int32],
) -> Bool raise Error {
  if !cat.pentagon_holds() {
    return false
  }
  let db = coboundary(cat.n, cat.modulus, beta)
  let om2 : Array[Int32] = []
  for i = 0; i < cat.omega.length(); i = i + 1 {
    om2.push(zm(cat.omega[i] + db[i], cat.modulus))
  }
  let cat2 = PointedCategory::make(cat.n, cat.modulus, om2)
  cat2.pentagon_holds()
}

///|
/// H³(Z_n,U(1)) ≅ Z_n 證書：典範族 ω_0..ω_{n−1} 全部滿足五边形，
/// 且 ω_0 為平凡上邊界（β=0）。回傳 (全部 coherent, ω_0 平凡)。
pub fn h3_zn_certificate(n : Int32) -> (Bool, Bool) raise Error {
  let mut all_ok = true
  for p = 0; p < n; p = p + 1 {
    let cat = canonical_cocycle(n, p)
    if !cat.pentagon_holds() {
      all_ok = false
    }
  }
  let zero = canonical_cocycle(n, 0)
  let mut trivial = true
  for v in zero.omega {
    if v != 0 {
      trivial = false
    }
  }
  (all_ok, trivial)
}
