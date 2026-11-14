///|
/// Module M23 (Part 1) — Permutation Groups & Schreier–Sims:
/// deterministic stabilizer chain (fixed base 0..n−1), orbit transversals,
/// Schreier generators, membership sifting, orbit-stabilizer order,
/// Burnside/Pólya orbit counting, and the Q₈ regular representation bridged
/// from M22's quaternion multiplication table.

///|
pub(all) suberror GroupError {
  InvalidPermutation(String)
  InvalidGroup(String)
}

///|
#derive(Eq, Debug)
pub(all) struct Perm {
  images : Array[Int32]
}

///|
pub extend Perm with Eq::{equal, not_equal}

///|
pub extend Perm with @debug.Debug::{to_repr}

///|
pub fn Perm::identity(n : Int32) -> Perm {
  let a = Array::make(n, 0)
  for i = 0; i < n; i = i + 1 {
    a[i] = i
  }
  { images: a, }
}

///|
pub fn Perm::make(images : Array[Int32]) -> Perm raise Error {
  let n = images.length()
  let seen = Array::make(n, false)
  for v in images {
    if v < 0 || v >= n || seen[v] {
      raise GroupError::InvalidPermutation("not a bijection")
    }
    seen[v] = true
  }
  { images, }
}

///|
/// compose(p, q) = p ∘ q（先 q 後 p）。
pub fn Perm::compose(self : Perm, other : Perm) -> Perm raise Error {
  let n = self.images.length()
  if other.images.length() != n {
    raise GroupError::InvalidPermutation("degree mismatch")
  }
  let out = Array::make(n, 0)
  for i = 0; i < n; i = i + 1 {
    out[i] = self.images[other.images[i]]
  }
  { images: out, }
}

///|
pub fn Perm::inv(self : Perm) -> Perm {
  let n = self.images.length()
  let out = Array::make(n, 0)
  for i = 0; i < n; i = i + 1 {
    out[self.images[i]] = i
  }
  { images: out, }
}

///|
pub fn Perm::apply(self : Perm, x : Int32) -> Int32 {
  self.images[x]
}

///|
pub fn Perm::is_identity(self : Perm) -> Bool {
  for i = 0; i < self.images.length(); i = i + 1 {
    if self.images[i] != i {
      return false
    }
  }
  true
}

///|
/// 符號（parity）：(−1)^{n − #cycles}。
pub fn Perm::sign(self : Perm) -> Int32 {
  let n = self.images.length()
  if (n - self.cycle_count()) % 2 == 0 {
    1
  } else {
    -1
  }
}

///|
pub fn Perm::cycle_count(self : Perm) -> Int32 {
  let n = self.images.length()
  let seen = Array::make(n, false)
  let mut cycles = 0
  for i = 0; i < n; i = i + 1 {
    if seen[i] {
      continue
    }
    cycles = cycles + 1
    let mut j = i
    while !seen[j] {
      seen[j] = true
      j = self.images[j]
    }
  }
  cycles
}

///|
pub fn perm_key(p : Perm) -> String {
  let mut s = ""
  for v in p.images {
    s = s + v.to_string() + ","
  }
  s
}

///|
pub fn dedup_perms(gens : Array[Perm]) -> Array[Perm] {
  let seen : Map[String, Bool] = Map([])
  let out : Array[Perm] = []
  for g in gens {
    let k = perm_key(g)
    if !seen.contains(k) {
      seen[k] = true
      out.push(g)
    }
  }
  out
}

///|
pub(all) struct StabilizerLevel {
  base_point : Int32
  generators : Array[Perm]
  orbit : Array[Int32]
  /// transversal[x] maps base_point → x
  transversal : Array[Perm]
}

///|
pub(all) struct SchreierSims {
  degree : Int32
  levels : Array[StabilizerLevel]
  order : @bigint.BigInt
}

///|
/// 軌道 + 橫截（BFS）。
pub fn orbit_transversal(
  gens : Array[Perm],
  base : Int32,
  n : Int32,
) -> (Array[Int32], Array[Perm]) raise Error {
  let id = Perm::identity(n)
  let trans = Array::make(n, id)
  let in_orbit = Array::make(n, false)
  let orbit : Array[Int32] = []
  let queue : Array[Int32] = [base]
  in_orbit[base] = true
  let mut head = 0
  while head < queue.length() {
    let x = queue[head]
    head = head + 1
    orbit.push(x)
    for g in gens {
      let y = g.apply(x)
      if !in_orbit[y] {
        in_orbit[y] = true
        trans[y] = g.compose(trans[x])
        queue.push(y)
      }
    }
  }
  (orbit, trans)
}

///|
/// 確定性 Schreier–Sims 穩定鏈（base = 0,1,...,n−1）。
pub fn schreier_sims(
  n : Int32,
  generators : Array[Perm],
) -> SchreierSims raise Error {
  if n < 0 {
    raise GroupError::InvalidGroup("negative degree")
  }
  for g in generators {
    if g.images.length() != n {
      raise GroupError::InvalidGroup("generator degree mismatch")
    }
  }
  let mut current = dedup_perms(generators)
  let levels : Array[StabilizerLevel] = []
  let mut order = @bigint.BigInt::from_int(1)
  for base = 0; base < n; base = base + 1 {
    let (orbit, trans) = orbit_transversal(current, base, n)
    order = order * @bigint.BigInt::from_int(orbit.length())
    levels.push({
      base_point: base,
      generators: current,
      orbit,
      transversal: trans,
    })
    // Schreier generators for stabilizer of base
    let next : Array[Perm] = []
    for g in current {
      for x in orbit {
        let y = g.apply(x)
        // s = trans[y]⁻¹ ∘ g ∘ trans[x]
        let s = trans[y].inv().compose(g.compose(trans[x]))
        if !s.is_identity() {
          next.push(s)
        }
      }
    }
    current = dedup_perms(next)
    if current.length() == 0 {
      // remaining stabilizers trivial; fill trivial levels
      for b = base + 1; b < n; b = b + 1 {
        let id = Perm::identity(n)
        levels.push({
          base_point: b,
          generators: [],
          orbit: [b],
          transversal: Array::make(n, id),
        })
      }
      break
    }
  }
  { degree: n, levels, order, }
}

///|
/// 成員測試（sifting）。
pub fn SchreierSims::contains(
  self : SchreierSims,
  p : Perm,
) -> Bool raise Error {
  if p.images.length() != self.degree {
    raise GroupError::InvalidPermutation("degree mismatch")
  }
  let mut cur = p
  for level in self.levels {
    let x = cur.apply(level.base_point)
    let mut found = false
    for o in level.orbit {
      if o == x {
        found = true
        break
      }
    }
    if !found {
      return false
    }
    cur = level.transversal[x].inv().compose(cur)
  }
  cur.is_identity()
}

///|
/// 枚舉群元素（橫截代表元之積，用於 Burnside）。
pub fn SchreierSims::elements(self : SchreierSims) -> Array[Perm] raise Error {
  let mut elems : Array[Perm] = [Perm::identity(self.degree)]
  // process levels from last to first
  let mut i = self.levels.length() - 1
  while i >= 0 {
    let level = self.levels[i]
    let next : Array[Perm] = []
    for x in level.orbit {
      let rep = level.transversal[x]
      for e in elems {
        next.push(rep.compose(e))
      }
    }
    elems = dedup_perms(next)
    i = i - 1
  }
  elems
}

///|
/// Burnside/Pólya：以 k 種顏色著色 n 個點之軌道數 = (1/|G|) Σ_g k^{c(g)}。
pub fn SchreierSims::polya_orbit_count(
  self : SchreierSims,
  colors : Int32,
) -> @m20.Rat raise Error {
  if colors < 0 {
    raise GroupError::InvalidGroup("negative colors")
  }
  let elems = self.elements()
  let mut sum = @bigint.BigInt::from_int(0)
  let k = @bigint.BigInt::from_int(colors)
  for g in elems {
    let c = g.cycle_count()
    let mut term = @bigint.BigInt::from_int(1)
    for j = 0; j < c; j = j + 1 {
      term = term * k
    }
    sum = sum + term
  }
  @m20.Rat::make(sum, @bigint.BigInt::from_int(elems.length()))
}

///|
/// Schreier–Sims 證書：生成元皆可 sift、橫截映射正確、軌道-穩定子階數一致。
pub fn SchreierSims::certificate(
  self : SchreierSims,
  generators : Array[Perm],
) -> Bool raise Error {
  for g in generators {
    if !self.contains(g) {
      return false
    }
  }
  let mut prod = @bigint.BigInt::from_int(1)
  for level in self.levels {
    prod = prod * @bigint.BigInt::from_int(level.orbit.length())
    for x in level.orbit {
      if level.transversal[x].apply(level.base_point) != x {
        return false
      }
      if !self.contains(level.transversal[x]) {
        return false
      }
    }
  }
  prod == self.order
}

///|
/// 相鄰對換生成 S_n。
pub fn symmetric_generators(n : Int32) -> Array[Perm] raise Error {
  let gens : Array[Perm] = []
  for i = 0; i + 1 < n; i = i + 1 {
    let a = Array::make(n, 0)
    for j = 0; j < n; j = j + 1 {
      a[j] = j
    }
    a[i] = i + 1
    a[i + 1] = i
    gens.push(Perm::make(a))
  }
  gens
}

///|
/// 3-循環 (0,1,k) 生成 A_n（n ≥ 3）。
pub fn alternating_generators(n : Int32) -> Array[Perm] raise Error {
  if n < 3 {
    raise GroupError::InvalidGroup("A_n needs n >= 3")
  }
  let gens : Array[Perm] = []
  for k = 2; k < n; k = k + 1 {
    let a = Array::make(n, 0)
    for j = 0; j < n; j = j + 1 {
      a[j] = j
    }
    a[0] = 1
    a[1] = k
    a[k] = 0
    gens.push(Perm::make(a))
  }
  gens
}

///|
/// Q₈ 左正則表示（由 M22 乘法表），接入 Schreier–Sims。
pub fn q8_regular_group() -> SchreierSims raise Error {
  let table = @m22.q8_table()
  let gens : Array[Perm] = []
  // left multiplication by i (index 2) and j (index 4) generates Q8
  for idx in [2, 4] {
    let a = Array::make(8, 0)
    for x = 0; x < 8; x = x + 1 {
      a[x] = table[idx][x]
    }
    gens.push(Perm::make(a))
  }
  schreier_sims(8, gens)
}
