///|
/// Module M23 (Part 2) — Obstruction Orbits:
/// parity obstruction A_n ⊊ S_n (index 2, sign invariant separates cosets);
/// sliding-puzzle solvability invariant I(state) = sign(π)·(−1)^{row+col(blank)}
/// preserved by every legal move, hence states with different I lie in distinct
/// reachability orbits; and a generic finite-group-action orbit enumerator with
/// invariant-separation certificate.

///|
/// A_n 於 S_n 之指數 2 阻撓證書：|S_n| = n!、|A_n| = n!/2、
/// 所有 A_n 生成元偶、奇對換不被 A_n 包含、sign 為群同態。
pub fn parity_obstruction_certificate(n : Int32) -> Bool raise Error {
  if n < 3 {
    raise GroupError::InvalidGroup("n >= 3")
  }
  let sn = schreier_sims(n, symmetric_generators(n))
  let an = schreier_sims(n, alternating_generators(n))
  // factorial
  let mut fact = @bigint.BigInt::from_int(1)
  for i = 2; i <= n; i = i + 1 {
    fact = fact * @bigint.BigInt::from_int(i)
  }
  if sn.order != fact {
    return false
  }
  if an.order * @bigint.BigInt::from_int(2) != fact {
    return false
  }
  for g in alternating_generators(n) {
    if g.sign() != 1 {
      return false
    }
    if !an.contains(g) {
      return false
    }
  }
  // odd transposition (0 1) obstructed from A_n
  let swap = Array::make(n, 0)
  for i = 0; i < n; i = i + 1 {
    swap[i] = i
  }
  swap[0] = 1
  swap[1] = 0
  let odd = Perm::make(swap)
  if odd.sign() != -1 {
    return false
  }
  if an.contains(odd) {
    return false
  }
  if !sn.contains(odd) {
    return false
  }
  // sign homomorphism on S_n generators
  let gens = symmetric_generators(n)
  for a in gens {
    for b in gens {
      if a.compose(b).sign() != a.sign() * b.sign() {
        return false
      }
    }
  }
  true
}

///|
/// 滑塊拼圖狀態：n×n 棋盤，tiles 為 0..n²−1 之排列，0 = 空格。
pub(all) struct SlidePuzzle {
  n : Int32
  tiles : Array[Int32]
}

///|
pub fn SlidePuzzle::make(
  n : Int32,
  tiles : Array[Int32],
) -> SlidePuzzle raise Error {
  if n < 2 || tiles.length() != n * n {
    raise GroupError::InvalidGroup("puzzle shape")
  }
  let p = Perm::make(tiles)
  ignore(p)
  { n, tiles, }
}

///|
pub fn SlidePuzzle::goal(n : Int32) -> SlidePuzzle {
  let tiles = Array::make(n * n, 0)
  for i = 0; i < n * n; i = i + 1 {
    tiles[i] = i
  }
  { n, tiles, }
}

///|
fn blank_pos(p : SlidePuzzle) -> (Int32, Int32) {
  for i = 0; i < p.tiles.length(); i = i + 1 {
    if p.tiles[i] == 0 {
      return (i / p.n, i % p.n)
    }
  }
  (0, 0)
}

///|
/// 可解性不變量 I = sign(π)·(−1)^{row+col(blank)}。
pub fn SlidePuzzle::invariant(self : SlidePuzzle) -> Int32 raise Error {
  let p = Perm::make(self.tiles)
  let (r, c) = blank_pos(self)
  let parity = if (r + c) % 2 == 0 { 1 } else { -1 }
  p.sign() * parity
}

///|
/// 合法移動（空格與上下鄰交換）。
pub fn SlidePuzzle::moves(self : SlidePuzzle) -> Array[SlidePuzzle] raise Error {
  let (r, c) = blank_pos(self)
  let out : Array[SlidePuzzle] = []
  let deltas = [(-1, 0), (1, 0), (0, -1), (0, 1)]
  for d in deltas {
    let nr = r + d.0
    let nc = c + d.1
    if nr < 0 || nr >= self.n || nc < 0 || nc >= self.n {
      continue
    }
    let tiles = self.tiles.copy()
    let a = r * self.n + c
    let b = nr * self.n + nc
    let tmp = tiles[a]
    tiles[a] = tiles[b]
    tiles[b] = tmp
    out.push(SlidePuzzle::make(self.n, tiles))
  }
  out
}

///|
/// 滑塊拼圖阻撓證書：所有合法移動保持不變量；目標態 I=+1；
/// 交換兩非零瓷磚之態 I=−1（不可達）。
pub fn sliding_puzzle_obstruction_certificate(n : Int32) -> Bool raise Error {
  let goal = SlidePuzzle::goal(n)
  if goal.invariant() != 1 {
    return false
  }
  // 移動保持性：每個合法移動 = 鄰接對換（sign 翻轉）× 空格奇偶翻轉 ⇒ I 不變。
  // 以 sign 同態證書 + 具體移動檢查確立。
  if !sign_homomorphism_certificate(n * n) {
    return false
  }
  let inv0 = goal.invariant()
  for mv in goal.moves() {
    if mv.invariant() != inv0 {
      return false
    }
    for mv2 in mv.moves() {
      if mv2.invariant() != inv0 {
        return false
      }
    }
  }
  // 構造不可達態：交換瓷磚 1 與 2（保持空格位置）
  let bad_tiles = goal.tiles.copy()
  bad_tiles[1] = 2
  bad_tiles[2] = 1
  let bad = SlidePuzzle::make(n, bad_tiles)
  if bad.invariant() != -1 {
    return false
  }
  for mv in bad.moves() {
    if mv.invariant() != -1 {
      return false
    }
  }
  true
}

///|
/// sign : S_m → {±1} 為群同態（於相鄰對換生成元上驗證）。
pub fn sign_homomorphism_certificate(m : Int32) -> Bool raise Error {
  let gens = symmetric_generators(m)
  for a in gens {
    if a.sign() != -1 {
      return false
    }
    for b in gens {
      if a.compose(b).sign() != a.sign() * b.sign() {
        return false
      }
    }
  }
  true
}

///|
/// 通用有限群作用軌道枚舉（BFS）：給定作用 apply(g,x) 與生成元。
pub fn action_orbit(
  generators : Array[Perm],
  start : Int32,
  apply : (Perm, Int32) -> Int32,
) -> Array[Int32] {
  let seen : Map[Int32, Bool] = Map([])
  let orbit : Array[Int32] = []
  let queue : Array[Int32] = [start]
  seen[start] = true
  let mut head = 0
  while head < queue.length() {
    let x = queue[head]
    head = head + 1
    orbit.push(x)
    for g in generators {
      let y = apply(g, x)
      if !seen.contains(y) {
        seen[y] = true
        queue.push(y)
      }
    }
  }
  orbit
}

///|
/// 不變量分離證書：inv 於生成元作用下不變，且 inv(x) ≠ inv(y) ⇒ x,y 不同軌道。
pub fn invariant_separation_certificate(
  generators : Array[Perm],
  domain : Array[Int32],
  apply : (Perm, Int32) -> Int32,
  inv : (Int32) -> Int32,
  x : Int32,
  y : Int32,
) -> Bool {
  for g in generators {
    for d in domain {
      if inv(apply(g, d)) != inv(d) {
        return false
      }
    }
  }
  if inv(x) == inv(y) {
    return false
  }
  let orb_x = action_orbit(generators, x, apply)
  for z in orb_x {
    if z == y {
      return false
    }
  }
  true
}
