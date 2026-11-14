///|
/// Module M26 (Part 2) — Superized Las Vegas Schreier–Sims:
/// splitmix64-driven random Schreier generators build a probably-complete
/// stabilizer chain; a deterministic BSGS verification step sifts every
/// Schreier generator and repairs the chain with any non-sifting residue.
/// The loop is Las Vegas: the output is always a verified correct BSGS,
/// while the number of rounds depends on the random seed.

///|
pub(all) struct LasVegasResult {
  chain : @m23.SchreierSims
  iterations : Int32
  random_samples : Int32
  verified : Bool
}

///|
/// 隨機穩定鏈：carry-forward 固定 base 之生成元 + 隨機 Schreier 採樣。
fn randomized_chain(
  n : Int32,
  gens : Array[@m23.Perm],
  rng : @splitmix.RandomState,
  samples : Int32,
) -> @m23.SchreierSims raise Error {
  let mut current = @m23.dedup_perms(gens)
  let levels : Array[@m23.StabilizerLevel] = []
  let mut order = @bigint.BigInt::from_int(1)
  for base = 0; base < n; base = base + 1 {
    let (orbit, trans) = @m23.orbit_transversal(current, base, n)
    order = order * @bigint.BigInt::from_int(orbit.length())
    levels.push({
      base_point: base,
      generators: current,
      orbit,
      transversal: trans,
    })
    let next : Array[@m23.Perm] = []
    for g in current {
      if g.apply(base) == base {
        next.push(g)
      }
    }
    if current.length() > 0 && orbit.length() > 0 {
      for s = 0; s < samples; s = s + 1 {
        let g = current[rng.next_positive_int() % current.length()]
        let x = orbit[rng.next_positive_int() % orbit.length()]
        let y = g.apply(x)
        let sch = trans[y].inv().compose(g.compose(trans[x]))
        if !sch.is_identity() {
          next.push(sch)
        }
      }
    }
    current = @m23.dedup_perms(next)
    if current.length() == 0 {
      for b = base + 1; b < n; b = b + 1 {
        let id = @m23.Perm::identity(n)
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
/// 由第 start_level 層起 sift p；是否 sift 至恆等。
fn sifts_to_identity_from(
  chain : @m23.SchreierSims,
  p : @m23.Perm,
  start_level : Int32,
) -> Bool raise Error {
  let mut cur = p
  for i = start_level; i < chain.levels.length(); i = i + 1 {
    let level = chain.levels[i]
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
/// BSGS 驗證：sift 每個 Schreier 生成元；回傳首個不 sift 之殘餘（witness）。
fn verify_bsgs(chain : @m23.SchreierSims) -> @m23.Perm? raise Error {
  for i = 0; i < chain.levels.length(); i = i + 1 {
    let level = chain.levels[i]
    for g in level.generators {
      for x in level.orbit {
        let y = g.apply(x)
        let sch = level.transversal[y]
          .inv()
          .compose(g.compose(level.transversal[x]))
        if sch.is_identity() {
          continue
        }
        if !sifts_to_identity_from(chain, sch, i + 1) {
          return Some(sch)
        }
      }
    }
  }
  None
}

///|
/// 隨機群元素（生成元隨機遊走）。
fn random_element(
  gens : Array[@m23.Perm],
  rng : @splitmix.RandomState,
  n : Int32,
) -> @m23.Perm raise Error {
  let mut acc = @m23.Perm::identity(n)
  let len = 2 * n + 1
  for step = 0; step < len; step = step + 1 {
    let g = gens[rng.next_positive_int() % gens.length()]
    if rng.next_positive_int() % 2 == 0 {
      acc = acc.compose(g)
    } else {
      acc = acc.compose(g.inv())
    }
  }
  acc
}

///|
/// Las Vegas Schreier–Sims：隨機採樣 + 驗證修復，輸出必為已驗證 BSGS。
pub fn las_vegas_schreier_sims(
  n : Int32,
  generators : Array[@m23.Perm],
  seed~ : UInt64,
  samples~ : Int32 = 8,
  max_iterations~ : Int32 = 200,
) -> LasVegasResult raise Error {
  let rng = @splitmix.RandomState(seed~)
  let strong = generators.copy()
  let mut iterations = 0
  let mut total_random = 0
  let mut chain = randomized_chain(n, strong, rng, samples)
  while true {
    match verify_bsgs(chain) {
      None =>
        return {
          chain,
          iterations,
          random_samples: total_random,
          verified: true,
        }
      Some(witness) => {
        strong.push(witness)
        for s = 0; s < samples; s = s + 1 {
          strong.push(random_element(generators, rng, n))
          total_random = total_random + 1
        }
        iterations = iterations + 1
        if iterations > max_iterations {
          raise SuperGroupError::VerificationFailed("exceeded max iterations")
        }
        chain = randomized_chain(n, strong, rng, samples)
      }
    }
  } nobreak {
    raise SuperGroupError::VerificationFailed("unreachable")
  }
}

///|
/// 符號置換生成元 → S_{2n} 置換生成元。
pub fn signed_generators_to_perm(
  gens : Array[SignedPerm],
) -> Array[@m23.Perm] raise Error {
  let out : Array[@m23.Perm] = []
  for g in gens {
    out.push(g.to_perm())
  }
  out
}

///|
/// B_n Las Vegas 證書：階數 = 2ⁿ·n!，BSGS 已驗證，生成元皆成員。
pub fn hyperoctahedral_las_vegas_certificate(
  n : Int32,
  seed~ : UInt64,
) -> Bool raise Error {
  let gens = signed_generators_to_perm(hyperoctahedral_generators(n))
  let res = las_vegas_schreier_sims(2 * n, gens, seed~)
  if !res.verified {
    return false
  }
  if res.chain.order != hyperoctahedral_order(n) {
    return false
  }
  res.chain.certificate(gens)
}

///|
/// D_n Las Vegas 證書：階數 = 2ⁿ⁻¹·n!（B_n 之指數 2 偶子群）。
pub fn even_signed_las_vegas_certificate(
  n : Int32,
  seed~ : UInt64,
) -> Bool raise Error {
  let gens = signed_generators_to_perm(even_signed_generators(n))
  let res = las_vegas_schreier_sims(2 * n, gens, seed~)
  if !res.verified {
    return false
  }
  let expected = hyperoctahedral_order(n) / @bigint.BigInt::from_int(2)
  if res.chain.order != expected {
    return false
  }
  res.chain.certificate(gens)
}

///|
/// 超 grading 證書：B_n 含奇偶兩類，D_n 全偶，且 |B_n| = 2|D_n|。
pub fn super_grading_certificate(n : Int32) -> Bool raise Error {
  if n < 2 {
    raise SuperGroupError::InvalidSignedPerm("n >= 2")
  }
  let bn = hyperoctahedral_generators(n)
  let dn = even_signed_generators(n)
  for g in dn {
    if g.parity() != 1 {
      return false
    }
  }
  let mut has_odd = false
  for g in bn {
    if g.parity() == -1 {
      has_odd = true
    }
  }
  if !has_odd {
    return false
  }
  // parity 為群同態
  for g in bn {
    for h in bn {
      if g.compose(h).parity() != g.parity() * h.parity() {
        return false
      }
    }
  }
  // 真實計算兩群階數並驗證指數 2（唔再用 order==order/2*2 恆真式）
  let bres = las_vegas_schreier_sims(
    2 * n,
    signed_generators_to_perm(bn),
    seed=17UL,
  )
  let dres = las_vegas_schreier_sims(
    2 * n,
    signed_generators_to_perm(dn),
    seed=17UL,
  )
  if !bres.verified || !dres.verified {
    return false
  }
  dres.chain.order * @bigint.BigInt::from_int(2) == bres.chain.order
}

///|
/// Las Vegas 正確性與種子無關：不同種子得到相同階數（輸出必正確）。
pub fn las_vegas_seed_independence_certificate(n : Int32) -> Bool raise Error {
  let gens = signed_generators_to_perm(hyperoctahedral_generators(n))
  let r1 = las_vegas_schreier_sims(2 * n, gens, seed=1UL)
  let r2 = las_vegas_schreier_sims(2 * n, gens, seed=12345UL)
  let r3 = las_vegas_schreier_sims(2 * n, gens, seed=99999UL)
  r1.verified &&
  r2.verified &&
  r3.verified &&
  r1.chain.order == r2.chain.order &&
  r2.chain.order == r3.chain.order &&
  r1.chain.order == hyperoctahedral_order(n)
}
