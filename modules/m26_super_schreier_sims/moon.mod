name = "dtt/m26_super_schreier_sims"

version = "0.1.0"

readme = "README.md"

license = "Apache-2.0"

keywords = [
  "schreier-sims",
  "las-vegas",
  "hyperoctahedral-group",
  "signed-permutation",
  "randomized-algorithm",
  "bsgs-verification",
]

description = "Module M26: Las Vegas Schreier-Sims for SIGNED permutation groups (classical B_n/D_n, not a supergroup algorithm) plus an explicit account of where superizing COLLIDES: odd unipotents have infinite order, so finite orbit counting fails and the correct structure is body-group BSGS plus an odd module (hyperoctahedral B_n and even subgroup D_n), splitmix64-driven random Schreier generators with deterministic BSGS verification-repair loop, orbit-stabilizer order certificates and Z2 parity grading"

import {
  "dtt/m20_polar2_jacobi_cohomology@0.1.0",
  "dtt/m22_supercube_euler@0.1.0",
  "dtt/m23_obstruction_orbits@0.1.0",
}
