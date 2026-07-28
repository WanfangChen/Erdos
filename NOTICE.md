# Third-party source notice

This repository contains compatibility-pinned adaptations of verified Lean
sources from the following Apache-2.0 projects:

1. `PrimeNumberTheoremAnd`, tag `v4.27.0-rc1`
   - Upstream: <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd>
   - Adapted files include the `PNT*.lean` and `WienerCore.lean` modules in
     `Erdos279/External/`.
2. Mathlib for Lean 4
   - Upstream: <https://github.com/leanprover-community/mathlib4>
   - Locked revision: `32d24245c7a12ded17325299fd41d412022cd3fe`
   - Adapted files include the `Sieve*.lean` modules in
     `Erdos279/External/`.
3. LeanArchitect
   - Upstream: <https://github.com/hanwenzhu/LeanArchitect>
   - Locked revision: `4373fe8a5bb2a26d60fbeb3d0f99d9d1aba3d824`
   - Used as a Lake dependency.

The full Apache License 2.0 text is included in `LICENSE`. Adaptations are
identified in the source tree and are distributed under the same license.
