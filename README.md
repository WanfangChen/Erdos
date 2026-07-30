# Lean 4 formalization of Erdős Problem 279

This project contains an unconditional Lean 4 proof of the affirmative
statement of Erdős Problem 279.

The exact formal statement is:

```lean
def GlobalAffirmative : Prop :=
  ∀ k : Nat, 3 ≤ k → P k
```

where `P k` says that there is one choice of a canonical residue class
modulo every prime which covers every sufficiently large integer with
quotient at least `k`.

The final theorem is:

```lean
theorem Erdos279.globalAffirmative :
    Erdos279.GlobalAffirmative
```

It has no mathematical hypotheses.

## Verification

- Lean toolchain: `v4.27.0-rc1`
- libraries: locked remote revisions of Mathlib and LeanArchitect
- `sorry` / `admit` / `sorryAx`: none
- custom `axiom` / `opaque` / `unsafe`: none
- final trusted dependencies reported by `#print axioms`:
  `propext`, `Classical.choice`, and `Quot.sound`

Those three are standard Lean logical principles, not assumptions introduced
by this project.

Run the complete check on Windows:

```powershell
./verify.ps1
```

Or run the two checks separately:

```text
lake build
lake env lean Erdos279/Audit.lean
```

The repository deliberately excludes `.lake/`. Lake reconstructs that
dependency and build cache from the committed `lakefile.lean`,
`lake-manifest.json`, and `lean-toolchain`.

GitHub Actions runs the build, rejects `sorryAx` through an independent
`nanoda` type check, and prints the trusted dependencies of the final
theorem on every push and pull request.

## Proof architecture

The formalization includes:

- the exact quantifier structure and equivalence of the integer, natural,
  and congruence formulations;
- finite-CSP compactness and the transfer from staged assignments to one
  global residue assignment;
- the controller semigroup, hub class, causal updates, stabilization, and
  completion of all target classes;
- fixed arithmetic-progression PNT, derived in Lean from Mathlib's
  weighted PNT;
- reciprocal divergence and density meshes for controller primes;
- an imported-and-audited Mathlib Selberg upper sieve;
- a translated-interval Selberg bound with explicit remainder control;
- a two-residue quotient sieve for each hard layer;
- uniform error estimates at the cutoff `⌊X^(1/64)⌋`;
- summation over all hard layers, the controller-reservoir capacity gap,
  and the final dynamic construction.

The last analytic step uses a direct two-residue Selberg sieve.  It proves
the bound needed by the paper's construction without requiring a separate
formalization of Bombieri–Vinogradov or Selberg–Delange.

## Main files

- `Erdos279/Definitions.lean`: exact statement.
- `Erdos279/ArithmeticProgressionPrimeCountingPNT.lean`: fixed AP PNT.
- `Erdos279/ShiftedIntervalSelberg.lean`: translated interval sieve.
- `Erdos279/DualResidueSieve.lean`: two-residue hard-layer covering.
- `Erdos279/DualSieveAsymptotic.lean`: uniform asymptotic bound.
- `Erdos279/DirectUniformHardReduction.lean`: capacity comparison and the
  unconditional final theorem.
- `Erdos279/Audit.lean`: kernel dependency audit.
