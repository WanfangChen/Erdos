import Erdos279.ArithmeticProgressionPrimeCountingPNT
import Erdos279.FixedPNTHardReduction

/-!
# Unconditional fixed-modulus prime number theorem

This packages the positive-modulus arithmetic-progression PNT and the
degenerate modulus-zero case into the universal input used by the hard-stage
reduction.
-/

namespace Erdos279

/-- The fixed arithmetic-progression PNT is available for every natural
modulus, including the project's harmless degenerate modulus zero. -/
theorem allFixedProgressionPrimeNumberTheorems :
    AllFixedProgressionPrimeNumberTheorems := by
  intro q
  cases q with
  | zero =>
      exact fixedProgressionPrimeNumberTheorem_zero
  | succ q =>
      exact fixedProgressionPrimeNumberTheorem
        (q + 1) (by omega)

end Erdos279
