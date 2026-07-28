import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.SumPrimeReciprocals

import Erdos279.Definitions

/-!
# Mathlib bridge for the analytic formalization

This module pins the mathlib foundations needed by the analytic part of the
paper and relates the project's small foundational primality predicate to
`Nat.Prime`.
-/

namespace Erdos279

theorem isPrime_iff_natPrime (p : Nat) :
    IsPrime p ↔ Nat.Prime p := by
  simp only [IsPrime, Nat.prime_def]

theorem Prime.natPrime (p : Prime) : Nat.Prime p.1 :=
  (isPrime_iff_natPrime p.1).mp p.2

end Erdos279
