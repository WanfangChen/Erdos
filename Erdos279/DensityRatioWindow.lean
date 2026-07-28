import Erdos279.ScaleTail

/-!
# The density window implies the prime-matching ratio window

The finite mesh construction gives

`k Δ_H < τ < h Δ_H`.

This file proves the exact reciprocal inequalities

`1/h < Δ_H/τ < 1/k`

used by the enumeration matching.
-/

namespace Erdos279

/-- The periodic prime density selected by an old-controller-prime mesh. -/
noncomputable def OldControllerPrimeDensityMesh.periodicDensity
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k) : Real :=
  (M.index : Real) *
    (controllerDensity h /
      ((M.modulus.1 : Real) - 1))

theorem OldControllerPrimeDensityMesh.periodicDensity_pos
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    (hh : 3 ≤ h.1) (hk : 0 < k) :
    0 < M.periodicDensity := by
  have hH :
      ∀ p ∈ oldControllerPrimes h M.cutoff,
        InControllerProgression h p := by
    intro p hp
    exact (mem_oldControllerPrimes.mp hp).1
  have hDelta :
      0 <
        controllerComplementDensity h
          (oldControllerPrimes h M.cutoff) :=
    controllerComplementDensity_pos
      h hh (oldControllerPrimes h M.cutoff) hH
  have hkR : (0 : Real) < (k : Real) := by
    exact_mod_cast hk
  have hleft :
      0 <
        (k : Real) *
          controllerComplementDensity h
            (oldControllerPrimes h M.cutoff) :=
    mul_pos hkR hDelta
  exact hleft.trans M.lower

/-- Algebraic form of (3.6)'s open interval. -/
theorem OldControllerPrimeDensityMesh.densityRatio_mem_Ioo
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    (hh : 3 ≤ h.1) (hk : 0 < k) :
    1 / (h.1 : Real) <
        controllerComplementDensity h
            (oldControllerPrimes h M.cutoff) /
          M.periodicDensity ∧
      controllerComplementDensity h
            (oldControllerPrimes h M.cutoff) /
          M.periodicDensity <
        1 / (k : Real) := by
  have hTau : 0 < M.periodicDensity :=
    M.periodicDensity_pos hh hk
  have hhR : (0 : Real) < (h.1 : Real) := by
    exact_mod_cast h.pos
  have hkR : (0 : Real) < (k : Real) := by
    exact_mod_cast hk
  constructor
  · apply (div_lt_div_iff₀ hhR hTau).2
    simpa [OldControllerPrimeDensityMesh.periodicDensity,
      mul_comm] using M.upper_hub
  · apply (div_lt_div_iff₀ hTau hkR).2
    simpa [OldControllerPrimeDensityMesh.periodicDensity,
      mul_comm] using M.lower

/-- An enumeration theorem with the precise density ratio predicted by the
fixed-progression prime number theorem. -/
structure MeshPrimeEnumerations
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k) where
  enumerations :
    PeriodicComplementaryEnumerations
      h M.modulus M.classes
        (oldControllerPrimes h M.cutoff)
  ratio_eq :
    enumerations.ratio =
      controllerComplementDensity h
          (oldControllerPrimes h M.cutoff) /
        M.periodicDensity

namespace MeshPrimeEnumerations

/-- The density mesh and the proved enumeration asymptotic produce the
tail prime-target matching. -/
theorem exists_tailMatching
    {h : Prime} {k : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    (E : MeshPrimeEnumerations M)
    (hh : 3 ≤ h.1) (hk : 0 < k) :
    Nonempty
      (TailPrimeTargetMatching
        E.enumerations.periodic
        E.enumerations.complementary k) := by
  have hwindow :=
    M.densityRatio_mem_Ioo hh hk
  apply E.enumerations.exists_tailMatching hk
  · simpa [E.ratio_eq] using hwindow.1
  · simpa [E.ratio_eq] using hwindow.2

end MeshPrimeEnumerations

end Erdos279
