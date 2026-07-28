import Erdos279.NthLogRatioInversion

/-!
# Fixed-progression PNT inputs for one density mesh

The finite CRT calculations determine both relevant prime densities exactly.
The elementary inversion theorem then converts the two count-form PNT
statements into the nth-prime asymptotics consumed by the matching layer.
Thus the complete prime-enumeration part of a mesh depends only on PNT in
two explicit fixed moduli.
-/

namespace Erdos279

/-- The two fixed-modulus progression PNT statements attached to a density
mesh. -/
structure MeshFixedProgressionPNTInputs
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k) where
  periodicPNT :
    FixedProgressionPrimeNumberTheorem
      (h.1 * M.modulus.1)
  complementaryPNT :
    FixedProgressionPrimeNumberTheorem
      (h.1 *
        primeSubsetModulus
          (oldControllerPrimes h M.cutoff))

namespace MeshFixedProgressionPNTInputs

/-- The two fixed-progression PNT statements imply both quantitative
nth-prime asymptotics for the mesh. -/
noncomputable def toMeshNthPrimeAsymptoticInputs
    {h : Prime} {k : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    {hh : 3 ≤ h.1} {hk : 0 < k}
    (A : MeshFixedProgressionPNTInputs M) :
    MeshNthPrimeAsymptoticInputs M hh hk where
  periodic_asymptotic := by
    apply projectNthAsymptotic_of_counting
    · exact M.periodicDensity_pos hh hk
    · exact
        mesh_periodicReservoir_countingAsymptotic
          M A.periodicPNT
  complementary_asymptotic := by
    have hH :
        ∀ p ∈ oldControllerPrimes h M.cutoff,
          InControllerProgression h p := by
      intro p hp
      exact (mem_oldControllerPrimes.mp hp).1
    apply projectNthAsymptotic_of_counting
    · exact
        controllerComplementDensity_pos
          h hh
          (oldControllerPrimes h M.cutoff)
          hH
    · exact
        mesh_complementaryTargets_countingAsymptotic
          M A.complementaryPNT

/-- Consequently the two fixed-progression PNT statements construct the
exact prime enumerations used by the tail matching theorem. -/
noncomputable def toMeshPrimeEnumerations
    {h : Prime} {k : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    {hh : 3 ≤ h.1} {hk : 0 < k}
    (A : MeshFixedProgressionPNTInputs M) :
    MeshPrimeEnumerations M :=
  (A.toMeshNthPrimeAsymptoticInputs
      (hh := hh) (hk := hk)).toMeshNthPrimeInputs
    |>.toMeshPrimeEnumerations hh hk

end MeshFixedProgressionPNTInputs

end Erdos279
