import Erdos279.SieveArithmetic

/-!
# Infinitely many controller primes

Mathlib contains Dirichlet's theorem on primes in a fixed reduced residue
class.  This file bridges that theorem to the project's internal prime type
and constructs an explicit strictly increasing sequence in `1 mod h`.
-/

namespace Erdos279

/-- Above every bound there is a project prime in the controller progression. -/
theorem exists_controllerPrime_gt
    (h : Prime) (n : Nat) :
    ∃ p : Prime, n < p.1 ∧ InControllerProgression h p := by
  letI : NeZero h.1 := ⟨Nat.ne_of_gt h.pos⟩
  obtain ⟨p, hpn, hp, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod
      (q := h.1) (a := (1 : ZMod h.1)) isUnit_one n
  let p' : Prime :=
    ⟨p, (isPrime_iff_natPrime p).mpr hp⟩
  refine ⟨p', hpn, ?_⟩
  change p % h.1 = 1
  have hpmodNat :
      (p : ZMod h.1) = ((1 : Nat) : ZMod h.1) := by
    simpa using hpmod
  have hpmod' : p ≡ 1 [MOD h.1] :=
    (ZMod.natCast_eq_natCast_iff p 1 h.1).mp hpmodNat
  change p % h.1 = 1 % h.1 at hpmod'
  simpa [Nat.mod_eq_of_lt h.one_lt] using hpmod'

/-- A chosen controller prime above a prescribed bound. -/
noncomputable def controllerPrimeAbove
    (h : Prime) (n : Nat) : Prime :=
  Classical.choose (exists_controllerPrime_gt h n)

theorem controllerPrimeAbove_gt
    (h : Prime) (n : Nat) :
    n < (controllerPrimeAbove h n).1 :=
  (Classical.choose_spec (exists_controllerPrime_gt h n)).1

theorem controllerPrimeAbove_mem
    (h : Prime) (n : Nat) :
    InControllerProgression h (controllerPrimeAbove h n) :=
  (Classical.choose_spec (exists_controllerPrime_gt h n)).2

/-- A canonical-by-choice increasing enumeration of an infinite controller-prime subsequence. -/
noncomputable def controllerPrimeSequence
    (h : Prime) : Nat → Prime
  | 0 => controllerPrimeAbove h h.1
  | n + 1 =>
      controllerPrimeAbove h (controllerPrimeSequence h n).1

theorem controllerPrimeSequence_mem
    (h : Prime) (n : Nat) :
    InControllerProgression h (controllerPrimeSequence h n) := by
  cases n with
  | zero =>
      exact controllerPrimeAbove_mem h h.1
  | succ n =>
      exact controllerPrimeAbove_mem h
        (controllerPrimeSequence h n).1

theorem controllerPrimeSequence_lt_succ
    (h : Prime) (n : Nat) :
    (controllerPrimeSequence h n).1 <
      (controllerPrimeSequence h (n + 1)).1 := by
  exact controllerPrimeAbove_gt h
    (controllerPrimeSequence h n).1

theorem controllerPrimeSequence_strictMono
    (h : Prime) :
    StrictMono fun n => (controllerPrimeSequence h n).1 := by
  exact strictMono_nat_of_lt_succ
    (controllerPrimeSequence_lt_succ h)

theorem controllerPrimeSequence_injective
    (h : Prime) :
    Function.Injective (controllerPrimeSequence h) := by
  intro m n hmn
  apply (controllerPrimeSequence_strictMono h).injective
  exact congrArg Subtype.val hmn

theorem controllerPrimeSequence_above_hub
    (h : Prime) (n : Nat) :
    h.1 < (controllerPrimeSequence h n).1 := by
  exact hub_lt_of_inControllerProgression
    (controllerPrimeSequence_mem h n)

/-- The increasing controller-prime sequence as an embedding. -/
noncomputable def controllerPrimeEmbedding
    (h : Prime) : Nat ↪ Prime where
  toFun := controllerPrimeSequence h
  inj' := controllerPrimeSequence_injective h

/-- The first `N` primes of the chosen controller-prime subsequence. -/
noncomputable def controllerPrimeInitialSegment
    (h : Prime) (N : Nat) : Finset Prime :=
  (Finset.range N).map (controllerPrimeEmbedding h)

@[simp]
theorem card_controllerPrimeInitialSegment
    (h : Prime) (N : Nat) :
    (controllerPrimeInitialSegment h N).card = N := by
  classical
  simp [controllerPrimeInitialSegment]

theorem mem_controllerPrimeInitialSegment_progression
    {h p : Prime} {N : Nat}
    (hp : p ∈ controllerPrimeInitialSegment h N) :
    InControllerProgression h p := by
  classical
  rw [controllerPrimeInitialSegment, Finset.mem_map] at hp
  rcases hp with ⟨n, _hn, rfl⟩
  exact controllerPrimeSequence_mem h n

theorem hub_not_mem_controllerPrimeInitialSegment
    (h : Prime) (N : Nat) :
    h ∉ controllerPrimeInitialSegment h N := by
  intro hh
  exact
    (inControllerProgression_ne_hub
      (mem_controllerPrimeInitialSegment_progression hh)) rfl

end Erdos279
