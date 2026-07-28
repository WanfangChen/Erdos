import Erdos279.Factorization

namespace Erdos279

/--
The product `1 * 2 * ... * n`, defined locally because the minimal `Std`
environment used by this project does not expose a factorial API.
-/
private def euclidProduct : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * euclidProduct n

private theorem euclidProduct_pos (n : Nat) :
    0 < euclidProduct n := by
  induction n with
  | zero => simp [euclidProduct]
  | succ n ih =>
      simp only [euclidProduct]
      exact Nat.mul_pos (by omega) ih

private theorem dvd_euclidProduct
    {d n : Nat} (hdpos : 1 ≤ d) (hdle : d ≤ n) :
    d ∣ euclidProduct n := by
  induction n with
  | zero =>
      omega
  | succ n ih =>
      by_cases hdeq : d = n + 1
      · subst d
        refine ⟨euclidProduct n, ?_⟩
        rfl
      · have hdle' : d ≤ n := by omega
        rcases ih hdle' with ⟨c, hc⟩
        refine ⟨(n + 1) * c, ?_⟩
        simp only [euclidProduct, hc]
        simp [Nat.mul_assoc, Nat.mul_comm]

/-- Euclid's theorem for the project's internal prime subtype. -/
theorem exists_prime_gt (n : Nat) :
    ∃ p : Prime, n < p.1 := by
  let q := euclidProduct n + 1
  have hqgt : 1 < q := by
    have hpos := euclidProduct_pos n
    simp only [q]
    omega
  rcases exists_isPrime_dvd hqgt with ⟨p, hpq⟩
  refine ⟨p, ?_⟩
  apply Nat.lt_of_not_ge
  intro hple
  have hponele : 1 ≤ p.1 := Nat.le_trans (by omega) p.two_le
  have hpprod : p.1 ∣ euclidProduct n :=
    dvd_euclidProduct hponele hple
  have hpone : p.1 ∣ 1 := by
    exact (Nat.dvd_add_iff_right hpprod).mpr (by simpa [q] using hpq)
  have hp_eq_one : p.1 = 1 := Nat.dvd_one.mp hpone
  have hp_two := p.two_le
  omega

end Erdos279
