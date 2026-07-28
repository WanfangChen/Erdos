import Erdos279.BaseCoverage
import Erdos279.SmoothHard

/-!
# Elementary completion with only the two genuine coverage inputs exposed

This module reduces the five fields of `CompletionData` to the two
construction results actually supplied by the analytic part of the paper:
coverage of hard-form targets and coverage of prime targets.  The same
shifted assignment occurs in both hypotheses.
-/

namespace Erdos279

/--
The threshold required by the elementary completion layer.  The first term
is the threshold from the two genuinely constructive inputs.  The others
exclude target `0`, make the hub class mature, and put the fourth case above
`k²`.
-/
def elementaryCompletionThreshold
    (k constructionThreshold : Nat) (h : Prime) : Nat :=
  max constructionThreshold (max 1 (max (k * h.1) (k * k + 1)))

theorem constructionThreshold_le_elementary
    (k constructionThreshold : Nat) (h : Prime) :
    constructionThreshold ≤
      elementaryCompletionThreshold k constructionThreshold h :=
  Nat.le_max_left _ _

theorem one_le_elementaryCompletionThreshold
    (k constructionThreshold : Nat) (h : Prime) :
    1 ≤ elementaryCompletionThreshold k constructionThreshold h :=
  Nat.le_trans
    (Nat.le_max_left 1 (max (k * h.1) (k * k + 1)))
    (Nat.le_max_right constructionThreshold
      (max 1 (max (k * h.1) (k * k + 1))))

theorem hubMaturity_le_elementaryThreshold
    (k constructionThreshold : Nat) (h : Prime) :
    k * h.1 ≤ elementaryCompletionThreshold k constructionThreshold h :=
  Nat.le_trans
    (Nat.le_max_left (k * h.1) (k * k + 1))
    (Nat.le_trans
      (Nat.le_max_right 1 (max (k * h.1) (k * k + 1)))
      (Nat.le_max_right constructionThreshold
        (max 1 (max (k * h.1) (k * k + 1)))))

theorem squareSucc_le_elementaryThreshold
    (k constructionThreshold : Nat) (h : Prime) :
    k * k + 1 ≤ elementaryCompletionThreshold k constructionThreshold h :=
  Nat.le_trans
    (Nat.le_max_right (k * h.1) (k * k + 1))
    (Nat.le_trans
      (Nat.le_max_right 1 (max (k * h.1) (k * k + 1)))
      (Nat.le_max_right constructionThreshold
        (max 1 (max (k * h.1) (k * k + 1)))))

/--
Intermediate constructor retaining an explicit smooth/non-hub coverage
hypothesis while discharging the small-outside and remaining-prime fields.
-/
def completionData_of_core_with_smooth
    {k : Nat}
    (hk : 3 ≤ k)
    (h : Prime)
    (hkh : k < h.1)
    (a : ShiftedAssignment)
    (constructionThreshold : Nat)
    (hzero :
      ∀ q : Prime, q ≠ h →
        ¬ InControllerProgression h q →
        (a q : Nat) = 0)
    (hsmooth :
      ∀ m : Nat, constructionThreshold ≤ m →
        SmoothFor h m → ¬ h.1 ∣ m →
        ShiftedMatureCovers k m a)
    (hhard :
      ∀ m : Nat, constructionThreshold ≤ m →
        HardTarget h m →
        ShiftedMatureCovers k m a)
    (hprime :
      ∀ m : Nat, constructionThreshold ≤ m →
        IsPrime m →
        ShiftedMatureCovers k m a) :
    CompletionData k where
  hub := h
  shifted := a
  threshold := elementaryCompletionThreshold k constructionThreshold h
  smooth_noHub := by
    intro m hm hsm hnh
    apply hsmooth m _ hsm hnh
    exact Nat.le_trans
      (constructionThreshold_le_elementary k constructionThreshold h)
      hm
  hard := by
    intro m hm htarget
    apply hhard m _ htarget
    exact Nat.le_trans
      (constructionThreshold_le_elementary k constructionThreshold h)
      hm
  smallOutside := by
    intro m _ houtside
    exact smallOutside_covered_by_zero_classes hzero houtside
  outsideLarge_isPrime := by
    intro m hm hnonsmooth hnosmall
    apply Erdos279.outsideLarge_isPrime hk hkh _ hnonsmooth hnosmall
    have hbound :
        k * k + 1 ≤ elementaryCompletionThreshold
          k constructionThreshold h :=
      squareSucc_le_elementaryThreshold k constructionThreshold h
    omega
  primeTarget := by
    intro m hm hp
    apply hprime m _ hp
    exact Nat.le_trans
      (constructionThreshold_le_elementary k constructionThreshold h)
      hm

theorem P_of_core_with_smooth
    {k : Nat}
    (hk : 3 ≤ k)
    (h : Prime)
    (hkh : k < h.1)
    (a : ShiftedAssignment)
    (constructionThreshold : Nat)
    (hzero :
      ∀ q : Prime, q ≠ h →
        ¬ InControllerProgression h q →
        (a q : Nat) = 0)
    (hsmooth :
      ∀ m : Nat, constructionThreshold ≤ m →
        SmoothFor h m → ¬ h.1 ∣ m →
        ShiftedMatureCovers k m a)
    (hhard :
      ∀ m : Nat, constructionThreshold ≤ m →
        HardTarget h m →
        ShiftedMatureCovers k m a)
    (hprime :
      ∀ m : Nat, constructionThreshold ≤ m →
        IsPrime m →
        ShiftedMatureCovers k m a) :
    P k :=
  P_of_completionData
    (completionData_of_core_with_smooth
      hk h hkh a constructionThreshold hzero hsmooth hhard hprime)

/--
Paper-aligned completion constructor.  Its only coverage assumptions are
the explicit hard form `h^e u` and prime targets.  All four elementary
classification branches are derived, and the same global assignment is
used throughout.
-/
def completionData_of_hardForm_and_prime
    {k : Nat}
    (hk : 3 ≤ k)
    (h : Prime)
    (hkh : k < h.1)
    (a : ShiftedAssignment)
    (constructionThreshold : Nat)
    (hhub : (a h : Nat) = 1)
    (hzero :
      ∀ q : Prime, q ≠ h →
        ¬ InControllerProgression h q →
        (a q : Nat) = 0)
    (hhard :
      ∀ m : Nat, constructionThreshold ≤ m →
        HasHardForm h m →
        ShiftedMatureCovers k m a)
    (hprime :
      ∀ m : Nat, constructionThreshold ≤ m →
        IsPrime m →
        ShiftedMatureCovers k m a) :
    CompletionData k where
  hub := h
  shifted := a
  threshold := elementaryCompletionThreshold k constructionThreshold h
  smooth_noHub := by
    intro m hm hsmooth hnotHub
    apply smoothFor_noHub_covered_by_hub hsmooth hnotHub hhub
    have hhubBound :
        k * h.1 ≤ elementaryCompletionThreshold
          k constructionThreshold h :=
      hubMaturity_le_elementaryThreshold k constructionThreshold h
    exact Nat.le_trans hhubBound
      (Nat.le_trans hm (Nat.le_add_right m 1))
  hard := by
    intro m hm htarget
    apply hhard m
    · exact Nat.le_trans
        (constructionThreshold_le_elementary k constructionThreshold h)
        hm
    · apply hardTarget_hasHardForm
      · have hmone : 1 ≤ m :=
          Nat.le_trans
            (one_le_elementaryCompletionThreshold
              k constructionThreshold h)
            hm
        omega
      · exact htarget
  smallOutside := by
    intro m _ houtside
    exact smallOutside_covered_by_zero_classes hzero houtside
  outsideLarge_isPrime := by
    intro m hm hnonsmooth hnosmall
    apply Erdos279.outsideLarge_isPrime hk hkh _ hnonsmooth hnosmall
    have hbound :
        k * k + 1 ≤ elementaryCompletionThreshold
          k constructionThreshold h :=
      squareSucc_le_elementaryThreshold k constructionThreshold h
    omega
  primeTarget := by
    intro m hm hp
    apply hprime m _ hp
    exact Nat.le_trans
      (constructionThreshold_le_elementary k constructionThreshold h)
      hm

theorem P_of_hardForm_and_prime
    {k : Nat}
    (hk : 3 ≤ k)
    (h : Prime)
    (hkh : k < h.1)
    (a : ShiftedAssignment)
    (constructionThreshold : Nat)
    (hhub : (a h : Nat) = 1)
    (hzero :
      ∀ q : Prime, q ≠ h →
        ¬ InControllerProgression h q →
        (a q : Nat) = 0)
    (hhard :
      ∀ m : Nat, constructionThreshold ≤ m →
        HasHardForm h m →
        ShiftedMatureCovers k m a)
    (hprime :
      ∀ m : Nat, constructionThreshold ≤ m →
        IsPrime m →
        ShiftedMatureCovers k m a) :
    P k :=
  P_of_completionData
    (completionData_of_hardForm_and_prime
      hk h hkh a constructionThreshold hhub hzero hhard hprime)

end Erdos279
