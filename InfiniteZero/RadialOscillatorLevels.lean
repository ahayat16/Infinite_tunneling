import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Ordering the radial magnetic oscillator modes

For a positive radial Hessian coefficient `d`, the unit-field oscillator
has frequency `sqrt (1 + 2*d)`. This module orders its classical mode
formula: the ground mode is `(0,0)` and the first excited value occurs at
`(0,1)`. These are scalar calculations; identification of the operator
spectrum with the mode formula is a separate spectral input.
-/

noncomputable section

namespace InfiniteZero

/-- The oscillator frequency for a radial potential with second derivative `d`. -/
def radialOscillatorFrequency (d : ℝ) : ℝ := Real.sqrt (1 + 2 * d)

/-- The unit-field oscillator mode value, indexed by radial and angular modes. -/
def radialOscillatorMode (d : ℝ) (n : ℕ) (m : ℤ) : ℝ :=
  radialOscillatorFrequency d * (2 * (n : ℝ) + |(m : ℝ)| + 1) - (m : ℝ)

theorem radialOscillatorFrequency_gt_one {d : ℝ} (hd : 0 < d) :
    1 < radialOscillatorFrequency d := by
  have hs := Real.sq_sqrt (show 0 ≤ 1 + 2 * d by linarith)
  have hn := Real.sqrt_nonneg (1 + 2 * d)
  unfold radialOscillatorFrequency
  nlinarith

/-- The mode `(0,0)` has energy equal to the oscillator frequency. -/
theorem radialOscillatorMode_ground (d : ℝ) :
    radialOscillatorMode d 0 0 = radialOscillatorFrequency d := by
  simp [radialOscillatorMode]

/-- Every mode lies above the ground value. -/
theorem radialOscillatorMode_ground_le {d : ℝ} (hd : 0 < d) (n : ℕ) (m : ℤ) :
    radialOscillatorFrequency d ≤ radialOscillatorMode d n m := by
  have hw := radialOscillatorFrequency_gt_one hd
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have ha := le_abs_self (m : ℝ)
  have hp := mul_nonneg (show 0 ≤ radialOscillatorFrequency d - 1 by linarith)
    (abs_nonneg (m : ℝ))
  have hpn := mul_nonneg (show 0 ≤ radialOscillatorFrequency d by linarith) hn
  unfold radialOscillatorMode
  nlinarith

/-- Outside `(0,0)`, every mode is at least `2*frequency - 1`. -/
theorem radialOscillatorMode_excited_lower {d : ℝ} (hd : 0 < d)
    {n : ℕ} {m : ℤ} (hne : n ≠ 0 ∨ m ≠ 0) :
    2 * radialOscillatorFrequency d - 1 ≤ radialOscillatorMode d n m := by
  have hw := radialOscillatorFrequency_gt_one hd
  have ha := le_abs_self (m : ℝ)
  have hp := mul_nonneg (show 0 ≤ radialOscillatorFrequency d - 1 by linarith)
    (abs_nonneg (m : ℝ))
  rcases hne with hn | hm
  · have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hpn := mul_nonneg (show 0 ≤ radialOscillatorFrequency d by linarith)
      (show 0 ≤ (n : ℝ) - 1 by linarith)
    unfold radialOscillatorMode
    nlinarith
  · have hm' : (1 : ℝ) ≤ |(m : ℝ)| := by
      have habs : (1 : ℤ) ≤ |m| := by
        have hp' : (0 : ℤ) < |m| := abs_pos.mpr hm
        omega
      exact_mod_cast habs
    have hpm := mul_nonneg (show 0 ≤ radialOscillatorFrequency d - 1 by linarith)
      (show 0 ≤ |(m : ℝ)| - 1 by linarith)
    have hpn := mul_nonneg (show 0 ≤ radialOscillatorFrequency d by linarith)
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    unfold radialOscillatorMode
    nlinarith

/-- The angular mode `(0,1)` attains the first excited value. -/
theorem radialOscillatorMode_firstExcited (d : ℝ) :
    radialOscillatorMode d 0 1 = 2 * radialOscillatorFrequency d - 1 := by
  norm_num [radialOscillatorMode]
  ring

/-- Equality with the ground value forces the unique mode `(0,0)`. -/
theorem radialOscillatorMode_eq_ground_iff {d : ℝ} (hd : 0 < d) (n : ℕ) (m : ℤ) :
    radialOscillatorMode d n m = radialOscillatorFrequency d ↔ n = 0 ∧ m = 0 := by
  constructor
  · intro heq
    by_contra h
    have hne : n ≠ 0 ∨ m ≠ 0 := by tauto
    have hl := radialOscillatorMode_excited_lower hd hne
    have hw := radialOscillatorFrequency_gt_one hd
    rw [heq] at hl
    linarith
  · rintro ⟨rfl, rfl⟩
    exact radialOscillatorMode_ground d

/-- Subtracting the first two mode values gives the positive oscillator gap. -/
theorem radialOscillatorMode_gap (d : ℝ) :
    radialOscillatorMode d 0 1 - radialOscillatorMode d 0 0 =
      Real.sqrt (1 + 2 * d) - 1 := by
  rw [radialOscillatorMode_firstExcited, radialOscillatorMode_ground]
  unfold radialOscillatorFrequency
  ring

/-- The bottom of the classical oscillator mode values. -/
def radialOscillatorGroundLevel (d : ℝ) : ℝ :=
  sInf {E : ℝ | ∃ n : ℕ, ∃ m : ℤ, radialOscillatorMode d n m = E}

/-- The bottom after removing the unique ground mode `(0,0)`. For `d>0`,
this is the second mode value, counting multiplicity. -/
def radialOscillatorSecondLevel (d : ℝ) : ℝ :=
  sInf {E : ℝ | ∃ n : ℕ, ∃ m : ℤ,
    (n ≠ 0 ∨ m ≠ 0) ∧ radialOscillatorMode d n m = E}

/-- The infimum of all mode values is attained at `(0,0)`. -/
theorem radialOscillatorGroundLevel_eq {d : ℝ} (hd : 0 < d) :
    radialOscillatorGroundLevel d = radialOscillatorFrequency d := by
  apply IsLeast.csInf_eq
  refine ⟨⟨0, 0, radialOscillatorMode_ground d⟩, ?_⟩
  rintro E ⟨n, m, rfl⟩
  exact radialOscillatorMode_ground_le hd n m

/-- The infimum over the remaining modes is attained at `(0,1)`. -/
theorem radialOscillatorSecondLevel_eq {d : ℝ} (hd : 0 < d) :
    radialOscillatorSecondLevel d = 2 * radialOscillatorFrequency d - 1 := by
  apply IsLeast.csInf_eq
  refine ⟨⟨0, 1, Or.inr (by norm_num), radialOscillatorMode_firstExcited d⟩, ?_⟩
  rintro E ⟨n, m, hne, rfl⟩
  exact radialOscillatorMode_excited_lower hd hne

/-- The difference of the first two ordered mode levels is the usual
positive magnetic oscillator gap. -/
theorem radialOscillatorLevel_gap {d : ℝ} (hd : 0 < d) :
    radialOscillatorSecondLevel d - radialOscillatorGroundLevel d =
      Real.sqrt (1 + 2 * d) - 1 := by
  rw [radialOscillatorSecondLevel_eq hd, radialOscillatorGroundLevel_eq hd]
  unfold radialOscillatorFrequency
  ring

end InfiniteZero
