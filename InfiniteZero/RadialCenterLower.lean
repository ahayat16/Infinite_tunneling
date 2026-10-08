import InfiniteZero.RealRadialState
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# A uniform lower bound at the center of a normalized decreasing radial state

An exterior mass at most one half leaves at least one half inside the
fixed ball. Monotonicity bounds the interior density by its central value.
The exact planar ball volume then gives an explicit positive lower bound,
independent of the wavefunction and of any coupling parameter.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero

/-- Radial monotonicity bounds the mass of a ball by its volume times the
squared central value. No differentiability of the state is needed. -/
theorem mass_ball_le_realRadialProfile_zero_sq {a : ℝ} (ha : 0 < a)
    {φ : Wavefunction} (hφ : MemLp φ 2 volume) (hpos : IsPositiveRadial φ)
    (hmono : AntitoneOn (realRadialProfile φ) (Ici 0)) :
    (∫ x in Metric.ball (0 : Plane) a, ‖φ x‖ ^ 2) ≤
      Real.pi * a ^ 2 * (realRadialProfile φ 0) ^ 2 := by
  have hbound (x : Plane) : ‖φ x‖ ^ 2 ≤ (realRadialProfile φ 0) ^ 2 := by
    rw [hpos.radial x, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    apply (sq_le_sq₀ (hpos.profile_pos ‖x‖).le (hpos.profile_pos 0).le).mpr
    exact hmono (by simp) (norm_nonneg x) (norm_nonneg x)
  have hvol : volume.real (Metric.ball (0 : Plane) a) = Real.pi * a ^ 2 := by
    simp [Measure.real, EuclideanSpace.volume_ball_fin_two, ha.le,
      Real.pi_pos.le, mul_comm]
  calc
    (∫ x in Metric.ball (0 : Plane) a, ‖φ x‖ ^ 2) ≤
        ∫ _x in Metric.ball (0 : Plane) a, (realRadialProfile φ 0) ^ 2 :=
      setIntegral_mono_on hφ.norm.integrable_sq.integrableOn
        (integrableOn_const measure_ball_lt_top.ne) measurableSet_ball
        (fun x _ => hbound x)
    _ = Real.pi * a ^ 2 * (realRadialProfile φ 0) ^ 2 := by
      rw [setIntegral_const, smul_eq_mul, hvol]

/-- Explicit central lower bound from normalized mass and a fixed exterior
probability bound. The exterior includes the boundary of the ball. -/
theorem realRadialProfile_zero_lower_of_exteriorMass {a : ℝ} (ha : 0 < a)
    {φ : Wavefunction} (hφ : MemLp φ 2 volume) (hmass : mass φ = 1)
    (hpos : IsPositiveRadial φ) (hmono : AntitoneOn (realRadialProfile φ) (Ici 0))
    (htail : (∫ x in {x : Plane | a ≤ ‖x‖}, ‖φ x‖ ^ 2) ≤ (1 / 2 : ℝ)) :
    Real.sqrt (1 / (2 * Real.pi * a ^ 2)) ≤ realRadialProfile φ 0 := by
  have hcompl : (Metric.ball (0 : Plane) a)ᶜ = {x : Plane | a ≤ ‖x‖} := by
    ext x
    simp [Metric.mem_ball, dist_zero_right]
  have hsplit := integral_add_compl (s := Metric.ball (0 : Plane) a)
    measurableSet_ball hφ.norm.integrable_sq
  rw [hcompl] at hsplit
  change (∫ x in Metric.ball (0 : Plane) a, ‖φ x‖ ^ 2) +
    (∫ x in {x : Plane | a ≤ ‖x‖}, ‖φ x‖ ^ 2) = mass φ at hsplit
  rw [hmass] at hsplit
  have hball := mass_ball_le_realRadialProfile_zero_sq ha hφ hpos hmono
  have hhalf : (1 / 2 : ℝ) ≤ Real.pi * a ^ 2 * (realRadialProfile φ 0) ^ 2 := by
    linarith
  apply Real.sqrt_le_iff.mpr
  refine ⟨(hpos.profile_pos 0).le, (div_le_iff₀ (by positivity)).mpr ?_⟩
  nlinarith only [hhalf]

/-- The central lower bound is chosen before the state. -/
theorem exists_uniform_realRadialProfile_zero_lower {a : ℝ} (ha : 0 < a) :
    ∃ c > 0, ∀ φ : Wavefunction, MemLp φ 2 volume → mass φ = 1 →
      IsPositiveRadial φ → AntitoneOn (realRadialProfile φ) (Ici 0) →
      (∫ x in {x : Plane | a ≤ ‖x‖}, ‖φ x‖ ^ 2) ≤ (1 / 2 : ℝ) →
      c ≤ realRadialProfile φ 0 := by
  refine ⟨Real.sqrt (1 / (2 * Real.pi * a ^ 2)), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro φ hφ hmass hpos hmono htail
  exact realRadialProfile_zero_lower_of_exteriorMass ha hφ hmass hpos hmono htail

end InfiniteZero
