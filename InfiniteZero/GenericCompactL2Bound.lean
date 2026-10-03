import InfiniteZero.WavefunctionL2Bridge
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Pointwise compact-support bounds in the actual L² space

A uniform bound on a wavefunction supported in a fixed planar ball gives
an explicit bound on its mass and on the norm of any represented L² vector.
The general estimate first retains the real measure of an arbitrary finite
measurable support set. No differential or spectral hypothesis is used.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero

/-- A bounded L² wavefunction supported in a finite measurable set has mass
at most the measure of that set times the squared pointwise bound. -/
theorem mass_le_measure_mul_bound_sq {F : Wavefunction} {s : Set Plane} {B : ℝ}
    (hF : MemLp F 2 volume) (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤)
    (hsupport : Function.support F ⊆ s) (hB : 0 ≤ B)
    (hbound : ∀ x, ‖F x‖ ≤ B) :
    mass F ≤ volume.real s * B ^ 2 := by
  have hzero (x : Plane) (hx : x ∉ s) : ‖F x‖ ^ 2 = 0 := by
    have hFx : F x = 0 := by
      by_contra hn
      exact hx (hsupport hn)
    simp [hFx]
  calc
    mass F = ∫ x in s, ‖F x‖ ^ 2 :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ ≤ ∫ _x in s, B ^ 2 :=
      setIntegral_mono_on hF.norm.integrable_sq.integrableOn
        (integrableOn_const hfinite) hs
        (fun x _ => (sq_le_sq₀ (norm_nonneg _) hB).mpr (hbound x))
    _ = volume.real s * B ^ 2 := by rw [setIntegral_const, smul_eq_mul]

/-- The exact area of a planar closed ball converts the support estimate to
an explicit mass bound. The radius may be zero. -/
theorem mass_le_pi_mul_radius_sq_mul_bound_sq {F : Wavefunction} {R B : ℝ}
    (hF : MemLp F 2 volume) (hR : 0 ≤ R)
    (hsupport : Function.support F ⊆ Metric.closedBall (0 : Plane) R)
    (hB : 0 ≤ B) (hbound : ∀ x, ‖F x‖ ≤ B) :
    mass F ≤ Real.pi * R ^ 2 * B ^ 2 := by
  have hvol : volume.real (Metric.closedBall (0 : Plane) R) = Real.pi * R ^ 2 := by
    simp [Measure.real, EuclideanSpace.volume_closedBall_fin_two, hR,
      Real.pi_pos.le, mul_comm]
  simpa only [hvol] using mass_le_measure_mul_bound_sq hF measurableSet_closedBall
    (isCompact_closedBall (0 : Plane) R).measure_lt_top.ne hsupport hB hbound

/-- A pointwise bound on a compactly supported representative bounds the
norm of the genuine Hilbert-space vector, independently of its representative. -/
theorem Represents.norm_le_sqrt_pi_mul_radius_mul_bound
    {u : L2Space} {F : Wavefunction} {R B : ℝ} (hu : Represents u F)
    (hR : 0 ≤ R) (hsupport : Function.support F ⊆ Metric.closedBall (0 : Plane) R)
    (hB : 0 ≤ B) (hbound : ∀ x, ‖F x‖ ≤ B) :
    ‖u‖ ≤ Real.sqrt Real.pi * R * B := by
  have hmass := mass_le_pi_mul_radius_sq_mul_bound_sq hu.memLp hR hsupport hB hbound
  rw [← hu.norm_sq_eq_mass] at hmass
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ Real.sqrt Real.pi * R * B)).mp
  simpa only [mul_pow, Real.sq_sqrt Real.pi_pos.le] using hmass

/-- Open-ball support is enough for the same explicit estimate. -/
theorem Represents.norm_le_sqrt_pi_mul_radius_mul_bound_of_support_ball
    {u : L2Space} {F : Wavefunction} {R B : ℝ} (hu : Represents u F)
    (hR : 0 ≤ R) (hsupport : Function.support F ⊆ Metric.ball (0 : Plane) R)
    (hB : 0 ≤ B) (hbound : ∀ x, ‖F x‖ ≤ B) :
    ‖u‖ ≤ Real.sqrt Real.pi * R * B :=
  hu.norm_le_sqrt_pi_mul_radius_mul_bound hR
    (hsupport.trans Metric.ball_subset_closedBall) hB hbound

/-- Continuity and support in a closed ball already imply L² membership. -/
theorem memLp_of_continuous_support_subset_closedBall {F : Wavefunction} {R : ℝ}
    (hF : Continuous F)
    (hsupport : Function.support F ⊆ Metric.closedBall (0 : Plane) R) :
    MemLp F 2 volume := by
  apply hF.memLp_of_hasCompactSupport
  exact (isCompact_closedBall (0 : Plane) R).of_isClosed_subset isClosed_closure
    (closure_minimal hsupport Metric.isClosed_closedBall)

/-- The mass estimate for continuous compact sources needs no supplied
integrability hypothesis. -/
theorem mass_le_pi_mul_radius_sq_mul_bound_sq_of_continuous
    {F : Wavefunction} {R B : ℝ} (hF : Continuous F) (hR : 0 ≤ R)
    (hsupport : Function.support F ⊆ Metric.closedBall (0 : Plane) R)
    (hB : 0 ≤ B) (hbound : ∀ x, ‖F x‖ ≤ B) :
    mass F ≤ Real.pi * R ^ 2 * B ^ 2 :=
  mass_le_pi_mul_radius_sq_mul_bound_sq
    (memLp_of_continuous_support_subset_closedBall hF hsupport) hR hsupport hB hbound

end InfiniteZero
