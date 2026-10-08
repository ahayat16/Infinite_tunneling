import InfiniteZero.LandauHeatApproximation
import InfiniteZero.LandauHeatEquation
import InfiniteZero.LandauHeatDecay
import InfiniteZero.LandauHeatSpacetime
import InfiniteZero.MagneticBilinearIntegrationByParts
import InfiniteZero.TestParameterIntegral
import InfiniteZero.PositiveTimeFTC

/-!
# The resolvent identity on compactly supported smooth functions

The explicit Gaussian solves the heat equation, has the correct initial
value, and decays after multiplication by a positive Laplace weight.
Integration in time gives a left inverse on the test-function core.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace InfiniteZero

/-- Differentiation of the magnetic Gaussian applied to a test function.
The Hamiltonian is transferred to that test function by integration by parts. -/
theorem hasDerivAt_landauHeatAction {B t : ℝ} (hB : 0 < B) (ht : 0 < t)
    {φ : Wavefunction} (hφ : IsTestFunction φ) (x : Plane) :
    HasDerivAt (fun s : ℝ => landauHeatAction B s φ x)
      (-landauHeatAction B t (magneticHamiltonian B 1 0 φ) x) t := by
  have hc : ContinuousOn (fun p : ℝ × Plane =>
      -(magneticHamiltonian (-B) 1 0 (landauHeatKernel B p.1 x) p.2))
      (Ioi 0 ×ˢ univ) := by
    simpa only [prod_univ, mem_Ioi] using
      (continuousOn_magneticHamiltonian_landauHeatKernel_source hB x).neg
  have hd := hasDerivAt_integral_mul_test
    (F := fun s y => landauHeatKernel B s x y)
    (F' := fun s y => -(magneticHamiltonian (-B) 1 0 (landauHeatKernel B s x) y))
    (fun s _ => continuous_landauHeatKernel_right B s x) hc
    (fun s hs y => hasDerivAt_landauHeatKernel hB hs x y) hφ ht
  convert hd using 1
  simp only [landauHeatAction, neg_mul, integral_neg]
  congr 1
  exact integral_mul_magneticHamiltonian_eq B 1 (show Continuous (0 : Potential) from continuous_const)
    (contDiff_landauHeatKernel_source B t x) hφ

/-- Compact continuous sources justify exchanging the time and source
integrals in the explicit resolvent formula. -/
theorem standardLandauResolventAction_eq_heatLaplace {B ρ : ℝ}
    (hB : 0 < B) (hρ : 0 < ρ) {f : Wavefunction}
    (hf : Continuous f) (hfc : HasCompactSupport f) (x : Plane) :
    standardLandauResolventAction B ρ f x =
      ∫ t in Ioi (0 : ℝ), (Real.exp (-ρ * t) : ℂ) * landauHeatAction B t f x := by
  obtain ⟨M, hM⟩ := hfc.exists_bound_of_continuous hf
  have hi := integrable_heatLaplace_source_timeSpace hB hρ x hf hM
  unfold standardLandauResolventAction landauHeatAction
  simp_rw [freeLandauKernel_eq_heatLaplace, ← integral_mul_const, ← integral_const_mul]
  have hs := integral_integral_swap
    (f := fun t y => (Real.exp (-ρ * t) : ℂ) * landauHeatKernel B t x y * f y) hi
  simpa only [mul_assoc] using hs.symm

/-- The Laplace-weighted heat action of a compact continuous source is
integrable on the positive time half-line. -/
theorem integrableOn_landauHeatAction_laplace {B ρ : ℝ}
    (hB : 0 < B) (hρ : 0 < ρ) {f : Wavefunction}
    (hf : Continuous f) (hfc : HasCompactSupport f) (x : Plane) :
    IntegrableOn (fun t : ℝ => (Real.exp (-ρ * t) : ℂ) * landauHeatAction B t f x)
      (Ioi 0) := by
  obtain ⟨M, hM⟩ := hfc.exists_bound_of_continuous hf
  have hi := (integrable_heatLaplace_source_timeSpace hB hρ x hf hM).integral_prod_left
  simpa only [landauHeatAction, mul_assoc, integral_const_mul] using hi

/-- Applying the heat kernel to a shifted Hamiltonian test source commutes
with the scalar shift. -/
theorem landauHeatAction_shifted_test (B ρ t : ℝ) {φ : Wavefunction}
    (hφ : IsTestFunction φ) (x : Plane) :
    landauHeatAction B t
      (fun y => magneticHamiltonian B 1 0 φ y + (ρ : ℂ) * φ y) x =
      landauHeatAction B t (magneticHamiltonian B 1 0 φ) x +
        (ρ : ℂ) * landauHeatAction B t φ x := by
  have hK := continuous_landauHeatKernel_right B t x
  have hi : Integrable (fun y => landauHeatKernel B t x y * magneticHamiltonian B 1 0 φ y) :=
    (hK.mul (hφ.continuous_magneticHamiltonian B 1 continuous_const)).integrable_of_hasCompactSupport
      ((hφ.hasCompactSupport_magneticHamiltonian B 1 0).mul_left)
  have hj : Integrable (fun y => landauHeatKernel B t x y * ((ρ : ℂ) * φ y)) :=
    (hK.mul (continuous_const.mul hφ.1.continuous)).integrable_of_hasCompactSupport
      ((hφ.2.mul_left).mul_left)
  unfold landauHeatAction
  simp_rw [mul_add]
  rw [integral_add hi hj]
  congr 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  ring

/-- Time derivative after inserting the positive resolvent weight. -/
theorem hasDerivAt_landauHeatAction_laplace {B ρ t : ℝ} (hB : 0 < B) (ht : 0 < t)
    {φ : Wavefunction} (hφ : IsTestFunction φ) (x : Plane) :
    HasDerivAt (fun s : ℝ => (Real.exp (-ρ * s) : ℂ) * landauHeatAction B s φ x)
      (-((Real.exp (-ρ * t) : ℂ) * landauHeatAction B t
        (fun y => magneticHamiltonian B 1 0 φ y + (ρ : ℂ) * φ y) x)) t := by
  have he := (((hasDerivAt_id t).const_mul (-ρ)).exp).ofReal_comp
  have hd := he.mul (hasDerivAt_landauHeatAction hB ht hφ x)
  convert hd using 1
  rw [landauHeatAction_shifted_test B ρ t hφ x]
  simp only [id_eq, mul_one, Complex.ofReal_mul, Complex.ofReal_neg]
  ring

/-- The weighted heat action has the original test function as its
right-hand initial value. -/
theorem landauHeatAction_weighted_tendsto_zero {B ρ : ℝ}
    (hB : 0 < B) {φ : Wavefunction} (hφ : IsTestFunction φ) (x : Plane) :
    Tendsto (fun t : ℝ => (Real.exp (-ρ * t) : ℂ) * landauHeatAction B t φ x)
      (𝓝[>] (0 : ℝ)) (𝓝 (φ x)) := by
  have he : Tendsto (fun t : ℝ => (Real.exp (-ρ * t) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
    have hc : Continuous (fun t : ℝ => (Real.exp (-ρ * t) : ℂ)) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  simpa only [one_mul] using he.mul (landauHeatAction_tendsto_zero hB hφ x)

/-- The explicit standard resolvent is a pointwise left inverse of
`H_B + ρ` on its compactly supported smooth core. -/
theorem standardLandauResolventAction_shifted_test {B ρ : ℝ}
    (hB : 0 < B) (hρ : 0 < ρ) {φ : Wavefunction} (hφ : IsTestFunction φ)
    (x : Plane) :
    standardLandauResolventAction B ρ
      (fun y => magneticHamiltonian B 1 0 φ y + (ρ : ℂ) * φ y) x = φ x := by
  let f : Wavefunction := fun y => magneticHamiltonian B 1 0 φ y + (ρ : ℂ) * φ y
  have hfc : Continuous f :=
    (hφ.continuous_magneticHamiltonian B 1 continuous_const).add
      (continuous_const.mul hφ.1.continuous)
  have hfs : HasCompactSupport f :=
    (hφ.hasCompactSupport_magneticHamiltonian B 1 0).add hφ.2.mul_left
  have hi := (integrableOn_landauHeatAction_laplace hB hρ hfc hfs x).neg
  have hftc := integral_Ioi_derivative_of_boundary_limits
    (fun t ht => hasDerivAt_landauHeatAction_laplace hB ht hφ x) hi
    (landauHeatAction_weighted_tendsto_zero hB hφ x)
    (landauHeatAction_weighted_tendsto_atTop hB hρ hφ x)
  rw [integral_neg, zero_sub, neg_inj] at hftc
  change standardLandauResolventAction B ρ f x = _
  rw [standardLandauResolventAction_eq_heatLaplace hB hρ hfc hfs x]
  exact hftc

end InfiniteZero
