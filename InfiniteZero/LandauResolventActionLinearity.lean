import InfiniteZero.LandauHeatSpacetime

/-!
# Linearity of the integral resolvent on test sources

Spatial row integrability and boundedness of test sources justify
subtracting their integrals. A squared `L²` estimate on single sources
therefore gives the difference estimate used in the closed-graph extension.
-/

noncomputable section
open MeasureTheory Set

namespace InfiniteZero

/-- A bounded continuous source can be integrated against every row of
the standard Landau resolvent kernel. -/
theorem integrable_freeLandauKernel_mul_bounded {B ρ : ℝ}
    (hB : 0 < B) (hρ : 0 < ρ) (x : Plane) {f : Wavefunction}
    (hf : Continuous f) {M : ℝ} (hM : ∀ y, ‖f y‖ ≤ M) :
    Integrable (fun y => freeLandauKernel B 1 ρ x y * f y) := by
  have hK := integrable_freeLandauKernel_standard hB hρ x
  apply (hK.norm.mul_const M).mono'
    (hK.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun y => by
    change ‖freeLandauKernel B 1 ρ x y * f y‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hM y) (norm_nonneg _)

/-- The resolvent action on a test source is an absolutely convergent
spatial integral at every observation point. -/
theorem integrable_freeLandauKernel_mul_test {B ρ : ℝ}
    (hB : 0 < B) (hρ : 0 < ρ) (x : Plane) {f : Wavefunction}
    (hf : IsTestFunction f) :
    Integrable (fun y => freeLandauKernel B 1 ρ x y * f y) := by
  obtain ⟨M, hM⟩ := hf.2.exists_bound_of_continuous hf.1.continuous
  exact integrable_freeLandauKernel_mul_bounded hB hρ x hf.1.continuous hM

/-- Subtraction of compact smooth sources commutes with the resolvent action. -/
theorem standardLandauResolventAction_sub {B ρ : ℝ}
    (hB : 0 < B) (hρ : 0 < ρ) {f g : Wavefunction}
    (hf : IsTestFunction f) (hg : IsTestFunction g) :
    standardLandauResolventAction B ρ (f - g) =
      standardLandauResolventAction B ρ f - standardLandauResolventAction B ρ g := by
  funext x
  simp only [standardLandauResolventAction, Pi.sub_apply, mul_sub]
  exact integral_sub (integrable_freeLandauKernel_mul_test hB hρ x hf)
    (integrable_freeLandauKernel_mul_test hB hρ x hg)

/-- A single-source squared mass bound also controls differences of test
sources, as required to pass to the closure of the operator graph. -/
theorem standardLandauResolventAction_mass_sub_le {B ρ C : ℝ}
    (hB : 0 < B) (hρ : 0 < ρ)
    (hbound : ∀ f : Wavefunction, IsTestFunction f →
      mass (standardLandauResolventAction B ρ f) ≤ C * mass f)
    {f g : Wavefunction} (hf : IsTestFunction f) (hg : IsTestFunction g) :
    mass (standardLandauResolventAction B ρ f - standardLandauResolventAction B ρ g) ≤
      C * mass (f - g) := by
  rw [← standardLandauResolventAction_sub hB hρ hf hg]
  exact hbound (f - g) ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

end InfiniteZero
