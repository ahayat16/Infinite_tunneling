import InfiniteZero.InactiveKernelBounds
import InfiniteZero.SourcePhaseInvariance

/-!
# Sesquilinearity and the exact four-term source-cell decomposition

Addition under the genuine double integral is justified by absolute
integrability. For the physical component sources this follows from
continuity, compact support and the positive horizontal bridge separation.
-/

noncomputable section
open MeasureTheory Set

namespace InfiniteZero

theorem channelIntegrand_add_left (K : Plane → Plane → ℂ) (F₁ F₂ G : Wavefunction) :
    channelIntegrand K (F₁ + F₂) G =
      channelIntegrand K F₁ G + channelIntegrand K F₂ G := by
  funext q
  simp only [channelIntegrand, Pi.add_apply, star_add, add_mul]

theorem channelIntegrand_add_right (K : Plane → Plane → ℂ) (F G₁ G₂ : Wavefunction) :
    channelIntegrand K F (G₁ + G₂) =
      channelIntegrand K F G₁ + channelIntegrand K F G₂ := by
  funext q
  simp only [channelIntegrand, Pi.add_apply, mul_add]

theorem sourcePairing_add_left (h : ℝ) (K : Plane → Plane → ℂ)
    (F₁ F₂ G : Wavefunction)
    (h₁ : Integrable (channelIntegrand K F₁ G) (volume.prod volume))
    (h₂ : Integrable (channelIntegrand K F₂ G) (volume.prod volume)) :
    sourcePairing h K (F₁ + F₂) G =
      sourcePairing h K F₁ G + sourcePairing h K F₂ G := by
  simp only [sourcePairing, channelIntegrand_add_left, Pi.add_apply,
    integral_add h₁ h₂, mul_add]

theorem sourcePairing_add_right (h : ℝ) (K : Plane → Plane → ℂ)
    (F G₁ G₂ : Wavefunction)
    (h₁ : Integrable (channelIntegrand K F G₁) (volume.prod volume))
    (h₂ : Integrable (channelIntegrand K F G₂) (volume.prod volume)) :
    sourcePairing h K F (G₁ + G₂) =
      sourcePairing h K F G₁ + sourcePairing h K F G₂ := by
  simp only [sourcePairing, channelIntegrand_add_right, Pi.add_apply,
    integral_add h₁ h₂, mul_add]

/-- The source pairing is conjugate-linear in the first source. -/
theorem sourcePairing_smul_left (h : ℝ) (K : Plane → Plane → ℂ)
    (z : ℂ) (F G : Wavefunction) :
    sourcePairing h K (z • F) G = star z * sourcePairing h K F G := by
  have he : channelIntegrand K (z • F) G =
      fun q => star z * channelIntegrand K F G q := by
    funext q
    simp only [channelIntegrand, Pi.smul_apply, smul_eq_mul, star_mul']
    ring
  simp only [sourcePairing, he, integral_const_mul]
  ring

/-- The source pairing is linear in the second source. -/
theorem sourcePairing_smul_right (h : ℝ) (K : Plane → Plane → ℂ)
    (z : ℂ) (F G : Wavefunction) :
    sourcePairing h K F (z • G) = z * sourcePairing h K F G := by
  have he : channelIntegrand K F (z • G) =
      fun q => z * channelIntegrand K F G q := by
    funext q
    simp only [channelIntegrand, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [sourcePairing, he, integral_const_mul]
  ring

theorem sourcePairing_add_add (h : ℝ) (K : Plane → Plane → ℂ)
    (F₁ F₂ G₁ G₂ : Wavefunction)
    (h₁₁ : Integrable (channelIntegrand K F₁ G₁) (volume.prod volume))
    (h₁₂ : Integrable (channelIntegrand K F₁ G₂) (volume.prod volume))
    (h₂₁ : Integrable (channelIntegrand K F₂ G₁) (volume.prod volume))
    (h₂₂ : Integrable (channelIntegrand K F₂ G₂) (volume.prod volume)) :
    sourcePairing h K (F₁ + F₂) (G₁ + G₂) =
      sourcePairing h K F₁ G₁ + sourcePairing h K F₁ G₂ +
        sourcePairing h K F₂ G₁ + sourcePairing h K F₂ G₂ := by
  have h₁ : Integrable (channelIntegrand K F₁ (G₁ + G₂)) (volume.prod volume) := by
    rw [channelIntegrand_add_right]
    exact h₁₁.add h₁₂
  have h₂ : Integrable (channelIntegrand K F₂ (G₁ + G₂)) (volume.prod volume) := by
    rw [channelIntegrand_add_right]
    exact h₂₁.add h₂₂
  rw [sourcePairing_add_left h K F₁ F₂ (G₁ + G₂) h₁ h₂,
    sourcePairing_add_right h K F₁ G₁ G₂ h₁₁ h₁₂,
    sourcePairing_add_right h K F₂ G₁ G₂ h₂₁ h₂₂]
  exact (add_assoc _ _ _).symm

theorem componentSource_add (p : CuspParameters) (h : ℝ)
    (u η : Wavefunction) (i : Fin 3) :
    componentSource p h (u + η) i = componentSource p h u i + componentSource p h η i :=
  atomicSource_add h (componentPotential p i) u η

/-- Mixed component sources are absolutely integrable in the true double
integral; the two wavefunctions need only be continuous. -/
theorem channelIntegrand_componentSource_integrable
    {p : CuspParameters} (hp : p.BasicConditions) {L h E : ℝ}
    (hL : p.R < 2 * L) (hh : 0 < h) (hE : 0 < E)
    {u η : Wavefunction} (hu : Continuous u) (hη : Continuous η) (i j : Fin 3) :
    Integrable (channelIntegrand (sourceKernel p.b L h E)
      (componentSource p h u i) (componentSource p h η j)) (volume.prod volume) := by
  have hsep : 0 < 2 * L - p.R := sub_pos.mpr hL
  apply channelIntegrand_integrable_of_bound
    (C := 1 / (Real.pi * E * (2 * L - p.R) ^ 2)) (by positivity)
    (componentSource_integrable hp h hu i) (componentSource_integrable hp h hη j)
    (measurable_sourceKernel p.b L h E)
  intro z hz w hw
  have hi : componentPotential p i z ≠ 0 := by
    intro hzero
    apply hz
    simp [componentSource, atomicSource, hzero]
  have hj : componentPotential p j w ≠ 0 := by
    intro hzero
    apply hw
    simp [componentSource, atomicSource, hzero]
  have hr : 2 * L - p.R ≤ ‖z + w - 2 • displacement L‖ := by
    have h₁ := componentPotential_support_horizontal hp i hi
    have h₂ := componentPotential_support_horizontal hp j hj
    linarith [bridge_distance_ge_horizontal z w L]
  have hrpos := hsep.trans_le hr
  rw [norm_sourceKernel hp.b_pos hh hE L z w hrpos]
  apply (landauKernel_le hp.b_pos hh hE hrpos).trans
  gcongr

/-- Exact incoming/incoming, incoming/response, response/incoming and
response/response decomposition, valid for every ordered pair of components. -/
theorem sourceCell_add_eq_four_pairings
    {p : CuspParameters} (hp : p.BasicConditions) {L h E : ℝ}
    (hL : p.R < 2 * L) (hh : 0 < h) (hE : 0 < E)
    {u η : Wavefunction} (hu : Continuous u) (hη : Continuous η) (i j : Fin 3) :
    sourceCell p L h E (u + η) i j =
      sourcePairing h (sourceKernel p.b L h E) (componentSource p h u i)
        (componentSource p h u j) +
      sourcePairing h (sourceKernel p.b L h E) (componentSource p h u i)
        (componentSource p h η j) +
      sourcePairing h (sourceKernel p.b L h E) (componentSource p h η i)
        (componentSource p h u j) +
      sourcePairing h (sourceKernel p.b L h E) (componentSource p h η i)
        (componentSource p h η j) := by
  simp only [sourceCell, componentSource_add]
  exact sourcePairing_add_add h _ _ _ _ _
    (channelIntegrand_componentSource_integrable hp hL hh hE hu hu i j)
    (channelIntegrand_componentSource_integrable hp hL hh hE hu hη i j)
    (channelIntegrand_componentSource_integrable hp hL hh hE hη hu i j)
    (channelIntegrand_componentSource_integrable hp hL hh hE hη hη i j)

/-- The same identity with an arbitrary complex coefficient factored out.
The left mixed term carries its conjugate, while the right one carries it. -/
theorem sourceCell_smul_add_eq_four_pairings
    {p : CuspParameters} (hp : p.BasicConditions) {L h E : ℝ}
    (hL : p.R < 2 * L) (hh : 0 < h) (hE : 0 < E)
    {φ η : Wavefunction} (hφ : Continuous φ) (hη : Continuous η)
    (c : ℂ) (i j : Fin 3) :
    sourceCell p L h E (c • φ + η) i j =
      (star c * c) * sourceCell p L h E φ i j +
      star c * sourcePairing h (sourceKernel p.b L h E) (componentSource p h φ i)
        (componentSource p h η j) +
      c * sourcePairing h (sourceKernel p.b L h E) (componentSource p h η i)
        (componentSource p h φ j) +
      sourceCell p L h E η i j := by
  rw [sourceCell_add_eq_four_pairings hp hL hh hE (u := c • φ) (hφ.const_smul c) hη i j]
  simp only [componentSource_smul, sourcePairing_smul_left, sourcePairing_smul_right,
    sourceCell]
  ring

end InfiniteZero
