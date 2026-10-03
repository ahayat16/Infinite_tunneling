import InfiniteZero.AtomicGroundEnergyBounds

/-!
# A fixed positive energy interval for the radial-core Landau kernel

Only the radial spectral data and the core realization are used. The lower
potential bound gives `Ecore ≥ -λ²` on the actual closed operator domain;
the radial energy estimate gives `Ecore ≤ -λ²+Bλ`. Consequently the positive
scaled kernel energy lies in `[1/2,1]` above one threshold fixed before `λ`.
No full-potential realization or spectral hypothesis enters these results.
-/

noncomputable section
open Set

namespace InfiniteZero

/-- The core energy lower bound uses its normalized true eigenstate and the
closed-graph lower bound; no global form integrability is assumed. -/
theorem IsAtomicGroundState.core_energy_lower {p : CuspParameters}
    {b coupling : ℝ} {φ : Wavefunction}
    (hφ : IsAtomicGroundState b p.core coupling φ) (hr : 0 < p.r₀)
    (hAcore : IsMagneticRealization b coupling p.core) :
    -coupling ^ 2 ≤ atomicGroundEnergy b p.core coupling := by
  let u : L2Space := hφ.1.2.1.toLp φ
  have hu : Represents u φ := represents_toLp hφ.1.2.1
  have huG : u ∈ operatorEigenspace (magneticOperator b coupling p.core)
      (atomicGroundEnergy b p.core coupling) :=
    (hAcore.eigenfunction_iff _ u).mpr ⟨φ, hφ.1, hu⟩
  obtain ⟨v, hv, hvA⟩ := (magneticOperator b coupling p.core).mem_graph_iff.mp
    ((mem_operatorEigenspace _ _ _).mp huG)
  have hveig : magneticOperator b coupling p.core v =
      (atomicGroundEnergy b p.core coupling : ℂ) • (v : L2Space) := by
    simpa only [hv] using hvA
  have hvnorm : ‖(v : L2Space)‖ ^ 2 = 1 := by
    rw [hv]
    exact hu.norm_sq_eq_mass.trans hφ.2
  have hbound := hAcore.lower_of_potential_ge_neg_one
    (CuspParameters.core_contDiff hr).continuous (fun x => (p.core_range x).1) v
  rw [re_inner_eq_of_operator_eigenvector _ _ _ hveig, hvnorm] at hbound
  simpa only [mul_one] using hbound

namespace CuspParameters

/-- A pointwise-in-coupling form with both sufficient threshold conditions
displayed. The energy interval is independent of the choice of ground state. -/
theorem scaledRadialCoreEnergy_bounds_of_radialData {p : CuspParameters}
    (hr : 0 < p.r₀) (hRad : RadialCoreSpectralData p.b p) {coupling : ℝ}
    (hAcore : IsMagneticRealization p.b coupling p.core)
    (hT : hRad.threshold ≤ coupling) (hB : 2 * hRad.energyBound ≤ coupling) :
    -((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling) ∈
      Icc (1 / 2 : ℝ) 1 := by
  have hc : 0 < coupling := hRad.threshold_pos.trans_le hT
  obtain ⟨φ, hφ, hupper, _⟩ := hRad.ground coupling hT
  have hquot : hRad.energyBound / coupling ≤ (1 / 2 : ℝ) :=
    (div_le_iff₀ hc).mpr (by linarith)
  have hlower := hφ.core_energy_lower hr hAcore
  have hscaled := mul_le_mul_of_nonneg_left hlower (sq_nonneg (coupling⁻¹))
  have hcancel : (coupling⁻¹) ^ 2 * coupling ^ 2 = 1 := by field_simp
  simp only [mul_neg, hcancel] at hscaled
  exact ⟨by linarith, by linarith⟩

/-- One positive threshold fixes the compact energy interval needed for
uniform estimates of the true radial-core exterior Landau kernel. -/
theorem exists_scaledRadialCoreEnergy_bounds_of_radialData {p : CuspParameters}
    (hr : 0 < p.r₀) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      -((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling) ∈
        Icc (1 / 2 : ℝ) 1 := by
  refine ⟨max hRad.threshold (2 * hRad.energyBound),
    hRad.threshold_pos.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc
  exact scaledRadialCoreEnergy_bounds_of_radialData hr hRad (hAcore coupling)
    ((le_max_left _ _).trans hc) ((le_max_right _ _).trans hc)

end CuspParameters
end InfiniteZero
