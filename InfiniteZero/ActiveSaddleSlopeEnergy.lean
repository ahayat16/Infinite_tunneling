import InfiniteZero.ActiveSaddleEnvelope
import InfiniteZero.RadialCoreEnergyBounds

/-!
# Freezing the normal action slope at limiting energy one

The full and core energies remain distinct. Their actual spectral bounds
give an O(1/coupling) error, which is stronger than convergence and is
needed before dividing the normal phase by the semiclassical parameter.
-/

noncomputable section
open Set

namespace InfiniteZero

theorem abs_deriv_bridgeAction_sub_energy_le {b E F : ℝ} (hb : b ≠ 0)
    (hE : (1 / 2 : ℝ) ≤ E) (hF : (1 / 2 : ℝ) ≤ F) (R : ℝ) :
    |deriv (bridgeAction b E) R - deriv (bridgeAction b F) R| ≤ |E - F| := by
  have hEp : 0 < E := lt_of_lt_of_le (by norm_num) hE
  have hFp : 0 < F := lt_of_lt_of_le (by norm_num) hF
  let x := Real.sqrt (b ^ 2 * R ^ 2 + 4 * E)
  let y := Real.sqrt (b ^ 2 * R ^ 2 + 4 * F)
  have hbase : 0 ≤ b ^ 2 * R ^ 2 := mul_nonneg (sq_nonneg b) (sq_nonneg R)
  have hx : 1 ≤ x := by
    dsimp [x]
    exact (Real.one_le_sqrt).mpr (by linarith)
  have hy : 1 ≤ y := by
    dsimp [y]
    exact (Real.one_le_sqrt).mpr (by linarith)
  have hx2 : x ^ 2 = b ^ 2 * R ^ 2 + 4 * E :=
    Real.sq_sqrt (by linarith)
  have hy2 : y ^ 2 = b ^ 2 * R ^ 2 + 4 * F :=
    Real.sq_sqrt (by linarith)
  have hprod : (x - y) * (x + y) = 4 * (E - F) := by nlinarith only [hx2, hy2]
  have habs : |x - y| * (x + y) = 4 * |E - F| := by
    have h := congrArg abs hprod
    simpa only [abs_mul, abs_of_nonneg (by linarith : 0 ≤ x + y),
      abs_of_pos (by norm_num : (0 : ℝ) < 4)] using h
  have hden : 2 ≤ x + y := by linarith
  have hdiff : |x - y| ≤ 2 * |E - F| := by
    nlinarith only [habs, mul_le_mul_of_nonneg_left hden (abs_nonneg (x - y))]
  rw [deriv_bridgeAction hb hEp, deriv_bridgeAction hb hFp, ← sub_div, abs_div]
  change |x - y| / |(2 : ℝ)| ≤ |E - F|
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

namespace CuspParameters

def movingActiveSaddleSlope (p : CuspParameters) (L Ecore Efull : ℝ) : ℂ :=
  (((deriv (bridgeAction p.b Ecore) p.R +
      deriv (bridgeAction p.b Efull) (Geometry.activeDistance p.R L)) / 2 : ℝ) : ℂ) -
    Complex.I * (Geometry.phaseSlope p.b L : ℂ)

@[simp] theorem movingActiveSaddleSlope_one (p : CuspParameters) (L : ℝ) :
    p.movingActiveSaddleSlope L 1 1 = p.activeSaddleSlope L := rfl

theorem norm_movingActiveSaddleSlope_sub_le {p : CuspParameters}
    (hb : p.b ≠ 0) (L : ℝ) {Ecore Efull : ℝ}
    (hc : (1 / 2 : ℝ) ≤ Ecore) (hf : (1 / 2 : ℝ) ≤ Efull) :
    ‖p.movingActiveSaddleSlope L Ecore Efull - p.activeSaddleSlope L‖ ≤
      (|Ecore - 1| + |Efull - 1|) / 2 := by
  have hcore := abs_deriv_bridgeAction_sub_energy_le hb hc (by norm_num : (1 / 2 : ℝ) ≤ 1) p.R
  have hfull := abs_deriv_bridgeAction_sub_energy_le hb hf (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (Geometry.activeDistance p.R L)
  have heq : p.movingActiveSaddleSlope L Ecore Efull - p.activeSaddleSlope L =
      (((deriv (bridgeAction p.b Ecore) p.R - deriv (bridgeAction p.b 1) p.R +
        (deriv (bridgeAction p.b Efull) (Geometry.activeDistance p.R L) -
          deriv (bridgeAction p.b 1) (Geometry.activeDistance p.R L))) / 2 : ℝ) : ℂ) := by
    dsimp [movingActiveSaddleSlope, activeSaddleSlope, Geometry.activeActionSlope]
    push_cast
    ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_div]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact (abs_add_le _ _).trans (add_le_add hcore hfull)

/-- Both true scaled energies have the same linear error bound, with one
threshold fixed before the coupling. -/
theorem exists_scaled_atomic_core_energy_linear_bounds_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      scaledAtomicEnergy p coupling ∈ Icc (1 / 2 : ℝ) 1 ∧
      (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ∈
        Icc (1 / 2 : ℝ) 1 ∧
      |scaledAtomicEnergy p coupling - 1| ≤ hRad.energyBound / coupling ∧
      |-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling) - 1| ≤
        hRad.energyBound / coupling := by
  obtain ⟨Tf, _hTf, hfull⟩ := exists_scaledAtomicEnergy_bounds_of_radialData hp hRad hAcore hApot
  obtain ⟨Tp, _hTp, hpos⟩ := exists_scaledAtomicEnergy_pos_of_radialData hp hRad hAcore hApot
  obtain ⟨Tc, _hTc, hcore⟩ := exists_scaledRadialCoreEnergy_bounds_of_radialData
    hp.r₀_pos hRad hAcore
  let T := max hRad.threshold (max Tf (max Tp Tc))
  refine ⟨T, hRad.threshold_pos.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc
  have hs : hRad.threshold ≤ coupling ∧ Tf ≤ coupling ∧ Tp ≤ coupling ∧ Tc ≤ coupling := by
    simpa only [T, max_le_iff] using hc
  obtain ⟨hct, hcf, hcp, hcc⟩ := hs
  have hf := hfull coupling hcf
  have hp' := hpos coupling hcp
  have hc' := hcore coupling hcc
  obtain ⟨φ, _hφ, hupper, _⟩ := hRad.ground coupling hct
  refine ⟨⟨hp'.1, hp'.2.2⟩, hc', ?_, ?_⟩
  · rw [abs_of_nonpos (sub_nonpos.mpr hf.2)]
    linarith [hf.1]
  · rw [abs_of_nonpos (sub_nonpos.mpr hc'.2)]
    linarith

theorem exists_activeSaddleSlope_energy_bound_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) (L : ℝ) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      ‖p.movingActiveSaddleSlope L
          (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling))
          (scaledAtomicEnergy p coupling) - p.activeSaddleSlope L‖ ≤
        hRad.energyBound / coupling := by
  obtain ⟨T, hT, hbound⟩ :=
    exists_scaled_atomic_core_energy_linear_bounds_of_radialData hp hRad hAcore hApot
  refine ⟨T, hT, ?_⟩
  intro coupling hc
  obtain ⟨hf, hr, hfe, hre⟩ := hbound coupling hc
  have hs := norm_movingActiveSaddleSlope_sub_le hp.b_pos.ne' L hr.1 hf.1
  linarith

end CuspParameters
end InfiniteZero
