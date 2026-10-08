import InfiniteZero.CuspIncomingSourceFormula
import InfiniteZero.HoppingIntegrability
import InfiniteZero.PlaneReflectionMeasure

/-!
# Exact source pairings in the two cusp charts

Fubini is applied only to the original integrable physical pairing. The
two changes of variables retain their real Jacobians, including the
reflection in the lower cusp. The incoming specialization uses the same
exterior radial coefficient in both sources, with a separate energy for
the bridge. No rearrangement of the four scalar coordinates is made here.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero.CuspParameters

/-- The reflected cusp has the same positive Jacobian as the upper chart.
This equality of Bochner integrals needs no integrability premise. -/
theorem integral_cuspMinus_smul_rectangle (p : CuspParameters) (g : Plane → ℂ) :
    (∫ x : Plane, p.cuspMinus x • g x) =
      ∫ q in p.cuspChartDomain,
        q.1 ^ 2 • (p.cuspPlus (p.cuspChart q) • g (reflection (p.cuspChart q))) := by
  calc
    _ = ∫ x : Plane, p.cuspMinus (reflection x) • g (reflection x) :=
      (integral_comp_reflection (fun x => p.cuspMinus x • g x)).symm
    _ = ∫ x : Plane, p.cuspPlus x • g (reflection x) := by
      simp only [cuspMinus_reflection]
    _ = _ := p.integral_cuspPlus_smul_rectangle (fun x => g (reflection x))

private theorem integral_integral_cuspPlus_cuspMinus_smul_rectangle
    (p : CuspParameters) (g : Plane → Plane → ℂ) :
    (∫ x : Plane, ∫ y : Plane, p.cuspPlus x • (p.cuspMinus y • g x y)) =
      ∫ q in p.cuspChartDomain, ∫ r in p.cuspChartDomain,
        q.1 ^ 2 • (r.1 ^ 2 • (p.cuspPlus (p.cuspChart q) •
          (p.cuspPlus (p.cuspChart r) • g (p.cuspChart q) (reflection (p.cuspChart r))))) := by
  calc
    _ = ∫ x : Plane, p.cuspPlus x • (∫ y : Plane, p.cuspMinus y • g x y) := by
      simp_rw [integral_smul]
    _ = ∫ q in p.cuspChartDomain,
        q.1 ^ 2 • (p.cuspPlus (p.cuspChart q) •
          (∫ y : Plane, p.cuspMinus y • g (p.cuspChart q) y)) :=
      p.integral_cuspPlus_smul_rectangle _
    _ = ∫ q in p.cuspChartDomain,
        q.1 ^ 2 • (p.cuspPlus (p.cuspChart q) •
          (∫ r in p.cuspChartDomain, r.1 ^ 2 •
            (p.cuspPlus (p.cuspChart r) •
              g (p.cuspChart q) (reflection (p.cuspChart r))))) := by
      simp_rw [integral_cuspMinus_smul_rectangle]
    _ = _ := by
      apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
      intro q _hq
      dsimp only
      rw [← integral_smul, ← integral_smul]
      apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
      intro r _hr
      dsimp only
      simp only [smul_smul]
      congr 1
      ring

/-- Exact chart formula for arbitrary upper and lower component sources.
The only analytic premise is integrability of the original physical
product integrand; the states in the two sources can be different. -/
theorem sourcePairing_components_eq_cuspCharts
    (p : CuspParameters) (h : ℝ) (K : Plane → Plane → ℂ) (u v : Wavefunction)
    (hInt : Integrable (channelIntegrand K
      (componentSource p h u 1) (componentSource p h v 2)) (volume.prod volume)) :
    sourcePairing h K (componentSource p h u 1) (componentSource p h v 2) =
      -((h ^ 2 : ℝ) : ℂ) *
        ∫ q in p.cuspChartDomain, ∫ r in p.cuspChartDomain,
          (q.1 ^ 2 * r.1 ^ 2) • channelIntegrand K
            (componentSource p h u 1) (componentSource p h v 2)
            (p.cuspChart q, reflection (p.cuspChart r)) := by
  let g : Plane → Plane → ℂ := fun x y =>
    (((h ^ 2)⁻¹ * p.ε : ℝ) : ℂ) ^ 2 * star (u x) * K x y * v y
  have he (x y : Plane) : channelIntegrand K
      (componentSource p h u 1) (componentSource p h v 2) (x, y) =
        p.cuspPlus x • (p.cuspMinus y • g x y) := by
    simp only [channelIntegrand, componentSource_plus_eq, componentSource_minus_eq,
      Complex.real_smul, Complex.star_def, map_mul, Complex.conj_ofReal, g]
    ring
  unfold sourcePairing
  congr 1
  rw [integral_prod _ hInt]
  simp_rw [he]
  rw [integral_integral_cuspPlus_cuspMinus_smul_rectangle]
  apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
  intro q _hq
  apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
  intro r _hr
  dsimp only
  rw [cuspMinus_reflection]
  simp only [smul_smul, mul_assoc]

/-- The incoming cross cell, with both exact source factors, both real
Jacobians, and the exterior factor `-h²`. The two core kernels and the
full-potential bridge kernel keep their distinct energies. -/
theorem incoming_sourceCell_eq_cuspCharts
    {p : CuspParameters} (hp : p.BasicConditions) {L h Efull : ℝ}
    (hL : p.R < 2 * L) (hh : 0 < h) (hEfull : 0 < Efull)
    (Ecore c Γ : ℝ) (φ : Wavefunction) (hφ : Continuous φ)
    (htail : ∀ x : Plane, p.r₀ < ‖x‖ →
      φ x = (Γ * landauKernel p.b h Ecore ‖x‖ : ℂ)) :
    sourceCell p L h Efull (fun x => (c : ℂ) * φ x) 1 2 =
      -((h ^ 2 : ℝ) : ℂ) *
        (((h ^ 2)⁻¹ * p.ε * p.a * c * Γ : ℝ) : ℂ) ^ 2 *
        ∫ q in p.cuspChartDomain, ∫ r in p.cuspChartDomain,
          ((q.1 ^ 2 * r.1 ^ 2 *
            (Real.exp (-p.β * Real.log (p.tStar / q.1) ^ 2) * p.χa q.1 * p.χb q.2) *
            (Real.exp (-p.β * Real.log (p.tStar / r.1) ^ 2) * p.χa r.1 * p.χb r.2) : ℝ) : ℂ) *
          (Geometry.complexCuspPlusKernel p.b h Ecore p.R q.2 ((q.1 : ℂ), (r.1 : ℂ)) *
            Geometry.complexCuspMinusKernel p.b h Ecore p.R r.2 ((q.1 : ℂ), (r.1 : ℂ)) *
            Geometry.complexCuspBridgeKernel p.b h Efull p.R L q.2 r.2
              ((q.1 : ℂ), (r.1 : ℂ)) *
            Complex.exp (Complex.I * Geometry.complexPhase p.b L
              (Geometry.complexCuspPlus p.R q.2 (q.1 : ℂ))
              (Geometry.complexCuspMinus p.R r.2 (r.1 : ℂ)) / (h : ℂ))) := by
  have hInt := (cellsIntegrable_of_continuous hp hL hh hEfull
    (φ := fun x => (c : ℂ) * φ x)
    (continuous_const.mul hφ)) 1 2
  unfold sourceCell
  rw [sourcePairing_components_eq_cuspCharts p h _ _ _ hInt, mul_assoc]
  congr 1
  rw [← integral_const_mul]
  apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
  intro q hq
  dsimp only
  rw [← integral_const_mul]
  apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
  intro r hr
  dsimp only
  rw [incoming_channelIntegrand_cuspChart_eq hp L h Ecore Efull c Γ φ htail
    hq.1.1 hr.1.1 q.2 r.2]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  ring

end InfiniteZero.CuspParameters
