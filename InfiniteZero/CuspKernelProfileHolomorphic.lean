import InfiniteZero.AtomicCuspKernelProfile

/-!
# Holomorphy of the true normalized incoming multiplier

The exact normalization rewrites the frozen profile as a constant times
an entire exponential, the three genuine kernels, and the exponential
of the polynomial magnetic phase. Only the kernel factors restrict the
domain. Their geometric bidisc is independent of h and of both positive
energies. No holomorphic continuation of the corrected atomic state is used.
-/

noncomputable section
open Set Metric

namespace InfiniteZero.CuspParameters

attribute [local fun_prop] analyticAt_fst analyticAt_snd

/-- Joint holomorphy of the normalized physical kernel product on its
actual common radius domain, with the two energies kept distinct. -/
theorem analyticOnNhd_frozenCuspKernelPhaseProfile
    {p : CuspParameters} {h Ecore Efull : ℝ}
    (hb : 0 < p.b) (hh : 0 < h) (hEc : 0 < Ecore) (hEf : 0 < Efull)
    (L s r : ℝ) :
    AnalyticOnNhd ℂ
      (fun q : Geometry.ComplexPoint =>
        p.frozenCuspKernelPhaseProfile L h Ecore Efull s r q.1 q.2)
      (Geometry.complexCuspRadiusDomain p.R L s r) := by
  intro q hq
  have hk := Geometry.analyticOnNhd_complexCuspKernelProduct
    hb hh hEc hEc hEf p.R L s r q hq
  simp_rw [frozenCuspKernelPhaseProfile_eq_normalized_product]
  apply AnalyticAt.mul
  · simp only [div_eq_mul_inv]
    fun_prop
  · apply hk.mul
    unfold Geometry.complexPhase Geometry.complexCuspPlus Geometry.complexCuspMinus
      Geometry.polynomialCuspChart
    simp only [div_eq_mul_inv]
    fun_prop

/-- One geometric bidisc works for every positive semiclassical parameter
and every pair of positive core and full energies. The radius is chosen
before the tangent parameters and before all three analytic parameters. -/
theorem exists_uniform_frozenCuspKernelPhaseProfile_bidisc
    {p : CuspParameters} (hp : p.BasicConditions) {L : ℝ} (hL : p.R < 2 * L) :
    ∃ η : ℝ, 0 < η ∧ ∀ s r : ℝ, |s| ≤ p.s₀ → |r| ≤ p.s₀ →
      ∀ h : ℝ, 0 < h → ∀ Ecore : ℝ, 0 < Ecore → ∀ Efull : ℝ, 0 < Efull →
        AnalyticOnNhd ℂ
          (fun q : Geometry.ComplexPoint =>
            p.frozenCuspKernelPhaseProfile L h Ecore Efull s r q.1 q.2)
          (ball (0 : ℂ) η ×ˢ ball (0 : ℂ) η) := by
  obtain ⟨η, hη, hdomain⟩ :=
    Geometry.exists_uniform_complexCuspKernel_bidisc hp.radius_pos hL p.s₀
  refine ⟨η, hη, ?_⟩
  intro s r hs hr h hh Ecore hEc Efull hEf
  exact (analyticOnNhd_frozenCuspKernelPhaseProfile hp.b_pos hh hEc hEf L s r).mono
    (hdomain s r hs hr).1

end InfiniteZero.CuspParameters
