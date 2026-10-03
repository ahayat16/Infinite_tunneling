import InfiniteZero.ComplexCuspGeometry
import InfiniteZero.ComplexLandauHolomorphic

/-!
# The three actual Landau kernels in complex cusp coordinates

The bilinear radius maps the geometric branch domain into the proved domain
of the proper-time kernel. Their compositions and product are jointly
holomorphic in the two normal variables. The common bidisc is fixed by the
geometry, independently of the positive kernel parameters.
-/

noncomputable section
open Set Metric

namespace InfiniteZero.Geometry

@[simp] theorem complexRadius_sq (z : ComplexPoint) :
    complexRadius z ^ 2 = complexSqNorm z := by
  simp [complexRadius, Complex.sqrt]

theorem complexRadius_mem_complexLandauRadiusDomain {z : ComplexPoint}
    (hz : 0 < (complexSqNorm z).re) : complexRadius z ∈ complexLandauRadiusDomain := by
  simpa only [complexLandauRadiusDomain, mem_setOf_eq, complexRadius_sq] using hz

def complexCuspPlusKernel (b h E R s : ℝ) (q : ComplexPoint) : ℂ :=
  complexLandauKernel b h E (complexRadius (complexCuspPlus R s q.1))

def complexCuspMinusKernel (b h E R r : ℝ) (q : ComplexPoint) : ℂ :=
  complexLandauKernel b h E (complexRadius (complexCuspMinus R r q.2))

def complexCuspBridgeKernel (b h E R L s r : ℝ) (q : ComplexPoint) : ℂ :=
  complexLandauKernel b h E (complexRadius
    (complexBridge L (complexCuspPlus R s q.1) (complexCuspMinus R r q.2)))

def complexCuspKernelProduct (b h Eplus Eminus Ebridge R L s r : ℝ)
    (q : ComplexPoint) : ℂ :=
  complexCuspPlusKernel b h Eplus R s q * complexCuspMinusKernel b h Eminus R r q *
    complexCuspBridgeKernel b h Ebridge R L s r q

theorem analyticOnNhd_complexCuspPlusKernel {b h E : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (R L s r : ℝ) :
    AnalyticOnNhd ℂ (complexCuspPlusKernel b h E R s) (complexCuspRadiusDomain R L s r) := by
  apply (analyticOnNhd_complexLandauKernel hb hh hE).comp
    (analyticOnNhd_complexCusp_radii R L s r).1
  intro q hq
  exact complexRadius_mem_complexLandauRadiusDomain hq.1

theorem analyticOnNhd_complexCuspMinusKernel {b h E : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (R L s r : ℝ) :
    AnalyticOnNhd ℂ (complexCuspMinusKernel b h E R r) (complexCuspRadiusDomain R L s r) := by
  apply (analyticOnNhd_complexLandauKernel hb hh hE).comp
    (analyticOnNhd_complexCusp_radii R L s r).2.1
  intro q hq
  exact complexRadius_mem_complexLandauRadiusDomain hq.2.1

theorem analyticOnNhd_complexCuspBridgeKernel {b h E : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hE : 0 < E) (R L s r : ℝ) :
    AnalyticOnNhd ℂ (complexCuspBridgeKernel b h E R L s r) (complexCuspRadiusDomain R L s r) := by
  apply (analyticOnNhd_complexLandauKernel hb hh hE).comp
    (analyticOnNhd_complexCusp_radii R L s r).2.2
  intro q hq
  exact complexRadius_mem_complexLandauRadiusDomain hq.2.2

/-- Three genuine proper-time kernels, allowing independent positive energies. -/
theorem analyticOnNhd_complexCuspKernels {b h Eplus Eminus Ebridge : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hplus : 0 < Eplus) (hminus : 0 < Eminus)
    (hbridge : 0 < Ebridge) (R L s r : ℝ) :
    AnalyticOnNhd ℂ (complexCuspPlusKernel b h Eplus R s) (complexCuspRadiusDomain R L s r) ∧
    AnalyticOnNhd ℂ (complexCuspMinusKernel b h Eminus R r) (complexCuspRadiusDomain R L s r) ∧
    AnalyticOnNhd ℂ (complexCuspBridgeKernel b h Ebridge R L s r) (complexCuspRadiusDomain R L s r) :=
  ⟨analyticOnNhd_complexCuspPlusKernel hb hh hplus R L s r,
    analyticOnNhd_complexCuspMinusKernel hb hh hminus R L s r,
    analyticOnNhd_complexCuspBridgeKernel hb hh hbridge R L s r⟩

theorem analyticOnNhd_complexCuspKernelProduct {b h Eplus Eminus Ebridge : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hplus : 0 < Eplus) (hminus : 0 < Eminus)
    (hbridge : 0 < Ebridge) (R L s r : ℝ) :
    AnalyticOnNhd ℂ (complexCuspKernelProduct b h Eplus Eminus Ebridge R L s r)
      (complexCuspRadiusDomain R L s r) := by
  obtain ⟨hp, hm, hbri⟩ := analyticOnNhd_complexCuspKernels hb hh hplus hminus hbridge R L s r
  exact (hp.mul hm).mul hbri

/-- One geometric bidisc works simultaneously for all positive magnetic,
semiclassical and real energy parameters. No atomic amplitudes occur here. -/
theorem exists_uniform_complexCuspKernel_bidisc {R L : ℝ}
    (hR : 0 < R) (hL : R < 2 * L) (s₀ : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ (s r : ℝ), |s| ≤ s₀ → |r| ≤ s₀ →
      (ball (0 : ℂ) η ×ˢ ball (0 : ℂ) η) ⊆ complexCuspRadiusDomain R L s r ∧
      ∀ (b h Eplus Eminus Ebridge : ℝ), 0 < b → 0 < h →
        0 < Eplus → 0 < Eminus → 0 < Ebridge →
        AnalyticOnNhd ℂ (complexCuspPlusKernel b h Eplus R s)
          (ball (0 : ℂ) η ×ˢ ball (0 : ℂ) η) ∧
        AnalyticOnNhd ℂ (complexCuspMinusKernel b h Eminus R r)
          (ball (0 : ℂ) η ×ˢ ball (0 : ℂ) η) ∧
        AnalyticOnNhd ℂ (complexCuspBridgeKernel b h Ebridge R L s r)
          (ball (0 : ℂ) η ×ˢ ball (0 : ℂ) η) ∧
        AnalyticOnNhd ℂ (complexCuspKernelProduct b h Eplus Eminus Ebridge R L s r)
          (ball (0 : ℂ) η ×ˢ ball (0 : ℂ) η) := by
  obtain ⟨η, hη, hdomain⟩ := exists_uniform_complexCusp_bidisc hR hL s₀
  refine ⟨η, hη, fun s r hs hr => ?_⟩
  have hsub : (ball (0 : ℂ) η ×ˢ ball (0 : ℂ) η) ⊆ complexCuspRadiusDomain R L s r := by
    intro q hq
    exact hdomain s r hs hr q.1 q.2
      (by simpa only [mem_ball, dist_zero_right] using hq.1)
      (by simpa only [mem_ball, dist_zero_right] using hq.2)
  refine ⟨hsub, fun b h Eplus Eminus Ebridge hb hh hp hm hbr => ?_⟩
  obtain ⟨hap, ham, hab⟩ := analyticOnNhd_complexCuspKernels hb hh hp hm hbr R L s r
  exact ⟨hap.mono hsub, ham.mono hsub, hab.mono hsub,
    (analyticOnNhd_complexCuspKernelProduct hb hh hp hm hbr R L s r).mono hsub⟩

end InfiniteZero.Geometry
