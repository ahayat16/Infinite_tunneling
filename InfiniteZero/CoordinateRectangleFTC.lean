import InfiniteZero.CuspChartJacobian
import InfiniteZero.LocalPoissonH2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Point evaluation by two applications of the fundamental theorem

For a smooth function supported strictly inside the unit ball, its value
at the origin is the integral of one mixed derivative over the negative
unit square. The boundary terms vanish by the support condition.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology
namespace InfiniteZero

/-- Ordinary Cartesian coordinates on the Euclidean plane. -/
def cartesianPoint (s t : ℝ) : Plane := CuspParameters.planeCartesianEquiv.symm (s, t)

@[simp] theorem cartesianPoint_apply_zero (s t : ℝ) : cartesianPoint s t 0 = s := rfl
@[simp] theorem cartesianPoint_apply_one (s t : ℝ) : cartesianPoint s t 1 = t := rfl
@[simp] theorem cartesianPoint_zero : cartesianPoint 0 0 = 0 := by ext i; fin_cases i <;> rfl

theorem cartesianPoint_eq (s t : ℝ) :
    cartesianPoint s t = s • coordinateVector 0 + t • coordinateVector 1 := by
  ext i
  fin_cases i <;> simp [cartesianPoint, CuspParameters.planeCartesianEquiv_symm_apply,
    coordinateVector]

theorem hasDerivAt_cartesianPoint_left (s t : ℝ) :
    HasDerivAt (fun z => cartesianPoint z t) (coordinateVector 0) s := by
  simpa only [cartesianPoint_eq, one_smul, add_zero] using
    ((hasDerivAt_id s).smul_const (coordinateVector 0)).add_const (t • coordinateVector 1)

theorem hasDerivAt_cartesianPoint_right (s t : ℝ) :
    HasDerivAt (fun z => cartesianPoint s z) (coordinateVector 1) t := by
  simpa only [cartesianPoint_eq, one_smul, zero_add] using
    ((hasDerivAt_id t).smul_const (coordinateVector 1)).const_add (s • coordinateVector 0)

theorem hasDerivAt_cartesian_slice_left {u : Wavefunction} (hu : Differentiable ℝ u)
    (s t : ℝ) : HasDerivAt (fun z => u (cartesianPoint z t))
      (partialDerivative 0 u (cartesianPoint s t)) s :=
  (hu (cartesianPoint s t)).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_cartesianPoint_left s t)

theorem hasDerivAt_cartesian_slice_right {u : Wavefunction} (hu : Differentiable ℝ u)
    (s t : ℝ) : HasDerivAt (fun z => u (cartesianPoint s z))
      (partialDerivative 1 u (cartesianPoint s t)) t :=
  (hu (cartesianPoint s t)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_cartesianPoint_right s t)

private theorem not_mem_ball_cartesian_left (t : ℝ) :
    cartesianPoint (-1) t ∉ Metric.ball (0 : Plane) 1 := by
  intro h
  have hnorm := PiLp.norm_apply_le (cartesianPoint (-1) t) (0 : Fin 2)
  simp only [cartesianPoint_apply_zero, norm_neg, norm_one] at hnorm
  have hlt := Metric.mem_ball.mp h
  rw [dist_zero_right] at hlt
  linarith

private theorem not_mem_ball_cartesian_right (s : ℝ) :
    cartesianPoint s (-1) ∉ Metric.ball (0 : Plane) 1 := by
  intro h
  have hnorm := PiLp.norm_apply_le (cartesianPoint s (-1)) (1 : Fin 2)
  simp only [cartesianPoint_apply_one, norm_neg, norm_one] at hnorm
  have hlt := Metric.mem_ball.mp h
  rw [dist_zero_right] at hlt
  linarith

/-- The mixed derivative reconstructs the value at the origin; the order
of the two scalar integrations is displayed explicitly. -/
theorem value_zero_eq_iterated_integral_mixed {u : Wavefunction}
    (hu : ContDiff ℝ ∞ u) (hs : tsupport u ⊆ Metric.ball (0 : Plane) 1) :
    u 0 = ∫ s in (-1 : ℝ)..0, ∫ t in (-1 : ℝ)..0,
      partialDerivative 1 (partialDerivative 0 u) (cartesianPoint s t) := by
  have hD := contDiff_partialDerivative 0 hu
  have hDD := contDiff_partialDerivative 1 hD
  have hc (s : ℝ) : Continuous (fun t => cartesianPoint s t) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_cartesianPoint_right s t).continuousAt
  have inner (s : ℝ) : (∫ t in (-1 : ℝ)..0,
      partialDerivative 1 (partialDerivative 0 u) (cartesianPoint s t)) =
      partialDerivative 0 u (cartesianPoint s 0) := by
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_cartesian_slice_right (hD.differentiable (by simp)) s t)
      ((hDD.continuous.comp (hc s)).intervalIntegrable (-1) 0)
    have hz : partialDerivative 0 u (cartesianPoint s (-1)) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => not_mem_ball_cartesian_right s
        (hs (tsupport_partialDerivative_subset u 0 h)))
    simpa only [hz, sub_zero] using hh
  simp_rw [inner]
  have hcl : Continuous (fun s => cartesianPoint s 0) :=
    continuous_iff_continuousAt.mpr fun s => (hasDerivAt_cartesianPoint_left s 0).continuousAt
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_cartesian_slice_left (hu.differentiable (by simp)) s 0)
    ((hD.continuous.comp hcl).intervalIntegrable (-1) 0)
  have hz : u (cartesianPoint (-1) 0) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => not_mem_ball_cartesian_left 0 (hs h))
  simpa only [cartesianPoint_zero, hz, sub_zero] using hh.symm

/-- The negative unit square in Cartesian coordinates. Its area is one. -/
def negativeUnitSquare : Set (ℝ × ℝ) := Ioc (-1) 0 ×ˢ Ioc (-1) 0

theorem volume_negativeUnitSquare : volume negativeUnitSquare = 1 := by
  rw [negativeUnitSquare, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioc]
  norm_num

theorem integrableOn_negativeUnitSquare_of_continuous {F : (ℝ × ℝ) → ℂ}
    (hF : Continuous F) : IntegrableOn F negativeUnitSquare :=
  (hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- The same reconstruction as a single planar Cartesian integral. -/
theorem value_zero_eq_integral_mixed_square {u : Wavefunction}
    (hu : ContDiff ℝ ∞ u) (hs : tsupport u ⊆ Metric.ball (0 : Plane) 1) :
    u 0 = ∫ q in negativeUnitSquare,
      partialDerivative 1 (partialDerivative 0 u) (cartesianPoint q.1 q.2) := by
  have hDD := contDiff_partialDerivative 1 (contDiff_partialDerivative 0 hu)
  have hc : Continuous (fun q : ℝ × ℝ => cartesianPoint q.1 q.2) :=
    CuspParameters.planeCartesianEquiv.symm.continuous
  have hi := integrableOn_negativeUnitSquare_of_continuous (hDD.continuous.comp hc)
  rw [value_zero_eq_iterated_integral_mixed hu hs]
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 0)]
  exact (setIntegral_prod _ (by simpa only [← Measure.volume_eq_prod] using hi)).symm

end InfiniteZero
