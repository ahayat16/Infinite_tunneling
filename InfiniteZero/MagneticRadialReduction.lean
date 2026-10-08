import InfiniteZero.MagneticIMS
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-! Pointwise radial reduction of the concrete magnetic Hamiltonian.
All differentiation is performed away from the origin. -/

noncomputable section
open Filter
open scoped Topology ContDiff
namespace InfiniteZero

private theorem hasFDerivAt_plane_norm {x : Plane} (hx : x ≠ 0) :
    HasFDerivAt (fun y : Plane => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hd := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  convert hd using 1
  · ext y
    exact (Real.sqrt_sq (norm_nonneg y)).symm
  · ext y
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, Real.sqrt_sq (norm_nonneg x)]
    field_simp
    ring

private theorem plane_inner_coordinate (x : Plane) (i : Fin 2) :
    innerSL ℝ x (coordinateVector i) = x i := by
  simp [coordinateVector, EuclideanSpace.inner_single_right]

/-- Coordinate derivative of a real radial wavefunction, without any
regularity assumption at the origin. -/
theorem partialDerivative_radial {f : ℝ → ℝ} {f' : ℝ} {x : Plane}
    (hx : x ≠ 0) (hf : HasDerivAt f f' ‖x‖) (i : Fin 2) :
    partialDerivative i (fun y => (f ‖y‖ : ℂ)) x =
      ((f' / ‖x‖ * x i : ℝ) : ℂ) := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp x
    (hf.comp_hasFDerivAt x (hasFDerivAt_plane_norm hx))
  have he := congrArg (fun L : Plane →L[ℝ] ℂ => L (coordinateVector i)) hd.fderiv
  simpa only [partialDerivative, Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply, smul_eq_mul,
    plane_inner_coordinate, div_eq_mul_inv, mul_assoc] using he

private theorem hasFDerivAt_radial_quotient {df : ℝ → ℝ} {ddf : ℝ} {x : Plane}
    (hx : x ≠ 0) (hdf : HasDerivAt df ddf ‖x‖) :
    HasFDerivAt (fun y : Plane => df ‖y‖ / ‖y‖)
      (((ddf * ‖x‖ - df ‖x‖) / ‖x‖ ^ 3) • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hn' := hasFDerivAt_plane_norm hx
  have hd := (hdf.div (hasDerivAt_id ‖x‖) hn).comp_hasFDerivAt x hn'
  convert hd using 1
  ext y
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, id_eq, mul_one]
  field_simp

/-- Both the local differentiability and the diagonal second coordinate
derivative of the radial wavefunction are explicit. -/
theorem partialDerivative_radial_second {f df : ℝ → ℝ} {ddf : ℝ} {x : Plane}
    (hf : ∀ r > 0, HasDerivAt f (df r) r) (hx : x ≠ 0)
    (hdf : HasDerivAt df ddf ‖x‖) (i : Fin 2) :
    DifferentiableAt ℝ (partialDerivative i (fun y => (f ‖y‖ : ℂ))) x ∧
      partialDerivative i (partialDerivative i (fun y => (f ‖y‖ : ℂ))) x =
        ((((ddf * ‖x‖ - df ‖x‖) / ‖x‖ ^ 3) * (x i) ^ 2 + df ‖x‖ / ‖x‖ : ℝ) : ℂ) := by
  have hq := hasFDerivAt_radial_quotient hx hdf
  have hp := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) i : Plane →L[ℝ] ℝ).hasFDerivAt (x := x)
  have hd := Complex.ofRealCLM.hasFDerivAt.comp x (hq.mul hp)
  have heq : partialDerivative i (fun y => (f ‖y‖ : ℂ)) =ᶠ[𝓝 x]
      fun y => ((df ‖y‖ / ‖y‖ * y i : ℝ) : ℂ) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact partialDerivative_radial hy (hf ‖y‖ (norm_pos_iff.mpr hy)) i
  have hd' := hd.congr_of_eventuallyEq heq
  refine ⟨hd'.differentiableAt, ?_⟩
  have he := congrArg (fun L : Plane →L[ℝ] ℂ => L (coordinateVector i)) hd'.fderiv
  rw [show partialDerivative i (partialDerivative i (fun y => (f ‖y‖ : ℂ))) x = _ from he]
  have hei : coordinateVector i i = (1 : ℝ) := by simp [coordinateVector]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    PiLp.proj_apply, plane_inner_coordinate, hei, mul_one]
  congr 1
  ring

private def magneticRadialCoordinate (b coupling : ℝ) (i : Fin 2) : Plane →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp ((b * coupling / 2) •
    (if i = 0 then -(PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1) else
      PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0))

private theorem magneticRadialCoordinate_apply (b coupling : ℝ) (i : Fin 2) (x : Plane) :
    magneticRadialCoordinate b coupling i x =
      ((b * coupling / 2 * perpCoordinate x i : ℝ) : ℂ) := by
  fin_cases i <;> simp [magneticRadialCoordinate, perpCoordinate]

private theorem magneticRadialCoordinate_coordinate (b coupling : ℝ) (i : Fin 2) :
    magneticRadialCoordinate b coupling i (coordinateVector i) = 0 := by
  fin_cases i <;> simp [magneticRadialCoordinate_apply, perpCoordinate, coordinateVector]

private theorem partialDerivative_covariantDerivative_local
    (b coupling : ℝ) (i : Fin 2) {ψ : Wavefunction} {x : Plane}
    (hψ : DifferentiableAt ℝ ψ x) (hpartial : DifferentiableAt ℝ (partialDerivative i ψ) x) :
    partialDerivative i (covariantDerivative b coupling i ψ) x =
      -Complex.I * partialDerivative i (partialDerivative i ψ) x -
        ((b * coupling / 2 * perpCoordinate x i : ℝ) : ℂ) * partialDerivative i ψ x := by
  have hd := (hpartial.hasFDerivAt.const_mul (-Complex.I)).sub
    ((magneticRadialCoordinate b coupling i).hasFDerivAt.mul hψ.hasFDerivAt)
  have hfun : (fun y => -Complex.I * partialDerivative i ψ y) -
      (magneticRadialCoordinate b coupling i : Plane → ℂ) * ψ =
        covariantDerivative b coupling i ψ := by
    ext y
    simp only [Pi.sub_apply, Pi.mul_apply, magneticRadialCoordinate_apply, covariantDerivative]
  rw [hfun] at hd
  have he := congrArg (fun L : Plane →L[ℝ] ℂ => L (coordinateVector i)) hd.fderiv
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, magneticRadialCoordinate_coordinate,
    mul_zero, add_zero] at he
  simpa only [partialDerivative, magneticRadialCoordinate_apply] using he

/-- Expansion of one squared covariant momentum at a point. The same
coordinate derivative of its linear magnetic coefficient vanishes. -/
theorem covariantDerivative_squared_local (b coupling : ℝ) (i : Fin 2)
    {ψ : Wavefunction} {x : Plane} (hψ : DifferentiableAt ℝ ψ x)
    (hpartial : DifferentiableAt ℝ (partialDerivative i ψ) x) :
    covariantDerivative b coupling i (covariantDerivative b coupling i ψ) x =
      -partialDerivative i (partialDerivative i ψ) x +
        2 * Complex.I * ((b * coupling / 2 * perpCoordinate x i : ℝ) : ℂ) *
          partialDerivative i ψ x +
        ((b * coupling / 2 * perpCoordinate x i : ℝ) : ℂ) ^ 2 * ψ x := by
  rw [covariantDerivative, partialDerivative_covariantDerivative_local b coupling i hψ hpartial]
  simp only [covariantDerivative]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Exact radial reduction of the concrete Hamiltonian. No differentiability
of the potential or smoothness of the radial wavefunction at zero is needed. -/
theorem magneticHamiltonian_radial {f df : ℝ → ℝ} {ddf : ℝ} {x : Plane}
    (hf : ∀ r > 0, HasDerivAt f (df r) r) (hx : x ≠ 0)
    (hdf : HasDerivAt df ddf ‖x‖) (b coupling : ℝ) (V : Potential) :
    magneticHamiltonian b coupling V (fun y => (f ‖y‖ : ℂ)) x =
      ((-ddf - ‖x‖⁻¹ * df ‖x‖ +
        (b ^ 2 * coupling ^ 2 / 4 * ‖x‖ ^ 2 + coupling ^ 2 * V x) * f ‖x‖ : ℝ) : ℂ) := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hfx := hf ‖x‖ (norm_pos_iff.mpr hx)
  have hψ : DifferentiableAt ℝ (fun y : Plane => (f ‖y‖ : ℂ)) x :=
    (Complex.ofRealCLM.hasFDerivAt.comp x
      (hfx.comp_hasFDerivAt x (hasFDerivAt_plane_norm hx))).differentiableAt
  have hs (i : Fin 2) := partialDerivative_radial_second hf hx hdf i
  simp only [magneticHamiltonian, Fin.sum_univ_two,
    covariantDerivative_squared_local b coupling 0 hψ (hs 0).1,
    covariantDerivative_squared_local b coupling 1 hψ (hs 1).1,
    (hs 0).2, (hs 1).2, partialDerivative_radial hx hfx]
  simp only [perpCoordinate, if_true, if_neg (by decide : (1 : Fin 2) ≠ 0)]
  have hnorm : (x 0) ^ 2 + (x 1) ^ 2 = ‖x‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hLap : ((ddf * ‖x‖ - df ‖x‖) / ‖x‖ ^ 3) * (x 0) ^ 2 + df ‖x‖ / ‖x‖ +
      (((ddf * ‖x‖ - df ‖x‖) / ‖x‖ ^ 3) * (x 1) ^ 2 + df ‖x‖ / ‖x‖) =
        ddf + df ‖x‖ / ‖x‖ := by
    calc
      _ = ((ddf * ‖x‖ - df ‖x‖) / ‖x‖ ^ 3) * ((x 0) ^ 2 + (x 1) ^ 2) +
          2 * df ‖x‖ / ‖x‖ := by ring
      _ = ((ddf * ‖x‖ - df ‖x‖) / ‖x‖ ^ 3) * ‖x‖ ^ 2 + 2 * df ‖x‖ / ‖x‖ := by
        rw [hnorm]
      _ = _ := by field_simp; ring
  simp only [← Complex.ofReal_pow]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, add_zero, zero_add,
      sub_zero]
    linear_combination (b ^ 2 * coupling ^ 2 / 4 * f ‖x‖) * hnorm - hLap
  · simp only [Complex.add_im, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, add_zero, zero_add,
      sub_zero]
    ring

end InfiniteZero
