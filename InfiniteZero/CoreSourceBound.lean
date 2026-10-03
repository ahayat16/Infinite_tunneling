import InfiniteZero.HoppingIntegrability

/-!
# The polynomial `L¹` bound for the core source

This is L5.6-core-source. Cauchy--Schwarz gives the slightly sharper constant
`‖core‖₂`, without introducing an exterior normalization or a spectral estimate.
The bound holds for every normalized `L²` wavefunction.
-/

noncomputable section
open MeasureTheory

namespace InfiniteZero

theorem norm_atomicSource (h : ℝ) (v : Potential) (φ : Wavefunction) (x : Plane) :
    ‖atomicSource h v φ x‖ = (h ^ 2)⁻¹ * (|v x| * ‖φ x‖) := by
  simp only [atomicSource, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg h))]
  ring

theorem integrable_norm_atomicSource_of_memLp {v : Potential} {φ : Wavefunction}
    (hv : MemLp v 2 volume) (hφ : MemLp φ 2 volume) (h : ℝ) :
    Integrable (fun x => ‖atomicSource h v φ x‖) volume := by
  have hi := (hv.norm.integrable_mul hφ.norm).const_mul ((h ^ 2)⁻¹)
  simpa only [norm_atomicSource, Real.norm_eq_abs, Pi.mul_apply] using hi

/-- Cauchy--Schwarz for the actual source, under only `L²` membership and normalization. -/
theorem integral_norm_atomicSource_le_of_mass_one {v : Potential} {φ : Wavefunction}
    (hv : MemLp v 2 volume) (hφ : MemLp φ 2 volume) (hm : mass φ = 1) (h : ℝ) :
    (∫ x : Plane, ‖atomicSource h v φ x‖) ≤
      Real.sqrt (∫ x : Plane, v x ^ 2) * (h ^ 2)⁻¹ := by
  have hholder := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (show MemLp v (ENNReal.ofReal (2 : ℝ)) volume by simpa using hv)
    (show MemLp (fun x => ‖φ x‖) (ENNReal.ofReal (2 : ℝ)) volume by simpa using hφ.norm)
  simp only [Real.rpow_two, Real.norm_eq_abs, abs_norm, sq_abs] at hholder
  have hmass : (∫ x : Plane, ‖φ x‖ ^ 2) = 1 := hm
  rw [hmass, Real.one_rpow, mul_one, ← Real.sqrt_eq_rpow] at hholder
  simp_rw [norm_atomicSource]
  rw [integral_const_mul]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hholder (inv_nonneg.mpr (sq_nonneg h))

/-- A positive constant depending only on the fixed radial core. -/
def coreSourceConstant (p : CuspParameters) : ℝ :=
  Real.sqrt (∫ x : Plane, p.core x ^ 2) + 1

theorem coreSourceConstant_pos (p : CuspParameters) : 0 < coreSourceConstant p := by
  unfold coreSourceConstant
  positivity

theorem core_memLp_two {p : CuspParameters} (hr₀ : 0 < p.r₀) : MemLp p.core 2 volume :=
  (CuspParameters.core_contDiff hr₀).continuous.memLp_of_hasCompactSupport
    (CuspParameters.core_hasCompactSupport p)

theorem coreSource_L1_le {p : CuspParameters} (hr₀ : 0 < p.r₀)
    {φ : Wavefunction} (hφ : MemLp φ 2 volume) (hm : mass φ = 1) (h : ℝ) :
    (∫ x : Plane, ‖componentSource p h φ 0 x‖) ≤
      Real.sqrt (∫ x : Plane, p.core x ^ 2) * (h ^ 2)⁻¹ := by
  simpa only [componentSource, componentPotential, Matrix.cons_val_zero] using
    integral_norm_atomicSource_le_of_mass_one (core_memLp_two hr₀) hφ hm h

theorem coreSource_L1_le_constant {p : CuspParameters} (hr₀ : 0 < p.r₀)
    {φ : Wavefunction} (hφ : MemLp φ 2 volume) (hm : mass φ = 1) (h : ℝ) :
    (∫ x : Plane, ‖componentSource p h φ 0 x‖) ≤ coreSourceConstant p * (h ^ 2)⁻¹ := by
  apply (coreSource_L1_le hr₀ hφ hm h).trans
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (sq_nonneg h))
  unfold coreSourceConstant
  linarith

theorem coreSource_L1_le_of_atomicGroundState {p : CuspParameters} (hr₀ : 0 < p.r₀)
    {coupling : ℝ} {φ : Wavefunction} (hφ : IsAtomicGroundState p.b p.potential coupling φ)
    (h : ℝ) :
    (∫ x : Plane, ‖componentSource p h φ 0 x‖) ≤ coreSourceConstant p * (h ^ 2)⁻¹ :=
  coreSource_L1_le_constant hr₀ hφ.1.2.1 hφ.2 h

/-- The same constant works for every `h > 0` and every normalized atomic ground state. -/
theorem exists_coreSource_L1_bound {p : CuspParameters} (hr₀ : 0 < p.r₀) :
    ∃ C > 0, ∀ h > 0, ∀ coupling : ℝ, ∀ φ : Wavefunction,
      IsAtomicGroundState p.b p.potential coupling φ →
        (∫ x : Plane, ‖componentSource p h φ 0 x‖) ≤ C * (h ^ 2)⁻¹ := by
  refine ⟨coreSourceConstant p, coreSourceConstant_pos p, ?_⟩
  intro h _ coupling φ hφ
  exact coreSource_L1_le_of_atomicGroundState hr₀ hφ h

end InfiniteZero
