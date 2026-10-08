import InfiniteZero.MagneticDilation
import InfiniteZero.WavefunctionL2Bridge

/-!
# Exact L² identities for magnetic dilation

The global dilation preserves square integrability, the scalar product,
and the L² norm. Its linearity and adjoint-transfer identities hold for
actual wavefunctions. No operator domain or graph is transported here.
-/

noncomputable section
open MeasureTheory
namespace InfiniteZero

theorem magneticDilation_add (coupling : ℝ) (φ ψ : Wavefunction) :
    magneticDilation coupling (φ + ψ) =
      magneticDilation coupling φ + magneticDilation coupling ψ := by
  ext x
  simp only [magneticDilation_apply, Pi.add_apply, mul_add]

theorem magneticDilation_sub (coupling : ℝ) (φ ψ : Wavefunction) :
    magneticDilation coupling (φ - ψ) =
      magneticDilation coupling φ - magneticDilation coupling ψ := by
  ext x
  simp only [magneticDilation_apply, Pi.sub_apply, mul_sub]

theorem magneticDilation_smul (coupling : ℝ) (z : ℂ) (φ : Wavefunction) :
    magneticDilation coupling (z • φ) = z • magneticDilation coupling φ := by
  ext x
  simp only [magneticDilation_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem _root_.MeasureTheory.MemLp.magneticDilation {coupling : ℝ} (hc : 0 < coupling)
    {φ : Wavefunction} (hφ : MemLp φ 2 volume) :
    MemLp (magneticDilation coupling φ) 2 volume := by
  have hr : (Real.sqrt coupling)⁻¹ ≠ 0 :=
    inv_ne_zero (Real.sqrt_pos.mpr hc).ne'
  have hm : AEStronglyMeasurable
      (fun y : Plane => φ ((Real.sqrt coupling)⁻¹ • y)) volume :=
    hφ.aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_smul volume hr)
  have hcomp : MemLp (fun y : Plane => φ ((Real.sqrt coupling)⁻¹ • y)) 2 volume :=
    (memLp_two_iff_integrable_sq_norm hm).mpr (hφ.norm.integrable_sq.comp_smul hr)
  change MemLp (fun y => ((Real.sqrt coupling : ℂ)⁻¹) *
    φ ((Real.sqrt coupling)⁻¹ • y)) 2 volume
  exact hcomp.const_mul ((Real.sqrt coupling : ℂ)⁻¹)

theorem memLp_magneticDilation_iff {coupling : ℝ} (hc : 0 < coupling)
    (φ : Wavefunction) :
    MemLp (magneticDilation coupling φ) 2 volume ↔ MemLp φ 2 volume := by
  constructor
  · intro h
    simpa only [magneticDilation_inv_cancel hc] using h.magneticDilation (inv_pos.mpr hc)
  · exact fun h => h.magneticDilation hc

theorem waveInner_magneticDilation {coupling : ℝ} (hc : 0 < coupling)
    (φ ψ : Wavefunction) :
    waveInner (magneticDilation coupling φ) (magneticDilation coupling ψ) =
      waveInner φ ψ := by
  let r := Real.sqrt coupling
  have hr : 0 < r := Real.sqrt_pos.mpr hc
  have hpoint (y : Plane) :
      star (magneticDilation coupling φ y) * magneticDilation coupling ψ y =
        ((r⁻¹ : ℂ) ^ 2) * (star (φ (r⁻¹ • y)) * ψ (r⁻¹ • y)) := by
    simp only [magneticDilation_apply, r, star_mul', Complex.star_def,
      Complex.conj_inv, Complex.conj_ofReal]
    ring
  unfold waveInner
  simp_rw [hpoint]
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg volume
      (fun y : Plane => star (φ y) * ψ y) hr.le]
  simp only [Plane, finrank_euclideanSpace_fin, Complex.real_smul, Complex.ofReal_pow]
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  field_simp

theorem waveInner_magneticDilation_left {coupling : ℝ} (hc : 0 < coupling)
    (φ ψ : Wavefunction) :
    waveInner (magneticDilation coupling φ) ψ =
      waveInner φ (magneticDilation coupling⁻¹ ψ) := by
  have h := waveInner_magneticDilation hc φ (magneticDilation coupling⁻¹ ψ)
  simpa only [magneticDilation_cancel_inv hc] using h

theorem waveInner_magneticDilation_right {coupling : ℝ} (hc : 0 < coupling)
    (φ ψ : Wavefunction) :
    waveInner φ (magneticDilation coupling ψ) =
      waveInner (magneticDilation coupling⁻¹ φ) ψ := by
  have h := waveInner_magneticDilation hc (magneticDilation coupling⁻¹ φ) ψ
  simpa only [magneticDilation_cancel_inv hc] using h

theorem mass_sub_magneticDilation {coupling : ℝ} (hc : 0 < coupling)
    (φ ψ : Wavefunction) :
    mass (magneticDilation coupling φ - magneticDilation coupling ψ) = mass (φ - ψ) := by
  rw [← magneticDilation_sub, mass_magneticDilation hc]

theorem norm_toLp_magneticDilation {coupling : ℝ} (hc : 0 < coupling)
    {φ : Wavefunction} (hφ : MemLp φ 2 volume) :
    ‖(hφ.magneticDilation hc).toLp (magneticDilation coupling φ)‖ = ‖hφ.toLp φ‖ := by
  have hsq : ‖(hφ.magneticDilation hc).toLp (magneticDilation coupling φ)‖ ^ 2 =
      ‖hφ.toLp φ‖ ^ 2 := by
    rw [norm_toLp_sq_eq_mass, mass_magneticDilation hc, norm_toLp_sq_eq_mass]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

end InfiniteZero
