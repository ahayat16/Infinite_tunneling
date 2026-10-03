import InfiniteZero.MagneticDilationL2
import InfiniteZero.UnitPhaseDistance
import InfiniteZero.AtomicGroundRankOne
import InfiniteZero.MagneticFormPotentialComparison

/-!
# Phase comparison of actual atomic ground states after dilation

The uniformly bounded difference of the dilated potentials controls the
reduced atomic energies. Transporting the actual rank-one test gap and
then extending it through the original closed graph controls the overlap
of two ground states. A scalar unit phase gives the resulting mass bound.
No continuous phase selection or new dilated operator realization is assumed.
-/

noncomputable section
open MeasureTheory
namespace InfiniteZero

private theorem atomicGround_test_lower {b coupling : ℝ} {V : Potential}
    (hA : IsMagneticRealization b coupling V) (hV : Continuous V)
    {ψ : Wavefunction} (hψ : IsTestFunction ψ) :
    atomicGroundEnergy b V coupling * mass ψ ≤ magneticForm b coupling V ψ := by
  have hz : Represents (0 : L2Space) (0 : Wavefunction) := Lp.coeFn_zero _ _ _
  have h := hA.test_rankOne_lower_of_operator hV hz
    (c := 0) (k := 0) (E := atomicGroundEnergy b V coupling)
    (fun u => by
      have h := hA.lower_bound u
      simpa only [zero_mul, sub_zero, sub_nonneg, atomicGroundEnergy] using h) hψ
  simpa only [zero_mul, sub_zero, sub_nonneg] using h

private theorem atomicGround_rankOne_from_test {b coupling c k E : ℝ}
    {V : Potential} (hA : IsMagneticRealization b coupling V) (hV : Continuous V)
    {φ ρ : Wavefunction} (hφ : IsAtomicGroundState b V coupling φ)
    (hρ : MemLp ρ 2 volume)
    (htest : ∀ ψ : Wavefunction, IsTestFunction ψ →
      c * mass ψ - k * ‖waveInner ρ ψ‖ ^ 2 ≤
        magneticForm b coupling V ψ - E * mass ψ) :
    c - k * ‖waveInner ρ φ‖ ^ 2 ≤ atomicGroundEnergy b V coupling - E := by
  let v : L2Space := hφ.1.2.1.toLp φ
  have hv : Represents v φ := represents_toLp hφ.1.2.1
  have heig := (hA.eigenfunction_iff (atomicGroundEnergy b V coupling) v).mpr ⟨φ, hφ.1, hv⟩
  obtain ⟨u, hu, hAu⟩ := (magneticOperator b coupling V).mem_graph_iff.mp heig
  have hAu' : magneticOperator b coupling V u =
      (atomicGroundEnergy b V coupling : ℂ) • (u : L2Space) := by
    simpa only [hu] using hAu
  have hm : ‖(u : L2Space)‖ ^ 2 = 1 := by
    rw [hu]
    exact hv.norm_sq_eq_mass.trans hφ.2
  have hi : inner ℂ (hρ.toLp ρ) (u : L2Space) = waveInner ρ φ := by
    rw [hu]
    exact (represents_toLp hρ).inner_eq_waveInner hv
  have h := hA.rankOne_lower hV hρ htest u
  rw [re_inner_eq_of_operator_eigenvector _ _ _ hAu', hm, hi] at h
  simpa only [mul_one] using h

private theorem magneticForm_div_eq_dilated {b coupling : ℝ} {V : Potential}
    (hc : 0 < coupling) {ψ : Wavefunction} (hψ : IsTestFunction ψ) :
    magneticForm b coupling V ψ / coupling =
      magneticForm b 1 (magneticDilationPotential V coupling) (magneticDilation coupling ψ) := by
  simpa only [div_eq_mul_inv, mul_comm] using
    (magneticForm_magneticDilation b V hc hψ).symm

/-- Uniform comparison of the reduced atomic energies from the actual test forms. -/
theorem atomicGroundEnergy_div_sub_le_of_dilation_bound
    {b coupling μ D : ℝ} {V : Potential} (hc : 0 < coupling) (hμ : 0 < μ)
    (hV : Continuous V) (hA : IsMagneticRealization b coupling V)
    (hAμ : IsMagneticRealization b μ V) {φμ : Wavefunction}
    (hφμ : IsAtomicGroundState b V μ φμ)
    (hbound : ∀ ψ : Wavefunction, IsTestFunction ψ →
      |magneticForm b 1 (magneticDilationPotential V coupling) ψ -
        magneticForm b 1 (magneticDilationPotential V μ) ψ| ≤ D * mass ψ) :
    atomicGroundEnergy b V coupling / coupling ≤ atomicGroundEnergy b V μ / μ + D := by
  have htest (ψ : Wavefunction) (hψ : IsTestFunction ψ) :
      (μ * (atomicGroundEnergy b V coupling / coupling - D)) * mass ψ ≤
        magneticForm b μ V ψ := by
    let τ := magneticDilation μ ψ
    have hτ : IsTestFunction τ := hψ.magneticDilation hμ
    let χ := magneticDilation coupling⁻¹ τ
    have hχ : IsTestFunction χ := hτ.magneticDilation (inv_pos.mpr hc)
    have hmχ : mass χ = mass ψ := by
      dsimp only [χ, τ]
      rw [mass_magneticDilation (inv_pos.mpr hc), mass_magneticDilation hμ]
    have hmτ : mass τ = mass ψ := mass_magneticDilation hμ ψ
    have hl := div_le_div_of_nonneg_right (atomicGround_test_lower hA hV hχ) hc.le
    rw [hmχ, magneticForm_div_eq_dilated hc hχ,
      magneticDilation_cancel_inv hc] at hl
    have hb := (le_abs_self _).trans (hbound τ hτ)
    rw [hmτ, ← magneticForm_div_eq_dilated hμ hψ] at hb
    have hs : (atomicGroundEnergy b V coupling / coupling - D) * mass ψ ≤
        magneticForm b μ V ψ / μ := by
      have hh : atomicGroundEnergy b V coupling * mass ψ / coupling =
          (atomicGroundEnergy b V coupling / coupling) * mass ψ := by ring
      rw [hh] at hl
      linarith
    have hh := (le_div_iff₀ hμ).mp hs
    nlinarith only [hh]
  have hh := atomicGround_rankOne_from_test hAμ hV hφμ
    (show MemLp (0 : Wavefunction) 2 volume from MemLp.zero)
    (c := 0) (k := 0) (E := μ * (atomicGroundEnergy b V coupling / coupling - D))
    (fun ψ hψ => by have h := htest ψ hψ; simpa only [zero_mul, sub_zero, sub_nonneg] using h)
  simp only [zero_mul, sub_zero] at hh
  have hs : (atomicGroundEnergy b V coupling / coupling - D) * μ ≤
      atomicGroundEnergy b V μ := by linarith
  exact sub_le_iff_le_add.mp ((le_div_iff₀ hμ).mpr hs)

/-- The test gap controls the overlap of two true ground states after dilation. -/
theorem atomicGround_overlap_deficit_le_of_dilation_bound
    {b coupling μ D γ : ℝ} {V : Potential} (hc : 0 < coupling) (hμ : 0 < μ)
    (hV : Continuous V) (hA : IsMagneticRealization b coupling V)
    (hAμ : IsMagneticRealization b μ V) {φ φμ : Wavefunction}
    (hφ : IsAtomicGroundState b V coupling φ)
    (hφμ : IsAtomicGroundState b V μ φμ)
    (hgap : ∀ ψ : Wavefunction, IsTestFunction ψ →
      (γ * μ) * (mass ψ - ‖waveInner φμ ψ‖ ^ 2) ≤
        magneticForm b μ V ψ - atomicGroundEnergy b V μ * mass ψ)
    (hbound : ∀ ψ : Wavefunction, IsTestFunction ψ →
      |magneticForm b 1 (magneticDilationPotential V coupling) ψ -
        magneticForm b 1 (magneticDilationPotential V μ) ψ| ≤ D * mass ψ) :
    γ * (1 - ‖waveInner
      (magneticDilation coupling⁻¹ (magneticDilation μ φμ)) φ‖ ^ 2) ≤ 2 * D := by
  let ρ := magneticDilation coupling⁻¹ (magneticDilation μ φμ)
  have hρ : MemLp ρ 2 volume :=
    (hφμ.1.2.1.magneticDilation hμ).magneticDilation (inv_pos.mpr hc)
  have htest (ψ : Wavefunction) (hψ : IsTestFunction ψ) :
      (coupling * γ) * mass ψ - (coupling * γ) * ‖waveInner ρ ψ‖ ^ 2 ≤
        magneticForm b coupling V ψ -
          (coupling * (atomicGroundEnergy b V μ / μ - D)) * mass ψ := by
    let τ := magneticDilation coupling ψ
    have hτ : IsTestFunction τ := hψ.magneticDilation hc
    let χ := magneticDilation μ⁻¹ τ
    have hχ : IsTestFunction χ := hτ.magneticDilation (inv_pos.mpr hμ)
    have hmχ : mass χ = mass ψ := by
      dsimp only [χ, τ]
      rw [mass_magneticDilation (inv_pos.mpr hμ), mass_magneticDilation hc]
    have hmτ : mass τ = mass ψ := mass_magneticDilation hc ψ
    have hi : waveInner φμ χ = waveInner ρ ψ := by
      change waveInner φμ (magneticDilation μ⁻¹ (magneticDilation coupling ψ)) = _
      rw [← waveInner_magneticDilation_left hμ, waveInner_magneticDilation_right hc]
    have hscaled : γ * (mass ψ - ‖waveInner ρ ψ‖ ^ 2) ≤
        magneticForm b 1 (magneticDilationPotential V μ) τ -
          (atomicGroundEnergy b V μ / μ) * mass ψ := by
      have hh := div_le_div_of_nonneg_right (hgap χ hχ) hμ.le
      rw [hmχ, hi, sub_div, magneticForm_div_eq_dilated hμ hχ,
        magneticDilation_cancel_inv hμ] at hh
      convert hh using 1 <;> field_simp
    have hb := neg_le_of_abs_le (hbound τ hτ)
    rw [hmτ, ← magneticForm_div_eq_dilated hc hψ] at hb
    have hs : γ * (mass ψ - ‖waveInner ρ ψ‖ ^ 2) +
        (atomicGroundEnergy b V μ / μ - D) * mass ψ ≤
          magneticForm b coupling V ψ / coupling := by linarith
    have hh := (le_div_iff₀ hc).mp hs
    nlinarith only [hh]
  have hh := atomicGround_rankOne_from_test hA hV hφ hρ htest
  have he := atomicGroundEnergy_div_sub_le_of_dilation_bound hc hμ hV hA hAμ hφμ hbound
  have hcancel : coupling * (atomicGroundEnergy b V coupling / coupling) =
      atomicGroundEnergy b V coupling := mul_div_cancel₀ _ hc.ne'
  have hle : coupling * (γ * (1 - ‖waveInner ρ φ‖ ^ 2)) ≤ coupling * (2 * D) := by
    have he' := mul_le_mul_of_nonneg_left he hc.le
    nlinarith only [hh, he', hcancel]
  exact (mul_le_mul_iff_right₀ hc).mp hle

/-- Physical L² phase alignment; phases need not depend continuously on parameters. -/
theorem exists_unit_phase_mass_sub_le {φ ψ : Wavefunction}
    (hφ : MemLp φ 2 volume) (hψ : MemLp ψ 2 volume)
    (hmφ : mass φ = 1) (hmψ : mass ψ = 1) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ mass (φ - z • ψ) ≤ 2 * (1 - ‖waveInner ψ φ‖ ^ 2) := by
  have hnφ : ‖hφ.toLp φ‖ = 1 := by
    have hh := (norm_toLp_sq_eq_mass hφ).trans hmφ
    nlinarith [norm_nonneg (hφ.toLp φ)]
  have hnψ : ‖hψ.toLp ψ‖ = 1 := by
    have hh := (norm_toLp_sq_eq_mass hψ).trans hmψ
    nlinarith [norm_nonneg (hψ.toLp ψ)]
  obtain ⟨z, hz, hh⟩ := exists_unit_phase_norm_sub_sq_le (hφ.toLp φ) (hψ.toLp ψ) hnφ hnψ
  refine ⟨z, hz, ?_⟩
  rw [← norm_toLp_sq_eq_mass (hφ.sub (hψ.const_smul z)), MemLp.toLp_sub hφ (hψ.const_smul z),
    MemLp.toLp_const_smul z hψ]
  simpa only [inner_toLp_eq_waveInner hψ hφ] using hh

/-- Two actual ground states align at the scale dictated by the bounded dilated perturbation. -/
theorem exists_atomicGround_phase_mass_sub_le_of_dilation_bound
    {b coupling μ D γ : ℝ} {V : Potential} (hc : 0 < coupling) (hμ : 0 < μ)
    (hγ : 0 < γ) (hV : Continuous V) (hA : IsMagneticRealization b coupling V)
    (hAμ : IsMagneticRealization b μ V) {φ φμ : Wavefunction}
    (hφ : IsAtomicGroundState b V coupling φ)
    (hφμ : IsAtomicGroundState b V μ φμ)
    (hgap : ∀ ψ : Wavefunction, IsTestFunction ψ →
      (γ * μ) * (mass ψ - ‖waveInner φμ ψ‖ ^ 2) ≤
        magneticForm b μ V ψ - atomicGroundEnergy b V μ * mass ψ)
    (hbound : ∀ ψ : Wavefunction, IsTestFunction ψ →
      |magneticForm b 1 (magneticDilationPotential V coupling) ψ -
        magneticForm b 1 (magneticDilationPotential V μ) ψ| ≤ D * mass ψ) :
    ∃ z : ℂ, ‖z‖ = 1 ∧
      mass (φ - z • magneticDilation coupling⁻¹ (magneticDilation μ φμ)) ≤ 4 * D / γ := by
  let ρ := magneticDilation coupling⁻¹ (magneticDilation μ φμ)
  have hρ : MemLp ρ 2 volume :=
    (hφμ.1.2.1.magneticDilation hμ).magneticDilation (inv_pos.mpr hc)
  have hmρ : mass ρ = 1 := by
    dsimp only [ρ]
    rw [mass_magneticDilation (inv_pos.mpr hc), mass_magneticDilation hμ, hφμ.2]
  have hov := atomicGround_overlap_deficit_le_of_dilation_bound hc hμ hV hA hAμ
    hφ hφμ hgap hbound
  obtain ⟨z, hz, hh⟩ := exists_unit_phase_mass_sub_le hφ.1.2.1 hρ hφ.2 hmρ
  refine ⟨z, hz, ?_⟩
  apply (le_div_iff₀ hγ).mpr
  have hh' := mul_le_mul_of_nonneg_left hh hγ.le
  change γ * (1 - ‖waveInner ρ φ‖ ^ 2) ≤ 2 * D at hov
  nlinarith only [hh', hov]

namespace CuspParameters

/-- One mass comparison constant and threshold work for all pairs of true atomic ground states. -/
theorem exists_atomicGround_phase_dilation_comparison_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions)
    (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential) :
    ∃ C > 0, ∃ T > 0, ∀ coupling μ : ℝ, T ≤ coupling → T ≤ μ →
      ∀ φ φμ : Wavefunction,
        IsAtomicGroundState p.b p.potential coupling φ →
        IsAtomicGroundState p.b p.potential μ φμ →
      ∃ z : ℂ, ‖z‖ = 1 ∧
        mass (φ - z • magneticDilation coupling⁻¹ (magneticDilation μ φμ)) ≤
          C * |coupling - μ| := by
  obtain ⟨C, hC, hbound⟩ := exists_magneticForm_dilationPotential_mass_bound
    (potential_contDiff hp) (potential_hasCompactSupport hp)
  obtain ⟨T, hT, hgap⟩ := exists_atomic_test_rankOne_gap_of_radialData hp hRad hAcore hApot
  have hγ : 0 < hRad.gap / 2 := div_pos hRad.gap_pos (by norm_num)
  refine ⟨4 * C / (hRad.gap / 2), by positivity, T, hT, ?_⟩
  intro coupling μ hc hμ φ φμ hφ hφμ
  have hcpos : 0 < coupling := hT.trans_le hc
  have hμpos : 0 < μ := hT.trans_le hμ
  obtain ⟨z, hz, hh⟩ := exists_atomicGround_phase_mass_sub_le_of_dilation_bound
    hcpos hμpos hγ (potential_contDiff hp).continuous (hApot coupling) (hApot μ)
    hφ hφμ (hgap μ hμ φμ hφμ) (hbound p.b coupling μ hcpos hμpos)
  refine ⟨z, hz, ?_⟩
  convert hh using 1
  ring

end CuspParameters
end InfiniteZero
