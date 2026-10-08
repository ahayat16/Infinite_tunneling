import InfiniteZero.AtomicSourceL1
import InfiniteZero.ComponentSourceL1Assembly
import InfiniteZero.CoreSourceBound

/-!
# The three genuine component sources in L¹

One pair of genuine ground states supplies the two full cusp sources and
the core source. The two cusp L¹ norms satisfy a common exponential bound;
the core source has its separate polynomial bound. The same exterior
coefficient belongs to the retained positive radial reference state.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero.CuspParameters

theorem exists_atomicGround_component_source_L1_of_radialData
    (hInterior : HasInteriorEllipticEstimate)
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (χ : CuspWeightCutoffs p) {β₁ : ℝ} (hβ₁ : 0 < β₁) (hβ₁β : β₁ < p.β) :
    ∃ C > 0, ∃ threshold > 0,
      ∀ coupling : ℝ, threshold ≤ coupling →
      ∃ φ ψ : Wavefunction,
        IsAtomicGroundState p.b p.core coupling φ ∧ IsPositiveRadial φ ∧
        IsAtomicGroundState p.b p.potential coupling ψ ∧
        ∃ c ∈ Icc (1 / 2 : ℝ) 1, ∃ Γ : ℝ, 0 < Γ ∧
          (∀ x : Plane, p.r₀ < ‖x‖ →
            φ x = (Γ * landauKernel p.b coupling⁻¹
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖ : ℂ)) ∧
          (∀ i : Fin 3, Integrable (componentSource p coupling⁻¹ ψ i)) ∧
          ((∫ x : Plane, ‖componentSource p coupling⁻¹ ψ 0 x‖) ≤
            coreSourceConstant p * coupling ^ 2) ∧
          ((∫ x : Plane, ‖componentSource p coupling⁻¹ ψ 1 x‖) +
            (∫ x : Plane, ‖componentSource p coupling⁻¹ ψ 2 x‖) ≤
              C * Γ * coupling ^ 6 * Real.exp (-coupling * bridgeAction p.b
                (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
                Real.exp (-β₁ * (Real.log coupling) ^ 2)) := by
  obtain ⟨Cin, hCin, Csc, hCsc, T, hT, hstates⟩ :=
    exists_atomicGround_source_L1_of_radialData
      hInterior hp hRad hAcore hApot χ hβ₁ hβ₁β hβ₁ hβ₁β hβ₁ hβ₁β
  refine ⟨2 * (Cin + Csc), by positivity, max T 1,
    zero_lt_one.trans_le (le_max_right _ _), ?_⟩
  intro coupling hc
  have hcT := (max_le_iff.mp hc).1
  have hc1 := (max_le_iff.mp hc).2
  have hcpos : 0 < coupling := zero_lt_one.trans_le hc1
  obtain ⟨φ, ψ, hφ, hφpos, hψ, c, hcRange, Γ, hΓ, htail,
    _hηsmooth, _hηLp, _horth, hsource⟩ := hstates coupling hcT
  let J := bridgeAction p.b
    (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R
  let G := c * Γ * Real.exp (-coupling * J)
  let G₀ := Γ * Real.exp (-coupling * J)
  let e := Real.exp (-β₁ * (Real.log coupling) ^ 2)
  have hc0 : 0 ≤ c := le_trans (by norm_num) hcRange.1
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hG₀ : 0 ≤ G₀ := by dsimp [G₀]; positivity
  have hGle : G ≤ G₀ := by
    dsimp [G, G₀]
    calc
      _ ≤ 1 * Γ * Real.exp (-coupling * J) := by
        gcongr
        exact hcRange.2
      _ = _ := by ring
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hpow : coupling ^ 4 ≤ coupling ^ 6 := by
    have hsq : 1 ≤ coupling ^ 2 := by nlinarith [sq_nonneg (coupling - 1)]
    calc
      _ = coupling ^ 4 * 1 := by ring
      _ ≤ coupling ^ 4 * coupling ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (pow_nonneg hcpos.le _)
      _ = _ := by ring
  have hexp : Real.exp (-(β₁ + β₁) * (Real.log coupling) ^ 2) ≤ e := by
    apply Real.exp_le_exp.mpr
    dsimp [e]
    nlinarith [mul_nonneg hβ₁.le (sq_nonneg (Real.log coupling))]
  have hbranch (i : Fin 3) (hi : i = 1 ∨ i = 2) :
      (∫ x : Plane, ‖componentSource p coupling⁻¹ ψ i x‖) ≤
        (Cin + Csc) * coupling ^ 6 * G₀ * e := by
    obtain ⟨_hiInt, _hsInt, hiBound, hsBound⟩ := hsource i hi
    have hiScale : Cin * coupling ^ 4 * G * e ≤ Cin * coupling ^ 6 * G₀ * e := by
      apply mul_le_mul_of_nonneg_right _ he
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hCin.le) hGle hG
        (mul_nonneg hCin.le (pow_nonneg hcpos.le _))
    have hsScale : Csc * coupling ^ 6 * G *
        Real.exp (-(β₁ + β₁) * (Real.log coupling) ^ 2) ≤
        Csc * coupling ^ 6 * G₀ * e := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hGle (mul_nonneg hCsc.le (pow_nonneg hcpos.le _)))
        hexp (Real.exp_pos _).le
        (mul_nonneg (mul_nonneg hCsc.le (pow_nonneg hcpos.le _)) hG₀)
    calc
      _ ≤ (∫ x : Plane, ‖componentSource p coupling⁻¹ (fun y => (c : ℂ) * φ y) i x‖) +
          ∫ x : Plane, ‖componentSource p coupling⁻¹ (fun y => ψ y - (c : ℂ) * φ y) i x‖ :=
        componentSource_integral_norm_le_incoming_add_scattered hp coupling⁻¹ c
          hφ.1.1.continuous hψ.1.1.continuous i
      _ ≤ Cin * coupling ^ 6 * G₀ * e + Csc * coupling ^ 6 * G₀ * e :=
        add_le_add (hiBound.trans hiScale) (hsBound.trans hsScale)
      _ = _ := by ring
  refine ⟨φ, ψ, hφ, hφpos, hψ, c, hcRange, Γ, hΓ, htail,
    (fun i => componentSource_integrable hp coupling⁻¹ hψ.1.1.continuous i), ?_, ?_⟩
  · simpa only [inv_pow, inv_inv] using
      coreSource_L1_le_of_atomicGroundState hp.r₀_pos hψ coupling⁻¹
  · calc
      _ ≤ (Cin + Csc) * coupling ^ 6 * G₀ * e +
          (Cin + Csc) * coupling ^ 6 * G₀ * e :=
        add_le_add (hbranch 1 (Or.inl rfl)) (hbranch 2 (Or.inr rfl))
      _ = _ := by dsimp [G₀, e, J]; ring

end InfiniteZero.CuspParameters
