import InfiniteZero.InactiveKernelBounds
import InfiniteZero.CoreSourceBound

/-!
# An exponential estimate for the actual core-core cell

The source L¹ bound and the uniform inactive kernel estimate are combined for
the concrete integral. No source asymptotic or exterior normalization is used.
This is an absolute estimate; comparison with the active envelope is separate.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero.CuspParameters

theorem coreSource_support_subset (p : CuspParameters) (h : ℝ) (φ : Wavefunction) :
    Function.support (componentSource p h φ 0) ⊆ tsupport p.core := by
  intro x hx
  apply subset_tsupport p.core
  intro hz
  apply hx
  simp [componentSource, componentPotential, atomicSource, hz]

/-- Uniform in the atomic state, its coupling, both energy parameters and h.
The positive separation L is fixed only after the single-well potential. -/
theorem exists_coreCell_exp_bound {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) {L Emin Emax η : ℝ}
    (hL : cert.L₀ ≤ L) (hEmin : 0 < Emin) (hEmax : Emin ≤ Emax) (hη : 0 < η) :
    ∃ C > 0, ∀ E ∈ Icc Emin Emax, ∀ E₀ ∈ Ioc (0 : ℝ) 2,
      ∀ h > 0, ∀ coupling : ℝ, ∀ φ : Wavefunction,
      IsAtomicGroundState p.b p.potential coupling φ →
        ‖sourceCell p L h E φ 0 0‖ ≤ C / h ^ 2 * Real.exp
          (-(p.activeReferenceAction L E E₀ + 32 * p.hopMargin - η) / h) := by
  obtain ⟨K, hK, hk⟩ := exists_inactiveKernelUpperBounds hp cert hL hEmin hEmax hη
  have hcore := coreSourceConstant_pos p
  refine ⟨K * coreSourceConstant p ^ 2, by positivity, ?_⟩
  intro E hE E₀ hE₀ h hh coupling φ hφ
  let e := Real.exp (-(p.activeReferenceAction L E E₀ + 32 * p.hopMargin - η) / h)
  have he : 0 < e := Real.exp_pos _
  have hF := componentSource_integrable hp h hφ.1.1.continuous 0
  have hrad : ∀ z ∈ Function.support (componentSource p h φ 0),
      ∀ w ∈ Function.support (componentSource p h φ 0),
      0 < ‖z + w - 2 • displacement L‖ := by
    intro z hz w hw
    have ha := cert.component_support_annulus hp hL
      (Or.inl (Or.inl (coreSource_support_subset p h φ hz)))
      (Or.inl (Or.inl (coreSource_support_subset p h φ hw)))
    exact ha.1.trans_le ha.2.1
  have hbound : ∀ z ∈ Function.support (componentSource p h φ 0),
      ∀ w ∈ Function.support (componentSource p h φ 0),
      landauKernel p.b h E ‖z + w - 2 • displacement L‖ ≤ K * e := by
    intro z hz w hw
    simpa only [e, activeReferenceAction, add_comm, add_left_comm, add_assoc] using
      hk.core_core E hE E₀ hE₀ z (coreSource_support_subset p h φ hz)
        w (coreSource_support_subset p h φ hw) h hh
  have hb := norm_sourcePairing_sourceKernel_le hp.b_pos hh (hEmin.trans_le hE.1)
    (mul_pos hK he).le hF hF hrad hbound
  have hn := coreSource_L1_le_of_atomicGroundState hp.r₀_pos hφ h
  change ‖sourceCell p L h E φ 0 0‖ ≤ _ at hb
  calc
    ‖sourceCell p L h E φ 0 0‖ ≤ h ^ 2 * (K * e) *
        (∫ z : Plane, ‖componentSource p h φ 0 z‖) *
        (∫ z : Plane, ‖componentSource p h φ 0 z‖) := hb
    _ ≤ h ^ 2 * (K * e) *
        (coreSourceConstant p * (h ^ 2)⁻¹) * (coreSourceConstant p * (h ^ 2)⁻¹) := by
      gcongr
    _ = K * coreSourceConstant p ^ 2 / h ^ 2 * e := by
      field_simp

end InfiniteZero.CuspParameters
