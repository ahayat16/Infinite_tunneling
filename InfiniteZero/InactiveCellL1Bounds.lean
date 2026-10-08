import InfiniteZero.CoreCellBound
import InfiniteZero.AtomicCuspSourceSupport

/-!
# Absolute bounds for all seven actual inactive source cells

The source estimates are explicit inputs here. The kernel estimates and
their action reserves are supplied by the proved geometric certificate.
The action contains two radial-core contributions and the distinct bridge
energy. No identification between the two energies is made.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero

/-- Triangle inequality for precisely the seven cells retained by
`inactiveCells`; the two cross cells do not enter this estimate. -/
theorem norm_inactiveCells_le_of_bound {I : Fin 3 → Fin 3 → ℂ} {B : ℝ}
    (hbound : ∀ i j : Fin 3, (i, j) ≠ (1, 2) → (i, j) ≠ (2, 1) → ‖I i j‖ ≤ B) :
    ‖inactiveCells I‖ ≤ 7 * B := by
  have h00 := hbound 0 0 (by decide) (by decide)
  have h01 := hbound 0 1 (by decide) (by decide)
  have h02 := hbound 0 2 (by decide) (by decide)
  have h10 := hbound 1 0 (by decide) (by decide)
  have h11 := hbound 1 1 (by decide) (by decide)
  have h20 := hbound 2 0 (by decide) (by decide)
  have h22 := hbound 2 2 (by decide) (by decide)
  have hnorm := norm_add_le_of_le
    (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le
      (norm_add_le_of_le (norm_add_le_of_le h00 h01) h02) h10) h11) h20) h22
  change ‖inactiveCells I‖ ≤ _ at hnorm
  convert hnorm using 1
  ring

namespace CuspParameters

set_option maxHeartbeats 1600000

/-- The polynomial bound is uniform in both energies, the source envelope,
the exterior coefficient, the coupling and the actual ground state. -/
theorem exists_inactiveCell_L1_bound {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) {L : ℝ} (hL : cert.L₀ ≤ L) :
    ∃ K > 0, ∀ coupling : ℝ, 1 ≤ coupling →
      ∀ E ∈ Icc (1 / 2 : ℝ) 1, ∀ E₀ ∈ Ioc (0 : ℝ) 2,
      ∀ Γ : ℝ, 0 ≤ Γ → ∀ S : ℝ, 0 ≤ S → ∀ ψ : Wavefunction,
      IsAtomicGroundState p.b p.potential coupling ψ →
      (∀ i : Fin 3, i = 1 ∨ i = 2 →
        (∫ x : Plane, ‖componentSource p coupling⁻¹ ψ i x‖) ≤
          S * Γ * coupling ^ 6 * Real.exp (-coupling * bridgeAction p.b E₀ p.R)) →
      ∀ i j : Fin 3, (i, j) ≠ (1, 2) → (i, j) ≠ (2, 1) →
        ‖sourceCell p L coupling⁻¹ E ψ i j‖ ≤
          K * (coreSourceConstant p + S + 1) ^ 2 * (Γ ^ 2 + 1) * coupling ^ 10 *
            Real.exp (-coupling * (p.activeReferenceAction L E E₀ + 31 * p.hopMargin)) := by
  obtain ⟨K, hK, hk⟩ := exists_inactiveKernelUpperBounds hp cert hL
    (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (hopMargin_pos hp)
  refine ⟨K, hK, ?_⟩
  intro coupling hc E hE E₀ hE₀ Γ hΓ S hS ψ hψ hsource
  have hcpos : 0 < coupling := zero_lt_one.trans_le hc
  have hh : 0 < coupling⁻¹ := inv_pos.mpr hcpos
  have hEpos : 0 < E := lt_of_lt_of_le (by norm_num) hE.1
  let Q := coreSourceConstant p + S + 1
  have hQ : 0 < Q := by dsimp [Q]; linarith [coreSourceConstant_pos p]
  have hCQ : coreSourceConstant p ≤ Q := by dsimp [Q]; linarith
  have hSQ : S ≤ Q := by dsimp [Q]; linarith [coreSourceConstant_pos p]
  let J := bridgeAction p.b E₀ p.R
  let A := p.activeReferenceAction L E E₀
  let d : Fin 3 → ℝ := ![0, J, J]
  let g : Fin 3 → ℝ := ![1, Γ, Γ]
  have hg (i : Fin 3) : 0 ≤ g i := by
    fin_cases i <;> simp [g] <;> exact hΓ
  have hgam (i j : Fin 3) : g i * g j ≤ Γ ^ 2 + 1 := by
    fin_cases i <;> fin_cases j <;> simp [g] <;>
      nlinarith [sq_nonneg (Γ - 1)]
  have hpow26 : coupling ^ 2 ≤ coupling ^ 6 := by
    have hfour : 1 ≤ coupling ^ 4 := one_le_pow₀ hc
    nlinarith [mul_le_mul_of_nonneg_left hfour (sq_nonneg coupling)]
  have hnorm (i : Fin 3) :
      (∫ x : Plane, ‖componentSource p coupling⁻¹ ψ i x‖) ≤
        Q * g i * coupling ^ 6 * Real.exp (-coupling * d i) := by
    fin_cases i
    · have hb := coreSource_L1_le_of_atomicGroundState hp.r₀_pos hψ coupling⁻¹
      simp only [inv_pow, inv_inv] at hb
      simpa [d, g] using hb.trans
        (mul_le_mul hCQ hpow26 (sq_nonneg coupling) hQ.le)
    · simpa [d, g, J] using (hsource 1 (Or.inl rfl)).trans
        (by gcongr; linarith)
    · simpa [d, g, J] using (hsource 2 (Or.inr rfl)).trans
        (by gcongr; linarith)
  have hs0 {x : Plane} (hx : x ∈ Function.support (componentSource p coupling⁻¹ ψ 0)) :
      x ∈ tsupport p.core := coreSource_support_subset p coupling⁻¹ ψ hx
  have hsp {x : Plane} (hx : x ∈ Function.support (componentSource p coupling⁻¹ ψ 1)) :
      x ∈ tsupport p.cuspPlus :=
    subset_tsupport p.cuspPlus (componentSource_plus_support_subset p coupling⁻¹ ψ hx)
  have hsm {x : Plane} (hx : x ∈ Function.support (componentSource p coupling⁻¹ ψ 2)) :
      x ∈ tsupport p.cuspMinus :=
    subset_tsupport p.cuspMinus (componentSource_minus_support_subset p coupling⁻¹ ψ hx)
  have hsall (i : Fin 3) {x : Plane}
      (hx : x ∈ Function.support (componentSource p coupling⁻¹ ψ i)) :
      x ∈ tsupport p.core ∪ tsupport p.cuspPlus ∪ tsupport p.cuspMinus := by
    fin_cases i
    · exact Or.inl (Or.inl (hs0 hx))
    · exact Or.inl (Or.inr (hsp hx))
    · exact Or.inr (hsm hx)
  have hstep (i j : Fin 3) (r a : ℝ)
      (hb : landauKernel p.b coupling⁻¹ E r ≤ K * Real.exp (-a / coupling⁻¹))
      (ha : A + 31 * p.hopMargin - d i - d j ≤ a) :
      landauKernel p.b coupling⁻¹ E r ≤
        K * Real.exp (-coupling * (A + 31 * p.hopMargin - d i - d j)) := by
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ hK.le
    apply Real.exp_le_exp.mpr
    rw [div_inv_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left ha hcpos.le]
  have hkernel (i j : Fin 3) (hij₁ : (i, j) ≠ (1, 2)) (hij₂ : (i, j) ≠ (2, 1))
      (z : Plane) (hz : z ∈ Function.support (componentSource p coupling⁻¹ ψ i))
      (w : Plane) (hw : w ∈ Function.support (componentSource p coupling⁻¹ ψ j)) :
      landauKernel p.b coupling⁻¹ E ‖z + w - 2 • displacement L‖ ≤
        K * Real.exp (-coupling * (A + 31 * p.hopMargin - d i - d j)) := by
    fin_cases i <;> fin_cases j
    · apply hstep _ _ _ _ (hk.core_core E hE E₀ hE₀ z (hs0 hz) w (hs0 hw) _ hh)
      dsimp [A, activeReferenceAction, d, J]
      ring_nf
      exact le_rfl
    · apply hstep _ _ _ _ (hk.mixed E hE E₀ hE₀ z w
        (Or.inl ⟨hs0 hz, Or.inl (hsp hw)⟩) _ hh)
      dsimp [A, activeReferenceAction, d, J]
      ring_nf
      exact le_rfl
    · apply hstep _ _ _ _ (hk.mixed E hE E₀ hE₀ z w
        (Or.inl ⟨hs0 hz, Or.inr (hsm hw)⟩) _ hh)
      dsimp [A, activeReferenceAction, d, J]
      ring_nf
      exact le_rfl
    · apply hstep _ _ _ _ (hk.mixed E hE E₀ hE₀ z w
        (Or.inr ⟨hs0 hw, Or.inl (hsp hz)⟩) _ hh)
      dsimp [A, activeReferenceAction, d, J]
      ring_nf
      exact le_rfl
    · apply hstep _ _ _ _ (hk.same_cusp E hE z w (Or.inl ⟨hsp hz, hsp hw⟩) _ hh)
      dsimp [A, activeReferenceAction, d, J]
      linarith [hopMargin_pos hp]
    · exact (hij₁ rfl).elim
    · apply hstep _ _ _ _ (hk.mixed E hE E₀ hE₀ z w
        (Or.inr ⟨hs0 hw, Or.inr (hsm hz)⟩) _ hh)
      dsimp [A, activeReferenceAction, d, J]
      ring_nf
      exact le_rfl
    · exact (hij₂ rfl).elim
    · apply hstep _ _ _ _ (hk.same_cusp E hE z w (Or.inr ⟨hsm hz, hsm hw⟩) _ hh)
      dsimp [A, activeReferenceAction, d, J]
      linarith [hopMargin_pos hp]
  intro i j hij₁ hij₂
  have hFi := componentSource_integrable hp coupling⁻¹ hψ.1.1.continuous i
  have hFj := componentSource_integrable hp coupling⁻¹ hψ.1.1.continuous j
  have hr : ∀ z ∈ Function.support (componentSource p coupling⁻¹ ψ i),
      ∀ w ∈ Function.support (componentSource p coupling⁻¹ ψ j),
      0 < ‖z + w - 2 • displacement L‖ := by
    intro z hz w hw
    have hb := cert.component_support_annulus hp hL (hsall i hz) (hsall j hw)
    exact hb.1.trans_le hb.2.1
  have hb := norm_sourcePairing_sourceKernel_le hp.b_pos hh hEpos
    (mul_nonneg hK.le (Real.exp_pos _).le) hFi hFj hr (hkernel i j hij₁ hij₂)
  change ‖sourceCell p L coupling⁻¹ E ψ i j‖ ≤ _ at hb
  have hpow : (coupling⁻¹) ^ 2 * coupling ^ 6 * coupling ^ 6 = coupling ^ 10 := by
    field_simp
  have hexp : Real.exp (-coupling * (A + 31 * p.hopMargin - d i - d j)) *
      Real.exp (-coupling * d i) * Real.exp (-coupling * d j) =
      Real.exp (-coupling * (A + 31 * p.hopMargin)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ (coupling⁻¹) ^ 2 *
        (K * Real.exp (-coupling * (A + 31 * p.hopMargin - d i - d j))) *
        (∫ x : Plane, ‖componentSource p coupling⁻¹ ψ i x‖) *
        (∫ x : Plane, ‖componentSource p coupling⁻¹ ψ j x‖) := hb
    _ ≤ (coupling⁻¹) ^ 2 *
        (K * Real.exp (-coupling * (A + 31 * p.hopMargin - d i - d j))) *
        (Q * g i * coupling ^ 6 * Real.exp (-coupling * d i)) *
        (Q * g j * coupling ^ 6 * Real.exp (-coupling * d j)) := by
      have hgi := hg i
      gcongr
      · exact hnorm i
      · exact hnorm j
    _ = K * Q ^ 2 * (g i * g j) *
        ((coupling⁻¹) ^ 2 * coupling ^ 6 * coupling ^ 6) *
        (Real.exp (-coupling * (A + 31 * p.hopMargin - d i - d j)) *
          Real.exp (-coupling * d i) * Real.exp (-coupling * d j)) := by ring
    _ = K * Q ^ 2 * (g i * g j) * coupling ^ 10 *
        Real.exp (-coupling * (A + 31 * p.hopMargin)) := by rw [hpow, hexp]
    _ ≤ _ := by
      change _ ≤ K * Q ^ 2 * (Γ ^ 2 + 1) * coupling ^ 10 *
        Real.exp (-coupling * (A + 31 * p.hopMargin))
      gcongr
      exact hgam i j

/-- The whole inactive contribution satisfies the same bound, with the
factor seven absorbed in the single uniform constant. -/
theorem exists_inactiveCells_L1_bound {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) {L : ℝ} (hL : cert.L₀ ≤ L) :
    ∃ K > 0, ∀ coupling : ℝ, 1 ≤ coupling →
      ∀ E ∈ Icc (1 / 2 : ℝ) 1, ∀ E₀ ∈ Ioc (0 : ℝ) 2,
      ∀ Γ : ℝ, 0 ≤ Γ → ∀ S : ℝ, 0 ≤ S → ∀ ψ : Wavefunction,
      IsAtomicGroundState p.b p.potential coupling ψ →
      (∀ i : Fin 3, i = 1 ∨ i = 2 →
        (∫ x : Plane, ‖componentSource p coupling⁻¹ ψ i x‖) ≤
          S * Γ * coupling ^ 6 * Real.exp (-coupling * bridgeAction p.b E₀ p.R)) →
        ‖inactiveCells (sourceCell p L coupling⁻¹ E ψ)‖ ≤
          K * (coreSourceConstant p + S + 1) ^ 2 * (Γ ^ 2 + 1) * coupling ^ 10 *
            Real.exp (-coupling * (p.activeReferenceAction L E E₀ + 31 * p.hopMargin)) := by
  obtain ⟨K, hK, hbound⟩ := exists_inactiveCell_L1_bound hp cert hL
  refine ⟨7 * K, by positivity, ?_⟩
  intro coupling hc E hE E₀ hE₀ Γ hΓ S hS ψ hψ hsource
  have hb := norm_inactiveCells_le_of_bound
    (hbound coupling hc E hE E₀ hE₀ Γ hΓ S hS ψ hψ hsource)
  convert hb using 1
  ring

end CuspParameters
end InfiniteZero
