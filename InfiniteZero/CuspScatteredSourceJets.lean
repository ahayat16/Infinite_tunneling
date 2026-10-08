import InfiniteZero.AtomicCuspSource
import InfiniteZero.ConstructionCuspJetBounds
import InfiniteZero.CuspPacketNeighborhood
import InfiniteZero.WeightedSemiclassicalProduct

/-!
# Local log-flat profiles of the scattered cusp source

Multiplication by the actual perturbation retains a second, local log-flat
factor. The input is a weighted bound for the jets of one smooth function
on the closed inner neighborhood. The output concerns the existing source
`atomicSource`, including its exact semiclassical factor and ε. All constants
precede the coupling, weight strength, wavefunction and response envelope.
-/

noncomputable section
open Set
open scoped ContDiff

namespace InfiniteZero.CuspParameters

set_option maxHeartbeats 1000000

theorem exists_cusp_scattered_source_jet_bound
    {p : CuspParameters} (hp : p.BasicConditions) (χ : CuspWeightCutoffs p)
    {βlocal : ℝ} (hl : 0 < βlocal) (hlβ : βlocal < p.β) (n : ℕ) :
    ∃ C > 0, ∀ coupling : ℝ, 1 ≤ coupling → ∀ κ : ℝ,
      ∀ η : Wavefunction, ContDiff ℝ ∞ η → ∀ M : ℝ, 0 ≤ M →
      (∀ j : ℕ, j ≤ n → ∀ x ∈ closure p.cuspPacketInnerNeighborhood,
        Real.exp (κ * coupling * χ.weight x) * (coupling⁻¹) ^ j *
          ‖iteratedFDeriv ℝ j η x‖ ≤ M) →
      ∀ j : ℕ, j ≤ n →
        (∀ x ∈ tsupport p.cuspPlus,
          (coupling⁻¹) ^ j *
            ‖iteratedFDeriv ℝ j (atomicSource coupling⁻¹ p.atomicPerturbation η) x‖ ≤
            C * coupling ^ 2 * M * logFlat βlocal p.tStar (p.normalCoordinate x) *
              Real.exp (-κ * coupling * p.normalCoordinate x)) ∧
        (∀ x ∈ tsupport p.cuspMinus,
          (coupling⁻¹) ^ j *
            ‖iteratedFDeriv ℝ j (atomicSource coupling⁻¹ p.atomicPerturbation η) x‖ ≤
            C * coupling ^ 2 * M *
              logFlat βlocal p.tStar (p.normalCoordinate (reflection x)) *
              Real.exp (-κ * coupling * p.normalCoordinate (reflection x))) := by
  choose A hA hAbound using fun i => exists_cuspPlus_jet_margin_bound hp hl hlβ i
  choose B hB hBbound using fun i => exists_cuspMinus_jet_margin_bound hp hl hlβ i
  obtain ⟨Sp, hSp, hplus⟩ := exists_weighted_semiclassical_smul_bound_upTo
    (E := Plane) (F := ℂ) n A (fun i _ => (hA i).le)
  obtain ⟨Sm, hSm, hminus⟩ := exists_weighted_semiclassical_smul_bound_upTo
    (E := Plane) (F := ℂ) n B (fun i _ => (hB i).le)
  refine ⟨p.ε * (Sp + Sm), mul_pos hp.ε_pos (add_pos hSp hSm), ?_⟩
  intro coupling hc κ η hη M hM hresponse j hj
  have hcpos : 0 < coupling := zero_lt_one.trans_le hc
  have hh : 0 ≤ coupling⁻¹ := (inv_pos.mpr hcpos).le
  have hh1 : coupling⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc
  have hfinish (q : Potential) (x : Plane) (t : ℝ)
      (hweight : χ.weight x = t)
      (hbound : Real.exp (κ * coupling * χ.weight x) * (coupling⁻¹) ^ j *
        ‖iteratedFDeriv ℝ j (fun y => q y • η y) x‖ ≤
          (Sp + Sm) * logFlat βlocal p.tStar t * M)
      (hsource : ‖iteratedFDeriv ℝ j
          (atomicSource coupling⁻¹ p.atomicPerturbation η) x‖ =
          (coupling ^ 2 * p.ε) * ‖iteratedFDeriv ℝ j (fun y => q y • η y) x‖) :
      (coupling⁻¹) ^ j *
        ‖iteratedFDeriv ℝ j (atomicSource coupling⁻¹ p.atomicPerturbation η) x‖ ≤
        (p.ε * (Sp + Sm)) * coupling ^ 2 * M * logFlat βlocal p.tStar t *
          Real.exp (-κ * coupling * t) := by
    rw [hweight] at hbound
    have hcancel : Real.exp (-κ * coupling * t) * Real.exp (κ * coupling * t) = 1 := by
      rw [← Real.exp_add]
      have hz : -κ * coupling * t + κ * coupling * t = 0 := by ring
      rw [hz, Real.exp_zero]
    calc
      _ = (coupling ^ 2 * p.ε) *
          (Real.exp (-κ * coupling * t) *
            (Real.exp (κ * coupling * t) * (coupling⁻¹) ^ j *
              ‖iteratedFDeriv ℝ j (fun y => q y • η y) x‖)) := by
        rw [hsource]
        calc
          _ = (coupling ^ 2 * p.ε) *
              ((Real.exp (-κ * coupling * t) * Real.exp (κ * coupling * t)) *
                ((coupling⁻¹) ^ j * ‖iteratedFDeriv ℝ j (fun y => q y • η y) x‖)) := by
            rw [hcancel, one_mul]
            ring
          _ = _ := by ring
      _ ≤ (coupling ^ 2 * p.ε) *
          (Real.exp (-κ * coupling * t) * ((Sp + Sm) * logFlat βlocal p.tStar t * M)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le)
          (mul_nonneg (sq_nonneg coupling) hp.ε_pos.le)
      _ = _ := by ring
  constructor
  · intro x hx
    refine hfinish p.cuspPlus x (p.normalCoordinate x) (χ.weight_eq_normal_on_plus hx) ?_ ?_
    · have hb := hplus p.cuspPlus η (cuspPlus_contDiff hp) hη x coupling⁻¹
        (Real.exp (κ * coupling * χ.weight x))
        (logFlat βlocal p.tStar (p.normalCoordinate x)) M
        hh hh1 (Real.exp_pos _).le (logFlat_nonneg _ _ _) hM
        (fun i _ => hAbound i x)
        (fun k hk => hresponse k hk x
          (subset_closure (cuspPlus_tsupport_subset_cuspPacketInnerNeighborhood hp hx))) j hj
      exact hb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hSm.le)
          (logFlat_nonneg _ _ _)) hM)
    · rw [iteratedFDeriv_atomicPerturbation_source_eq_plus hp coupling⁻¹ η hx j,
        norm_iteratedFDeriv_componentSource_plus hp hη, inv_pow, inv_inv]
  · intro x hx
    refine hfinish p.cuspMinus x (p.normalCoordinate (reflection x))
      (χ.weight_eq_normal_on_minus hx) ?_ ?_
    · have hb := hminus p.cuspMinus η (cuspMinus_contDiff hp) hη x coupling⁻¹
        (Real.exp (κ * coupling * χ.weight x))
        (logFlat βlocal p.tStar (p.normalCoordinate (reflection x))) M
        hh hh1 (Real.exp_pos _).le (logFlat_nonneg _ _ _) hM
        (fun i _ => hBbound i x)
        (fun k hk => hresponse k hk x
          (subset_closure (cuspMinus_tsupport_subset_cuspPacketInnerNeighborhood hp hx))) j hj
      exact hb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hSp.le)
          (logFlat_nonneg _ _ _)) hM)
    · rw [iteratedFDeriv_atomicPerturbation_source_eq_minus hp coupling⁻¹ η hx j,
        norm_iteratedFDeriv_componentSource_minus hp hη, inv_pow, inv_inv]

end InfiniteZero.CuspParameters
