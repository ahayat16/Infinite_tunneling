import InfiniteZero.AtomicSourceProfiles
import InfiniteZero.AtomicCuspSourceSupport
import InfiniteZero.CuspProfileIntegralReflection

/-!
# Fine L¹ bounds for the actual incoming and scattered cusp sources

The local logarithmic margin is spent only in the real cusp integral.
The scattered source retains its independent global margin. A single pair
of genuine atomic states and one exterior coefficient supplies both cusp
branches. Constants and thresholds precede the coupling. The norms below
are integrals of pointwise norms of proved integrable functions, hence are
the actual L¹ norms via `norm_toL1_eq_integral_norm`.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero.CuspParameters

set_option maxHeartbeats 1400000

theorem exists_atomicGround_source_L1_of_radialData
    (hInterior : HasInteriorEllipticEstimate)
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (χ : CuspWeightCutoffs p) {βin βglobal βlocal : ℝ}
    (hi : 0 < βin) (hiβ : βin < p.β)
    (hg : 0 < βglobal) (hgβ : βglobal < p.β)
    (hl : 0 < βlocal) (hlβ : βlocal < p.β) :
    ∃ Cin > 0, ∃ Csc > 0, ∃ threshold > 0,
      ∀ coupling : ℝ, threshold ≤ coupling →
      ∃ φ ψ : Wavefunction,
        IsAtomicGroundState p.b p.core coupling φ ∧ IsPositiveRadial φ ∧
        IsAtomicGroundState p.b p.potential coupling ψ ∧
        ∃ c ∈ Icc (1 / 2 : ℝ) 1, ∃ Γ : ℝ, 0 < Γ ∧
          (∀ x : Plane, p.r₀ < ‖x‖ →
            φ x = (Γ * landauKernel p.b coupling⁻¹
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖ : ℂ)) ∧
          let η : Wavefunction := fun x => ψ x - (c : ℂ) * φ x
          let G : ℝ := c * Γ * Real.exp (-coupling * bridgeAction p.b
            (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R)
          ContDiff ℝ ∞ η ∧ MemLp η 2 volume ∧ waveInner φ η = 0 ∧
          ∀ i : Fin 3, i = 1 ∨ i = 2 →
            Integrable (componentSource p coupling⁻¹ (fun y => (c : ℂ) * φ y) i) ∧
            Integrable (componentSource p coupling⁻¹ η i) ∧
            (∫ x : Plane, ‖componentSource p coupling⁻¹ (fun y => (c : ℂ) * φ y) i x‖) ≤
              Cin * coupling ^ 4 * G * Real.exp (-βin * (Real.log coupling) ^ 2) ∧
            (∫ x : Plane, ‖componentSource p coupling⁻¹ η i x‖) ≤
              Csc * coupling ^ 6 * G *
                Real.exp (-(βglobal + βlocal) * (Real.log coupling) ^ 2) := by
  let βi := (βin + p.β) / 2
  let βl := (βlocal + p.β) / 2
  have hi' : 0 < βi := by dsimp [βi]; linarith
  have hii' : βin < βi := by dsimp [βi]; linarith
  have hi'β : βi < p.β := by dsimp [βi]; linarith
  have hl' : 0 < βl := by dsimp [βl]; linarith
  have hll' : βlocal < βl := by dsimp [βl]; linarith
  have hl'β : βl < p.β := by dsimp [βl]; linarith
  obtain ⟨κ₀, hκ₀, Ci, hCi, Cs, hCs, T, hT, hstates⟩ :=
    exists_atomicGround_source_profiles_of_radialData
      hInterior hp hRad hAcore hApot χ hi' hi'β hg hgβ hl' hl'β 0
  let κ := κ₀ / 2
  have hκpos : 0 < κ := half_pos hκ₀
  have hκ : κ ∈ Icc 0 κ₀ := ⟨hκpos.le, by dsimp [κ]; linarith⟩
  obtain ⟨Tip, _hTip, hintIp⟩ := exists_cuspPlus_profile_integral_threshold
    hp hi hii' (show (0 : ℝ) < 1 / 8 by norm_num)
  obtain ⟨Tim, _hTim, hintIm⟩ := exists_cuspMinus_profile_integral_threshold
    hp hi hii' (show (0 : ℝ) < 1 / 8 by norm_num)
  obtain ⟨Tsp, _hTsp, hintSp⟩ := exists_cuspPlus_profile_integral_threshold hp hl hll' hκpos
  obtain ⟨Tsm, _hTsm, hintSm⟩ := exists_cuspMinus_profile_integral_threshold hp hl hll' hκpos
  let threshold := max T (max 1 (max Tip (max Tim (max Tsp Tsm))))
  have hs0 : 0 < 2 * p.s₀ := mul_pos (by norm_num) hp.s₀_pos
  refine ⟨(2 * p.s₀) * Ci, mul_pos hs0 hCi,
    (2 * p.s₀) * Cs, mul_pos hs0 hCs, threshold,
    hT.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc
  have hthresholds : T ≤ coupling ∧ 1 ≤ coupling ∧ Tip ≤ coupling ∧
      Tim ≤ coupling ∧ Tsp ≤ coupling ∧ Tsm ≤ coupling := by
    simpa only [threshold, max_le_iff] using hc
  obtain ⟨hcT, hc1, hcTip, hcTim, hcTsp, hcTsm⟩ := hthresholds
  have hcpos : 0 < coupling := zero_lt_one.trans_le hc1
  obtain ⟨φ, ψ, hφ, hφpos, hψ, c, hcRange, Γ, hΓ, htail,
    hηsmooth, hηLp, horth, hprofiles⟩ := hstates coupling hcT
  let u : Wavefunction := fun x => (c : ℂ) * φ x
  let η : Wavefunction := fun x => ψ x - (c : ℂ) * φ x
  let J := bridgeAction p.b
    (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R
  let G := c * Γ * Real.exp (-coupling * J)
  let Bi := Ci * coupling ^ 4 * G
  let Bs := Cs * coupling ^ 6 * G * Real.exp (-βglobal * (Real.log coupling) ^ 2)
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hcRange.1
  have hG : 0 < G := by dsimp [G]; positivity
  have hBi : 0 ≤ Bi := by dsimp [Bi]; positivity
  have hBs : 0 ≤ Bs := by dsimp [Bs]; positivity
  have hu : Continuous u := continuous_const.mul hφ.1.1.continuous
  have hη : Continuous η := hηsmooth.continuous
  obtain ⟨hip, him, hsp, hsm⟩ := hprofiles κ hκ 0 le_rfl
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero, Nat.zero_add] at hip him hsp hsm
  have hexp (t : ℝ) : Real.exp (-coupling * (J + t / 8)) =
      Real.exp (-coupling * J) * Real.exp (-(1 / 8 : ℝ) * coupling * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hip' : ∀ x ∈ tsupport p.cuspPlus,
      ‖componentSource p coupling⁻¹ u 1 x‖ ≤
        Bi * logFlat βi p.tStar (p.normalCoordinate x) *
          Real.exp (-(1 / 8 : ℝ) * coupling * p.normalCoordinate x) := by
    intro x hx
    have hb := hip x hx
    rw [atomicPerturbation_source_eq_plus hp coupling⁻¹ _ hx] at hb
    calc
      _ ≤ Ci * c * Γ * coupling ^ 4 * logFlat βi p.tStar (p.normalCoordinate x) *
          Real.exp (-coupling * (J + p.normalCoordinate x / 8)) := hb
      _ = _ := by dsimp [Bi, G]; rw [hexp]; ring
  have him' : ∀ x ∈ tsupport p.cuspMinus,
      ‖componentSource p coupling⁻¹ u 2 x‖ ≤
        Bi * logFlat βi p.tStar (p.normalCoordinate (reflection x)) *
          Real.exp (-(1 / 8 : ℝ) * coupling * p.normalCoordinate (reflection x)) := by
    intro x hx
    have hb := him x hx
    rw [atomicPerturbation_source_eq_minus hp coupling⁻¹ _ hx] at hb
    calc
      _ ≤ Ci * c * Γ * coupling ^ 4 * logFlat βi p.tStar (p.normalCoordinate (reflection x)) *
          Real.exp (-coupling * (J + p.normalCoordinate (reflection x) / 8)) := hb
      _ = _ := by dsimp [Bi, G]; rw [hexp]; ring
  have hsp' : ∀ x ∈ tsupport p.cuspPlus,
      ‖componentSource p coupling⁻¹ η 1 x‖ ≤
        Bs * logFlat βl p.tStar (p.normalCoordinate x) *
          Real.exp (-κ * coupling * p.normalCoordinate x) := by
    intro x hx
    have hb := hsp x hx
    rw [atomicPerturbation_source_eq_plus hp coupling⁻¹ _ hx] at hb
    convert hb using 1
    dsimp [Bs, G, J]
    ring
  have hsm' : ∀ x ∈ tsupport p.cuspMinus,
      ‖componentSource p coupling⁻¹ η 2 x‖ ≤
        Bs * logFlat βl p.tStar (p.normalCoordinate (reflection x)) *
          Real.exp (-κ * coupling * p.normalCoordinate (reflection x)) := by
    intro x hx
    have hb := hsm x hx
    rw [atomicPerturbation_source_eq_minus hp coupling⁻¹ _ hx] at hb
    convert hb using 1
    dsimp [Bs, G, J]
    ring
  have hIp := hintIp coupling hcTip (1 / 8) le_rfl Bi hBi
    (componentSource p coupling⁻¹ u 1) (componentSource_continuous hp coupling⁻¹ hu 1)
    (componentSource_plus_support_subset p coupling⁻¹ u) hip'
  have hIm := hintIm coupling hcTim (1 / 8) le_rfl Bi hBi
    (componentSource p coupling⁻¹ u 2) (componentSource_continuous hp coupling⁻¹ hu 2)
    (componentSource_minus_support_subset p coupling⁻¹ u) him'
  have hSp := hintSp coupling hcTsp κ le_rfl Bs hBs
    (componentSource p coupling⁻¹ η 1) (componentSource_continuous hp coupling⁻¹ hη 1)
    (componentSource_plus_support_subset p coupling⁻¹ η) hsp'
  have hSm := hintSm coupling hcTsm κ le_rfl Bs hBs
    (componentSource p coupling⁻¹ η 2) (componentSource_continuous hp coupling⁻¹ hη 2)
    (componentSource_minus_support_subset p coupling⁻¹ η) hsm'
  have hscaleI : (2 * p.s₀) * Bi * Real.exp (-βin * (Real.log coupling) ^ 2) =
      ((2 * p.s₀) * Ci) * coupling ^ 4 * G * Real.exp (-βin * (Real.log coupling) ^ 2) := by
    dsimp [Bi]
    ring
  have hscaleS : (2 * p.s₀) * Bs * Real.exp (-βlocal * (Real.log coupling) ^ 2) =
      ((2 * p.s₀) * Cs) * coupling ^ 6 * G *
        Real.exp (-(βglobal + βlocal) * (Real.log coupling) ^ 2) := by
    dsimp [Bs]
    calc
      _ = ((2 * p.s₀) * Cs) * coupling ^ 6 * G *
          (Real.exp (-βglobal * (Real.log coupling) ^ 2) *
            Real.exp (-βlocal * (Real.log coupling) ^ 2)) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  refine ⟨φ, ψ, hφ, hφpos, hψ, c, hcRange, Γ, hΓ, htail,
    hηsmooth, hηLp, horth, ?_⟩
  intro i hi
  rcases hi with rfl | rfl
  · exact ⟨hIp.1, hSp.1, hIp.2.trans_eq hscaleI, hSp.2.trans_eq hscaleS⟩
  · exact ⟨hIm.1, hSm.1, hIm.2.trans_eq hscaleI, hSm.2.trans_eq hscaleS⟩

end InfiniteZero.CuspParameters
