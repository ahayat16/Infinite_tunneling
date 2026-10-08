import InfiniteZero.AtomicCuspFineForcingDerivatives
import InfiniteZero.RadialCoreEnergyBounds
import InfiniteZero.RadialCoreExteriorState
import InfiniteZero.GenericFiniteL2Bound

/-!
# Fine forcing derivatives for the genuine positive radial core state

The true scaled core energy supplies the compact energy interval, and the
radial ODE supplies the exterior Landau coefficient of the same state.
One constant and one coupling threshold control every derivative up to a
fixed order. The coefficient is chosen once, before each derivative order
`j ≤ n`, weight strength and directions. The Lipschitz weight is not differentiated.

These results assume only the radial spectral data and the core operator
realizations. They use neither a nonradial spectral input nor the free
resolvent kernel contract.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace InfiniteZero.CuspParameters

/-- A common constant and threshold for the finitely many semiclassical
directional derivatives. This intermediate statement still displays the
exterior-tail hypothesis explicitly. -/
theorem exists_atomic_cusp_fine_forcing_jets_mass_coupling
    {p : CuspParameters} (hp : p.BasicConditions) (χ : CuspWeightCutoffs p)
    {β₁ : ℝ} (hβ₁ : 0 < β₁) (hβ₁β : β₁ < p.β) (n : ℕ) :
    ∃ C > 0, ∃ N > 0, ∀ coupling : ℝ, N ≤ coupling →
      ∀ E ∈ Icc (1 / 2 : ℝ) 1, ∀ κ ∈ Icc (0 : ℝ) (1 / 16),
      ∀ Γ : ℝ, 0 ≤ Γ → ∀ φ : Wavefunction, ContDiff ℝ ∞ φ →
      (∀ x, p.r₀ < ‖x‖ →
        φ x = (Γ * landauKernel p.b coupling⁻¹ E ‖x‖ : ℂ)) →
      ∀ j : ℕ, j ≤ n → ∀ v : Fin j → Plane, (∀ i, ‖v i‖ ≤ 1) →
        MemLp (weightedAtomicForcingJet χ coupling⁻¹ κ φ j v) 2 volume ∧
        mass (weightedAtomicForcingJet χ coupling⁻¹ κ φ j v) ≤
          (C * Γ * coupling ^ 2 * Real.exp (-coupling * bridgeAction p.b E p.R) *
            Real.exp (-β₁ * (Real.log coupling) ^ 2)) ^ 2 := by
  choose C hC hforce using fun j : ℕ =>
    exists_atomic_cusp_fine_forcing_jet_mass hp χ hβ₁ hβ₁β j
  have hall := (eventually_all_finset (Finset.range (n + 1))).mpr
    (fun j _ => hforce j)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (tendsto_inv_atTop_nhdsGT_zero.eventually hall)
  let Csum := 1 + ∑ j ∈ Finset.range (n + 1), C j
  have hCsum : 0 < Csum := by
    have hs : 0 ≤ ∑ j ∈ Finset.range (n + 1), C j :=
      Finset.sum_nonneg (fun j _ => (hC j).le)
    dsimp [Csum]
    linarith
  refine ⟨Csum, hCsum, max N 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
  intro coupling hc E hE κ hκ Γ hΓ φ hφ htail j hj v hv
  have hjmem : j ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hCj : C j ≤ Csum := by
    have hs := Finset.single_le_sum (fun i _ => (hC i).le) hjmem
    dsimp [Csum]
    linarith
  have hbound := hN coupling ((le_max_left _ _).trans hc) j hjmem
    E hE κ hκ Γ hΓ φ hφ htail v hv
  refine ⟨hbound.1, ?_⟩
  have hm : mass (weightedAtomicForcingJet χ coupling⁻¹ κ φ j v) ≤
      (C j * Γ * coupling ^ 2 * Real.exp (-coupling * bridgeAction p.b E p.R) *
        Real.exp (-β₁ * (Real.log coupling) ^ 2)) ^ 2 := by
    simpa only [inv_inv, inv_pow, one_div, div_eq_mul_inv, mul_one, one_mul,
      mul_neg, neg_mul, mul_comm, mul_left_comm, mul_assoc] using hbound.2
  have hCjpos : 0 < C j := hC j
  exact hm.trans (by gcongr)

/-- Fine forcing bounds at the actual energy of every normalized positive
radial core ground state. The same positive coefficient represents its
exterior tail and controls all orders up to `n`. No tail or energy-window
hypothesis remains in this statement. -/
theorem exists_radialCore_fine_forcing_derivatives_mass_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (χ : CuspWeightCutoffs p) {β₁ : ℝ} (hβ₁ : 0 < β₁) (hβ₁β : β₁ < p.β)
    (n : ℕ) :
    ∃ C > 0, ∃ N > 0, ∀ coupling : ℝ, N ≤ coupling →
      ∀ φ : Wavefunction, IsAtomicGroundState p.b p.core coupling φ →
      IsPositiveRadial φ → ∃ Γ : ℝ, 0 < Γ ∧
        (∀ x : Plane, p.r₀ < ‖x‖ →
          φ x = (Γ * landauKernel p.b coupling⁻¹
            (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖ : ℂ)) ∧
        ∀ κ ∈ Icc (0 : ℝ) (1 / 16), ∀ j : ℕ, j ≤ n →
        ∀ v : Fin j → Plane, (∀ i, ‖v i‖ ≤ 1) →
          MemLp (weightedAtomicForcingJet χ coupling⁻¹ κ φ j v) 2 volume ∧
          mass (weightedAtomicForcingJet χ coupling⁻¹ κ φ j v) ≤
            (C * Γ * coupling ^ 2 * Real.exp (-coupling * bridgeAction p.b
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
              Real.exp (-β₁ * (Real.log coupling) ^ 2)) ^ 2 := by
  obtain ⟨C, hC, Nf, hNf, hforce⟩ :=
    exists_atomic_cusp_fine_forcing_jets_mass_coupling hp χ hβ₁ hβ₁β n
  obtain ⟨NE, _hNE, henergy⟩ :=
    exists_scaledRadialCoreEnergy_bounds_of_radialData hp.r₀_pos hRad hAcore
  refine ⟨C, hC, max Nf NE, hNf.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc φ hφ hpos
  have hcf : Nf ≤ coupling := (le_max_left _ _).trans hc
  have hcpos : 0 < coupling := hNf.trans_le hcf
  have hE := henergy coupling ((le_max_right _ _).trans hc)
  obtain ⟨Γ, hΓ, htail⟩ := hφ.exists_pos_radialCore_kernel
    hp.b_pos hp.r₀_pos hcpos hpos (by linarith only [hE.1])
  refine ⟨Γ, hΓ, htail, ?_⟩
  intro κ hκ j hj v hv
  exact hforce coupling hcf _ hE κ hκ Γ hΓ.le φ hφ.1.1 htail j hj v hv

/-- Existence of an actual positive radial normalized core state with the
common finite-order forcing bounds. Both the state and its single exterior
coefficient precede the weight strength, derivative order and directions. -/
theorem exists_positive_radialCore_fine_forcing_derivatives_mass_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (χ : CuspWeightCutoffs p) {β₁ : ℝ} (hβ₁ : 0 < β₁) (hβ₁β : β₁ < p.β)
    (n : ℕ) :
    ∃ C > 0, ∃ N > 0, ∀ coupling : ℝ, N ≤ coupling →
      ∃ φ : Wavefunction, IsAtomicGroundState p.b p.core coupling φ ∧
      IsPositiveRadial φ ∧ ∃ Γ : ℝ, 0 < Γ ∧
        (∀ x : Plane, p.r₀ < ‖x‖ →
          φ x = (Γ * landauKernel p.b coupling⁻¹
            (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖ : ℂ)) ∧
        ∀ κ ∈ Icc (0 : ℝ) (1 / 16), ∀ j : ℕ, j ≤ n →
        ∀ v : Fin j → Plane, (∀ i, ‖v i‖ ≤ 1) →
          MemLp (weightedAtomicForcingJet χ coupling⁻¹ κ φ j v) 2 volume ∧
          mass (weightedAtomicForcingJet χ coupling⁻¹ κ φ j v) ≤
            (C * Γ * coupling ^ 2 * Real.exp (-coupling * bridgeAction p.b
              (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
              Real.exp (-β₁ * (Real.log coupling) ^ 2)) ^ 2 := by
  obtain ⟨C, hC, N, hN, hforce⟩ :=
    exists_radialCore_fine_forcing_derivatives_mass_of_radialData
      hp hRad hAcore χ hβ₁ hβ₁β n
  refine ⟨C, hC, max N hRad.threshold, hN.trans_le (le_max_left _ _), ?_⟩
  intro coupling hc
  obtain ⟨φ, hφ, hpos⟩ := hRad.positive_radial_ground coupling
    ((le_max_right _ _).trans hc)
  exact ⟨φ, hφ, hpos, hforce coupling ((le_max_left _ _).trans hc) φ hφ hpos⟩

/-- The common finite-order mass estimate gives an actual finite sum of
Hilbert L² norms. The constant and threshold are independent even of the
finite family; its cardinality is retained explicitly. Repeated orders or
directions are allowed, and all terms concern the same state and coefficient. -/
theorem exists_radialCore_fine_forcing_derivatives_sum_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (χ : CuspWeightCutoffs p) {β₁ : ℝ} (hβ₁ : 0 < β₁) (hβ₁β : β₁ < p.β)
    (n : ℕ) :
    ∃ C > 0, ∃ N > 0, ∀ coupling : ℝ, N ≤ coupling →
      ∀ φ : Wavefunction, IsAtomicGroundState p.b p.core coupling φ →
      IsPositiveRadial φ → ∃ Γ : ℝ, 0 < Γ ∧
        (∀ x : Plane, p.r₀ < ‖x‖ →
          φ x = (Γ * landauKernel p.b coupling⁻¹
            (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) ‖x‖ : ℂ)) ∧
        ∀ κ ∈ Icc (0 : ℝ) (1 / 16),
        ∀ (ι : Type*) [Fintype ι] (orders : ι → ℕ), (∀ i, orders i ≤ n) →
        ∀ v : (i : ι) → Fin (orders i) → Plane, (∀ i j, ‖v i j‖ ≤ 1) →
          ∃ hF : ∀ i, MemLp
              (weightedAtomicForcingJet χ coupling⁻¹ κ φ (orders i) (v i)) 2 volume,
            (∑ i, ‖(hF i).toLp
              (weightedAtomicForcingJet χ coupling⁻¹ κ φ (orders i) (v i))‖) ≤
              (Fintype.card ι : ℝ) * C * Γ * coupling ^ 2 *
                Real.exp (-coupling * bridgeAction p.b
                  (-((coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.core coupling)) p.R) *
                Real.exp (-β₁ * (Real.log coupling) ^ 2) := by
  obtain ⟨C, hC, N, hN, hforce⟩ :=
    exists_radialCore_fine_forcing_derivatives_mass_of_radialData
      hp hRad hAcore χ hβ₁ hβ₁β n
  refine ⟨C, hC, N, hN, ?_⟩
  intro coupling hc φ hφ hpos
  obtain ⟨Γ, hΓ, htail, hbounds⟩ := hforce coupling hc φ hφ hpos
  refine ⟨Γ, hΓ, htail, ?_⟩
  intro κ hκ ι _ orders horders v hv
  have hi (i : ι) := hbounds κ hκ (orders i) (horders i) (v i) (hv i)
  refine ⟨fun i => (hi i).1, ?_⟩
  convert sum_norm_toLp_le_card_mul_of_mass_le_sq
    (fun i => weightedAtomicForcingJet χ coupling⁻¹ κ φ (orders i) (v i))
    (fun i => (hi i).1) (by positivity) (fun i => (hi i).2) using 1
  ring

end InfiniteZero.CuspParameters
