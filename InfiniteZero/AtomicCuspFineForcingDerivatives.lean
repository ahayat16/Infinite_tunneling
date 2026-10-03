import InfiniteZero.AtomicCuspFineForcing
import InfiniteZero.ConstructionSmooth
import InfiniteZero.CuspFineForcingJets

/-!
# Fine L² bounds for directional derivatives of the actual cusp forcing

The derivatives belong to the physical product `W φ`. The Lipschitz weight
is multiplied afterwards and is never differentiated. Smoothness and fixed
compact support give the integrability of each resulting wavefunction.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace InfiniteZero.CuspParameters

/-- The semiclassical directional jet of the actual force, weighted after
taking derivatives. The directions may be arbitrary; unit bounds are only
needed for the subsequent quantitative estimate. -/
def weightedAtomicForcingJet {p : CuspParameters} (χ : CuspWeightCutoffs p)
    (h κ : ℝ) (φ : Wavefunction) (n : ℕ) (v : Fin n → Plane) : Wavefunction :=
  fun x => (Real.exp (κ / h * χ.weight x) : ℂ) * (h ^ n : ℂ) *
    (iteratedFDeriv ℝ n (fun y => (p.atomicPerturbation y : ℂ) * φ y) x v)

/-- Global smoothness is only required of the actual unweighted state.
The weight itself is used through its continuity. -/
theorem weightedAtomicForcingJet_continuous {p : CuspParameters}
    (hp : p.BasicConditions) (χ : CuspWeightCutoffs p) (h κ : ℝ)
    (φ : Wavefunction) (hφ : ContDiff ℝ ∞ φ) (n : ℕ) (v : Fin n → Plane) :
    Continuous (weightedAtomicForcingJet χ h κ φ n v) := by
  have hW : ContDiff ℝ ∞ p.atomicPerturbation :=
    (potential_contDiff hp).sub (core_contDiff hp.r₀_pos)
  have hprod : ContDiff ℝ ∞ (fun y => (p.atomicPerturbation y : ℂ) * φ y) := by
    simpa only [Complex.real_smul] using hW.smul hφ
  have hjet := (contDiff_infty.mp hprod n).continuous_iteratedFDeriv'.eval_const v
  have hweight : Continuous (fun x => (Real.exp (κ / h * χ.weight x) : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_const.mul χ.weight_continuous).rexp)
  exact (hweight.mul continuous_const).mul hjet

/-- Taking jets and multiplying by a weight do not enlarge the fixed
closed support of the force. This does not assume regularity of `φ`. -/
theorem weightedAtomicForcingJet_support_subset_closedBall {p : CuspParameters}
    (hp : p.BasicConditions) (χ : CuspWeightCutoffs p) (h κ : ℝ)
    (φ : Wavefunction) (n : ℕ) (v : Fin n → Plane) :
    Function.support (weightedAtomicForcingJet χ h κ φ n v) ⊆
      Metric.closedBall (0 : Plane) p.cuspSupportRadius := by
  have hs : Function.support (fun y => (p.atomicPerturbation y : ℂ) * φ y) ⊆
      Metric.closedBall (0 : Plane) p.cuspSupportRadius := by
    simpa only [one_mul] using
      weightedAtomicPerturbation_support_subset_closedBall hp (fun _ => 1) φ
  have hts : tsupport (fun y => (p.atomicPerturbation y : ℂ) * φ y) ⊆
      Metric.closedBall (0 : Plane) p.cuspSupportRadius :=
    closure_minimal hs Metric.isClosed_closedBall
  intro x hx
  have hjet : iteratedFDeriv ℝ n (fun y => (p.atomicPerturbation y : ℂ) * φ y) x ≠ 0 := by
    intro hzero
    exact hx (by simp only [weightedAtomicForcingJet, hzero,
      ContinuousMultilinearMap.zero_apply, mul_zero])
  exact hts (support_iteratedFDeriv_subset n hjet)

/-- Integrability of the genuine weighted derivative follows from continuity
and the actual compact support, without an L² hypothesis on `φ`. -/
theorem weightedAtomicForcingJet_memLp {p : CuspParameters}
    (hp : p.BasicConditions) (χ : CuspWeightCutoffs p) (h κ : ℝ)
    (φ : Wavefunction) (hφ : ContDiff ℝ ∞ φ) (n : ℕ) (v : Fin n → Plane) :
    MemLp (weightedAtomicForcingJet χ h κ φ n v) 2 volume :=
  memLp_of_continuous_support_subset_closedBall
    (weightedAtomicForcingJet_continuous hp χ h κ φ hφ n v)
    (weightedAtomicForcingJet_support_subset_closedBall hp χ h κ φ n v)

/-- The multilinear operator norm controls every unit-bounded tuple of
directions, including the empty tuple at order zero. -/
theorem norm_weightedAtomicForcingJet_le {p : CuspParameters}
    (χ : CuspWeightCutoffs p) {h : ℝ} (hh : 0 ≤ h) (κ : ℝ)
    (φ : Wavefunction) (n : ℕ) (v : Fin n → Plane) (hv : ∀ i, ‖v i‖ ≤ 1)
    (x : Plane) :
    ‖weightedAtomicForcingJet χ h κ φ n v x‖ ≤
      Real.exp (κ / h * χ.weight x) * h ^ n *
        ‖iteratedFDeriv ℝ n (fun y => (p.atomicPerturbation y : ℂ) * φ y) x‖ := by
  have hvnorm : ‖v‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr hv
  have heval := (iteratedFDeriv ℝ n
    (fun y => (p.atomicPerturbation y : ℂ) * φ y) x).unit_le_opNorm hvnorm
  simp only [weightedAtomicForcingJet, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_nonneg hh]
  exact mul_le_mul_of_nonneg_left heval (by positivity)

/-- A pointwise derivative bound yields the mass estimate with the exact
area factor of the fixed support ball. -/
theorem mass_weightedAtomicForcingJet_le {p : CuspParameters}
    (hp : p.BasicConditions) (χ : CuspWeightCutoffs p) (h κ : ℝ)
    (φ : Wavefunction) (hφ : ContDiff ℝ ∞ φ) (n : ℕ) (v : Fin n → Plane)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, ‖weightedAtomicForcingJet χ h κ φ n v x‖ ≤ B) :
    mass (weightedAtomicForcingJet χ h κ φ n v) ≤
      (Real.sqrt Real.pi * p.cuspSupportRadius * B) ^ 2 := by
  have hm := mass_le_pi_mul_radius_sq_mul_bound_sq
    (weightedAtomicForcingJet_memLp hp χ h κ φ hφ n v) (cuspSupportRadius_pos hp).le
    (weightedAtomicForcingJet_support_subset_closedBall hp χ h κ φ n v) hB hbound
  simpa only [mul_pow, Real.sq_sqrt Real.pi_pos.le] using hm

/-- Every fixed semiclassical derivative of the actual forcing has the
same full action and every strict log-flat margin in L². The directions,
state and exterior coefficient all follow the common constant and threshold. -/
theorem exists_atomic_cusp_fine_forcing_jet_mass {p : CuspParameters}
    (hp : p.BasicConditions) (χ : CuspWeightCutoffs p) {β₁ : ℝ}
    (hβ₁ : 0 < β₁) (hβ₁β : β₁ < p.β) (n : ℕ) :
    ∃ C > 0, ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∀ E ∈ Icc (1 / 2 : ℝ) 1, ∀ κ ∈ Icc (0 : ℝ) (1 / 16),
      ∀ Γ : ℝ, 0 ≤ Γ → ∀ φ : Wavefunction, ContDiff ℝ ∞ φ →
      (∀ x, p.r₀ < ‖x‖ → φ x = (Γ * landauKernel p.b h E ‖x‖ : ℂ)) →
      ∀ v : Fin n → Plane, (∀ i, ‖v i‖ ≤ 1) →
        MemLp (weightedAtomicForcingJet χ h κ φ n v) 2 volume ∧
        mass (weightedAtomicForcingJet χ h κ φ n v) ≤
          (C * Γ * (h ^ 2)⁻¹ * Real.exp (-bridgeAction p.b E p.R / h) *
            Real.exp (-β₁ * (Real.log (1 / h)) ^ 2)) ^ 2 := by
  obtain ⟨C, hC, hpoint⟩ := exists_cusp_fine_forcing_jet_bound hp χ hβ₁ hβ₁β n
  have hr := cuspSupportRadius_pos hp
  refine ⟨Real.sqrt Real.pi * p.cuspSupportRadius * C, by positivity, ?_⟩
  filter_upwards [hpoint, self_mem_nhdsWithin] with h hh hpos
  have hhp : 0 < h := hpos
  intro E hE κ hκ Γ hΓ φ hφ htail v hv
  refine ⟨weightedAtomicForcingJet_memLp hp χ h κ φ hφ n v, ?_⟩
  have hbound (x : Plane) : ‖weightedAtomicForcingJet χ h κ φ n v x‖ ≤
      C * Γ * (h ^ 2)⁻¹ * Real.exp (-bridgeAction p.b E p.R / h) *
        Real.exp (-β₁ * (Real.log (1 / h)) ^ 2) :=
    (norm_weightedAtomicForcingJet_le χ hhp.le κ φ n v hv x).trans
      (hh E hE κ hκ Γ hΓ φ hφ htail x)
  have hm := mass_weightedAtomicForcingJet_le hp χ h κ φ hφ n v (by positivity) hbound
  convert hm using 1
  ring

end InfiniteZero.CuspParameters
