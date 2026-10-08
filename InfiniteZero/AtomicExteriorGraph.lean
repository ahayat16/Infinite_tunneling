import InfiniteZero.AtomicLocalizationForms
import InfiniteZero.MagneticTestGraph
import InfiniteZero.L2Restriction

/-!
# Exterior probability from the closed radial graph

The exterior-mass estimate is closed in the graph norm. In particular a
radial ground state obeys the required O(1 / coupling) probability bound
without any assumption on integrability of its differential energy density.
-/

noncomputable section
open MeasureTheory Set

namespace InfiniteZero.CuspParameters

theorem core_exteriorMass_closedGraph {p : CuspParameters} (hr₀ : 0 < p.r₀)
    (b coupling : ℝ) :
    ∀ q ∈ magneticClosedGraph b coupling p.core,
      coupling ^ 2 * ‖l2Restrict {x : Plane | p.r₀ ≤ ‖x‖} q.1‖ ^ 2 ≤
        (inner ℂ q.1 q.2).re + coupling ^ 2 * ‖q.1‖ ^ 2 := by
  have hl : Continuous (fun q : L2Space × L2Space =>
      coupling ^ 2 * ‖l2Restrict {x : Plane | p.r₀ ≤ ‖x‖} q.1‖ ^ 2) :=
    continuous_const.mul ((continuous_restricted_mass _).comp continuous_fst)
  have hr : Continuous (fun q : L2Space × L2Space =>
      (inner ℂ q.1 q.2).re + coupling ^ 2 * ‖q.1‖ ^ 2) := by fun_prop
  intro q hq
  have hclosure : q ∈ closure (magneticTestGraph b coupling p.core) := by
    rwa [← magneticClosedGraph_eq_closure b coupling p.core]
  apply closure_minimal (s := magneticTestGraph b coupling p.core) _
    (isClosed_le hl hr) hclosure
  rintro z ⟨ψ, hψ, hψLp, hHLp, hz, hzH⟩
  change coupling ^ 2 * ‖l2Restrict {x : Plane | p.r₀ ≤ ‖x‖} z.1‖ ^ 2 ≤
    (inner ℂ z.1 z.2).re + coupling ^ 2 * ‖z.1‖ ^ 2
  rw [hz, hzH, norm_l2Restrict_sq (represents_toLp hψLp),
    norm_toLp_sq_eq_mass hψLp,
    re_inner_toLp_magneticHamiltonian_eq_magneticForm b coupling
      (core_contDiff hr₀).continuous hψ hψLp hHLp]
  exact core_exteriorMass_le_test hr₀ b coupling hψ

/-- The radial energy identity needed here is an operator eigenvalue equation,
not an identity for a potentially nonintegrable differential density. -/
theorem core_exteriorMass_le_groundEnergy {p : CuspParameters} (hr₀ : 0 < p.r₀)
    {b coupling : ℝ} (hA : IsMagneticRealization b coupling p.core)
    {φ : Wavefunction} (hφ : IsAtomicGroundState b p.core coupling φ) :
    coupling ^ 2 * (∫ x in {x : Plane | p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) ≤
      atomicGroundEnergy b p.core coupling + coupling ^ 2 := by
  let u : L2Space := hφ.1.2.1.toLp φ
  have hu : Represents u φ := represents_toLp hφ.1.2.1
  have heig : u ∈ operatorEigenspace (magneticOperator b coupling p.core)
      (atomicGroundEnergy b p.core coupling) :=
    (hA.eigenfunction_iff _ u).mpr ⟨φ, hφ.1, hu⟩
  have hgraph : (u, (atomicGroundEnergy b p.core coupling : ℂ) • u) ∈
      magneticClosedGraph b coupling p.core := by
    rw [← hA.graph_eq]
    exact heig
  have hb := core_exteriorMass_closedGraph hr₀ b coupling _ hgraph
  have hnorm : ‖u‖ ^ 2 = 1 := hu.norm_sq_eq_mass.trans hφ.2
  have hinner : (inner ℂ u ((atomicGroundEnergy b p.core coupling : ℂ) • u)).re =
      atomicGroundEnergy b p.core coupling := by
    rw [inner_smul_right, hu.inner_eq_waveInner hu, waveInner_self_eq_mass, hφ.2]
    simp
  simpa only [norm_l2Restrict_sq hu, Prod.fst, Prod.snd, hnorm, mul_one,
    hinner] using hb

/-- An O(coupling) energy excess gives O(1/coupling) exterior mass, using only
the classical eigenfunction and the already specified graph realization. -/
theorem core_exteriorMass_le_of_atomicGroundState {p : CuspParameters}
    (hr₀ : 0 < p.r₀) {b coupling B : ℝ} (hCoupling : 0 < coupling)
    (hA : IsMagneticRealization b coupling p.core)
    {φ : Wavefunction} (hφ : IsAtomicGroundState b p.core coupling φ)
    (hupper : (coupling⁻¹) ^ 2 * atomicGroundEnergy b p.core coupling ≤
      -1 + B / coupling) :
    (∫ x in {x : Plane | p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) ≤ B / coupling := by
  have hb := core_exteriorMass_le_groundEnergy hr₀ hA hφ
  have hscaled := mul_le_mul_of_nonneg_left hupper (sq_nonneg coupling)
  have hE : coupling ^ 2 * ((coupling⁻¹) ^ 2 *
      atomicGroundEnergy b p.core coupling) = atomicGroundEnergy b p.core coupling := by
    field_simp
  have hB : coupling ^ 2 * (-1 + B / coupling) =
      -coupling ^ 2 + coupling * B := by field_simp
  rw [hE, hB] at hscaled
  apply (le_div_iff₀ hCoupling).mpr
  have hb' : coupling ^ 2 *
      (∫ x in {x : Plane | p.r₀ ≤ ‖x‖}, ‖φ x‖ ^ 2) ≤ coupling * B := by
    linarith
  apply (mul_le_mul_iff_right₀ hCoupling).mp
  nlinarith only [hb']

end InfiniteZero.CuspParameters
