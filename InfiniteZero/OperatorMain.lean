import InfiniteZero.Main
import InfiniteZero.OperatorBridge
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The main theorem as a statement about the actual L² Hamiltonian

Reviewer reading order: `ConstructedPotentialMainTheorem` fixes the potential
and the order of quantifiers; `OperatorMainConclusion` gives the conclusions
for a fixed separation; `MainConclusion` in `Main.lean` contains the three
items of the active TeX `thm:main`. The proofs `elementaryPotential_main` and
`thm_main` are in `Remaining.lean`.

The unbounded Hamiltonian is the closure of its specified test-function
graph on complex L² (`OperatorBridge.lean`), with the differential expression
of TeX `eq:double-well-unscaled`. At a large crossing we exhibit its lowest
eigenspace with complex dimension exactly two, both inversion parities, and
a positive gap on its orthogonal complement. This expresses the lowest
doublet assertion without choosing an enumeration of the entire discrete
spectrum. See `docs/STATEMENT_AUDIT.md` for the statement comparison.
-/

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace InfiniteZero

theorem AdmissiblePotential.bounded {v : Potential} (h : AdmissiblePotential v) :
    ∃ C : ℝ, ∀ x, |v x| ≤ C := by
  refine ⟨1, fun x => ?_⟩
  rw [abs_le]
  have hx := h.range x
  exact ⟨hx.1, le_trans hx.2 (by norm_num)⟩

theorem AdmissiblePotential.doubleWell_smooth {v : Potential}
    (h : AdmissiblePotential v) (L : ℝ) : ContDiff ℝ ∞ (doubleWellPotential v L) := by
  exact (h.smooth.comp (contDiff_id.add contDiff_const)).add
    (h.smooth.comp (contDiff_id.neg.add contDiff_const))

theorem AdmissiblePotential.doubleWell_bounded {v : Potential}
    (h : AdmissiblePotential v) (L : ℝ) :
    ∃ C : ℝ, ∀ x, |doubleWellPotential v L x| ≤ C := by
  refine ⟨2, fun x => ?_⟩
  have hleft := h.range (x + displacement L)
  have hright := h.range (-x + displacement L)
  rw [abs_le]
  dsimp [doubleWellPotential]
  constructor <;> linarith [hleft.1, hleft.2, hright.1, hright.2]

/-- The full eigenspace in physical complex L² of `H_v(λ)` at the energy
`groundEnergy b v L λ`. Here `coupling = λ` and `d = (L,0)` in TeX
`eq:double-well-unscaled`. Its elements belong to the actual operator
domain. The realization and existence fields of `OperatorMainConclusion`
justify calling this variationally defined energy the attained lowest level. -/
def OperatorGroundSpace (b : ℝ) (v : Potential) (L coupling : ℝ) : Submodule ℂ L2Space :=
  operatorEigenspace (magneticOperator b coupling (doubleWellPotential v L))
    (groundEnergy b v L coupling)

/-- The full L² ground eigenspace has complex dimension one and contains
a nonzero vector of the indicated inversion parity, almost everywhere:
`even = true` means `u(-x) = u(x)`, and `false` means `u(-x) = -u(x)`.
This is the simple-ground-state assertion used at the alternating samples
in TeX `thm:main` (iii). -/
def OperatorSimpleParity (b : ℝ) (v : Potential) (L coupling : ℝ) (even : Bool) : Prop :=
  Module.finrank ℂ (OperatorGroundSpace b v L coupling) = 1 ∧
    ∃ u : L2Space, u ∈ OperatorGroundSpace b v L coupling ∧ u ≠ 0 ∧ HasL2Parity even u

theorem transfer_simple_parity {b L coupling : ℝ} {v : Potential} {even : Bool}
    (h : IsMagneticRealization b coupling (doubleWellPotential v L))
    (hg : SimpleGroundParity b v L coupling even) : OperatorSimpleParity b v L coupling even := by
  refine ⟨transfer_simple_ground h hg, ?_⟩
  obtain ⟨G, hG, _, ψ, hψ, hm, hp⟩ := hg
  exact h.transfer_normalized_parity_eigenfunction ((hG ψ).mp hψ) hm hp

/-- The multiplicity clause of TeX `thm:main` (i): the full L² eigenspace
at `groundEnergy` has complex dimension exactly two and contains nonzero
even and odd vectors. Together with the lower bound in
`OperatorMainConclusion.realization` and the gap in
`OperatorMainConclusion.eventual_ground_gap`, this gives an isolated
lowest level counted twice. No enumeration of the remaining spectrum is
part of this predicate. -/
def OperatorDoubleGround (b : ℝ) (v : Potential) (L coupling : ℝ) : Prop :=
  Module.finrank ℂ (OperatorGroundSpace b v L coupling) = 2 ∧
    ∃ uEven uOdd : L2Space,
      uEven ∈ OperatorGroundSpace b v L coupling ∧
      uOdd ∈ OperatorGroundSpace b v L coupling ∧
      uEven ≠ 0 ∧ uOdd ≠ 0 ∧ HasL2Parity true uEven ∧ HasL2Parity false uOdd

/-- Operator formulation of all three items of the active TeX `thm:main`,
at fixed `b`, `v` and half-separation `L`. `variational` includes both exact
zero sequences and the intrinsic complex hopping coefficient of
`eq:rho-intro`. The additional fields identify the concrete self-adjoint
Hamiltonians and describe their genuine lowest L² eigenspaces.


The gap is positive for each sufficiently large λ; this structure does not
require a single positive gap uniform in λ or in L. All large-coupling
thresholds and exceptional sequences may depend on L. The existence of
arbitrarily large isolated double ground levels is extracted explicitly by
`OperatorMainConclusion.arbitrarily_large_operator_crossings`. -/
structure OperatorMainConclusion (b : ℝ) (v : Potential) (L : ℝ) : Prop where
  /-- The classical/variational version of items (i)--(iii), including
  normalized atomic states and the zeros of the actual complex hopping. -/
  variational : MainConclusion b v L
  /-- Realization of the single-well `h_v(λ)` from `eq:one-well-unscaled`:
  its test-graph closure is self-adjoint and agrees with the variational
  and smooth-eigenfunction descriptions. -/
  atomic_realization : ∀ coupling, IsMagneticRealization b coupling v
  /-- The same realization for `H_v(λ)` from `eq:double-well-unscaled`.
  In particular, its variational bottom bounds the quadratic expression
  from below on every vector of its operator domain. -/
  realization : ∀ coupling, IsMagneticRealization b coupling (doubleWellPotential v L)
  /-- At each sufficiently large λ there is a strictly positive energy
  gap above the full ground eigenspace, expressed on its orthogonal
  complement in the operator domain. This also holds at a crossing. -/
  eventual_ground_gap : ∃ T, ∀ coupling, T ≤ coupling →
    HasGapAboveGround (magneticOperator b coupling (doubleWellPotential v L))
      (groundEnergy b v L coupling)
  /-- TeX `thm:main` (i), operator multiplicity clause: every sufficiently
  large zero of the min-max gap has a two-dimensional L² ground space
  with both inversion parities. -/
  large_operator_crossings : ∃ T, ∀ coupling, T ≤ coupling →
    secondEnergy b v L coupling - groundEnergy b v L coupling = 0 →
      OperatorDoubleGround b v L coupling
  /-- TeX `thm:main` (iii): interlaced positive couplings tending to
  infinity, with a simple even ground state at `p_n` and a simple odd
  ground state at `q_n`, now as eigenspaces of the unbounded operator. -/
  operator_parity_changes : ∃ p q : ℕ → ℝ,
    Tendsto p atTop atTop ∧ Tendsto q atTop atTop ∧
    ∀ n, 0 < p n ∧ p n < q n ∧ q n < p (n + 1) ∧
      OperatorSimpleParity b v L (p n) true ∧ OperatorSimpleParity b v L (q n) false

/-- Direct operator content of item (i), avoiding an enumeration of the entire
discrete spectrum: arbitrarily large couplings have an isolated, genuinely
two-dimensional lowest eigenspace with both parities. -/
theorem OperatorMainConclusion.arbitrarily_large_operator_crossings
    {b L : ℝ} {v : Potential} (h : OperatorMainConclusion b v L) (T : ℝ) :
    ∃ coupling : ℝ, T < coupling ∧ OperatorDoubleGround b v L coupling ∧
      HasGapAboveGround (magneticOperator b coupling (doubleWellPotential v L))
        (groundEnergy b v L coupling) := by
  obtain ⟨z, _, hztop, hz⟩ := h.variational.spectral_zeros
  obtain ⟨Tc, hTc⟩ := h.large_operator_crossings
  obtain ⟨Tg, hTg⟩ := h.eventual_ground_gap
  have hevent : ∀ᶠ n in atTop, max T (max Tc Tg) < z n :=
    hztop.eventually (eventually_gt_atTop _)
  obtain ⟨n, hn⟩ := hevent.exists
  have htc : Tc ≤ z n :=
    (le_trans (le_max_left Tc Tg) (le_max_right T (max Tc Tg))).trans hn.le
  have htg : Tg ≤ z n :=
    (le_trans (le_max_right Tc Tg) (le_max_right T (max Tc Tg))).trans hn.le
  exact ⟨z n, lt_of_le_of_lt (le_max_left T (max Tc Tg)) hn,
    hTc _ htc (hz n).2, hTg _ htg⟩

theorem MainConclusion.toOperator {b L : ℝ} {v : Potential} (h : MainConclusion b v L)
    (ha : ∀ coupling, IsMagneticRealization b coupling v)
    (hr : ∀ coupling, IsMagneticRealization b coupling (doubleWellPotential v L))
    (hg : ∃ T, ∀ coupling, T ≤ coupling →
      HasGapAboveGround (magneticOperator b coupling (doubleWellPotential v L))
        (groundEnergy b v L coupling)) :
    OperatorMainConclusion b v L := by
  refine ⟨h, ha, hr, hg, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := h.large_crossings
    refine ⟨T, fun coupling hc hz => ?_⟩
    have hg := hT coupling hc hz
    exact ⟨transfer_ground_exactly_two (hr coupling) hg,
      transfer_ground_parity_modes (hr coupling) hg⟩
  · obtain ⟨p, q, hp, hq, hs⟩ := h.parity_changes
    refine ⟨p, q, hp, hq, fun n => ?_⟩
    obtain ⟨hpos, hpq, hqp, he, ho⟩ := hs n
    exact ⟨hpos, hpq, hqp, transfer_simple_parity (hr (p n)) he,
      transfer_simple_parity (hr (q n)) ho⟩

/-- The existential quantifiers of the active TeX `thm:main`:
there exist `b > 0`, `L₀ > 0`, and one smooth compactly supported nonradial
potential valued in `[-1,0]`, such that all three conclusions hold for
every `L ≥ L₀`. `AdmissiblePotential` records exactly these four properties;
the constructed well's unique nondegenerate minimum is proved separately
in `ConstructionMinimum.lean`. The zero sequences are chosen inside
`OperatorMainConclusion`, after fixing L, so they may depend on L.
`ConstructedPotentialMainTheorem.toOperatorMainTheorem` deduces this
statement from the explicit-construction version used by `thm_main`. -/
def OperatorMainTheorem : Prop :=
  ∃ b L₀ : ℝ, ∃ v : Potential,
    0 < b ∧ 0 < L₀ ∧ AdmissiblePotential v ∧
      ∀ L, L₀ ≤ L → OperatorMainConclusion b v L

/-- The proposition proved by `thm_main`, strengthening the existential
potential in the active TeX `thm:main` to the specified construction of
`sec:construction`, `eq:explicit-core`, `eq:cusp-def`, and `eq:final-v`.
It says: there is a parameter record p, satisfying the elementary geometric
and cutoff conditions, whose potential
`p.core + p.ε * (p.cuspPlus + p.cuspMinus)` is admissible; there is then
`L₀ > p.R` such that all three operator conclusions hold for every `L ≥ L₀`.

All scalars and both cutoff functions are contained in `CuspParameters`.
That record contains neither L nor λ. Thus the order is: fix p (hence b
and v), choose L₀, fix any L ≥ L₀, then obtain the sequences of couplings.
`p.BasicConditions` and admissibility are conclusions to prove for the
witness, not premises supplied by the caller. Positivity of b and L₀
follows from `BasicConditions` and `p.R < L₀`.

The actual witness is `CuspParameters.elementaryParameters`; the stronger
theorem `elementaryPotential_main` in `Remaining.lean` states the result
with that witness written literally in its type. For the three items,
unfold `OperatorMainConclusion` and then `MainConclusion`; for v, follow
`CuspParameters.potential` in `Construction.lean`. No spectral or tunneling
data are hypotheses of this proposition. The three remaining classical
admissions are listed at `thm_main` and in `docs/ADMISSIONS.md`. The
conditional assembly retains an elliptic-estimate interface, which is
supplied by a proved theorem. -/
def ConstructedPotentialMainTheorem : Prop :=
  ∃ p : CuspParameters, p.BasicConditions ∧ AdmissiblePotential p.potential ∧
    ∃ L₀ : ℝ, p.R < L₀ ∧ ∀ L, L₀ ≤ L → OperatorMainConclusion p.b p.potential L

theorem ConstructedPotentialMainTheorem.toOperatorMainTheorem
    (h : ConstructedPotentialMainTheorem) : OperatorMainTheorem := by
  obtain ⟨p, hp, hv, L₀, hL₀, hconcl⟩ := h
  exact ⟨p.b, L₀, p.potential, hp.b_pos, hp.radius_pos.trans hL₀, hv, hconcl⟩

/-- Auxiliary conditional assembly for the constructed potential.
This is NOT the final theorem: the argument `h` still has to be constructed. -/
theorem constructed_main_of_analytic_data (h : FixedAnalyticData)
    (hKernel : HasPositiveLandauResolvent h.parameters.b)
    (ha : ∀ coupling, IsMagneticRealization h.parameters.b coupling h.parameters.potential)
    (hr : ∀ L coupling, IsMagneticRealization h.parameters.b coupling
      (doubleWellPotential h.parameters.potential L)) : ConstructedPotentialMainTheorem := by
  refine ⟨h.parameters, h.basic, h.admissible, h.L₀, h.separation, fun L hL => ?_⟩
  exact ((h.localData L hL).conclusion h.basic hKernel
    (by linarith [h.basic.radius_pos, h.separation])
    (CuspParameters.phase_pos h.basic h.separation hL)).toOperator ha (hr L)
    ⟨(h.localData L hL).threshold, (h.localData L hL).ground_gap⟩

/-- The original analytic data and the two classical interfaces are explicit arguments. -/
theorem thm_main_operator_of_analytic_data (h : FixedAnalyticData)
    (hKernel : HasPositiveLandauResolvent h.parameters.b)
    (ha : ∀ coupling, IsMagneticRealization h.parameters.b coupling h.parameters.potential)
    (hr : ∀ L coupling, IsMagneticRealization h.parameters.b coupling
      (doubleWellPotential h.parameters.potential L)) : OperatorMainTheorem := by
  refine ⟨h.parameters.b, h.L₀, h.parameters.potential, h.basic.b_pos,
    lt_trans h.basic.radius_pos h.separation, h.admissible, fun L hL => ?_⟩
  exact ((h.localData L hL).conclusion h.basic hKernel
    (by linarith [h.basic.radius_pos, h.separation])
    (CuspParameters.phase_pos h.basic h.separation hL)).toOperator ha (hr L)
    ⟨(h.localData L hL).threshold, (h.localData L hL).ground_gap⟩

end InfiniteZero
