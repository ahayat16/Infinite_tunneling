import InfiniteZero.Construction
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# An explicit witness for the elementary construction conditions

We choose all scalar parameters explicitly and use mathlib's smooth bump
functions for the two cutoffs required before `eq:cusp-def` in
`Infinite_Zero_Tunneling_Lean_oriented_V2.tex`. The manuscript permits choices
of these parameters and cutoffs; the numerical values and mathlib bump functions
below specify one such choice and are implementation choices, not additional
formulas asserted in the manuscript.

This module proves `BasicConditions` for that choice without admissions.
Admissibility is proved in `ConstructionExistence.lean`, and the spectral and
tunneling conclusions for this very same potential are proved later by
`elementaryPotential_main` in `Remaining.lean`, modulo the four recorded
classical admissions. No further adjustment of this witness is made there.
-/

noncomputable section

open scoped ContDiff

namespace InfiniteZero.CuspParameters

/-- The explicit choice of `χ_a` from the cutoff paragraph before `eq:cusp-def`.
This is mathlib's smooth bump centered at zero, taking values in `[0,1]`,
equal to one on `[-1/400,1/400]`, and zero for `|t| ≥ 1/200`.
Its closed support lies inside the required interval `(-tStar/2,t₀)` for
`elementaryParameters`. The cusp uses only its positive-normal part; negative
arguments allow the cutoff itself to be globally smooth around zero. -/
def elementaryNormalCutoff : ContDiffBump (0 : ℝ) where
  rIn := 1 / 400
  rOut := 1 / 200
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The explicit choice of the even cutoff `χ_b` before `eq:cusp-def`.
This is mathlib's smooth bump centered at zero, taking values in `[0,1]`,
equal to one on `[-1/2,1/2]`, and zero for `|s| ≥ 3/4`.
For `elementaryParameters`, `s₀ = 1`, so both the support condition and the
required plateau on `[-s₀/2,s₀/2]` hold. -/
def elementaryTangentialCutoff : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 3 / 4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The particular construction used in the final theorem:
`r₀ = 1`, `R = 16`, `b = 1`, `ε = 1/16`,
`a = β = tStar = s₀ = 1`, and `t₀ = 1/100`, with the two bumps above.

Thus the cusp tips are `(8, ±8√3)`, and the one-well potential is exactly
`elementaryParameters.core + (1/16) * (cuspPlus + cuspMinus)`, with core and
cusps evaluated at these parameters. This specializes the family in
`eq:explicit-core`--`eq:final-v`; the manuscript does not specify these numbers.
All choices precede `L` and `λ`. `elementaryParameters_basicConditions`
checks their elementary compatibility, and `elementaryPotential_main` in
`Remaining.lean` establishes the final spectral and hopping conclusions for
this same potential for every sufficiently large separation. -/
def elementaryParameters : CuspParameters where
  r₀ := 1
  R := 16
  b := 1
  ε := 1 / 16
  a := 1
  β := 1
  tStar := 1
  t₀ := 1 / 100
  s₀ := 1
  χa := elementaryNormalCutoff
  χb := elementaryTangentialCutoff

/-- Direct verification of every scalar inequality, cutoff support, plateau,
range, smoothness, and symmetry requirement in `BasicConditions` for the fixed
witness. This proof has no analytic admission; the later spectral and tunneling
proofs use this certificate without changing `elementaryParameters`. -/
theorem elementaryParameters_basicConditions : elementaryParameters.BasicConditions := by
  refine {
    r₀_pos := by norm_num [elementaryParameters]
    radius_large := by norm_num [elementaryParameters]
    b_pos := by norm_num [elementaryParameters]
    ε_pos := by norm_num [elementaryParameters]
    a_pos := by norm_num [elementaryParameters]
    β_pos := by norm_num [elementaryParameters]
    t₀_pos := by norm_num [elementaryParameters]
    t₀_lt := by norm_num [elementaryParameters]
    s₀_pos := by norm_num [elementaryParameters]
    depth_small := by norm_num [elementaryParameters]
    width_small := ?_
    χa_smooth := elementaryNormalCutoff.contDiff
    χb_smooth := elementaryTangentialCutoff.contDiff
    χa_support := elementaryNormalCutoff.hasCompactSupport
    χb_support := elementaryTangentialCutoff.hasCompactSupport
    χa_range := fun _ => ⟨elementaryNormalCutoff.nonneg, elementaryNormalCutoff.le_one⟩
    χb_range := fun _ => ⟨elementaryTangentialCutoff.nonneg, elementaryTangentialCutoff.le_one⟩
    χa_localization := ?_
    χb_localization := ?_
    χa_one := ?_
    χb_one := ?_
    χb_even := elementaryTangentialCutoff.neg }
  · norm_num [elementaryParameters]
    have hs : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  · intro t ht
    change t ∈ tsupport elementaryNormalCutoff at ht
    rw [elementaryNormalCutoff.tsupport_eq, Real.closedBall_eq_Icc] at ht
    norm_num [elementaryNormalCutoff, Set.mem_Icc] at ht
    change -(1 : ℝ) / 2 < t ∧ t < 1 / 100
    constructor <;> linarith [ht.1, ht.2]
  · intro s hs
    change s ∈ tsupport elementaryTangentialCutoff at hs
    rw [elementaryTangentialCutoff.tsupport_eq, Real.closedBall_eq_Icc] at hs
    norm_num [elementaryTangentialCutoff, Set.mem_Icc] at hs
    change -(1 : ℝ) < s ∧ s < 1
    constructor <;> linarith [hs.1, hs.2]
  · refine ⟨1 / 400, by norm_num, by norm_num [elementaryParameters], ?_⟩
    intro t ht
    apply elementaryNormalCutoff.one_of_mem_closedBall
    rw [Real.closedBall_eq_Icc]
    norm_num [elementaryNormalCutoff, Set.mem_Icc]
    exact ⟨by linarith [ht.1], ht.2⟩
  · intro s hs
    apply elementaryTangentialCutoff.one_of_mem_closedBall
    norm_num [Real.closedBall_eq_Icc, elementaryTangentialCutoff, elementaryParameters] at hs ⊢
    exact hs

/-- Nonemptiness of the elementary parameter constraints, with no analytic admission. -/
theorem exists_basicConditions : ∃ p : CuspParameters, p.BasicConditions :=
  ⟨elementaryParameters, elementaryParameters_basicConditions⟩

end InfiniteZero.CuspParameters
