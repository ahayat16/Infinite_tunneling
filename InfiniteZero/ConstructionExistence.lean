import InfiniteZero.ConstructionSmooth
import InfiniteZero.ConstructionParameters
import InfiniteZero.ConstructionMinimum
import InfiniteZero.ConstructionSupportSeparation
import InfiniteZero.ConstructionCuspJets

/-!
# An explicit admissible nonradial potential

These existence results have no analytic admission. They certify the elementary
construction requirements and the admissibility claimed in `lem:smooth-new`
of `Infinite_Zero_Tunneling_Lean_oriented_V2.tex` for the fixed witness
`elementaryParameters`. The spectral and tunneling conclusions are established
later for this same witness by `elementaryPotential_main` in `Remaining.lean`,
modulo the four recorded classical admissions.
-/

namespace InfiniteZero.CuspParameters

/-- The concrete potential used by `elementaryPotential_main` is smooth,
compactly supported, takes values in `[-1,0]`, and is nonradial. These are the
four fields of `AdmissiblePotential`, corresponding to part of `lem:smooth-new`.
The unchanged unique nondegenerate minimum is established separately by
`potential_unique_minimum` and `potential_second_directional_derivative` in
`ConstructionMinimum.lean`. None of these construction proofs assumes a
spectral or tunneling conclusion. -/
theorem elementaryParameters_admissible :
    AdmissiblePotential elementaryParameters.potential :=
  admissiblePotential elementaryParameters_basicConditions

/-- The construction family contains an admissible potential satisfying the
elementary parameter conditions, witnessed by `elementaryParameters` itself.
This records only the potential construction; `thm_main` later proves the
spectral and hopping conclusions for that witness as well. -/
theorem exists_admissible_cuspPotential :
    ∃ p : CuspParameters, p.BasicConditions ∧ AdmissiblePotential p.potential :=
  ⟨elementaryParameters, elementaryParameters_basicConditions, elementaryParameters_admissible⟩

end InfiniteZero.CuspParameters
