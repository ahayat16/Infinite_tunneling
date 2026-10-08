import InfiniteZero.MagneticModel
import InfiniteZero.Geometry

/-!
# The fixed potential, before either separation or coupling is chosen

This file defines the one-well potential of the manuscript's `sec:construction`:
the radial core (`eq:explicit-core`), the fixed cusp tips and frames
(`eq:fixed-tips`, `eq:fixed-frames`), the log-flat cusp profile
(`eq:log-flat-function`, `eq:chart`, `eq:cusp-def`), and their sum (`eq:final-v`).
The labels refer to `Infinite_Zero_Tunneling_Lean_oriented_V2.tex`.

`CuspParameters` contains the actual scalar parameters and cutoff functions;
`CuspParameters.BasicConditions` records elementary inequalities and cutoff
properties, not spectral or tunneling assumptions. Neither contains `L` or `λ`:
the same potential is fixed before separation and coupling are chosen.
`CuspParameters.admissiblePotential` in `ConstructionSmooth.lean` proves its
admissibility. `elementaryPotential_main` in `Remaining.lean` proves the final
conclusion for the explicit choice `CuspParameters.elementaryParameters`.
-/

noncomputable section

open scoped ContDiff

namespace InfiniteZero

/-- Data fixed in `sec:construction` before the separation `L` and semiclassical
parameter `h = λ⁻¹`. The potential itself is `CuspParameters.potential`.

The scalar `a` here is the cusp amplitude called `a_q` in `eq:cusp-def`, not the
support radius later called `a` in `eq:support-radius-a`. Likewise, `R` is the
distance of each cusp tip from the origin, not a radius bounding the full support.
The magnetic field strength `b` is fixed alongside the potential, but does not
occur in its pointwise formula. Positivity and compatibility are imposed by
`CuspParameters.BasicConditions`, not by this data structure. -/
structure CuspParameters where
  /-- Radius `r₀` of the compactly supported radial core (`eq:explicit-core`). -/
  r₀ : ℝ
  /-- Distance `R` of the two fixed cusp tips from the origin (`eq:fixed-tips`). -/
  R : ℝ
  /-- Magnetic field parameter `b`, fixed before `L` and `λ` (`eq:Dh`). -/
  b : ℝ
  /-- Weight `ε` of the sum of the exterior cusps in `eq:final-v`. -/
  ε : ℝ
  /-- Positive cusp amplitude `a_q` in `eq:cusp-def`. -/
  a : ℝ
  /-- Coefficient `β` in the log-flat factor `exp (-β log²(tStar / t))`. -/
  β : ℝ
  /-- Reference scale `t_*` in `ℓ(t) = log(t_* / t)` (`eq:log-flat-function`). -/
  tStar : ℝ
  /-- Upper bound `t₀` on the positive normal chart coordinate (`eq:chart`). -/
  t₀ : ℝ
  /-- Half-width `s₀` in the rescaled tangential chart coordinate (`eq:chart`). -/
  s₀ : ℝ
  /-- Smooth normal cutoff `χ_a(t)` appearing before and in `eq:cusp-def`. -/
  χa : ℝ → ℝ
  /-- Smooth even tangential cutoff `χ_b(s)` appearing before and in `eq:cusp-def`. -/
  χb : ℝ → ℝ

namespace CuspParameters

/-- The reflection `ℛ(x₁,x₂) = (x₁,-x₂)` of `eq:fixed-tips`, interchanging
the upper and lower cusps. Lean indexes the two coordinates by `0` and `1`.
This is distinct from the central inversion used to place the second well. -/
def reflection (x : Plane) : Plane := WithLp.toLp 2 ![x 0, -x 1]

/-- The exact reference potential `v°` of `eq:explicit-core`:
`-exp (-|x|² / (r₀² - |x|²))` for `|x| < r₀`, and zero otherwise.
For positive `r₀` this is a smooth compactly supported well with unique minimum
`-1` at the origin; these properties are proved separately. Neither the magnetic
field nor the cusp parameters enter this formula. -/
def core (p : CuspParameters) (x : Plane) : ℝ :=
  if ‖x‖ < p.r₀ then
    -Real.exp (-(‖x‖ ^ 2 / (p.r₀ ^ 2 - ‖x‖ ^ 2)))
  else 0

/-- The coefficient `t = (x - p₊) · n₊` in the upper orthonormal frame of
`eq:fixed-tips` and `eq:fixed-frames`, where
`p₊ = (R/2, √3 R/2)` and `n₊ = (-1/2, √3/2)`.
It is the first inverse coordinate of `Ψ₊(t,s) = p₊ + t n₊ + t² s τ₊`
in `eq:chart`. -/
def normalCoordinate (p : CuspParameters) (x : Plane) : ℝ :=
  -(x 0 - p.R / 2) / 2 + Real.sqrt 3 / 2 * (x 1 - Real.sqrt 3 * p.R / 2)

/-- The frame coefficient `(x - p₊) · τ₊`, with
`τ₊ = (-√3/2,-1/2)` from `eq:fixed-frames`.
On the chart `Ψ₊(t,s)` this equals `t² s`, not `s` itself. Thus `cuspPlus`
recovers the manuscript's coordinate `s` by dividing this value by `t²`. -/
def tangentCoordinate (p : CuspParameters) (x : Plane) : ℝ :=
  -Real.sqrt 3 / 2 * (x 0 - p.R / 2) - (x 1 - Real.sqrt 3 * p.R / 2) / 2

/-- The upper exterior cusp `q₊` in `eq:cusp-def`, written using the inverse
of `eq:chart`. Inside `0 < t < t₀`, `|s| < s₀` it is
`-a exp (-β log²(tStar / t)) χa(t) χb(s)`; outside it is zero.

The guard implements the one-sided chart and its zero extension, including zero
at the tip `t = 0`. The division defining `s` is total in Lean, but its value at
`t = 0` cannot contribute because the guard is false there. Smoothness across
the tip and all support boundaries is proved later from `BasicConditions`;
it is not presumed by this definition. -/
def cuspPlus (p : CuspParameters) (x : Plane) : ℝ :=
  let t := p.normalCoordinate x
  let s := p.tangentCoordinate x / t ^ 2
  if 0 < t ∧ t < p.t₀ ∧ |s| < p.s₀ then
    -p.a * Real.exp (-p.β * (Real.log (p.tStar / t)) ^ 2) * p.χa t * p.χb s
  else 0

/-- The reflected lower cusp `q₋ = q₊ ∘ ℛ` of `eq:cusp-def`.
Its tip is `(R/2,-√3 R/2)`, with the reflected frame of `eq:fixed-frames`. -/
def cuspMinus (p : CuspParameters) (x : Plane) : ℝ := p.cuspPlus (reflection x)

/-- The full fixed one-well potential `v = v° + ε(q₊ + q₋)` of `eq:final-v`.
This is an explicit function of the construction data, with no dependence on
`L`, `λ`, or `h`. `CuspParameters.admissiblePotential` proves smoothness,
compact support, range, and nonradiality from `BasicConditions`.
`potential_unique_minimum` and `potential_second_directional_derivative` in
`ConstructionMinimum.lean` separately prove the unchanged minimum and its
nondegeneracy. The double-well potential is formed from this same function
later, in `doubleWellPotential`; it is not the function defined here. -/
def potential (p : CuspParameters) (x : Plane) : ℝ :=
  p.core x + p.ε * (p.cuspPlus x + p.cuspMinus x)

/-- Elementary conditions on the construction data in `sec:construction`.

The first group fixes positive scales with `R > 8 r₀`. `depth_small` packages
`eq:epsilon-small` without introducing an auxiliary `δ₀`: a positive product
`ε a_q < 1/4` can itself be chosen as `δ₀`. `width_small` is the explicit
sufficient width inequality used in Lean for the one-sided geometry of
`lem:smooth-new`, replacing the instruction to decrease the chart widths.
The remaining fields state the cutoff conditions immediately before
`eq:cusp-def`; positivity of the integral of `χb` follows from its plateau
and range, so is not an extra field.

These are only elementary conditions on numbers and functions. In particular,
no existence of eigenfunctions, spectral gap, action certificate, or tunneling
asymptotic is assumed here. Subsequent theorems derive admissibility and the
required estimates; `CuspParameters.mainConclusion` in `Remaining.lean` obtains
the final conclusion from this predicate, using the three recorded classical
admissions. `elementaryParameters_basicConditions` supplies a concrete proof
of this predicate with no admission. -/
structure BasicConditions (p : CuspParameters) : Prop where
  /-- The radial reference well has positive radius. -/
  r₀_pos : 0 < p.r₀
  /-- The cusp tips are placed beyond eight core radii, as in `ssec:geometry`. -/
  radius_large : 8 * p.r₀ < p.R
  /-- The magnetic field has the orientation and positive strength used in the manuscript. -/
  b_pos : 0 < p.b
  /-- The cusps enter the potential with positive weight. -/
  ε_pos : 0 < p.ε
  /-- The cusp amplitude `a_q` is strictly positive. -/
  a_pos : 0 < p.a
  /-- The log-flat profile has a positive decay coefficient. -/
  β_pos : 0 < p.β
  /-- The one-sided chart has a nonempty normal interval. -/
  t₀_pos : 0 < p.t₀
  /-- The chart stays below the logarithmic reference scale; this also implies `tStar > 0`. -/
  t₀_lt : p.t₀ < p.tStar
  /-- The rescaled tangential interval has positive width. -/
  s₀_pos : 0 < p.s₀
  /-- Each weighted cusp has depth less than `1/4` (`eq:epsilon-small`). -/
  depth_small : p.ε * p.a < 1 / 4
  /-- Quantitative chart-width condition ensuring the required one-sided support geometry. -/
  width_small : Real.sqrt 3 * p.s₀ * p.t₀ ≤ 1 / 2
  /-- The normal cutoff is smooth on the whole real line. -/
  χa_smooth : ContDiff ℝ ∞ p.χa
  /-- The tangential cutoff is smooth on the whole real line. -/
  χb_smooth : ContDiff ℝ ∞ p.χb
  /-- The normal cutoff has compact support. -/
  χa_support : HasCompactSupport p.χa
  /-- The tangential cutoff has compact support. -/
  χb_support : HasCompactSupport p.χb
  /-- The normal cutoff takes values between zero and one. -/
  χa_range : ∀ t, p.χa t ∈ Set.Icc 0 1
  /-- The tangential cutoff takes values between zero and one. -/
  χb_range : ∀ s, p.χb s ∈ Set.Icc 0 1
  /-- The closed support of `χa` lies strictly inside the permitted cutoff interval. -/
  χa_localization : tsupport p.χa ⊆ Set.Ioo (-p.tStar / 2) p.t₀
  /-- The closed support of `χb` lies strictly inside the tangential chart interval. -/
  χb_localization : tsupport p.χb ⊆ Set.Ioo (-p.s₀) p.s₀
  /-- The normal cutoff is exactly one on a positive interval starting at the tip. -/
  χa_one : ∃ t₂, 0 < t₂ ∧ t₂ < p.t₀ ∧ ∀ t ∈ Set.Icc 0 t₂, p.χa t = 1
  /-- The tangential cutoff is exactly one on the middle half of its chart interval. -/
  χb_one : ∀ s ∈ Set.Icc (-p.s₀ / 2) (p.s₀ / 2), p.χb s = 1
  /-- The tangential cutoff is even, as required before `eq:cusp-def`. -/
  χb_even : ∀ s, p.χb (-s) = p.χb s

theorem BasicConditions.radius_pos {p : CuspParameters} (h : p.BasicConditions) :
    0 < p.R := by linarith [h.r₀_pos, h.radius_large]

@[simp] theorem reflection_involutive (x : Plane) : reflection (reflection x) = x := by
  ext i
  fin_cases i <;> simp [reflection]

@[simp] theorem norm_reflection (x : Plane) : ‖reflection x‖ = ‖x‖ := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, reflection]

@[simp] theorem core_reflection (p : CuspParameters) (x : Plane) :
    p.core (reflection x) = p.core x := by
  simp [core]

@[simp] theorem cuspPlus_reflection (p : CuspParameters) (x : Plane) :
    p.cuspPlus (reflection x) = p.cuspMinus x := rfl

@[simp] theorem cuspMinus_reflection (p : CuspParameters) (x : Plane) :
    p.cuspMinus (reflection x) = p.cuspPlus x := by
  simp [cuspMinus]

/-- The fixed potential has the horizontal-axis reflection symmetry required
by the two-cusp construction, for every choice of its parameters. -/
theorem potential_reflection (p : CuspParameters) (x : Plane) :
    p.potential (reflection x) = p.potential x := by
  simp [potential, add_comm]

/-- Cauchy--Schwarz bounds the outgoing normal coordinate. -/
theorem normalCoordinate_le_norm (p : CuspParameters) (x : Plane) :
    p.normalCoordinate x ≤ ‖x‖ - p.R / 2 := by
  let n : Plane := WithLp.toLp 2 ![-1 / 2, Real.sqrt 3 / 2]
  have hn : ‖n‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    norm_num [n, Fin.sum_univ_two, div_pow]
  have hi := real_inner_le_norm x n
  rw [hn, mul_one] at hi
  have he : inner ℝ x n = p.normalCoordinate x + p.R / 2 := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,
      n, normalCoordinate]
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  rw [he] at hi
  linarith

/-- The upper cusp vanishes throughout the core ball. This geometric separation
already follows from the radius condition and the positive-normal half-space. -/
theorem cuspPlus_eq_zero_of_norm_le {p : CuspParameters} (h : p.BasicConditions)
    {x : Plane} (hx : ‖x‖ ≤ p.r₀) : p.cuspPlus x = 0 := by
  have ht : ¬0 < p.normalCoordinate x := by
    have := normalCoordinate_le_norm p x
    linarith [h.r₀_pos, h.radius_large]
  simp [cuspPlus, ht]

theorem cuspMinus_eq_zero_of_norm_le {p : CuspParameters} (h : p.BasicConditions)
    {x : Plane} (hx : ‖x‖ ≤ p.r₀) : p.cuspMinus x = 0 := by
  apply cuspPlus_eq_zero_of_norm_le h
  simpa using hx

/-- The radial core and the two cusp components have disjoint nonzero sets. -/
theorem core_cusp_separation {p : CuspParameters} (h : p.BasicConditions) (x : Plane) :
    p.core x = 0 ∨ (p.cuspPlus x = 0 ∧ p.cuspMinus x = 0) := by
  by_cases hx : ‖x‖ < p.r₀
  · exact Or.inr ⟨cuspPlus_eq_zero_of_norm_le h hx.le,
      cuspMinus_eq_zero_of_norm_le h hx.le⟩
  · exact Or.inl (by simp [core, hx])

/-- The reference well always takes values in `[-1,0]`. -/
theorem core_range (p : CuspParameters) (x : Plane) : p.core x ∈ Set.Icc (-1) 0 := by
  unfold core
  split_ifs with hx
  · have hden : 0 < p.r₀ ^ 2 - ‖x‖ ^ 2 := by
      nlinarith [mul_self_lt_mul_self (norm_nonneg x) hx]
    have hex : Real.exp (-(‖x‖ ^ 2 / (p.r₀ ^ 2 - ‖x‖ ^ 2))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (sq_nonneg _) hden.le))
    exact ⟨by linarith, neg_nonpos.mpr (Real.exp_pos _).le⟩
  · norm_num

theorem core_zero {p : CuspParameters} (hr : 0 < p.r₀) : p.core 0 = -1 := by
  simp [core, hr]

/-- The minimum of the radial core is unique. This does not by itself establish
the minimum property of the full potential, whose component separation is separate. -/
theorem core_gt_neg_one {p : CuspParameters} {x : Plane} (hx : x ≠ 0) :
    -1 < p.core x := by
  unfold core
  split_ifs with hxr
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hden : 0 < p.r₀ ^ 2 - ‖x‖ ^ 2 := by
      nlinarith [mul_self_lt_mul_self hn.le hxr]
    have hex : Real.exp (-(‖x‖ ^ 2 / (p.r₀ ^ 2 - ‖x‖ ^ 2))) < 1 :=
      Real.exp_lt_one_iff.mpr (neg_neg_of_pos (div_pos (sq_pos_of_pos hn) hden))
    linarith
  · norm_num

theorem logFlatFactor_range {β : ℝ} (hβ : 0 ≤ β) (u : ℝ) :
    Real.exp (-β * u ^ 2) ∈ Set.Icc 0 1 := by
  exact ⟨(Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ) (sq_nonneg u))⟩

/-- The cusp depth is bounded by its fixed amplitude; no smoothness or
support-separation theorem is used in this estimate. -/
theorem cuspPlus_range {p : CuspParameters} (h : p.BasicConditions) (x : Plane) :
    p.cuspPlus x ∈ Set.Icc (-p.a) 0 := by
  unfold cuspPlus
  dsimp only
  split_ifs
  · have he := logFlatFactor_range h.β_pos.le (Real.log (p.tStar / p.normalCoordinate x))
    have ha := h.χa_range (p.normalCoordinate x)
    have hb := h.χb_range (p.tangentCoordinate x / p.normalCoordinate x ^ 2)
    have hzero := mul_nonneg (mul_nonneg he.1 ha.1) hb.1
    have hone := mul_le_one₀ (mul_le_one₀ he.2 ha.1 ha.2) hb.1 hb.2
    constructor <;> dsimp only [Set.mem_Icc] at * <;> nlinarith [h.a_pos]
  · exact ⟨by linarith [h.a_pos], le_rfl⟩

theorem cuspMinus_range {p : CuspParameters} (h : p.BasicConditions) (x : Plane) :
    p.cuspMinus x ∈ Set.Icc (-p.a) 0 :=
  cuspPlus_range h (reflection x)

theorem potential_nonpos {p : CuspParameters} (h : p.BasicConditions) (x : Plane) :
    p.potential x ≤ 0 := by
  exact add_nonpos (core_range p x).2
    (mul_nonpos_of_nonneg_of_nonpos h.ε_pos.le
      (add_nonpos (cuspPlus_range h x).2 (cuspMinus_range h x).2))

/-- Component separation is explicit here: wherever the core is nonzero,
both cusps must vanish. The elementary depth bound even permits the two cusps
to overlap; their stronger geometric disjointness is not needed for this range bound. -/
theorem potential_range_of_core_cusp_separation {p : CuspParameters}
    (h : p.BasicConditions)
    (hsep : ∀ x, p.core x = 0 ∨ (p.cuspPlus x = 0 ∧ p.cuspMinus x = 0))
    (x : Plane) : p.potential x ∈ Set.Icc (-1) 0 := by
  refine ⟨?_, potential_nonpos h x⟩
  rcases hsep x with hcore | ⟨hplus, hminus⟩
  · have hp := (cuspPlus_range h x).1
    have hm := (cuspMinus_range h x).1
    have hε := mul_le_mul_of_nonneg_left (show -2 * p.a ≤ p.cuspPlus x + p.cuspMinus x by
      linarith) h.ε_pos.le
    unfold potential
    rw [hcore]
    nlinarith [h.depth_small]
  · simpa [potential, hplus, hminus] using (core_range p x).1

/-- Every parameter set satisfying the stated elementary conditions gives the
required value range. Smoothness, compact support and nonradiality are separate. -/
theorem potential_range {p : CuspParameters} (h : p.BasicConditions) (x : Plane) :
    p.potential x ∈ Set.Icc (-1) 0 :=
  potential_range_of_core_cusp_separation h (core_cusp_separation h) x

/-- The phase coefficient is positive for every subsequently admissible L. -/
theorem phase_pos {p : CuspParameters} (h : p.BasicConditions)
    {L₀ L : ℝ} (hL₀ : p.R < L₀) (hL : L₀ ≤ L) :
    0 < Geometry.phaseStar p.b p.R L := by
  apply Geometry.phaseStar_pos h.b_pos h.radius_pos
  linarith [h.radius_pos]

end CuspParameters
end InfiniteZero
