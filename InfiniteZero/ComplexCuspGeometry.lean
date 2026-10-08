import InfiniteZero.GeometryActionSlopes
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Holomorphic radii of the polynomial cusp charts

The complex radius uses the bilinear square, not the Hermitian norm.
Its principal square-root branch agrees with the Euclidean radius on real
points and is holomorphic when the bilinear square has positive real part.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace InfiniteZero.Geometry

attribute [local fun_prop] analyticAt_fst analyticAt_snd

abbrev ComplexPoint := ℂ × ℂ

def complexifyPoint (p : Point) : ComplexPoint := ((p.1 : ℂ), (p.2 : ℂ))

def complexSqNorm (z : ComplexPoint) : ℂ := z.1 ^ 2 + z.2 ^ 2

def complexRadius (z : ComplexPoint) : ℂ := Complex.sqrt (complexSqNorm z)

def polynomialCuspChart (p n τ : Point) (s : ℝ) (t : ℂ) : ComplexPoint :=
  ((p.1 : ℂ) + t * (n.1 : ℂ) + (s : ℂ) * t ^ 2 * (τ.1 : ℂ),
   (p.2 : ℂ) + t * (n.2 : ℂ) + (s : ℂ) * t ^ 2 * (τ.2 : ℂ))

def complexCuspPlus (R s : ℝ) : ℂ → ComplexPoint :=
  polynomialCuspChart (tipPlus R) normalPlus tangentPlus s

def complexCuspMinus (R r : ℝ) : ℂ → ComplexPoint :=
  polynomialCuspChart (tipMinus R) normalMinus tangentMinus r

def complexBridge (L : ℝ) (z w : ComplexPoint) : ComplexPoint :=
  (z.1 + w.1 - 2 * (L : ℂ), z.2 + w.2)

@[simp] theorem polynomialCuspChart_zero (p n τ : Point) (s : ℝ) :
    polynomialCuspChart p n τ s 0 = complexifyPoint p := by
  simp [polynomialCuspChart, complexifyPoint]

@[simp] theorem complexSqNorm_complexifyPoint (p : Point) :
    complexSqNorm (complexifyPoint p) = (sqNorm p : ℂ) := by
  simp [complexSqNorm, complexifyPoint, sqNorm]

@[simp] theorem complexBridge_complexifyPoint (L : ℝ) (z w : Point) :
    complexBridge L (complexifyPoint z) (complexifyPoint w) =
      complexifyPoint (bridge L z w) := by
  ext <;> simp [complexBridge, complexifyPoint, bridge]

/-- Agreement with the actual Euclidean radius, including the zero vector. -/
theorem complexRadius_complexifyPoint (p : Point) :
    complexRadius (complexifyPoint p) = (length p : ℂ) := by
  rw [complexRadius, complexSqNorm_complexifyPoint, Complex.sqrt_of_nonneg]
  · rfl
  · exact_mod_cast (show 0 ≤ sqNorm p by dsimp [sqNorm]; positivity)

theorem complexRadius_complexBridge_real (L : ℝ) (z w : Point) :
    complexRadius (complexBridge L (complexifyPoint z) (complexifyPoint w)) =
      (length (bridge L z w) : ℂ) := by
  rw [complexBridge_complexifyPoint, complexRadius_complexifyPoint]

@[simp] theorem complexRadius_cuspPlus_zero {R : ℝ} (hR : 0 ≤ R) (s : ℝ) :
    complexRadius (complexCuspPlus R s 0) = (R : ℂ) := by
  rw [complexCuspPlus, polynomialCuspChart_zero, complexRadius_complexifyPoint, length_tipPlus hR]

@[simp] theorem complexRadius_cuspMinus_zero {R : ℝ} (hR : 0 ≤ R) (r : ℝ) :
    complexRadius (complexCuspMinus R r 0) = (R : ℂ) := by
  rw [complexCuspMinus, polynomialCuspChart_zero, complexRadius_complexifyPoint, length_tipMinus hR]

@[simp] theorem complexRadius_bridge_zero {R L : ℝ} (hL : R < 2 * L) (s r : ℝ) :
    complexRadius (complexBridge L (complexCuspPlus R s 0) (complexCuspMinus R r 0)) =
      (activeDistance R L : ℂ) := by
  rw [complexCuspPlus, complexCuspMinus, polynomialCuspChart_zero,
    polynomialCuspChart_zero, complexRadius_complexBridge_real, length_bridge_cross hL]

theorem polynomialCuspChart_real (p n τ : Point) (s t : ℝ) :
    polynomialCuspChart p n τ s (t : ℂ) =
      complexifyPoint (p.1 + t * n.1 + s * t ^ 2 * τ.1,
        p.2 + t * n.2 + s * t ^ 2 * τ.2) := by
  ext <;> simp [polynomialCuspChart, complexifyPoint]

theorem complexRadius_polynomialCuspChart_real (p n τ : Point) (s t : ℝ) :
    complexRadius (polynomialCuspChart p n τ s (t : ℂ)) =
      (length (p.1 + t * n.1 + s * t ^ 2 * τ.1,
        p.2 + t * n.2 + s * t ^ 2 * τ.2) : ℂ) := by
  rw [polynomialCuspChart_real, complexRadius_complexifyPoint]

theorem analyticAt_complexRadius {z : ComplexPoint} (hz : 0 < (complexSqNorm z).re) :
    AnalyticAt ℂ complexRadius z := by
  have hs : complexSqNorm z ∈ Complex.slitPlane := Or.inl hz
  have ha := Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds hs)
  exact ha.comp (by unfold complexSqNorm; fun_prop)

private theorem hasDerivAt_complex_sqrt_div {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt Complex.sqrt (1 / (2 * Complex.sqrt z)) z := by
  convert Complex.hasDerivAt_sqrt hz using 1
  rw [show (-1 / 2 : ℂ) = -(2⁻¹ : ℂ) by norm_num, Complex.cpow_neg]
  unfold Complex.sqrt
  ring

theorem hasDerivAt_complexSqNorm_polynomialCuspChart_zero (p n τ : Point) (s : ℝ) :
    HasDerivAt (fun t : ℂ => complexSqNorm (polynomialCuspChart p n τ s t))
      (2 * (dot p n : ℂ)) 0 := by
  have hd (a b d : ℝ) : HasDerivAt
      (fun t : ℂ => (a : ℂ) + t * (b : ℂ) + (s : ℂ) * t ^ 2 * (d : ℂ)) (b : ℂ) 0 := by
    convert (((hasDerivAt_id (0 : ℂ)).mul_const (b : ℂ)).const_add (a : ℂ)).add
      ((((hasDerivAt_id (0 : ℂ)).pow 2).const_mul (s : ℂ)).mul_const (d : ℂ)) using 1
    norm_num
  convert ((hd p.1 n.1 τ.1).pow 2).add ((hd p.2 n.2 τ.2).pow 2) using 1
  simp [dot]
  ring

/-- Quadratic tangential displacement contributes no first derivative. -/
theorem hasDerivAt_complexRadius_polynomialCuspChart_zero {r : ℝ} (hr : 0 < r)
    {p n : Point} (hp : sqNorm p = r ^ 2) (hd : dot p n = r / 2)
    (τ : Point) (s : ℝ) :
    HasDerivAt (fun t : ℂ => complexRadius (polynomialCuspChart p n τ s t))
      (1 / 2 : ℂ) 0 := by
  have hz : (r ^ 2 : ℝ) > 0 := sq_pos_of_pos hr
  have hval : complexSqNorm (polynomialCuspChart p n τ s 0) = (r ^ 2 : ℝ) := by
    simp [hp]
  have hs := (hasDerivAt_complex_sqrt_div (Complex.ofReal_mem_slitPlane.2 hz)).comp_of_eq 0
    (hasDerivAt_complexSqNorm_polynomialCuspChart_zero p n τ s) hval.symm
  convert hs using 1
  rw [hd, Complex.sqrt_of_nonneg (by exact_mod_cast hz.le)]
  simp only [Complex.ofReal_re, Real.sqrt_sq hr.le]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hr.ne']

theorem hasDerivAt_complexRadius_cuspPlus_zero {R : ℝ} (hR : 0 < R) (s : ℝ) :
    HasDerivAt (fun t : ℂ => complexRadius (complexCuspPlus R s t)) (1 / 2 : ℂ) 0 :=
  hasDerivAt_complexRadius_polynomialCuspChart_zero hR (sqNorm_tipPlus R)
    (tipPlus_dot_normalPlus R) tangentPlus s

theorem hasDerivAt_complexRadius_cuspMinus_zero {R : ℝ} (hR : 0 < R) (r : ℝ) :
    HasDerivAt (fun u : ℂ => complexRadius (complexCuspMinus R r u)) (1 / 2 : ℂ) 0 :=
  hasDerivAt_complexRadius_polynomialCuspChart_zero hR (sqNorm_tipMinus R)
    (tipMinus_dot_normalMinus R) tangentMinus r

theorem complexBridge_polynomialCuspChart_left (L : ℝ) (p n τ w : Point) (s : ℝ) (t : ℂ) :
    complexBridge L (polynomialCuspChart p n τ s t) (complexifyPoint w) =
      polynomialCuspChart (bridge L p w) n τ s t := by
  ext <;> simp [complexBridge, polynomialCuspChart, complexifyPoint, bridge] <;> ring

theorem complexBridge_polynomialCuspChart_right (L : ℝ) (p w n τ : Point) (r : ℝ) (u : ℂ) :
    complexBridge L (complexifyPoint p) (polynomialCuspChart w n τ r u) =
      polynomialCuspChart (bridge L p w) n τ r u := by
  ext <;> simp [complexBridge, polynomialCuspChart, complexifyPoint, bridge] <;> ring

theorem hasDerivAt_complexRadius_bridge_left_zero {R L : ℝ} (hL : R < 2 * L) (s r : ℝ) :
    HasDerivAt (fun t : ℂ => complexRadius
      (complexBridge L (complexCuspPlus R s t) (complexCuspMinus R r 0))) (1 / 2 : ℂ) 0 := by
  simp only [complexCuspPlus, complexCuspMinus, polynomialCuspChart_zero,
    complexBridge_polynomialCuspChart_left]
  exact hasDerivAt_complexRadius_polynomialCuspChart_zero (activeDistance_pos hL)
    (sqNorm_bridge_cross R L) (dot_bridge_normalPlus R L) tangentPlus s

theorem hasDerivAt_complexRadius_bridge_right_zero {R L : ℝ} (hL : R < 2 * L) (s r : ℝ) :
    HasDerivAt (fun u : ℂ => complexRadius
      (complexBridge L (complexCuspPlus R s 0) (complexCuspMinus R r u))) (1 / 2 : ℂ) 0 := by
  simp only [complexCuspPlus, complexCuspMinus, polynomialCuspChart_zero,
    complexBridge_polynomialCuspChart_right]
  exact hasDerivAt_complexRadius_polynomialCuspChart_zero (activeDistance_pos hL)
    (sqNorm_bridge_cross R L) (dot_bridge_normalMinus R L) tangentMinus r

/-- A concrete simultaneous branch domain for the three bilinear radii. -/
def complexCuspRadiusDomain (R L s r : ℝ) : Set ComplexPoint :=
  {q | 0 < (complexSqNorm (complexCuspPlus R s q.1)).re ∧
    0 < (complexSqNorm (complexCuspMinus R r q.2)).re ∧
    0 < (complexSqNorm (complexBridge L (complexCuspPlus R s q.1)
      (complexCuspMinus R r q.2))).re}

theorem isOpen_complexCuspRadiusDomain (R L s r : ℝ) :
    IsOpen (complexCuspRadiusDomain R L s r) := by
  apply IsOpen.inter
  · exact isOpen_lt (continuous_const (y := (0 : ℝ)))
      (show Continuous (fun q : ComplexPoint => (complexSqNorm (complexCuspPlus R s q.1)).re) by
        unfold complexSqNorm complexCuspPlus polynomialCuspChart
        fun_prop)
  · apply IsOpen.inter
    · exact isOpen_lt (continuous_const (y := (0 : ℝ)))
        (show Continuous (fun q : ComplexPoint => (complexSqNorm (complexCuspMinus R r q.2)).re) by
          unfold complexSqNorm complexCuspMinus polynomialCuspChart
          fun_prop)
    · exact isOpen_lt (continuous_const (y := (0 : ℝ)))
        (show Continuous (fun q : ComplexPoint => (complexSqNorm (complexBridge L
          (complexCuspPlus R s q.1) (complexCuspMinus R r q.2))).re) by
          unfold complexSqNorm complexBridge complexCuspPlus complexCuspMinus polynomialCuspChart
          fun_prop)

theorem zero_mem_complexCuspRadiusDomain {R L : ℝ}
    (hR : 0 < R) (hL : R < 2 * L) (s r : ℝ) :
    (0 : ComplexPoint) ∈ complexCuspRadiusDomain R L s r := by
  simp only [complexCuspRadiusDomain, mem_setOf_eq, Prod.fst_zero, Prod.snd_zero,
    complexCuspPlus, complexCuspMinus, polynomialCuspChart_zero,
    complexBridge_complexifyPoint, complexSqNorm_complexifyPoint, Complex.ofReal_re,
    sqNorm_tipPlus, sqNorm_tipMinus, sqNorm_bridge_cross]
  exact ⟨sq_pos_of_pos hR, sq_pos_of_pos hR, sq_pos_of_pos (activeDistance_pos hL)⟩

/-- All three radius functions are jointly holomorphic on the explicit branch domain. -/
theorem analyticOnNhd_complexCusp_radii (R L s r : ℝ) :
    AnalyticOnNhd ℂ (fun q : ComplexPoint => complexRadius (complexCuspPlus R s q.1))
      (complexCuspRadiusDomain R L s r) ∧
    AnalyticOnNhd ℂ (fun q : ComplexPoint => complexRadius (complexCuspMinus R r q.2))
      (complexCuspRadiusDomain R L s r) ∧
    AnalyticOnNhd ℂ (fun q : ComplexPoint => complexRadius
      (complexBridge L (complexCuspPlus R s q.1) (complexCuspMinus R r q.2)))
      (complexCuspRadiusDomain R L s r) := by
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · apply (analyticAt_complexRadius hq.1).comp (f := fun z : ComplexPoint => complexCuspPlus R s z.1)
    unfold complexCuspPlus polynomialCuspChart
    apply AnalyticAt.prod <;> fun_prop
  · apply (analyticAt_complexRadius hq.2.1).comp (f := fun z : ComplexPoint => complexCuspMinus R r z.2)
    unfold complexCuspMinus polynomialCuspChart
    apply AnalyticAt.prod <;> fun_prop
  · apply (analyticAt_complexRadius hq.2.2).comp (f := fun z : ComplexPoint =>
      complexBridge L (complexCuspPlus R s z.1) (complexCuspMinus R r z.2))
    unfold complexBridge complexCuspPlus complexCuspMinus polynomialCuspChart
    apply AnalyticAt.prod <;> fun_prop

/-- Bounded real tangential parameters share a single nonzero bidisc.
The domain is produced by continuity and compactness, not assumed. -/
theorem exists_uniform_complexCusp_bidisc {R L : ℝ}
    (hR : 0 < R) (hL : R < 2 * L) (s₀ : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (s r : ℝ), |s| ≤ s₀ → |r| ≤ s₀ →
      ∀ (t u : ℂ), ‖t‖ < δ → ‖u‖ < δ →
        (t, u) ∈ complexCuspRadiusDomain R L s r := by
  let K : Set Point := Icc (-s₀) s₀ ×ˢ Icc (-s₀) s₀
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hlocal (sr : Point) :
      ∀ᶠ z : ComplexPoint × Point in 𝓝 ((0 : ComplexPoint), sr),
        z.1 ∈ complexCuspRadiusDomain R L z.2.1 z.2.2 := by
    have h1 : Continuous (fun z : ComplexPoint × Point =>
        (complexSqNorm (complexCuspPlus R z.2.1 z.1.1)).re) := by
      unfold complexSqNorm complexCuspPlus polynomialCuspChart
      fun_prop
    have h2 : Continuous (fun z : ComplexPoint × Point =>
        (complexSqNorm (complexCuspMinus R z.2.2 z.1.2)).re) := by
      unfold complexSqNorm complexCuspMinus polynomialCuspChart
      fun_prop
    have h3 : Continuous (fun z : ComplexPoint × Point =>
        (complexSqNorm (complexBridge L (complexCuspPlus R z.2.1 z.1.1)
          (complexCuspMinus R z.2.2 z.1.2))).re) := by
      unfold complexSqNorm complexBridge complexCuspPlus complexCuspMinus polynomialCuspChart
      fun_prop
    have hz := zero_mem_complexCuspRadiusDomain hR hL sr.1 sr.2
    exact ((h1.tendsto ((0 : ComplexPoint), sr)).eventually (Ioi_mem_nhds hz.1)).and
      (((h2.tendsto ((0 : ComplexPoint), sr)).eventually (Ioi_mem_nhds hz.2.1)).and
        ((h3.tendsto ((0 : ComplexPoint), sr)).eventually (Ioi_mem_nhds hz.2.2)))
  have he : ∀ᶠ q : ComplexPoint in 𝓝 0, ∀ sr ∈ K,
      q ∈ complexCuspRadiusDomain R L sr.1 sr.2 :=
    hK.eventually_forall_of_forall_eventually (fun sr _ => hlocal sr)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ, hδ, fun s r hs hr t u ht hu => ?_⟩
  have htu : (t, u) ∈ Metric.ball (0 : ComplexPoint) δ := by
    simpa only [Metric.mem_ball, dist_zero_right, Prod.norm_mk, max_lt_iff] using And.intro ht hu
  exact hball htu (s, r) ⟨abs_le.mp hs, abs_le.mp hr⟩

end InfiniteZero.Geometry
