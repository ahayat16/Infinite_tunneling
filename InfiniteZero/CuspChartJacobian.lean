import InfiniteZero.ConstructionCuspSmoothAway
import InfiniteZero.LogFlatIntegral
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The actual cusp chart and its Jacobian

The source coordinates carry product Lebesgue measure; the target is the
Euclidean plane. Cartesian coordinates identify these measures exactly.
The chart is injective on `t > 0`, and its Cartesian derivative has determinant
`t²`. No smoothness or asymptotic assertion about an eigenfunction is used.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace InfiniteZero.CuspParameters

def cuspChart (p : CuspParameters) (q : ℝ × ℝ) : Plane :=
  p.cuspTip + q.1 • cuspNormal + (q.2 * q.1 ^ 2) • cuspTangent

theorem normalCoordinate_cuspChart (p : CuspParameters) (q : ℝ × ℝ) :
    p.normalCoordinate (p.cuspChart q) = q.1 := by
  simp [cuspChart, cuspTip, cuspNormal, cuspTangent, normalCoordinate]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ring

theorem tangentCoordinate_cuspChart (p : CuspParameters) (q : ℝ × ℝ) :
    p.tangentCoordinate (p.cuspChart q) = q.2 * q.1 ^ 2 := by
  simp [cuspChart, cuspTip, cuspNormal, cuspTangent, tangentCoordinate]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ring

def cuspChartInverse (p : CuspParameters) (x : Plane) : ℝ × ℝ :=
  (p.normalCoordinate x, p.tangentCoordinate x / p.normalCoordinate x ^ 2)

theorem cuspChartInverse_cuspChart (p : CuspParameters) {q : ℝ × ℝ} (ht : q.1 ≠ 0) :
    p.cuspChartInverse (p.cuspChart q) = q := by
  ext <;> simp [cuspChartInverse, normalCoordinate_cuspChart,
    tangentCoordinate_cuspChart, ht]

theorem cuspChart_cuspChartInverse (p : CuspParameters) {x : Plane}
    (ht : p.normalCoordinate x ≠ 0) : p.cuspChart (p.cuspChartInverse x) = x := by
  simp only [cuspChart, cuspChartInverse, div_mul_cancel₀ _ (pow_ne_zero 2 ht)]
  exact (cuspFrame_reconstruction p x).symm

theorem cuspChartInverse_contDiffAt (p : CuspParameters) {x : Plane}
    (ht : p.normalCoordinate x ≠ 0) : ContDiffAt ℝ ∞ p.cuspChartInverse x :=
  (normalCoordinate_contDiff p).contDiffAt.prodMk
    ((tangentCoordinate_contDiff p).contDiffAt.div
      ((normalCoordinate_contDiff p).contDiffAt.pow 2) (pow_ne_zero 2 ht))

theorem cuspChart_injOn (p : CuspParameters) :
    InjOn p.cuspChart {q : ℝ × ℝ | 0 < q.1} := by
  intro q hq r hr he
  have hi := congrArg p.cuspChartInverse he
  simpa only [cuspChartInverse_cuspChart p (ne_of_gt hq),
    cuspChartInverse_cuspChart p (ne_of_gt hr)] using hi

theorem cuspChart_contDiff (p : CuspParameters) : ContDiff ℝ ∞ p.cuspChart := by
  unfold cuspChart
  fun_prop

def cuspChartFDeriv (q : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] Plane :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight cuspNormal +
    (q.2 • ((2 * q.1) • ContinuousLinearMap.fst ℝ ℝ ℝ) +
      q.1 ^ 2 • ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight cuspTangent

theorem hasFDerivAt_cuspChart (p : CuspParameters) (q : ℝ × ℝ) :
    HasFDerivAt p.cuspChart (cuspChartFDeriv q) q := by
  have ht := (hasFDerivAt_fst (𝕜 := ℝ) (p := q)).smul_const cuspNormal
  have hs := ((hasFDerivAt_snd (𝕜 := ℝ) (p := q)).mul
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := q)).pow 2)).smul_const cuspTangent
  simpa [cuspChart, cuspChartFDeriv, two_smul, two_mul] using
    ((hasFDerivAt_const p.cuspTip q).add ht).add hs

def planeCartesianEquiv : Plane ≃L[ℝ] ℝ × ℝ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

@[simp] theorem planeCartesianEquiv_apply (x : Plane) :
    planeCartesianEquiv x = (x 0, x 1) := rfl

@[simp] theorem planeCartesianEquiv_symm_apply (q : ℝ × ℝ) :
    planeCartesianEquiv.symm q = WithLp.toLp 2 ![q.1, q.2] := rfl

def cuspChartCartesian (p : CuspParameters) (q : ℝ × ℝ) : ℝ × ℝ :=
  planeCartesianEquiv (p.cuspChart q)

/-- The Cartesian matrix has the chart partial derivatives as columns. -/
def cuspChartCartesianFDeriv (q : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![-1 / 2 - Real.sqrt 3 * q.1 * q.2, -Real.sqrt 3 / 2 * q.1 ^ 2;
      Real.sqrt 3 / 2 - q.1 * q.2, -1 / 2 * q.1 ^ 2]).toContinuousLinearMap

theorem hasFDerivAt_cuspChartCartesian (p : CuspParameters) (q : ℝ × ℝ) :
    HasFDerivAt p.cuspChartCartesian (cuspChartCartesianFDeriv q) q := by
  have hh := planeCartesianEquiv.hasFDerivAt.comp q (hasFDerivAt_cuspChart p q)
  apply hh.congr_fderiv
  ext <;> simp [cuspChartCartesianFDeriv,
    Matrix.toLin_finTwoProd_toContinuousLinearMap, cuspChartFDeriv, cuspNormal, cuspTangent] <;> ring

theorem det_cuspChartCartesianFDeriv (q : ℝ × ℝ) :
    (cuspChartCartesianFDeriv q).det = q.1 ^ 2 := by
  simp only [cuspChartCartesianFDeriv, LinearMap.det_toContinuousLinearMap,
    LinearMap.det_toLin, Matrix.det_fin_two_of]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ring

theorem abs_det_cuspChartCartesianFDeriv (q : ℝ × ℝ) :
    |(cuspChartCartesianFDeriv q).det| = q.1 ^ 2 := by
  rw [det_cuspChartCartesianFDeriv, abs_of_nonneg (sq_nonneg _)]

theorem abs_det_fderiv_cuspChartCartesian (p : CuspParameters) (q : ℝ × ℝ) :
    |(fderiv ℝ p.cuspChartCartesian q).det| = q.1 ^ 2 := by
  rw [(hasFDerivAt_cuspChartCartesian p q).fderiv, abs_det_cuspChartCartesianFDeriv]

theorem planeCartesianEquiv_measurePreserving :
    MeasurePreserving planeCartesianEquiv (volume : Measure Plane) volume :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

theorem planeCartesianEquiv_symm_measurePreserving :
    MeasurePreserving planeCartesianEquiv.symm volume (volume : Measure Plane) :=
  (PiLp.volume_preserving_toLp (Fin 2)).comp (volume_preserving_finTwoArrow ℝ).symm

theorem cuspChartCartesian_injOn (p : CuspParameters) :
    InjOn p.cuspChartCartesian {q : ℝ × ℝ | 0 < q.1} :=
  planeCartesianEquiv.injective.comp_injOn p.cuspChart_injOn

local instance : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- Actual change of variables into the Euclidean plane, with its fixed
Lebesgue normalization. It holds for every measurable subdomain of `t > 0`. -/
theorem integral_image_cuspChart (p : CuspParameters) {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (ht : s ⊆ {q : ℝ × ℝ | 0 < q.1})
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : Plane → F) :
    ∫ x in p.cuspChart '' s, g x = ∫ q in s, q.1 ^ 2 • g (p.cuspChart q) := by
  have himage : planeCartesianEquiv.symm '' (p.cuspChartCartesian '' s) = p.cuspChart '' s := by
    rw [Set.image_image]
    congr 1
    funext q
    exact planeCartesianEquiv.symm_apply_apply (p.cuspChart q)
  calc
    _ = ∫ q in p.cuspChartCartesian '' s, g (planeCartesianEquiv.symm q) := by
      rw [← himage]
      exact planeCartesianEquiv_symm_measurePreserving.setIntegral_image_emb
        planeCartesianEquiv.symm.toHomeomorph.measurableEmbedding g _
    _ = ∫ q in s, |(cuspChartCartesianFDeriv q).det| •
        g (planeCartesianEquiv.symm (p.cuspChartCartesian q)) :=
      integral_image_eq_integral_abs_det_fderiv_smul volume hs
        (fun q _ => (hasFDerivAt_cuspChartCartesian p q).hasFDerivWithinAt)
        (p.cuspChartCartesian_injOn.mono ht) _
    _ = _ := by simp only [abs_det_cuspChartCartesianFDeriv, cuspChartCartesian,
      ContinuousLinearEquiv.symm_apply_apply]

theorem cuspChart_image_normal_halfPlane (p : CuspParameters) :
    p.cuspChart '' {q : ℝ × ℝ | 0 < q.1} = {x : Plane | 0 < p.normalCoordinate x} := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa only [Set.mem_setOf_eq, normalCoordinate_cuspChart] using hq
  · intro hx
    exact ⟨p.cuspChartInverse x, hx, p.cuspChart_cuspChartInverse (ne_of_gt hx)⟩

theorem integral_normal_halfPlane (p : CuspParameters)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : Plane → F) :
    ∫ x in {x : Plane | 0 < p.normalCoordinate x}, g x =
      ∫ q in {q : ℝ × ℝ | 0 < q.1}, q.1 ^ 2 • g (p.cuspChart q) := by
  rw [← cuspChart_image_normal_halfPlane]
  exact integral_image_cuspChart p (isOpen_lt continuous_const continuous_fst).measurableSet
    Subset.rfl g

theorem cuspPlus_cuspChart {p : CuspParameters} (hp : p.BasicConditions) {q : ℝ × ℝ}
    (ht : 0 < q.1) : p.cuspPlus (p.cuspChart q) =
      -p.a * Real.exp (-p.β * (Real.log (p.tStar / q.1)) ^ 2) * p.χa q.1 * p.χb q.2 := by
  rw [cuspPlus_eq_formula_of_normal_pos hp (by simpa only [normalCoordinate_cuspChart] using ht)]
  simp [normalCoordinate_cuspChart, tangentCoordinate_cuspChart, ne_of_gt ht]

/-- The Jacobian factor in an integral against the physical cusp potential,
with any real-normed-vector-valued observable. -/
theorem integral_cuspPlus_smul (p : CuspParameters)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : Plane → F) :
    ∫ x : Plane, p.cuspPlus x • g x =
      ∫ q in {q : ℝ × ℝ | 0 < q.1},
        q.1 ^ 2 • (p.cuspPlus (p.cuspChart q) • g (p.cuspChart q)) := by
  rw [← p.integral_normal_halfPlane (fun x => p.cuspPlus x • g x)]
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
  intro x hx
  have hz : p.cuspPlus x = 0 := by
    simp only [Set.mem_setOf_eq, not_lt] at hx
    simp [cuspPlus, not_lt.mpr hx]
  rw [hz, zero_smul]

def cuspChartDomain (p : CuspParameters) : Set (ℝ × ℝ) :=
  Ioo 0 p.t₀ ×ˢ Ioo (-p.s₀) p.s₀

theorem cuspPlus_support_subset_chartImage (p : CuspParameters) :
    Function.support p.cuspPlus ⊆ p.cuspChart '' p.cuspChartDomain := by
  intro x hx
  have hc : 0 < p.normalCoordinate x ∧ p.normalCoordinate x < p.t₀ ∧
      |p.tangentCoordinate x / p.normalCoordinate x ^ 2| < p.s₀ := by
    by_contra hn
    exact hx (by simp [cuspPlus, hn])
  exact ⟨p.cuspChartInverse x, ⟨⟨hc.1, hc.2.1⟩, abs_lt.mp hc.2.2⟩,
    p.cuspChart_cuspChartInverse hc.1.ne'⟩

theorem integral_cuspPlus_smul_rectangle (p : CuspParameters)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : Plane → F) :
    ∫ x : Plane, p.cuspPlus x • g x = ∫ q in p.cuspChartDomain,
      q.1 ^ 2 • (p.cuspPlus (p.cuspChart q) • g (p.cuspChart q)) := by
  have hi : (∫ x in p.cuspChart '' p.cuspChartDomain, p.cuspPlus x • g x) =
      ∫ x : Plane, p.cuspPlus x • g x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : p.cuspPlus x = 0 := by
      by_contra hn
      exact hx (p.cuspPlus_support_subset_chartImage hn)
    rw [hz, zero_smul]
  rw [← hi]
  exact integral_image_cuspChart p (measurableSet_Ioo.prod measurableSet_Ioo)
    (fun _ hq => hq.1.1) _

/-- Exact reduction of a physical two-dimensional cusp integral to the
one-dimensional normal integral with Jacobian power two and a fixed
tangential-cutoff integral. No tail estimate is assumed here. -/
theorem integral_abs_cuspPlus_mul_exp {p : CuspParameters} (hp : p.BasicConditions)
    (a h : ℝ) :
    (∫ x : Plane, |p.cuspPlus x| * Real.exp (-a * p.normalCoordinate x / h)) =
      p.a * (∫ s in Ioo (-p.s₀) p.s₀, p.χb s) *
        (∫ t in Ioo 0 p.t₀, p.χa t * (t ^ 2 *
          Real.exp (-p.β * (Real.log (p.tStar / t)) ^ 2 - a * t / h))) := by
  have he : (fun x : Plane => |p.cuspPlus x| * Real.exp (-a * p.normalCoordinate x / h)) =
      (fun x => p.cuspPlus x • (-Real.exp (-a * p.normalCoordinate x / h))) := by
    funext x
    rw [abs_of_nonpos (cuspPlus_range hp x).2, smul_eq_mul]
    ring
  rw [he, integral_cuspPlus_smul_rectangle]
  calc
    _ = ∫ q in p.cuspChartDomain, p.a *
        ((p.χa q.1 * (q.1 ^ 2 * Real.exp
          (-p.β * (Real.log (p.tStar / q.1)) ^ 2 - a * q.1 / h))) * p.χb q.2) := by
      apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
      intro q hq
      dsimp only
      rw [cuspPlus_cuspChart hp hq.1.1, normalCoordinate_cuspChart]
      simp only [smul_eq_mul, Real.exp_sub, neg_mul, Real.exp_neg, div_eq_mul_inv]
      ring
    _ = _ := by
      rw [integral_const_mul, cuspChartDomain, Measure.volume_eq_prod ℝ ℝ,
        setIntegral_prod_mul (fun t : ℝ => p.χa t * (t ^ 2 *
          Real.exp (-p.β * (Real.log (p.tStar / t)) ^ 2 - a * t / h))) p.χb
          (Ioo 0 p.t₀) (Ioo (-p.s₀) p.s₀) (μ := volume) (ν := volume)]
      ring

/-- The proven scalar log-flat bound now controls an actual integral over
the physical cusp, uniformly over all positive normal slopes above `aMin`. -/
theorem eventually_integral_abs_cuspPlus_mul_exp_le {p : CuspParameters}
    (hp : p.BasicConditions) {aMin η : ℝ} (haMin : 0 < aMin) (hη : 0 < η) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ a : ℝ, aMin ≤ a →
      (∫ x : Plane, |p.cuspPlus x| * Real.exp (-a * p.normalCoordinate x / h)) ≤
        p.a * (∫ s in Ioo (-p.s₀) p.s₀, p.χb s) *
          Real.exp (-(p.β - η) * (Real.log (1 / h)) ^ 2) := by
  have htStar := hp.t₀_pos.trans hp.t₀_lt
  have he := eventually_logFlat_cutoff_integral_le_exp hp.β_pos htStar hp.t₀_pos
    haMin hη 2 hp.χa_smooth.continuous (fun t _ => (hp.χa_range t).2)
  filter_upwards [he] with h hh
  intro a ha
  rw [integral_abs_cuspPlus_mul_exp hp a h]
  exact mul_le_mul_of_nonneg_left (hh a ha)
    (mul_nonneg hp.a_pos.le (integral_nonneg (fun s => (hp.χb_range s).1)))

end InfiniteZero.CuspParameters
