import InfiniteZero.CuspSourcePairingCoordinates
import InfiniteZero.ConstructionCuspBounds
import InfiniteZero.LandauRadialL2
import InfiniteZero.LogFlatSmooth

/-!
# Absolute integrability and Fubini for the incoming cusp cell

The density retains both chart Jacobians and the three physical kernels.
Its log-flat factors use their continuous zero extension at the cusp tips.
On the closed coordinate rectangle all three radial arguments stay positive;
compactness therefore proves integrability before any use of Fubini.
-/

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace InfiniteZero

private theorem measurePreserving_four_shuffle
    (μ₁ μ₂ μ₃ μ₄ : Measure ℝ) [SFinite μ₁] [SFinite μ₂]
    [SFinite μ₃] [SFinite μ₄] :
    MeasurePreserving (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      ((q.1.1, q.2.1), (q.1.2, q.2.2)))
      ((μ₁.prod μ₂).prod (μ₃.prod μ₄))
      ((μ₁.prod μ₃).prod (μ₂.prod μ₄)) := by
  have h₁ := measurePreserving_prodAssoc μ₁ μ₂ (μ₃.prod μ₄)
  have h₂ := (MeasurePreserving.id μ₁).prod
    ((measurePreserving_prodAssoc μ₂ μ₃ μ₄).symm MeasurableEquiv.prodAssoc)
  have h₃ := (MeasurePreserving.id μ₁).prod
    ((Measure.measurePreserving_swap (μ := μ₂) (ν := μ₃)).prod
      (MeasurePreserving.id μ₄))
  have h₄ := (MeasurePreserving.id μ₁).prod (measurePreserving_prodAssoc μ₃ μ₂ μ₄)
  have h₅ := (measurePreserving_prodAssoc μ₁ μ₃ (μ₂.prod μ₄)).symm
    MeasurableEquiv.prodAssoc
  exact h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁)))

private theorem integral_four
    (μ₁ μ₂ μ₃ μ₄ : Measure ℝ) [SFinite μ₁] [SFinite μ₂]
    [SFinite μ₃] [SFinite μ₄]
    (f : (ℝ × ℝ) × (ℝ × ℝ) → ℂ)
    (hf : Integrable f ((μ₁.prod μ₂).prod (μ₃.prod μ₄))) :
    (∫ q, f q ∂((μ₁.prod μ₂).prod (μ₃.prod μ₄))) =
      ∫ a, ∫ b, ∫ c, ∫ d, f ((a, b), (c, d)) ∂μ₄ ∂μ₃ ∂μ₂ ∂μ₁ := by
  rw [integral_prod _ hf]
  have he : (fun q => ∫ r, f (q, r) ∂μ₃.prod μ₄) =ᵐ[μ₁.prod μ₂]
      (fun q => ∫ c, ∫ d, f (q, (c, d)) ∂μ₄ ∂μ₃) := by
    filter_upwards [hf.prod_right_ae] with q hq
    exact integral_prod _ hq
  rw [integral_congr_ae he]
  exact integral_prod _ (hf.integral_prod_left.congr he)

namespace CuspParameters

/-- Incoming density without the constant source prefactor and `-h²`.
The scalar argument order is normal, normal, tangent, tangent. -/
def incomingCuspDensity (p : CuspParameters) (L h Ecore Efull t u s r : ℝ) : ℂ :=
  ((t ^ 2 * u ^ 2 *
    (logFlat p.β p.tStar t * p.χa t * p.χb s) *
    (logFlat p.β p.tStar u * p.χa u * p.χb r) *
    landauKernel p.b h Ecore ‖p.cuspChart (t, s)‖ *
    landauKernel p.b h Ecore ‖p.cuspChart (u, r)‖ : ℝ) : ℂ) *
    sourceKernel p.b L h Efull (p.cuspChart (t, s))
      (reflection (p.cuspChart (u, r)))

private def closedCuspChartDomain (p : CuspParameters) : Set (ℝ × ℝ) :=
  Icc 0 p.t₀ ×ˢ Icc (-p.s₀) p.s₀

private theorem closedCuspChartDomain_compact (p : CuspParameters) :
    IsCompact p.closedCuspChartDomain := isCompact_Icc.prod isCompact_Icc

private theorem cuspChart_closed_bounds {p : CuspParameters} (hp : p.BasicConditions)
    {q : ℝ × ℝ} (hq : q ∈ p.closedCuspChartDomain) :
    (p.cuspChart q) 0 ≤ p.R / 2 ∧ p.R ≤ ‖p.cuspChart q‖ := by
  have hs : |q.2| ≤ p.s₀ := abs_le.mpr hq.2
  have ht : 0 ≤ p.normalCoordinate (p.cuspChart q) := by
    simpa only [normalCoordinate_cuspChart] using hq.1.1
  have htt : p.normalCoordinate (p.cuspChart q) ≤ p.t₀ := by
    simpa only [normalCoordinate_cuspChart] using hq.1.2
  have hu : |p.tangentCoordinate (p.cuspChart q)| ≤
      p.s₀ * p.normalCoordinate (p.cuspChart q) ^ 2 := by
    rw [tangentCoordinate_cuspChart, normalCoordinate_cuspChart, abs_mul, abs_sq]
    exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  obtain ⟨hx, hn⟩ := cusp_horizontal_radial_bounds hp ht htt hu
  constructor <;> linarith

private theorem incomingCuspDensity_continuousOn_closed
    {p : CuspParameters} (hp : p.BasicConditions) {L h Ecore Efull : ℝ}
    (hL : p.R < 2 * L) (hh : 0 < h) (hEc : 0 < Ecore) (hEf : 0 < Efull) :
    ContinuousOn (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      p.incomingCuspDensity L h Ecore Efull q.1.1 q.2.1 q.1.2 q.2.2)
      (p.closedCuspChartDomain ×ˢ p.closedCuspChartDomain) := by
  intro q hq
  have hb₁ := cuspChart_closed_bounds hp hq.1
  have hb₂ := cuspChart_closed_bounds hp hq.2
  have hbridge : 0 < ‖p.cuspChart q.1 + reflection (p.cuspChart q.2) -
      2 • displacement L‖ := by
    have hb := bridge_distance_ge_horizontal (p.cuspChart q.1)
      (reflection (p.cuspChart q.2)) L
    have hr : (reflection (p.cuspChart q.2)) 0 = (p.cuspChart q.2) 0 := by
      simp [reflection]
    rw [hr] at hb
    linarith
  have hc₁ : ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ) => p.cuspChart z.1) q :=
    p.cuspChart_contDiff.continuous.continuousAt.comp continuousAt_fst
  have hc₂ : ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ) => p.cuspChart z.2) q :=
    p.cuspChart_contDiff.continuous.continuousAt.comp continuousAt_snd
  have hcr := reflection_contDiff.continuous.continuousAt.comp hc₂
  have hk₁ : ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      landauKernel p.b h Ecore ‖p.cuspChart z.1‖) q :=
    (continuousAt_landauKernel hp.b_pos hh hEc
    (hp.radius_pos.trans_le hb₁.2)).comp
      (f := fun z : (ℝ × ℝ) × (ℝ × ℝ) => ‖p.cuspChart z.1‖) hc₁.norm
  have hk₂ : ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      landauKernel p.b h Ecore ‖p.cuspChart z.2‖) q :=
    (continuousAt_landauKernel hp.b_pos hh hEc
    (hp.radius_pos.trans_le hb₂.2)).comp
      (f := fun z : (ℝ × ℝ) × (ℝ × ℝ) => ‖p.cuspChart z.2‖) hc₂.norm
  have hkb : ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      landauKernel p.b h Efull
        ‖p.cuspChart z.1 + reflection (p.cuspChart z.2) - 2 • displacement L‖) q :=
    (continuousAt_landauKernel hp.b_pos hh hEf hbridge).comp
    (f := fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      ‖p.cuspChart z.1 + reflection (p.cuspChart z.2) - 2 • displacement L‖)
    ((hc₁.add hcr).sub continuousAt_const).norm
  have hlog := (contDiff_logFlat hp.β_pos (hp.t₀_pos.trans hp.t₀_lt)).continuous
  have ha := hp.χa_smooth.continuous
  have hb := hp.χb_smooth.continuous
  apply ContinuousAt.continuousWithinAt
  unfold incomingCuspDensity sourceKernel
  apply ContinuousAt.mul
  · apply Complex.continuous_ofReal.continuousAt.comp
    exact (((((continuousAt_fst.fst.pow 2).mul (continuousAt_snd.fst.pow 2)).mul
      (((hlog.continuousAt.comp continuousAt_fst.fst).mul
        (ha.continuousAt.comp continuousAt_fst.fst)).mul
        (hb.continuousAt.comp continuousAt_fst.snd))).mul
      (((hlog.continuousAt.comp continuousAt_snd.fst).mul
        (ha.continuousAt.comp continuousAt_snd.fst)).mul
        (hb.continuousAt.comp continuousAt_snd.snd))).mul hk₁).mul hk₂
  · apply (Complex.continuous_ofReal.continuousAt.comp hkb).mul
    unfold sourcePhase
    fun_prop

/-- Joint absolute integrability of the physical incoming density, in the
original two chart coordinates. No integrability assumption is required. -/
theorem integrableOn_incomingCuspDensity_chartProduct
    {p : CuspParameters} (hp : p.BasicConditions) {L h Ecore Efull : ℝ}
    (hL : p.R < 2 * L) (hh : 0 < h) (hEc : 0 < Ecore) (hEf : 0 < Efull) :
    IntegrableOn (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      p.incomingCuspDensity L h Ecore Efull q.1.1 q.2.1 q.1.2 q.2.2)
      (p.cuspChartDomain ×ˢ p.cuspChartDomain) := by
  apply (ContinuousOn.integrableOn_compact
    (p.closedCuspChartDomain_compact.prod p.closedCuspChartDomain_compact)
      (incomingCuspDensity_continuousOn_closed hp hL hh hEc hEf)).mono_set
  intro q hq
  exact ⟨⟨⟨hq.1.1.1.le, hq.1.1.2.le⟩, ⟨hq.1.2.1.le, hq.1.2.2.le⟩⟩,
    ⟨⟨hq.2.1.1.le, hq.2.1.2.le⟩, ⟨hq.2.2.1.le, hq.2.2.2.le⟩⟩⟩

/-- The density is exactly the three complex kernels and the magnetic phase
on the real contour. This version also includes the zero-extended tips. -/
theorem incomingCuspDensity_eq_complex (p : CuspParameters)
    (L h Ecore Efull t u s r : ℝ) :
    p.incomingCuspDensity L h Ecore Efull t u s r =
      ((t ^ 2 * u ^ 2 *
        (logFlat p.β p.tStar t * p.χa t * p.χb s) *
        (logFlat p.β p.tStar u * p.χa u * p.χb r) : ℝ) : ℂ) *
      (Geometry.complexCuspPlusKernel p.b h Ecore p.R s ((t : ℂ), (u : ℂ)) *
        Geometry.complexCuspMinusKernel p.b h Ecore p.R r ((t : ℂ), (u : ℂ)) *
        Geometry.complexCuspBridgeKernel p.b h Efull p.R L s r ((t : ℂ), (u : ℂ)) *
        Complex.exp (Complex.I * Geometry.complexPhase p.b L
          (Geometry.complexCuspPlus p.R s (t : ℂ))
          (Geometry.complexCuspMinus p.R r (u : ℂ)) / (h : ℂ))) := by
  rw [incomingCuspDensity, sourceKernel_cuspChart_eq,
    complexCuspPlusKernel_ofReal, complexCuspMinusKernel_ofReal, norm_reflection]
  push_cast
  ring

/-- Absolute integrability after grouping the two normal coordinates
together and the two tangent coordinates together. -/
theorem integrableOn_incomingCuspDensity_normalProduct
    {p : CuspParameters} (hp : p.BasicConditions) {L h Ecore Efull : ℝ}
    (hL : p.R < 2 * L) (hh : 0 < h) (hEc : 0 < Ecore) (hEf : 0 < Efull) :
    IntegrableOn (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      p.incomingCuspDensity L h Ecore Efull q.1.1 q.1.2 q.2.1 q.2.2)
      ((Ioo 0 p.t₀ ×ˢ Ioo 0 p.t₀) ×ˢ
        (Ioo (-p.s₀) p.s₀ ×ˢ Ioo (-p.s₀) p.s₀)) := by
  let μn : Measure ℝ := volume.restrict (Ioo 0 p.t₀)
  let μs : Measure ℝ := volume.restrict (Ioo (-p.s₀) p.s₀)
  have ho : Integrable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      p.incomingCuspDensity L h Ecore Efull q.1.1 q.2.1 q.1.2 q.2.2)
      ((μn.prod μs).prod (μn.prod μs)) := by
    simpa only [μn, μs, Measure.prod_restrict, ← Measure.volume_eq_prod,
      IntegrableOn, cuspChartDomain] using
      integrableOn_incomingCuspDensity_chartProduct hp hL hh hEc hEf
  have hs := ((measurePreserving_four_shuffle μn μs μn μs).integrable_comp_emb
    (Homeomorph.prodProdProdComm ℝ ℝ ℝ ℝ).toMeasurableEquiv.measurableEmbedding
    (g := fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      p.incomingCuspDensity L h Ecore Efull q.1.1 q.1.2 q.2.1 q.2.2)).mp ho
  simpa only [μn, μs, Measure.prod_restrict, ← Measure.volume_eq_prod,
    IntegrableOn] using hs

/-- Fubini with the normal integrations outside and the tangent integrations
inside, starting from the exact pair of chart integrals. -/
theorem incomingCuspDensity_integral_eq_normals_first
    {p : CuspParameters} (hp : p.BasicConditions) {L h Ecore Efull : ℝ}
    (hL : p.R < 2 * L) (hh : 0 < h) (hEc : 0 < Ecore) (hEf : 0 < Efull) :
    (∫ q in p.cuspChartDomain, ∫ r in p.cuspChartDomain,
      p.incomingCuspDensity L h Ecore Efull q.1 r.1 q.2 r.2) =
      ∫ t in Ioo 0 p.t₀, ∫ u in Ioo 0 p.t₀,
        ∫ s in Ioo (-p.s₀) p.s₀, ∫ r in Ioo (-p.s₀) p.s₀,
          p.incomingCuspDensity L h Ecore Efull t u s r := by
  let μn : Measure ℝ := volume.restrict (Ioo 0 p.t₀)
  let μs : Measure ℝ := volume.restrict (Ioo (-p.s₀) p.s₀)
  let f : (ℝ × ℝ) × (ℝ × ℝ) → ℂ := fun q =>
    p.incomingCuspDensity L h Ecore Efull q.1.1 q.1.2 q.2.1 q.2.2
  have hf : Integrable f ((μn.prod μn).prod (μs.prod μs)) := by
    simpa only [f, μn, μs, Measure.prod_restrict, ← Measure.volume_eq_prod,
      IntegrableOn] using integrableOn_incomingCuspDensity_normalProduct hp hL hh hEc hEf
  have he := (measurePreserving_four_shuffle μn μs μn μs).integral_comp
    (Homeomorph.prodProdProdComm ℝ ℝ ℝ ℝ).toMeasurableEquiv.measurableEmbedding f
  have ho := (measurePreserving_four_shuffle μn μs μn μs).integrable_comp_of_integrable hf
  simp only [Function.comp_def] at ho
  rw [integral_prod _ ho] at he
  simpa only [μn, μs, Measure.prod_restrict, ← Measure.volume_eq_prod,
    cuspChartDomain, f] using he.trans (integral_four μn μn μs μs f hf)

/-- Fubini with both real tangent coordinates outside. This is the order
needed to treat the two normal variables for each fixed real tangent pair. -/
theorem incomingCuspDensity_integral_eq_tangents_first
    {p : CuspParameters} (hp : p.BasicConditions) {L h Ecore Efull : ℝ}
    (hL : p.R < 2 * L) (hh : 0 < h) (hEc : 0 < Ecore) (hEf : 0 < Efull) :
    (∫ q in p.cuspChartDomain, ∫ r in p.cuspChartDomain,
      p.incomingCuspDensity L h Ecore Efull q.1 r.1 q.2 r.2) =
      ∫ s in Ioo (-p.s₀) p.s₀, ∫ r in Ioo (-p.s₀) p.s₀,
        ∫ t in Ioo 0 p.t₀, ∫ u in Ioo 0 p.t₀,
          p.incomingCuspDensity L h Ecore Efull t u s r := by
  let μn : Measure ℝ := volume.restrict (Ioo 0 p.t₀)
  let μs : Measure ℝ := volume.restrict (Ioo (-p.s₀) p.s₀)
  let f : (ℝ × ℝ) × (ℝ × ℝ) → ℂ := fun q =>
    p.incomingCuspDensity L h Ecore Efull q.1.1 q.1.2 q.2.1 q.2.2
  have hf : Integrable f ((μn.prod μn).prod (μs.prod μs)) := by
    simpa only [f, μn, μs, Measure.prod_restrict, ← Measure.volume_eq_prod,
      IntegrableOn] using integrableOn_incomingCuspDensity_normalProduct hp hL hh hEc hEf
  rw [incomingCuspDensity_integral_eq_normals_first hp hL hh hEc hEf]
  calc
    _ = ∫ q, f q ∂((μn.prod μn).prod (μs.prod μs)) :=
      (integral_four μn μn μs μs f hf).symm
    _ = ∫ q, f q.swap ∂((μs.prod μs).prod (μn.prod μn)) :=
      (integral_prod_swap f).symm
    _ = _ := integral_four μs μs μn μn (fun q => f q.swap) hf.swap

/-- Every fixed real tangent pair in the closed cutoff rectangle gives an
absolutely integrable two-normal slice, not merely almost every pair. -/
theorem integrableOn_incomingCuspDensity_normals
    {p : CuspParameters} (hp : p.BasicConditions) {L h Ecore Efull s r : ℝ}
    (hL : p.R < 2 * L) (hh : 0 < h) (hEc : 0 < Ecore) (hEf : 0 < Efull)
    (hs : s ∈ Icc (-p.s₀) p.s₀) (hr : r ∈ Icc (-p.s₀) p.s₀) :
    IntegrableOn (fun q : ℝ × ℝ => p.incomingCuspDensity L h Ecore Efull q.1 q.2 s r)
      (Ioo 0 p.t₀ ×ˢ Ioo 0 p.t₀) := by
  have hc := (incomingCuspDensity_continuousOn_closed hp hL hh hEc hEf).comp
    (f := fun q : ℝ × ℝ => ((q.1, s), (q.2, r)))
    (s := Icc 0 p.t₀ ×ˢ Icc 0 p.t₀)
    (by fun_prop) (by intro q hq; exact ⟨⟨hq.1, hs⟩, ⟨hq.2, hr⟩⟩)
  apply (ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) hc).mono_set
  intro q hq
  exact ⟨⟨hq.1.1.le, hq.1.2.le⟩, ⟨hq.2.1.le, hq.2.2.le⟩⟩

private theorem incoming_sourceCell_eq_density
    {p : CuspParameters} (hp : p.BasicConditions) {L h Ecore Efull : ℝ}
    (hL : p.R < 2 * L) (hh : 0 < h) (hEf : 0 < Efull)
    (c Γ : ℝ) (φ : Wavefunction) (hφ : Continuous φ)
    (htail : ∀ x : Plane, p.r₀ < ‖x‖ →
      φ x = (Γ * landauKernel p.b h Ecore ‖x‖ : ℂ)) :
    sourceCell p L h Efull (fun x => (c : ℂ) * φ x) 1 2 =
      -((h ^ 2 : ℝ) : ℂ) *
        (((h ^ 2)⁻¹ * p.ε * p.a * c * Γ : ℝ) : ℂ) ^ 2 *
        ∫ q in p.cuspChartDomain, ∫ r in p.cuspChartDomain,
          p.incomingCuspDensity L h Ecore Efull q.1 r.1 q.2 r.2 := by
  rw [incoming_sourceCell_eq_cuspCharts hp hL hh hEf Ecore c Γ φ hφ htail]
  congr 1
  apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
  intro q hq
  apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
  intro r hr
  dsimp only
  rw [incomingCuspDensity_eq_complex, logFlat_of_pos _ _ hq.1.1,
    logFlat_of_pos _ _ hr.1.1]

/-- The exact physical incoming cell as four iterated integrals, normals
first. The normalization, `-h²`, both Jacobians, and both energies remain exact. -/
theorem incoming_sourceCell_eq_normals_first
    {p : CuspParameters} (hp : p.BasicConditions) {L h Ecore Efull : ℝ}
    (hL : p.R < 2 * L) (hh : 0 < h) (hEc : 0 < Ecore) (hEf : 0 < Efull)
    (c Γ : ℝ) (φ : Wavefunction) (hφ : Continuous φ)
    (htail : ∀ x : Plane, p.r₀ < ‖x‖ →
      φ x = (Γ * landauKernel p.b h Ecore ‖x‖ : ℂ)) :
    sourceCell p L h Efull (fun x => (c : ℂ) * φ x) 1 2 =
      -((h ^ 2 : ℝ) : ℂ) *
        (((h ^ 2)⁻¹ * p.ε * p.a * c * Γ : ℝ) : ℂ) ^ 2 *
        ∫ t in Ioo 0 p.t₀, ∫ u in Ioo 0 p.t₀,
          ∫ s in Ioo (-p.s₀) p.s₀, ∫ r in Ioo (-p.s₀) p.s₀,
            p.incomingCuspDensity L h Ecore Efull t u s r := by
  rw [incoming_sourceCell_eq_density hp hL hh hEf c Γ φ hφ htail,
    incomingCuspDensity_integral_eq_normals_first hp hL hh hEc hEf]

/-- The exact physical incoming cell with fixed real tangent parameters
outside the two normal integrations. No contour deformation is asserted. -/
theorem incoming_sourceCell_eq_tangents_first
    {p : CuspParameters} (hp : p.BasicConditions) {L h Ecore Efull : ℝ}
    (hL : p.R < 2 * L) (hh : 0 < h) (hEc : 0 < Ecore) (hEf : 0 < Efull)
    (c Γ : ℝ) (φ : Wavefunction) (hφ : Continuous φ)
    (htail : ∀ x : Plane, p.r₀ < ‖x‖ →
      φ x = (Γ * landauKernel p.b h Ecore ‖x‖ : ℂ)) :
    sourceCell p L h Efull (fun x => (c : ℂ) * φ x) 1 2 =
      -((h ^ 2 : ℝ) : ℂ) *
        (((h ^ 2)⁻¹ * p.ε * p.a * c * Γ : ℝ) : ℂ) ^ 2 *
        ∫ s in Ioo (-p.s₀) p.s₀, ∫ r in Ioo (-p.s₀) p.s₀,
          ∫ t in Ioo 0 p.t₀, ∫ u in Ioo 0 p.t₀,
            p.incomingCuspDensity L h Ecore Efull t u s r := by
  rw [incoming_sourceCell_eq_density hp hL hh hEf c Γ φ hφ htail,
    incomingCuspDensity_integral_eq_tangents_first hp hL hh hEc hEf]

end CuspParameters
end InfiniteZero
