import InfiniteZero.SeparationCertificate
import InfiniteZero.AtomicLocalizationCutoffs
import InfiniteZero.CutoffGradientProduct

/-!
# Fixed smooth localization around both complete wells

The plateau contains the complete potential support and the ball of radius
`4 r₀`. Its two radii are fixed strictly below the separation threshold.
Only the centers move with `L`; neither the bump nor the derivative bounds
depend on the coupling. Sine and cosine give the square partition without
taking the square root of a function vanishing at a boundary.
-/

noncomputable section
open Set
open scoped ContDiff

namespace InfiniteZero.CuspParameters

def doubleWellLocalizationSupportRadius {p : CuspParameters}
    (cert : p.SeparationCertificate) : ℝ := max cert.supportRadius (4 * p.r₀)

def doubleWellPlateauRadius {p : CuspParameters} (cert : p.SeparationCertificate) : ℝ :=
  (2 * doubleWellLocalizationSupportRadius cert + cert.L₀) / 3

def doubleWellCutoffRadius {p : CuspParameters} (cert : p.SeparationCertificate) : ℝ :=
  (doubleWellLocalizationSupportRadius cert + 2 * cert.L₀) / 3

theorem doubleWellLocalizationRadii {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) :
    0 < doubleWellLocalizationSupportRadius cert ∧
    doubleWellLocalizationSupportRadius cert < doubleWellPlateauRadius cert ∧
    doubleWellPlateauRadius cert < doubleWellCutoffRadius cert ∧
    doubleWellCutoffRadius cert < cert.L₀ := by
  have hS := lt_of_le_of_lt (le_max_left cert.supportRadius p.R) cert.separation
  have hR := lt_of_le_of_lt (le_max_right cert.supportRadius p.R) cert.separation
  have hsmall : 4 * p.r₀ < cert.L₀ := by linarith [hp.r₀_pos, hp.radius_large]
  have hmax : doubleWellLocalizationSupportRadius cert < cert.L₀ :=
    max_lt hS hsmall
  have hpos : 0 < doubleWellLocalizationSupportRadius cert :=
    cert.supportRadius_pos.trans_le (le_max_left _ _)
  dsimp only [doubleWellPlateauRadius, doubleWellCutoffRadius]
  exact ⟨hpos, by linarith, by linarith, by linarith⟩

def doubleWellLocalizationBump {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) : ContDiffBump (0 : Plane) where
  rIn := doubleWellPlateauRadius cert
  rOut := doubleWellCutoffRadius cert
  rIn_pos := (doubleWellLocalizationRadii hp cert).1.trans
    (doubleWellLocalizationRadii hp cert).2.1
  rIn_lt_rOut := (doubleWellLocalizationRadii hp cert).2.2.1

def doubleWellBaseInnerCutoff {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (x : Plane) : ℝ :=
  Real.sin (Real.pi / 2 * doubleWellLocalizationBump hp cert x)

def doubleWellBaseOuterCutoff {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (x : Plane) : ℝ :=
  Real.cos (Real.pi / 2 * doubleWellLocalizationBump hp cert x)

def doubleWellLeftCutoff {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (L : ℝ) (x : Plane) : ℝ :=
  doubleWellBaseInnerCutoff hp cert (x + displacement L)

def doubleWellRightCutoff {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (L : ℝ) (x : Plane) : ℝ :=
  doubleWellBaseInnerCutoff hp cert (x - displacement L)

def doubleWellExteriorCutoff {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (L : ℝ) (x : Plane) : ℝ :=
  doubleWellBaseOuterCutoff hp cert (x + displacement L) *
    doubleWellBaseOuterCutoff hp cert (x - displacement L)

def doubleWellLeftOuterCutoff {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (L : ℝ) (x : Plane) : ℝ :=
  doubleWellBaseOuterCutoff hp cert (x + displacement L)

def doubleWellRightOuterCutoff {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (L : ℝ) (x : Plane) : ℝ :=
  doubleWellBaseOuterCutoff hp cert (x - displacement L)

theorem doubleWellBaseInnerCutoff_contDiff {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) : ContDiff ℝ ∞ (doubleWellBaseInnerCutoff hp cert) :=
  (contDiff_const.mul (doubleWellLocalizationBump hp cert).contDiff).sin

theorem doubleWellBaseOuterCutoff_contDiff {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) : ContDiff ℝ ∞ (doubleWellBaseOuterCutoff hp cert) :=
  (contDiff_const.mul (doubleWellLocalizationBump hp cert).contDiff).cos

theorem doubleWellLeftCutoff_contDiff {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (L : ℝ) : ContDiff ℝ ∞ (doubleWellLeftCutoff hp cert L) :=
  (doubleWellBaseInnerCutoff_contDiff hp cert).comp (contDiff_id.add contDiff_const)

theorem doubleWellRightCutoff_contDiff {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (L : ℝ) : ContDiff ℝ ∞ (doubleWellRightCutoff hp cert L) :=
  (doubleWellBaseInnerCutoff_contDiff hp cert).comp (contDiff_id.sub contDiff_const)

theorem doubleWellExteriorCutoff_contDiff {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (L : ℝ) : ContDiff ℝ ∞ (doubleWellExteriorCutoff hp cert L) :=
  ((doubleWellBaseOuterCutoff_contDiff hp cert).comp (contDiff_id.add contDiff_const)).mul
    ((doubleWellBaseOuterCutoff_contDiff hp cert).comp (contDiff_id.sub contDiff_const))

theorem doubleWellLeftOuterCutoff_contDiff {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (L : ℝ) :
    ContDiff ℝ ∞ (doubleWellLeftOuterCutoff hp cert L) :=
  (doubleWellBaseOuterCutoff_contDiff hp cert).comp (contDiff_id.add contDiff_const)

theorem doubleWellRightOuterCutoff_contDiff {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (L : ℝ) :
    ContDiff ℝ ∞ (doubleWellRightOuterCutoff hp cert L) :=
  (doubleWellBaseOuterCutoff_contDiff hp cert).comp (contDiff_id.sub contDiff_const)

theorem doubleWellBaseCutoffs_range {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (x : Plane) :
    doubleWellBaseInnerCutoff hp cert x ∈ Icc (0 : ℝ) 1 ∧
    doubleWellBaseOuterCutoff hp cert x ∈ Icc (0 : ℝ) 1 := by
  have hnonneg : 0 ≤ Real.pi / 2 * doubleWellLocalizationBump hp cert x :=
    mul_nonneg (by positivity) (doubleWellLocalizationBump hp cert).nonneg
  have hle : Real.pi / 2 * doubleWellLocalizationBump hp cert x ≤ Real.pi / 2 := by
    nlinarith [(doubleWellLocalizationBump hp cert).le_one (x := x), Real.pi_pos]
  refine ⟨⟨Real.sin_nonneg_of_nonneg_of_le_pi hnonneg (by linarith [Real.pi_pos]),
    Real.sin_le_one _⟩, ⟨?_, Real.cos_le_one _⟩⟩
  exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hle⟩

theorem doubleWellCutoffs_range {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (L : ℝ) (x : Plane) :
    doubleWellLeftCutoff hp cert L x ∈ Icc (0 : ℝ) 1 ∧
    doubleWellRightCutoff hp cert L x ∈ Icc (0 : ℝ) 1 ∧
    doubleWellExteriorCutoff hp cert L x ∈ Icc (0 : ℝ) 1 := by
  have hl := doubleWellBaseCutoffs_range hp cert (x + displacement L)
  have hr := doubleWellBaseCutoffs_range hp cert (x - displacement L)
  refine ⟨hl.1, hr.1, mul_nonneg hl.2.1 hr.2.1, ?_⟩
  exact (mul_le_mul hl.2.2 hr.2.2 hr.2.1 (by norm_num)).trans_eq (one_mul 1)

theorem doubleWellBaseCutoffs_partition {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (x : Plane) :
    doubleWellBaseInnerCutoff hp cert x ^ 2 + doubleWellBaseOuterCutoff hp cert x ^ 2 = 1 :=
  Real.sin_sq_add_cos_sq _

theorem doubleWellLeftOuterCutoff_range {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (L : ℝ) (x : Plane) :
    doubleWellLeftOuterCutoff hp cert L x ∈ Icc (0 : ℝ) 1 :=
  (doubleWellBaseCutoffs_range hp cert (x + displacement L)).2

theorem doubleWellRightOuterCutoff_range {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (L : ℝ) (x : Plane) :
    doubleWellRightOuterCutoff hp cert L x ∈ Icc (0 : ℝ) 1 :=
  (doubleWellBaseCutoffs_range hp cert (x - displacement L)).2

theorem doubleWellLeftCutoffs_partition {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (L : ℝ) (x : Plane) :
    doubleWellLeftCutoff hp cert L x ^ 2 + doubleWellLeftOuterCutoff hp cert L x ^ 2 = 1 :=
  doubleWellBaseCutoffs_partition hp cert (x + displacement L)

theorem doubleWellRightCutoffs_partition {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (L : ℝ) (x : Plane) :
    doubleWellRightCutoff hp cert L x ^ 2 + doubleWellRightOuterCutoff hp cert L x ^ 2 = 1 :=
  doubleWellBaseCutoffs_partition hp cert (x - displacement L)

theorem doubleWellRightOuterCutoff_mul_leftOuterCutoff {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate) (L : ℝ) (x : Plane) :
    doubleWellRightOuterCutoff hp cert L x * doubleWellLeftOuterCutoff hp cert L x =
      doubleWellExteriorCutoff hp cert L x := mul_comm _ _

theorem doubleWellBaseCutoffs_one_zero {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) {x : Plane} (hx : ‖x‖ ≤ doubleWellPlateauRadius cert) :
    doubleWellBaseInnerCutoff hp cert x = 1 ∧ doubleWellBaseOuterCutoff hp cert x = 0 := by
  have hb : doubleWellLocalizationBump hp cert x = 1 := by
    apply (doubleWellLocalizationBump hp cert).one_of_mem_closedBall
    simpa only [Metric.mem_closedBall, dist_zero_right, doubleWellLocalizationBump] using hx
  simp [doubleWellBaseInnerCutoff, doubleWellBaseOuterCutoff, hb]

theorem doubleWellBaseCutoffs_zero_one {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) {x : Plane} (hx : doubleWellCutoffRadius cert ≤ ‖x‖) :
    doubleWellBaseInnerCutoff hp cert x = 0 ∧ doubleWellBaseOuterCutoff hp cert x = 1 := by
  have hb : doubleWellLocalizationBump hp cert x = 0 := by
    apply (doubleWellLocalizationBump hp cert).zero_of_le_dist
    simpa only [dist_zero_right, doubleWellLocalizationBump] using hx
  simp [doubleWellBaseInnerCutoff, doubleWellBaseOuterCutoff, hb]

theorem doubleWellLeftCutoff_one {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (L : ℝ) {x : Plane}
    (hx : ‖x + displacement L‖ ≤ doubleWellPlateauRadius cert) :
    doubleWellLeftCutoff hp cert L x = 1 := (doubleWellBaseCutoffs_one_zero hp cert hx).1

theorem doubleWellRightCutoff_one {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (L : ℝ) {x : Plane}
    (hx : ‖x - displacement L‖ ≤ doubleWellPlateauRadius cert) :
    doubleWellRightCutoff hp cert L x = 1 := (doubleWellBaseCutoffs_one_zero hp cert hx).1

theorem doubleWellLeftCutoff_one_on_coreBall {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (L : ℝ) {x : Plane}
    (hx : ‖x + displacement L‖ ≤ 4 * p.r₀) : doubleWellLeftCutoff hp cert L x = 1 :=
  doubleWellLeftCutoff_one hp cert L
    (hx.trans ((le_max_right _ _).trans (doubleWellLocalizationRadii hp cert).2.1.le))

theorem doubleWellRightCutoff_one_on_coreBall {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (L : ℝ) {x : Plane}
    (hx : ‖x - displacement L‖ ≤ 4 * p.r₀) : doubleWellRightCutoff hp cert L x = 1 :=
  doubleWellRightCutoff_one hp cert L
    (hx.trans ((le_max_right _ _).trans (doubleWellLocalizationRadii hp cert).2.1.le))

theorem doubleWellExteriorCutoff_zero {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (L : ℝ) {x : Plane}
    (hx : ‖x + displacement L‖ ≤ doubleWellPlateauRadius cert ∨
      ‖x - displacement L‖ ≤ doubleWellPlateauRadius cert) :
    doubleWellExteriorCutoff hp cert L x = 0 := by
  rcases hx with hx | hx
  · simp only [doubleWellExteriorCutoff, (doubleWellBaseCutoffs_one_zero hp cert hx).2, zero_mul]
  · simp only [doubleWellExteriorCutoff, (doubleWellBaseCutoffs_one_zero hp cert hx).2, mul_zero]

theorem doubleWellExteriorCutoff_one {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (L : ℝ) {x : Plane}
    (hl : doubleWellCutoffRadius cert ≤ ‖x + displacement L‖)
    (hr : doubleWellCutoffRadius cert ≤ ‖x - displacement L‖) :
    doubleWellExteriorCutoff hp cert L x = 1 := by
  simp only [doubleWellExteriorCutoff, (doubleWellBaseCutoffs_zero_one hp cert hl).2,
    (doubleWellBaseCutoffs_zero_one hp cert hr).2, mul_one]

private theorem center_norm_separation {L : ℝ} (hL : 0 ≤ L) (x : Plane) :
    2 * L ≤ ‖x + displacement L‖ + ‖x - displacement L‖ := by
  have hn : ‖(2 : ℝ) • displacement L‖ = 2 * L := by
    simp [displacement, coordinateVector, norm_smul, Real.norm_eq_abs, abs_of_nonneg hL]
  have ht := norm_sub_le (x + displacement L) (x - displacement L)
  rw [show (x + displacement L) - (x - displacement L) =
    (2 : ℝ) • displacement L by simp [two_smul], hn] at ht
  exact ht

theorem doubleWell_at_least_one_cutoff_outside {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) {L : ℝ} (hL : cert.L₀ ≤ L) (x : Plane) :
    doubleWellCutoffRadius cert ≤ ‖x + displacement L‖ ∨
      doubleWellCutoffRadius cert ≤ ‖x - displacement L‖ := by
  have hr := doubleWellLocalizationRadii hp cert
  have hb : doubleWellCutoffRadius cert < L := hr.2.2.2.trans_le hL
  have hpos : 0 < L := hr.1.trans (hr.2.1.trans (hr.2.2.1.trans hb))
  have ht := center_norm_separation hpos.le x
  by_contra hn
  push Not at hn
  linarith

theorem doubleWellCutoffs_partition {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) {L : ℝ} (hL : cert.L₀ ≤ L) (x : Plane) :
    doubleWellLeftCutoff hp cert L x ^ 2 + doubleWellRightCutoff hp cert L x ^ 2 +
      doubleWellExteriorCutoff hp cert L x ^ 2 = 1 := by
  rcases doubleWell_at_least_one_cutoff_outside hp cert hL x with hl | hr
  · obtain ⟨ha, hb⟩ := doubleWellBaseCutoffs_zero_one hp cert hl
    simpa only [doubleWellLeftCutoff, doubleWellRightCutoff, doubleWellExteriorCutoff,
      ha, hb, zero_pow (by norm_num : 2 ≠ 0), zero_add, one_mul] using
        doubleWellBaseCutoffs_partition hp cert (x - displacement L)
  · obtain ⟨ha, hb⟩ := doubleWellBaseCutoffs_zero_one hp cert hr
    simpa only [doubleWellLeftCutoff, doubleWellRightCutoff, doubleWellExteriorCutoff,
      ha, hb, zero_pow (by norm_num : 2 ≠ 0), add_zero, mul_one] using
        doubleWellBaseCutoffs_partition hp cert (x + displacement L)

theorem doubleWellLeftOuterCutoff_mul_rightCutoff {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    {L : ℝ} (hL : cert.L₀ ≤ L) (x : Plane) :
    doubleWellLeftOuterCutoff hp cert L x * doubleWellRightCutoff hp cert L x =
      doubleWellRightCutoff hp cert L x := by
  rcases doubleWell_at_least_one_cutoff_outside hp cert hL x with hl | hr
  · simp only [doubleWellLeftOuterCutoff, (doubleWellBaseCutoffs_zero_one hp cert hl).2, one_mul]
  · simp only [doubleWellRightCutoff, (doubleWellBaseCutoffs_zero_one hp cert hr).1, mul_zero]

theorem doubleWellLeftCutoff_tsupport_subset {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (L : ℝ) :
    tsupport (doubleWellLeftCutoff hp cert L) ⊆
      {x | ‖x + displacement L‖ ≤ doubleWellCutoffRadius cert} := by
  apply closure_minimal _ (isClosed_le (continuous_id.add continuous_const).norm continuous_const)
  intro x hx
  by_contra hn
  exact hx (doubleWellBaseCutoffs_zero_one hp cert (le_of_not_ge hn)).1

theorem doubleWellRightCutoff_tsupport_subset {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (L : ℝ) :
    tsupport (doubleWellRightCutoff hp cert L) ⊆
      {x | ‖x - displacement L‖ ≤ doubleWellCutoffRadius cert} := by
  apply closure_minimal _ (isClosed_le (continuous_id.sub continuous_const).norm continuous_const)
  intro x hx
  by_contra hn
  exact hx (doubleWellBaseCutoffs_zero_one hp cert (le_of_not_ge hn)).1

theorem doubleWellCutoffs_disjoint {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) {L : ℝ} (hL : cert.L₀ ≤ L) :
    Disjoint (tsupport (doubleWellLeftCutoff hp cert L))
      (tsupport (doubleWellRightCutoff hp cert L)) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have hl := doubleWellLeftCutoff_tsupport_subset hp cert L hx
  have hr := doubleWellRightCutoff_tsupport_subset hp cert L hy
  have hrad := doubleWellLocalizationRadii hp cert
  have hb : doubleWellCutoffRadius cert < L := hrad.2.2.2.trans_le hL
  have hpos : 0 < L := hrad.1.trans (hrad.2.1.trans (hrad.2.2.1.trans hb))
  have ht := center_norm_separation hpos.le x
  change ‖x + displacement L‖ ≤ doubleWellCutoffRadius cert at hl
  change ‖x - displacement L‖ ≤ doubleWellCutoffRadius cert at hr
  linarith

theorem doubleWellLeftCutoff_inversion {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (L : ℝ) (x : Plane) :
    doubleWellLeftCutoff hp cert L (-x) = doubleWellRightCutoff hp cert L x := by
  simp only [doubleWellLeftCutoff, doubleWellRightCutoff, doubleWellBaseInnerCutoff,
    show -x + displacement L = -(x - displacement L) by abel,
    (doubleWellLocalizationBump hp cert).neg]

theorem doubleWellExteriorCutoff_inversion {p : CuspParameters} (hp : p.BasicConditions)
    (cert : p.SeparationCertificate) (L : ℝ) (x : Plane) :
    doubleWellExteriorCutoff hp cert L (-x) = doubleWellExteriorCutoff hp cert L x := by
  simp only [doubleWellExteriorCutoff, doubleWellBaseOuterCutoff,
    show -x + displacement L = -(x - displacement L) by abel,
    show -x - displacement L = -(x + displacement L) by abel,
    (doubleWellLocalizationBump hp cert).neg]
  ring

private theorem potential_norm_le {p : CuspParameters} (cert : p.SeparationCertificate)
    {x : Plane} (hx : p.potential x ≠ 0) : ‖x‖ ≤ doubleWellLocalizationSupportRadius cert :=
  (cert.support_bound x (subset_tsupport _ hx)).trans (le_max_left _ _)

theorem potential_mul_doubleWellExteriorCutoff_left {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate) (L : ℝ) (x : Plane) :
    p.potential (x + displacement L) * doubleWellExteriorCutoff hp cert L x = 0 := by
  by_cases hv : p.potential (x + displacement L) = 0
  · simp [hv]
  · rw [doubleWellExteriorCutoff_zero hp cert L (Or.inl
      ((potential_norm_le cert hv).trans (doubleWellLocalizationRadii hp cert).2.1.le)), mul_zero]

theorem potential_mul_doubleWellExteriorCutoff_right {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate) (L : ℝ) (x : Plane) :
    p.potential (-x + displacement L) * doubleWellExteriorCutoff hp cert L x = 0 := by
  by_cases hv : p.potential (-x + displacement L) = 0
  · simp [hv]
  · have hn := potential_norm_le cert hv
    rw [show -x + displacement L = -(x - displacement L) by abel, norm_neg] at hn
    rw [doubleWellExteriorCutoff_zero hp cert L
      (Or.inr (hn.trans (doubleWellLocalizationRadii hp cert).2.1.le)), mul_zero]

theorem doubleWellPotential_mul_exteriorCutoff {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate) (L : ℝ) (x : Plane) :
    doubleWellPotential p.potential L x * doubleWellExteriorCutoff hp cert L x = 0 := by
  simp only [doubleWellPotential, add_mul, potential_mul_doubleWellExteriorCutoff_left,
    potential_mul_doubleWellExteriorCutoff_right, add_zero]

theorem potential_mul_doubleWellLeftCutoff_opposite {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    {L : ℝ} (hL : cert.L₀ ≤ L) (x : Plane) :
    p.potential (-x + displacement L) * doubleWellLeftCutoff hp cert L x = 0 := by
  by_cases hv : p.potential (-x + displacement L) = 0
  · simp [hv]
  · have hn := potential_norm_le cert hv
    rw [show -x + displacement L = -(x - displacement L) by abel, norm_neg] at hn
    have hr := doubleWellLocalizationRadii hp cert
    rcases doubleWell_at_least_one_cutoff_outside hp cert hL x with hl | hx
    · rw [show doubleWellLeftCutoff hp cert L x = 0 from
        (doubleWellBaseCutoffs_zero_one hp cert hl).1, mul_zero]
    · exfalso
      linarith [hr.2.1, hr.2.2.1]

theorem potential_mul_doubleWellRightCutoff_opposite {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    {L : ℝ} (hL : cert.L₀ ≤ L) (x : Plane) :
    p.potential (x + displacement L) * doubleWellRightCutoff hp cert L x = 0 := by
  simpa only [neg_neg, doubleWellLeftCutoff_inversion] using
    potential_mul_doubleWellLeftCutoff_opposite hp cert hL (-x)

theorem doubleWellPotential_mul_leftCutoff {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    {L : ℝ} (hL : cert.L₀ ≤ L) (x : Plane) :
    doubleWellPotential p.potential L x * doubleWellLeftCutoff hp cert L x =
      p.potential (x + displacement L) * doubleWellLeftCutoff hp cert L x := by
  rw [doubleWellPotential, add_mul, potential_mul_doubleWellLeftCutoff_opposite hp cert hL, add_zero]

theorem doubleWellPotential_mul_rightCutoff {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    {L : ℝ} (hL : cert.L₀ ≤ L) (x : Plane) :
    doubleWellPotential p.potential L x * doubleWellRightCutoff hp cert L x =
      p.potential (-x + displacement L) * doubleWellRightCutoff hp cert L x := by
  rw [doubleWellPotential, add_mul, potential_mul_doubleWellRightCutoff_opposite hp cert hL, zero_add]

theorem doubleWellBaseInnerCutoff_hasCompactSupport {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate) :
    HasCompactSupport (doubleWellBaseInnerCutoff hp cert) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Plane) (doubleWellCutoffRadius cert))
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  exact (doubleWellBaseCutoffs_zero_one hp cert (le_of_not_ge hx)).1

theorem doubleWellBaseOuterCutoff_sub_one_hasCompactSupport {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate) :
    HasCompactSupport (fun x => doubleWellBaseOuterCutoff hp cert x - 1) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Plane) (doubleWellCutoffRadius cert))
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  rw [(doubleWellBaseCutoffs_zero_one hp cert (le_of_not_ge hx)).2, sub_self]

theorem doubleWellLeftCutoff_hasCompactSupport {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate) (L : ℝ) :
    HasCompactSupport (doubleWellLeftCutoff hp cert L) :=
  (doubleWellBaseInnerCutoff_hasCompactSupport hp cert).comp_homeomorph
    (Homeomorph.addRight (displacement L))

theorem doubleWellRightCutoff_hasCompactSupport {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate) (L : ℝ) :
    HasCompactSupport (doubleWellRightCutoff hp cert L) := by
  simpa only [doubleWellRightCutoff, sub_eq_add_neg] using
    (doubleWellBaseInnerCutoff_hasCompactSupport hp cert).comp_homeomorph
      (Homeomorph.addRight (-displacement L))

private theorem exists_fixed_cutoff_gradient_bound {f : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∃ C > 0, ∀ x, cutoffGradientSq f x ≤ C := by
  obtain ⟨B, hB, hb⟩ := ((hc.fderiv ℝ).isCompact_range
    (hf.continuous_fderiv (by simp))).isBounded.exists_pos_norm_le
  have hpartial (i : Fin 2) (x : Plane) : |realPartialDerivative i f x| ≤ B := by
    calc
      _ = ‖fderiv ℝ f x (coordinateVector i)‖ := rfl
      _ ≤ ‖fderiv ℝ f x‖ * ‖coordinateVector i‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ B := by
        rw [show ‖coordinateVector i‖ = 1 by simp [coordinateVector], mul_one]
        exact hb _ ⟨x, rfl⟩
  refine ⟨2 * B ^ 2, by positivity, fun x => ?_⟩
  have hs (i : Fin 2) : realPartialDerivative i f x ^ 2 ≤ B ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) hB.le).mpr (hpartial i x)
  simpa only [cutoffGradientSq, Fin.sum_univ_two, two_mul] using add_le_add (hs 0) (hs 1)

theorem exists_doubleWellBaseCutoffs_gradient_bound {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate) :
    ∃ C > 0, ∀ x,
      cutoffGradientSq (doubleWellBaseInnerCutoff hp cert) x ≤ C ∧
      cutoffGradientSq (doubleWellBaseOuterCutoff hp cert) x ≤ C := by
  obtain ⟨Ci, hCi, hi⟩ := exists_fixed_cutoff_gradient_bound
    (doubleWellBaseInnerCutoff_contDiff hp cert) (doubleWellBaseInnerCutoff_hasCompactSupport hp cert)
  obtain ⟨Co, hCo, ho⟩ := exists_fixed_cutoff_gradient_bound
    ((doubleWellBaseOuterCutoff_contDiff hp cert).sub contDiff_const)
    (doubleWellBaseOuterCutoff_sub_one_hasCompactSupport hp cert)
  refine ⟨Ci + Co, by positivity, fun x => ?_⟩
  have ho' : cutoffGradientSq (doubleWellBaseOuterCutoff hp cert) x ≤ Co := by
    simpa only [cutoffGradientSq, realPartialDerivative, fderiv_sub_const] using ho x
  exact ⟨(hi x).trans (by linarith), ho'.trans (by linarith)⟩

private theorem cutoffGradientSq_comp_add (f : Plane → ℝ) (a x : Plane) :
    cutoffGradientSq (fun y => f (y + a)) x = cutoffGradientSq f (x + a) := by
  simp only [cutoffGradientSq, realPartialDerivative, fderiv_comp_add_right]

/-- Both binary IMS errors are bounded before either center or coupling is chosen. -/
theorem exists_doubleWellIMSError_bound {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate) :
    ∃ C > 0, ∀ (L : ℝ) (x : Plane),
      magneticIMSError (doubleWellLeftCutoff hp cert L) (doubleWellLeftOuterCutoff hp cert L) x ≤ C ∧
      magneticIMSError (doubleWellRightCutoff hp cert L) (doubleWellRightOuterCutoff hp cert L) x ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_doubleWellBaseCutoffs_gradient_bound hp cert
  refine ⟨2 * C, by positivity, fun L x => ?_⟩
  have herr (f g : Plane → ℝ) : magneticIMSError f g x =
      cutoffGradientSq f x + cutoffGradientSq g x := by
    simp only [magneticIMSError, cutoffGradientSq, Finset.sum_add_distrib]
  rw [herr, herr]
  unfold doubleWellLeftCutoff doubleWellLeftOuterCutoff doubleWellRightCutoff
    doubleWellRightOuterCutoff
  simp only [sub_eq_add_neg, cutoffGradientSq_comp_add]
  exact ⟨by linarith [(hb (x + displacement L)).1, (hb (x + displacement L)).2],
    by linarith [(hb (x + -displacement L)).1, (hb (x + -displacement L)).2]⟩

theorem exists_doubleWellCutoffs_gradient_bound {p : CuspParameters}
    (hp : p.BasicConditions) (cert : p.SeparationCertificate) :
    ∃ C > 0, ∀ (L : ℝ) (x : Plane),
      cutoffGradientSq (doubleWellLeftCutoff hp cert L) x +
        cutoffGradientSq (doubleWellRightCutoff hp cert L) x +
        cutoffGradientSq (doubleWellExteriorCutoff hp cert L) x ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_doubleWellBaseCutoffs_gradient_bound hp cert
  refine ⟨6 * C, by positivity, fun L x => ?_⟩
  have hleft : cutoffGradientSq (doubleWellLeftCutoff hp cert L) x ≤ C := by
    unfold doubleWellLeftCutoff
    rw [cutoffGradientSq_comp_add]
    exact (hb (x + displacement L)).1
  have hright : cutoffGradientSq (doubleWellRightCutoff hp cert L) x ≤ C := by
    unfold doubleWellRightCutoff
    simp only [sub_eq_add_neg, cutoffGradientSq_comp_add]
    exact (hb (x + -displacement L)).1
  have houterLeft : cutoffGradientSq (doubleWellLeftOuterCutoff hp cert L) x ≤ C := by
    unfold doubleWellLeftOuterCutoff
    rw [cutoffGradientSq_comp_add]
    exact (hb (x + displacement L)).2
  have houterRight : cutoffGradientSq (doubleWellRightOuterCutoff hp cert L) x ≤ C := by
    unfold doubleWellRightOuterCutoff
    simp only [sub_eq_add_neg, cutoffGradientSq_comp_add]
    exact (hb (x + -displacement L)).2
  have hl := doubleWellLeftOuterCutoff_range hp cert L x
  have hr := doubleWellRightOuterCutoff_range hp cert L x
  have hls : doubleWellLeftOuterCutoff hp cert L x ^ 2 ≤ 1 := (sq_le_one_iff₀ hl.1).mpr hl.2
  have hrs : doubleWellRightOuterCutoff hp cert L x ^ 2 ≤ 1 := (sq_le_one_iff₀ hr.1).mpr hr.2
  have hproduct := cutoffGradientSq_mul_le
    ((doubleWellLeftOuterCutoff_contDiff hp cert L).differentiable (by simp) x)
    ((doubleWellRightOuterCutoff_contDiff hp cert L).differentiable (by simp) x)
  have htermLeft := mul_le_mul hrs houterLeft
    (cutoffGradientSq_nonneg _ _) (by norm_num : (0 : ℝ) ≤ 1)
  have htermRight := mul_le_mul hls houterRight
    (cutoffGradientSq_nonneg _ _) (by norm_num : (0 : ℝ) ≤ 1)
  change cutoffGradientSq (doubleWellExteriorCutoff hp cert L) x ≤ _ at hproduct
  simp only [one_mul] at htermLeft htermRight
  nlinarith only [hleft, hright, hproduct, htermLeft, htermRight]

end InfiniteZero.CuspParameters
