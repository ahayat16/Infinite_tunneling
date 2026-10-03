import InfiniteZero.LandauExteriorConvolution
import InfiniteZero.ActiveCrossKernelBound
import InfiniteZero.InactiveKernelBounds
import InfiniteZero.AtomicCuspSourceSupport
import InfiniteZero.WavefunctionL2Bridge

/-!
# Reconstruction on the opposite well support

The actual one-state resolvent formula is estimated almost everywhere by the
three component source L¹ norms. The magnetic phases have norm one, and all
integrability needed to bound the convolution follows from the component
source bounds. No pointwise choice of the ground-state phase is required.
-/

noncomputable section
open MeasureTheory Set Filter

namespace InfiniteZero

theorem norm_rightPhysicalSource_affine (b : ℝ) (v : Potential)
    (L coupling : ℝ) (φ : Wavefunction) (z : Plane) :
    ‖rightPhysicalSource b v L coupling φ (displacement L - z)‖ =
      ‖atomicSource coupling⁻¹ v φ z‖ := by
  rw [rightPhysicalSource_gauge, norm_mul, Complex.norm_exp]
  simp only [sub_sub_cancel, Complex.neg_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_self, neg_zero, Real.exp_zero, one_mul]

private theorem rightSourceAffine_measurable {p : CuspParameters}
    (hp : p.BasicConditions) {φ : Wavefunction} (hφ : Continuous φ)
    (L coupling : ℝ) :
    Measurable (fun z : Plane =>
      rightPhysicalSource p.b p.potential L coupling φ (displacement L - z)) := by
  have he : (fun z : Plane =>
      rightPhysicalSource p.b p.potential L coupling φ (displacement L - z)) =
      (fun z => Complex.exp (-Complex.I *
          ((p.b * coupling / 2 * wedge (displacement L - z) (displacement L) : ℝ) : ℂ)) *
        ∑ i : Fin 3, componentSource p coupling⁻¹ φ i z) := by
    funext z
    rw [rightPhysicalSource_gauge, sub_sub_cancel]
    exact congrArg (fun a : ℂ => _ * a) (congrFun (componentSource_sum p coupling⁻¹ φ) z).symm
  rw [he]
  apply Measurable.mul
  · unfold wedge
    fun_prop
  · exact (continuous_finsetSum _ fun i _ =>
      componentSource_continuous hp coupling⁻¹ hφ i).measurable

/-- A resolvent convolution at a fixed target is bounded by the three genuine
source L¹ norms. Kernel bounds are required only where each source is nonzero.
The integrability of the transformed complex convolution is proved here. -/
theorem norm_rightState_le_componentL1_of_representation
    {p : CuspParameters} (hp : p.BasicConditions) {L coupling E : ℝ}
    (hc : 0 < coupling) (hE : 0 < E) {φ : Wavefunction} (hφ : Continuous φ)
    (C : Fin 3 → ℝ) (x : Plane)
    (hsep : ∀ i : Fin 3, ∀ z ∈ Function.support (componentSource p coupling⁻¹ φ i),
      0 < ‖z + (x + displacement L) - 2 • displacement L‖)
    (hbound : ∀ i : Fin 3, ∀ z ∈ Function.support (componentSource p coupling⁻¹ φ i),
      landauKernel p.b coupling⁻¹ E
        ‖z + (x + displacement L) - 2 • displacement L‖ ≤ C i)
    (hrep : rightState p.b L coupling φ x =
      -(((coupling⁻¹) ^ 2 : ℝ) : ℂ) *
        ∫ y : Plane, freeLandauKernel p.b coupling⁻¹ E x y *
          rightPhysicalSource p.b p.potential L coupling φ y) :
    ‖rightState p.b L coupling φ x‖ ≤
      (coupling⁻¹) ^ 2 *
        ∑ i : Fin 3, C i * ∫ z : Plane, ‖componentSource p coupling⁻¹ φ i z‖ := by
  let F : Fin 3 → Wavefunction := componentSource p coupling⁻¹ φ
  let G : Wavefunction := fun z =>
    freeLandauKernel p.b coupling⁻¹ E x (displacement L - z) *
      rightPhysicalSource p.b p.potential L coupling φ (displacement L - z)
  let B : Plane → ℝ := fun z => ∑ i : Fin 3, C i * ‖F i z‖
  have hdist (z : Plane) : x - (displacement L - z) =
      z + (x + displacement L) - 2 • displacement L := by module
  have hB : Integrable B := integrable_finsetSum Finset.univ fun i _ =>
    ((componentSource_integrable hp coupling⁻¹ hφ i).norm.const_mul (C i))
  have hGm : Measurable G :=
    ((measurable_freeLandauKernel p.b coupling⁻¹ E).comp
      (measurable_const.prodMk (measurable_const.sub measurable_id))).mul
        (rightSourceAffine_measurable hp hφ L coupling)
  have hGB : ∀ z, ‖G z‖ ≤ B z := by
    intro z
    have hsum : ‖atomicSource coupling⁻¹ p.potential φ z‖ ≤
        ∑ i : Fin 3, ‖F i z‖ := by
      rw [← componentSource_sum]
      exact norm_sum_le _ _
    calc
      ‖G z‖ = ‖freeLandauKernel p.b coupling⁻¹ E x (displacement L - z)‖ *
          ‖atomicSource coupling⁻¹ p.potential φ z‖ := by
        dsimp only [G]
        rw [norm_mul, norm_rightPhysicalSource_affine]
      _ ≤ ‖freeLandauKernel p.b coupling⁻¹ E x (displacement L - z)‖ *
          ∑ i : Fin 3, ‖F i z‖ :=
        mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
      _ = ∑ i : Fin 3,
          ‖freeLandauKernel p.b coupling⁻¹ E x (displacement L - z)‖ * ‖F i z‖ :=
        Finset.mul_sum _ _ _
      _ ≤ B z := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hz : F i z = 0
        · simp only [hz, norm_zero, mul_zero, le_refl]
        · have hrad : 0 < ‖x - (displacement L - z)‖ := by
            rw [hdist]
            exact hsep i z hz
          rw [norm_freeLandauKernel hp.b_pos (inv_pos.mpr hc) hE hrad, hdist]
          exact mul_le_mul_of_nonneg_right (hbound i z hz) (norm_nonneg _)
  have hG : Integrable G := hB.mono' hGm.aestronglyMeasurable (Eventually.of_forall hGB)
  have hb : (∫ z : Plane, ‖G z‖) ≤
      ∑ i : Fin 3, C i * ∫ z : Plane, ‖F i z‖ := by
    calc
      _ ≤ ∫ z : Plane, B z := integral_mono_ae hG.norm hB (Eventually.of_forall hGB)
      _ = _ := by
        rw [integral_finsetSum Finset.univ (fun i _ =>
          (componentSource_integrable hp coupling⁻¹ hφ i).norm.const_mul (C i))]
        simp only [integral_const_mul, F]
  have hint : (∫ y : Plane, freeLandauKernel p.b coupling⁻¹ E x y *
      rightPhysicalSource p.b p.potential L coupling φ y) = ∫ z : Plane, G z := by
    exact (integral_sub_left_eq_self
      (fun y : Plane => freeLandauKernel p.b coupling⁻¹ E x y *
        rightPhysicalSource p.b p.potential L coupling φ y)
      volume (displacement L)).symm
  rw [hrep, hint, norm_mul, norm_neg]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_pow, sq_abs]
  exact mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm G).trans hb)
    (sq_nonneg coupling⁻¹)

/-- The fixed-target bound applies almost everywhere on any specified target
set. No pointwise strengthening of the resolvent representation is assumed. -/
theorem RightResolventRepresentation.ae_norm_rightState_le_componentL1
    {p : CuspParameters} (hp : p.BasicConditions) {L coupling E : ℝ}
    (hc : 0 < coupling) (hE : 0 < E) {φ : Wavefunction} (hφ : Continuous φ)
    (hR : RightResolventRepresentation p.b p.potential L coupling E φ)
    (S : Set Plane) (C : Fin 3 → ℝ)
    (hsep : ∀ w ∈ S, ∀ i : Fin 3,
      ∀ z ∈ Function.support (componentSource p coupling⁻¹ φ i),
        0 < ‖z + w - 2 • displacement L‖)
    (hbound : ∀ w ∈ S, ∀ i : Fin 3,
      ∀ z ∈ Function.support (componentSource p coupling⁻¹ φ i),
        landauKernel p.b coupling⁻¹ E ‖z + w - 2 • displacement L‖ ≤ C i) :
    ∀ᵐ x : Plane, x + displacement L ∈ S →
      ‖rightState p.b L coupling φ x‖ ≤ (coupling⁻¹) ^ 2 *
        ∑ i : Fin 3, C i * ∫ z : Plane, ‖componentSource p coupling⁻¹ φ i z‖ := by
  filter_upwards [hR] with x hx hS
  exact norm_rightState_le_componentL1_of_representation hp hc hE hφ C x
    (hsep _ hS) (hbound _ hS) hx

namespace CuspParameters

/-- The three closed component supports contain the support of the actual
potential. No cancellation assumption or strict interior condition is needed. -/
theorem potential_support_subset_component_tsupports (p : CuspParameters) :
    Function.support p.potential ⊆
      tsupport p.core ∪ tsupport p.cuspPlus ∪ tsupport p.cuspMinus := by
  intro x hx
  by_cases h0 : p.core x = 0
  · by_cases h1 : p.cuspPlus x = 0
    · have h2 : p.cuspMinus x ≠ 0 := by
        intro h2
        exact hx (by simp [potential, h0, h1, h2])
      exact Or.inr (subset_tsupport _ h2)
    · exact Or.inl (Or.inr (subset_tsupport _ h1))
  · exact Or.inl (Or.inl (subset_tsupport _ h0))

private theorem componentSource_support_subset_union (p : CuspParameters)
    (h : ℝ) (φ : Wavefunction) (i : Fin 3) :
    Function.support (componentSource p h φ i) ⊆
      tsupport p.core ∪ tsupport p.cuspPlus ∪ tsupport p.cuspMinus := by
  intro z hz
  fin_cases i
  · have h0 : p.core z ≠ 0 := by
      intro h0
      exact hz (by simp [componentSource, atomicSource, componentPotential, h0])
    exact Or.inl (Or.inl (subset_tsupport _ h0))
  · exact Or.inl (Or.inr (subset_tsupport _ (componentSource_plus_support_subset p h φ hz)))
  · exact Or.inr (subset_tsupport _ (componentSource_minus_support_subset p h φ hz))

/-- One constant bounds the kernel from a core source by the complete route
action `G+J`, and from either cusp source by the bridge action `J`.
The latter keeps the explicit factor `λ²`; the source L¹ bound supplies G.
Both energies remain independent, and the constant precedes all of them. -/
theorem exists_oppositeSupport_kernel_component_bounds
    {p : CuspParameters} (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    {L : ℝ} (hL : cert.L₀ ≤ L) :
    ∃ C > 0, ∀ coupling : ℝ, 1 ≤ coupling →
      ∀ E ∈ Icc (1 / 2 : ℝ) 1, ∀ E₀ ∈ Ioc (0 : ℝ) 2,
      ∀ w ∈ tsupport p.core ∪ tsupport p.cuspPlus ∪ tsupport p.cuspMinus,
      (∀ z ∈ tsupport p.core,
        landauKernel p.b coupling⁻¹ E ‖z + w - 2 • displacement L‖ ≤
          C * Real.exp (-coupling * (bridgeAction p.b E₀ p.R +
            bridgeAction p.b E (Geometry.activeDistance p.R L)))) ∧
      (∀ z ∈ tsupport p.cuspPlus ∪ tsupport p.cuspMinus,
        landauKernel p.b coupling⁻¹ E ‖z + w - 2 • displacement L‖ ≤
          C * coupling ^ 2 *
            Real.exp (-coupling * bridgeAction p.b E (Geometry.activeDistance p.R L))) := by
  obtain ⟨Ki, hKi, hi⟩ := exists_inactiveKernelUpperBounds hp cert hL
    (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (hopMargin_pos hp)
  have hRL : p.R < 2 * L := by linarith [cert.radius_lt hL, hp.radius_pos]
  obtain ⟨Ka, hKa, ha⟩ := exists_activeCrossKernel_exact_action_upper hp hRL
  let C := Ki + Ka
  have hC : 0 < C := add_pos hKi hKa
  refine ⟨C, hC, ?_⟩
  intro coupling hc E hE E₀ hE₀ w hw
  have hcp : 0 < coupling := zero_lt_one.trans_le hc
  have hh : 0 < coupling⁻¹ := inv_pos.mpr hcp
  have hh1 : coupling⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc
  have hc2 : 1 ≤ coupling ^ 2 := one_le_pow₀ hc
  have hG : 0 < bridgeAction p.b E₀ p.R :=
    bridgeAction_pos hp.b_pos.ne' hE₀.1 hp.radius_pos
  have hd := (hopMargin_pos hp).le
  have hKiC : Ki ≤ C := le_add_of_nonneg_right hKa.le
  have hKaC : Ka ≤ C := le_add_of_nonneg_left hKi.le
  have hstep {r a d : ℝ}
      (hb : landauKernel p.b coupling⁻¹ E r ≤ Ki * Real.exp (-a / coupling⁻¹))
      (had : d ≤ a) :
      landauKernel p.b coupling⁻¹ E r ≤ C * Real.exp (-coupling * d) := by
    apply hb.trans
    apply mul_le_mul hKiC _ (Real.exp_pos _).le hC.le
    apply Real.exp_le_exp.mpr
    rw [div_inv_eq_mul]
    nlinarith only [mul_le_mul_of_nonneg_left had hcp.le]
  have hstep2 {r a : ℝ}
      (hb : landauKernel p.b coupling⁻¹ E r ≤ Ki * Real.exp (-a / coupling⁻¹))
      (had : bridgeAction p.b E (Geometry.activeDistance p.R L) ≤ a) :
      landauKernel p.b coupling⁻¹ E r ≤ C * coupling ^ 2 *
        Real.exp (-coupling * bridgeAction p.b E (Geometry.activeDistance p.R L)) := by
    apply (hstep hb had).trans
    exact mul_le_mul_of_nonneg_right
      (by nlinarith only [mul_le_mul_of_nonneg_left hc2 hC.le]) (Real.exp_pos _).le
  have hactive {z : Plane}
      (hz : (z ∈ tsupport p.cuspPlus ∧ w ∈ tsupport p.cuspMinus) ∨
        (z ∈ tsupport p.cuspMinus ∧ w ∈ tsupport p.cuspPlus)) :
      landauKernel p.b coupling⁻¹ E ‖z + w - 2 • displacement L‖ ≤
        C * coupling ^ 2 *
          Real.exp (-coupling * bridgeAction p.b E (Geometry.activeDistance p.R L)) := by
    have hh := ha E hE coupling⁻¹ hh hh1 z w hz
    simp only [inv_pow, inv_inv, div_inv_eq_mul] at hh
    apply hh.trans
    rw [show -bridgeAction p.b E (Geometry.activeDistance p.R L) * coupling =
      -coupling * bridgeAction p.b E (Geometry.activeDistance p.R L) by ring]
    gcongr
  constructor
  · intro z hz
    rcases hw with (hw | hw) | hw
    · exact hstep (hi.core_core E hE E₀ hE₀ z hz w hw coupling⁻¹ hh) (by linarith)
    · exact hstep (hi.mixed E hE E₀ hE₀ z w (Or.inl ⟨hz, Or.inl hw⟩)
        coupling⁻¹ hh) (by linarith)
    · exact hstep (hi.mixed E hE E₀ hE₀ z w (Or.inl ⟨hz, Or.inr hw⟩)
        coupling⁻¹ hh) (by linarith)
  · intro z hz
    rcases hw with (hw | hw) | hw
    · exact hstep2 (hi.mixed E hE E₀ hE₀ z w (Or.inr ⟨hw, hz⟩)
        coupling⁻¹ hh) (by linarith)
    · rcases hz with hz | hz
      · exact hstep2 (hi.same_cusp E hE z w (Or.inl ⟨hz, hw⟩)
          coupling⁻¹ hh) (by linarith)
      · exact hactive (Or.inr ⟨hz, hw⟩)
    · rcases hz with hz | hz
      · exact hactive (Or.inl ⟨hz, hw⟩)
      · exact hstep2 (hi.same_cusp E hE z w (Or.inr ⟨hz, hw⟩)
          coupling⁻¹ hh) (by linarith)

/-- Actual reconstruction on the left potential support, with the right
atomic state. The bridge energy E and radial source energy E₀ are distinct.
Only the genuine resolvent equation is supplied; all kernel estimates and
source integrability are consequences of the proved geometric bounds. -/
theorem exists_oppositeSupport_reconstruction_componentL1
    {p : CuspParameters} (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    {L : ℝ} (hL : cert.L₀ ≤ L) :
    ∃ C > 0, ∀ coupling : ℝ, 1 ≤ coupling →
      ∀ E ∈ Icc (1 / 2 : ℝ) 1, ∀ E₀ ∈ Ioc (0 : ℝ) 2,
      ∀ φ : Wavefunction, Continuous φ →
      RightResolventRepresentation p.b p.potential L coupling E φ →
      ∀ᵐ x : Plane, p.potential (x + displacement L) ≠ 0 →
        ‖rightState p.b L coupling φ x‖ ≤ C *
          ((coupling⁻¹) ^ 2 * Real.exp (-coupling *
            (bridgeAction p.b E₀ p.R + bridgeAction p.b E (Geometry.activeDistance p.R L))) *
              (∫ z : Plane, ‖componentSource p coupling⁻¹ φ 0 z‖) +
            Real.exp (-coupling * bridgeAction p.b E (Geometry.activeDistance p.R L)) *
              ((∫ z : Plane, ‖componentSource p coupling⁻¹ φ 1 z‖) +
                ∫ z : Plane, ‖componentSource p coupling⁻¹ φ 2 z‖)) := by
  obtain ⟨C, hC, hk⟩ := exists_oppositeSupport_kernel_component_bounds hp cert hL
  refine ⟨C, hC, ?_⟩
  intro coupling hc E hE E₀ hE₀ φ hφ hR
  have hcp : 0 < coupling := zero_lt_one.trans_le hc
  let S := tsupport p.core ∪ tsupport p.cuspPlus ∪ tsupport p.cuspMinus
  let K0 := C * Real.exp (-coupling * (bridgeAction p.b E₀ p.R +
    bridgeAction p.b E (Geometry.activeDistance p.R L)))
  let K1 := C * coupling ^ 2 *
    Real.exp (-coupling * bridgeAction p.b E (Geometry.activeDistance p.R L))
  let K : Fin 3 → ℝ := ![K0, K1, K1]
  have hsep : ∀ w ∈ S, ∀ i : Fin 3,
      ∀ z ∈ Function.support (componentSource p coupling⁻¹ φ i),
        0 < ‖z + w - 2 • displacement L‖ := by
    intro w hw i z hz
    have ha := cert.component_support_annulus hp hL
      (componentSource_support_subset_union p coupling⁻¹ φ i hz) hw
    exact ha.1.trans_le ha.2.1
  have hkernel : ∀ w ∈ S, ∀ i : Fin 3,
      ∀ z ∈ Function.support (componentSource p coupling⁻¹ φ i),
        landauKernel p.b coupling⁻¹ E ‖z + w - 2 • displacement L‖ ≤ K i := by
    intro w hw i z hz
    have hh := hk coupling hc E hE E₀ hE₀ w hw
    fin_cases i
    · apply hh.1 z
      apply subset_tsupport
      intro hz0
      exact hz (by simp [componentSource, atomicSource, componentPotential, hz0])
    · exact hh.2 z (Or.inl (subset_tsupport _
        (componentSource_plus_support_subset p coupling⁻¹ φ hz)))
    · exact hh.2 z (Or.inr (subset_tsupport _
        (componentSource_minus_support_subset p coupling⁻¹ φ hz)))
  have h := hR.ae_norm_rightState_le_componentL1 hp hcp
    (lt_of_lt_of_le (by norm_num) hE.1) hφ S K hsep hkernel
  filter_upwards [h] with x hx hxV
  have hb := hx (potential_support_subset_component_tsupports p hxV)
  convert hb using 1
  norm_num [K, Fin.sum_univ_succ, K0, K1]
  field_simp

end CuspParameters

/-- An AE bound on the support of a bounded compact potential controls both
the diagonal defect integral and the mass of its multiplication operator.
All integrability follows from continuity and compact support. -/
theorem potential_weighted_mass_le_of_ae_norm_bound
    (V : Potential) (hV : Continuous V) (hVc : HasCompactSupport V)
    (hVb : ∀ x, |V x| ≤ 1) {u : Wavefunction} (hu : Continuous u)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᵐ x : Plane, V x ≠ 0 → ‖u x‖ ≤ B) :
    |∫ x : Plane, V x * ‖u x‖ ^ 2| ≤ B ^ 2 * ∫ x : Plane, |V x| ∧
      mass (fun x => (V x : ℂ) * u x) ≤ B ^ 2 * ∫ x : Plane, |V x| := by
  let f : Plane → ℝ := fun x => V x * ‖u x‖ ^ 2
  let a : Plane → ℝ := fun x => |V x| * ‖u x‖ ^ 2
  let q : Wavefunction := fun x => (V x : ℂ) * u x
  have hfc : HasCompactSupport f := by
    apply HasCompactSupport.intro hVc
    intro x hx
    simp only [f, image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hac : HasCompactSupport a := by
    apply HasCompactSupport.intro hVc
    intro x hx
    simp only [a, image_eq_zero_of_notMem_tsupport hx, abs_zero, zero_mul]
  have hqc : HasCompactSupport q := by
    apply HasCompactSupport.intro hVc
    intro x hx
    simp only [q, image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero, zero_mul]
  have hfi : Integrable f :=
    (hV.mul (hu.norm.pow 2)).integrable_of_hasCompactSupport hfc
  have hai : Integrable a :=
    (hV.abs.mul (hu.norm.pow 2)).integrable_of_hasCompactSupport hac
  have hqLp : MemLp q 2 volume :=
    ((Complex.continuous_ofReal.comp hV).mul hu).memLp_of_hasCompactSupport hqc
  have hVi : Integrable (fun x => |V x|) := by
    simpa only [Real.norm_eq_abs] using (hV.integrable_of_hasCompactSupport hVc).norm
  have hai_le : (∫ x : Plane, a x) ≤ B ^ 2 * ∫ x : Plane, |V x| := by
    calc
      _ ≤ ∫ x : Plane, B ^ 2 * |V x| := by
        apply integral_mono_ae hai (hVi.const_mul (B ^ 2))
        filter_upwards [hb] with x hx
        by_cases hz : V x = 0
        · simp only [a, hz, abs_zero, zero_mul, mul_zero, le_refl]
        · have hn := (sq_le_sq₀ (norm_nonneg _) hB).mpr (hx hz)
          dsimp only [a]
          nlinarith only [mul_le_mul_of_nonneg_left hn (abs_nonneg (V x))]
      _ = _ := integral_const_mul _ _
  constructor
  · calc
      _ ≤ ∫ x : Plane, a x := by
        simpa only [f, a, Real.norm_eq_abs, abs_mul, abs_pow, abs_norm] using
          norm_integral_le_integral_norm f
      _ ≤ _ := hai_le
  · calc
      _ ≤ ∫ x : Plane, a x := by
        apply integral_mono_ae hqLp.norm.integrable_sq hai
        filter_upwards [] with x
        have hv : |V x| ^ 2 ≤ |V x| := by
          nlinarith only [hVb x, abs_nonneg (V x)]
        simpa only [q, a, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow] using
          mul_le_mul_of_nonneg_right hv (sq_nonneg ‖u x‖)
      _ ≤ _ := hai_le

/-- A continuous atomic representative gives a continuous translated right
state; no smoothness or differential equation is used for this fact. -/
theorem continuous_rightState_of_continuous (b L coupling : ℝ)
    {φ : Wavefunction} (hφ : Continuous φ) : Continuous (rightState b L coupling φ) := by
  unfold rightState leftState magneticTranslation
  apply Continuous.mul
  · unfold wedge
    fun_prop
  · exact hφ.comp (continuous_id.neg.sub continuous_const)

namespace CuspParameters

/-- The actual opposite-potential mass and defect follow from the component
L¹ reconstruction. The fixed factor `∫ |V|` is independent of the separation,
energy and coupling. These are absolute integral bounds, not assumptions on
the form domain or pointwise validity of the resolvent equation. -/
theorem exists_oppositeSupport_mass_bound_componentL1
    {p : CuspParameters} (hp : p.BasicConditions) (cert : p.SeparationCertificate)
    {L : ℝ} (hL : cert.L₀ ≤ L) :
    ∃ C > 0, ∀ coupling : ℝ, 1 ≤ coupling →
      ∀ E ∈ Icc (1 / 2 : ℝ) 1, ∀ E₀ ∈ Ioc (0 : ℝ) 2,
      ∀ φ : Wavefunction, Continuous φ →
      RightResolventRepresentation p.b p.potential L coupling E φ →
      let B := C *
        ((coupling⁻¹) ^ 2 * Real.exp (-coupling *
          (bridgeAction p.b E₀ p.R + bridgeAction p.b E (Geometry.activeDistance p.R L))) *
            (∫ z : Plane, ‖componentSource p coupling⁻¹ φ 0 z‖) +
          Real.exp (-coupling * bridgeAction p.b E (Geometry.activeDistance p.R L)) *
            ((∫ z : Plane, ‖componentSource p coupling⁻¹ φ 1 z‖) +
              ∫ z : Plane, ‖componentSource p coupling⁻¹ φ 2 z‖))
      |∫ x : Plane, p.potential (x + displacement L) *
        ‖rightState p.b L coupling φ x‖ ^ 2| ≤ B ^ 2 * ∫ x : Plane, |p.potential x| ∧
      mass (fun x => (p.potential (x + displacement L) : ℂ) *
        rightState p.b L coupling φ x) ≤ B ^ 2 * ∫ x : Plane, |p.potential x| := by
  obtain ⟨C, hC, hb⟩ := exists_oppositeSupport_reconstruction_componentL1 hp cert hL
  refine ⟨C, hC, ?_⟩
  intro coupling hc E hE E₀ hE₀ φ hφ hR
  dsimp only
  have hVc : HasCompactSupport (fun x : Plane => p.potential (x + displacement L)) :=
    (potential_hasCompactSupport hp).comp_homeomorph (Homeomorph.addRight (displacement L))
  have hVb (x : Plane) : |p.potential (x + displacement L)| ≤ 1 :=
    abs_le.mpr ⟨(potential_range hp _).1, (potential_range hp _).2.trans (by norm_num)⟩
  have h := potential_weighted_mass_le_of_ae_norm_bound
    (fun x : Plane => p.potential (x + displacement L))
    ((potential_contDiff hp).continuous.comp (continuous_id.add continuous_const)) hVc hVb
    (continuous_rightState_of_continuous p.b L coupling hφ) (by positivity)
    (hb coupling hc E hE E₀ hE₀ φ hφ hR)
  simpa only [integral_add_right_eq_self (fun x : Plane => |p.potential x|) (displacement L)]
    using h

end CuspParameters
end InfiniteZero
