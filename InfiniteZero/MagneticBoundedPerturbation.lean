import InfiniteZero.MagneticTestGraph
import Mathlib.MeasureTheory.Function.Holder

/-!
# Bounded potential perturbations of the actual closed graph

Multiplication by a bounded continuous real potential is a bounded operator on
physical complex L². The associated shear of L² × L² transports the concrete
test graph, and therefore its closure, to the perturbed magnetic graph.
-/

noncomputable section
open MeasureTheory Set
namespace InfiniteZero

private theorem memLp_complexPotential_top (W : Potential) (hW : Continuous W)
    {C : ℝ} (hbound : ∀ x, |W x| ≤ C) :
    MemLp (fun x => (W x : ℂ)) ⊤ volume := by
  apply memLp_top_of_bound (Complex.continuous_ofReal.comp hW).aestronglyMeasurable C
  exact Filter.Eventually.of_forall fun x => by simpa using hbound x

/-- Actual multiplication by `W` as a bounded complex-linear map on physical L². -/
def boundedPotentialMul (W : Potential) (hW : Continuous W)
    {C : ℝ} (hbound : ∀ x, |W x| ≤ C) : L2Space →L[ℂ] L2Space :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2
    ((memLp_complexPotential_top W hW hbound).toLp (fun x => (W x : ℂ)))

theorem coe_boundedPotentialMul (W : Potential) (hW : Continuous W)
    {C : ℝ} (hbound : ∀ x, |W x| ≤ C) (u : L2Space) :
    boundedPotentialMul W hW hbound u =ᵐ[volume] fun x => (W x : ℂ) * u x := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2)
    ((memLp_complexPotential_top W hW hbound).toLp (fun x => (W x : ℂ))) u
  filter_upwards [h, (memLp_complexPotential_top W hW hbound).coeFn_toLp] with x hx hWx
  simpa only [boundedPotentialMul, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.mul_apply', hWx] using hx

theorem norm_boundedPotentialMul_apply_le (W : Potential) (hW : Continuous W)
    {C : ℝ} (hbound : ∀ x, |W x| ≤ C) (u : L2Space) :
    ‖boundedPotentialMul W hW hbound u‖ ≤ C * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coe_boundedPotentialMul W hW hbound u] with x hx
  rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)

theorem memLp_boundedPotential_mul (W : Potential) (hW : Continuous W)
    {C : ℝ} (hbound : ∀ x, |W x| ≤ C) {ψ : Wavefunction} (hψ : MemLp ψ 2 volume) :
    MemLp (fun x => (W x : ℂ) * ψ x) 2 volume :=
  (ContinuousLinearMap.mul ℂ ℂ).memLp_of_bilin 2
    (memLp_complexPotential_top W hW hbound) hψ

theorem boundedPotentialMul_toLp (W : Potential) (hW : Continuous W)
    {C : ℝ} (hbound : ∀ x, |W x| ≤ C) {ψ : Wavefunction} (hψ : MemLp ψ 2 volume) :
    boundedPotentialMul W hW hbound (hψ.toLp ψ) =
      (memLp_boundedPotential_mul W hW hbound hψ).toLp (fun x => (W x : ℂ) * ψ x) := by
  apply Lp.ext
  filter_upwards [coe_boundedPotentialMul W hW hbound (hψ.toLp ψ), hψ.coeFn_toLp,
    (memLp_boundedPotential_mul W hW hbound hψ).coeFn_toLp] with x hx hψx hWx
  simp only [hx, hψx, hWx]

/-- Adding a bounded operator to the second coordinate is a continuous linear equivalence. -/
def magneticGraphShear (coupling : ℝ) (B : L2Space →L[ℂ] L2Space) :
    (L2Space × L2Space) ≃L[ℂ] (L2Space × L2Space) where
  toFun q := (q.1, q.2 + (coupling ^ 2 : ℂ) • B q.1)
  invFun q := (q.1, q.2 - (coupling ^ 2 : ℂ) • B q.1)
  left_inv q := by
    change (q.1, q.2 + (coupling ^ 2 : ℂ) • B q.1 - (coupling ^ 2 : ℂ) • B q.1) = q
    rw [add_sub_cancel_right]
  right_inv q := by
    change (q.1, q.2 - (coupling ^ 2 : ℂ) • B q.1 + (coupling ^ 2 : ℂ) • B q.1) = q
    rw [sub_add_cancel]
  map_add' q p := by
    apply Prod.ext
    · rfl
    · change q.2 + p.2 + (coupling ^ 2 : ℂ) • B (q.1 + p.1) = _
      simp only [map_add, smul_add, Prod.snd_add]
      abel
  map_smul' c q := by
    apply Prod.ext
    · rfl
    · change c • q.2 + (coupling ^ 2 : ℂ) • B (c • q.1) =
        c • (q.2 + (coupling ^ 2 : ℂ) • B q.1)
      simp only [map_smul, smul_add]
      rw [smul_comm (coupling ^ 2 : ℂ) c]
  continuous_toFun := continuous_fst.prodMk
    (continuous_snd.add ((B.continuous.comp continuous_fst).const_smul _))
  continuous_invFun := continuous_fst.prodMk
    (continuous_snd.sub ((B.continuous.comp continuous_fst).const_smul _))

@[simp] theorem magneticGraphShear_apply (coupling : ℝ) (B : L2Space →L[ℂ] L2Space)
    (q : L2Space × L2Space) :
    magneticGraphShear coupling B q = (q.1, q.2 + (coupling ^ 2 : ℂ) • B q.1) := rfl

theorem magneticHamiltonian_add_potential (b coupling : ℝ) (V W : Potential)
    (ψ : Wavefunction) :
    magneticHamiltonian b coupling (V + W) ψ =
      magneticHamiltonian b coupling V ψ +
        (coupling ^ 2 : ℂ) • (fun x => (W x : ℂ) * ψ x) := by
  ext x
  simp only [magneticHamiltonian, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_pow]
  ring

theorem memLp_magneticHamiltonian_add_potential_iff (b coupling : ℝ)
    (V W : Potential) (hW : Continuous W) {C : ℝ} (hbound : ∀ x, |W x| ≤ C)
    {ψ : Wavefunction} (hψ : MemLp ψ 2 volume) :
    MemLp (magneticHamiltonian b coupling (V + W) ψ) 2 volume ↔
      MemLp (magneticHamiltonian b coupling V ψ) 2 volume := by
  rw [magneticHamiltonian_add_potential]
  have hp := (memLp_boundedPotential_mul W hW hbound hψ).const_smul (coupling ^ 2 : ℂ)
  constructor
  · intro h
    simpa only [add_sub_cancel_right] using h.sub hp
  · exact fun h => h.add hp

theorem toLp_magneticHamiltonian_add_potential (b coupling : ℝ)
    (V W : Potential) (hW : Continuous W) {C : ℝ} (hbound : ∀ x, |W x| ≤ C)
    {ψ : Wavefunction} (hψ : MemLp ψ 2 volume)
    (hH : MemLp (magneticHamiltonian b coupling V ψ) 2 volume)
    (hHW : MemLp (magneticHamiltonian b coupling (V + W) ψ) 2 volume) :
    hHW.toLp (magneticHamiltonian b coupling (V + W) ψ) =
      hH.toLp (magneticHamiltonian b coupling V ψ) +
        (coupling ^ 2 : ℂ) • boundedPotentialMul W hW hbound (hψ.toLp ψ) := by
  rw [boundedPotentialMul_toLp W hW hbound hψ,
    ← MemLp.toLp_const_smul, ← MemLp.toLp_add]
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun x =>
    congrFun (magneticHamiltonian_add_potential b coupling V W ψ) x

/-- The shear transports graph membership with no assumption on the base potential. -/
theorem magneticGraphShear_mem_testGraph_iff (b coupling : ℝ)
    (V W : Potential) (hW : Continuous W) {C : ℝ} (hbound : ∀ x, |W x| ≤ C)
    (q : L2Space × L2Space) :
    magneticGraphShear coupling (boundedPotentialMul W hW hbound) q ∈
        magneticTestGraph b coupling (V + W) ↔ q ∈ magneticTestGraph b coupling V := by
  constructor
  · rintro ⟨ψ, hψ, hψL, hHW, hq₁, hq₂⟩
    have hH := (memLp_magneticHamiltonian_add_potential_iff b coupling V W hW hbound hψL).mp hHW
    refine ⟨ψ, hψ, hψL, hH, hq₁, ?_⟩
    change q.2 + (coupling ^ 2 : ℂ) • boundedPotentialMul W hW hbound q.1 = _ at hq₂
    change q.1 = hψL.toLp ψ at hq₁
    rw [toLp_magneticHamiltonian_add_potential b coupling V W hW hbound hψL hH hHW,
      hq₁] at hq₂
    exact add_right_cancel hq₂
  · rintro ⟨ψ, hψ, hψL, hH, hq₁, hq₂⟩
    have hHW := (memLp_magneticHamiltonian_add_potential_iff b coupling V W hW hbound hψL).mpr hH
    refine ⟨ψ, hψ, hψL, hHW, hq₁, ?_⟩
    change q.2 + (coupling ^ 2 : ℂ) • boundedPotentialMul W hW hbound q.1 = _
    rw [toLp_magneticHamiltonian_add_potential b coupling V W hW hbound hψL hH hHW,
      hq₁, hq₂]

theorem magneticGraphShear_image_testGraph (b coupling : ℝ)
    (V W : Potential) (hW : Continuous W) {C : ℝ} (hbound : ∀ x, |W x| ≤ C) :
    magneticGraphShear coupling (boundedPotentialMul W hW hbound) ''
      magneticTestGraph b coupling V = magneticTestGraph b coupling (V + W) := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (magneticGraphShear_mem_testGraph_iff b coupling V W hW hbound p).mpr hp
  · intro hq
    let S := magneticGraphShear coupling (boundedPotentialMul W hW hbound)
    refine ⟨S.symm q, ?_, S.apply_symm_apply q⟩
    apply (magneticGraphShear_mem_testGraph_iff b coupling V W hW hbound (S.symm q)).mp
    simpa only [S, ContinuousLinearEquiv.apply_symm_apply] using hq

/-- Equality of the actual closed graphs under the bounded perturbation shear. -/
theorem magneticGraphShear_image_closedGraph (b coupling : ℝ)
    (V W : Potential) (hW : Continuous W) {C : ℝ} (hbound : ∀ x, |W x| ≤ C) :
    magneticGraphShear coupling (boundedPotentialMul W hW hbound) ''
      (magneticClosedGraph b coupling V : Set (L2Space × L2Space)) =
        (magneticClosedGraph b coupling (V + W) : Set (L2Space × L2Space)) := by
  rw [magneticClosedGraph_eq_closure, magneticClosedGraph_eq_closure]
  trans closure (magneticGraphShear coupling (boundedPotentialMul W hW hbound) ''
    magneticTestGraph b coupling V)
  · exact (magneticGraphShear coupling (boundedPotentialMul W hW hbound)).toHomeomorph.image_closure _
  · rw [magneticGraphShear_image_testGraph b coupling V W hW hbound]

theorem magneticGraphShear_mem_closedGraph_iff (b coupling : ℝ)
    (V W : Potential) (hW : Continuous W) {C : ℝ} (hbound : ∀ x, |W x| ≤ C)
    (q : L2Space × L2Space) :
    magneticGraphShear coupling (boundedPotentialMul W hW hbound) q ∈
        magneticClosedGraph b coupling (V + W) ↔ q ∈ magneticClosedGraph b coupling V := by
  change magneticGraphShear coupling (boundedPotentialMul W hW hbound) q ∈
    (magneticClosedGraph b coupling (V + W) : Set _) ↔ _
  rw [← magneticGraphShear_image_closedGraph b coupling V W hW hbound]
  exact (magneticGraphShear coupling (boundedPotentialMul W hW hbound)).injective.mem_set_image

/-- Bounded continuous potentials preserve the domain of the canonical operator.
This follows already from projection of the actual closed graphs. -/
theorem magneticOperator_domain_add_potential (b coupling : ℝ)
    (V W : Potential) (hW : Continuous W) {C : ℝ} (hbound : ∀ x, |W x| ≤ C) :
    (magneticOperator b coupling (V + W)).domain = (magneticOperator b coupling V).domain := by
  ext u
  change u ∈ (magneticClosedGraph b coupling (V + W)).map (LinearMap.fst ℂ L2Space L2Space) ↔
    u ∈ (magneticClosedGraph b coupling V).map (LinearMap.fst ℂ L2Space L2Space)
  constructor
  · rintro ⟨q, hq, hqu⟩
    let S := magneticGraphShear coupling (boundedPotentialMul W hW hbound)
    refine ⟨S.symm q, ?_, hqu⟩
    apply (magneticGraphShear_mem_closedGraph_iff b coupling V W hW hbound (S.symm q)).mp
    simpa only [S, ContinuousLinearEquiv.apply_symm_apply] using hq
  · rintro ⟨q, hq, hqu⟩
    refine ⟨magneticGraphShear coupling (boundedPotentialMul W hW hbound) q, ?_, hqu⟩
    exact (magneticGraphShear_mem_closedGraph_iff b coupling V W hW hbound q).mpr hq

end InfiniteZero
