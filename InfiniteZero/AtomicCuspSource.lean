import InfiniteZero.HoppingChannels
import InfiniteZero.AtomicPerturbationTail

/-!
# The genuine cusp sources and their local jets

The sources are exactly those of `HoppingChannels`. Separation of the closed
cusp supports makes the perturbation source agree with the corresponding
component source on a neighborhood of every point of each closed support.
The resulting jet equalities include the cusp tips and require no smoothness
for the germ comparison itself.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace InfiniteZero

theorem atomicSource_contDiff (h : ℝ) {V : Potential} {η : Wavefunction}
    (hV : ContDiff ℝ ∞ V) (hη : ContDiff ℝ ∞ η) :
    ContDiff ℝ ∞ (atomicSource h V η) :=
  (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul hV)).mul hη

theorem atomicSource_add (h : ℝ) (V : Potential) (φ η : Wavefunction) :
    atomicSource h V (φ + η) = atomicSource h V φ + atomicSource h V η := by
  funext x
  simp only [atomicSource, Pi.add_apply, mul_add]

theorem atomicSource_smul (h : ℝ) (V : Potential) (c : ℂ) (φ : Wavefunction) :
    atomicSource h V (c • φ) = c • atomicSource h V φ := by
  funext x
  simp only [atomicSource, Pi.smul_apply, smul_eq_mul]
  ring

theorem atomicSource_eq_add_of_decomposition (h : ℝ) (V : Potential) (c : ℂ)
    {ψ φ η : Wavefunction} (hψ : ψ = c • φ + η) :
    atomicSource h V ψ = c • atomicSource h V φ + atomicSource h V η := by
  rw [hψ, atomicSource_add, atomicSource_smul]

namespace CuspParameters

theorem componentSource_plus_eq (p : CuspParameters) (h : ℝ) (η : Wavefunction) :
    componentSource p h η 1 =
      fun x => ((h ^ 2)⁻¹ * p.ε) • (p.cuspPlus x • η x) := by
  funext x
  simp [componentSource, componentPotential, atomicSource, Complex.real_smul, mul_assoc]

theorem componentSource_minus_eq (p : CuspParameters) (h : ℝ) (η : Wavefunction) :
    componentSource p h η 2 =
      fun x => ((h ^ 2)⁻¹ * p.ε) • (p.cuspMinus x • η x) := by
  funext x
  simp [componentSource, componentPotential, atomicSource, Complex.real_smul, mul_assoc]

theorem atomicPerturbation_source_contDiff {p : CuspParameters} (hp : p.BasicConditions)
    (h : ℝ) {η : Wavefunction} (hη : ContDiff ℝ ∞ η) :
    ContDiff ℝ ∞ (atomicSource h p.atomicPerturbation η) :=
  atomicSource_contDiff h ((potential_contDiff hp).sub (core_contDiff hp.r₀_pos)) hη

theorem componentSource_plus_contDiff {p : CuspParameters} (hp : p.BasicConditions)
    (h : ℝ) {η : Wavefunction} (hη : ContDiff ℝ ∞ η) :
    ContDiff ℝ ∞ (componentSource p h η 1) := by
  rw [componentSource_plus_eq]
  exact ((cuspPlus_contDiff hp).smul hη).const_smul _

theorem componentSource_minus_contDiff {p : CuspParameters} (hp : p.BasicConditions)
    (h : ℝ) {η : Wavefunction} (hη : ContDiff ℝ ∞ η) :
    ContDiff ℝ ∞ (componentSource p h η 2) := by
  rw [componentSource_minus_eq]
  exact ((cuspMinus_contDiff hp).smul hη).const_smul _

theorem atomicPerturbation_source_eventuallyEq_plus {p : CuspParameters}
    (hp : p.BasicConditions) (h : ℝ) (η : Wavefunction) {x : Plane}
    (hx : x ∈ tsupport p.cuspPlus) :
    atomicSource h p.atomicPerturbation η =ᶠ[𝓝 x] componentSource p h η 1 := by
  have hnot : x ∉ tsupport p.cuspMinus :=
    Set.disjoint_left.mp (cuspPlus_cuspMinus_tsupport_disjoint hp) hx
  have hzero : p.cuspMinus =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hnot
  filter_upwards [hzero] with y hy
  simp [componentSource, componentPotential, atomicSource, atomicPerturbation_eq_cusps,
    show p.cuspMinus y = 0 from hy]

theorem atomicPerturbation_source_eventuallyEq_minus {p : CuspParameters}
    (hp : p.BasicConditions) (h : ℝ) (η : Wavefunction) {x : Plane}
    (hx : x ∈ tsupport p.cuspMinus) :
    atomicSource h p.atomicPerturbation η =ᶠ[𝓝 x] componentSource p h η 2 := by
  have hnot : x ∉ tsupport p.cuspPlus :=
    Set.disjoint_left.mp (cuspPlus_cuspMinus_tsupport_disjoint hp).symm hx
  have hzero : p.cuspPlus =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hnot
  filter_upwards [hzero] with y hy
  simp [componentSource, componentPotential, atomicSource, atomicPerturbation_eq_cusps,
    show p.cuspPlus y = 0 from hy]

theorem iteratedFDeriv_atomicPerturbation_source_eq_plus {p : CuspParameters}
    (hp : p.BasicConditions) (h : ℝ) (η : Wavefunction) {x : Plane}
    (hx : x ∈ tsupport p.cuspPlus) (n : ℕ) :
    iteratedFDeriv ℝ n (atomicSource h p.atomicPerturbation η) x =
      iteratedFDeriv ℝ n (componentSource p h η 1) x :=
  ((atomicPerturbation_source_eventuallyEq_plus hp h η hx).iteratedFDeriv ℝ n).self_of_nhds

theorem iteratedFDeriv_atomicPerturbation_source_eq_minus {p : CuspParameters}
    (hp : p.BasicConditions) (h : ℝ) (η : Wavefunction) {x : Plane}
    (hx : x ∈ tsupport p.cuspMinus) (n : ℕ) :
    iteratedFDeriv ℝ n (atomicSource h p.atomicPerturbation η) x =
      iteratedFDeriv ℝ n (componentSource p h η 2) x :=
  ((atomicPerturbation_source_eventuallyEq_minus hp h η hx).iteratedFDeriv ℝ n).self_of_nhds

theorem norm_iteratedFDeriv_componentSource_plus {p : CuspParameters}
    (hp : p.BasicConditions) {η : Wavefunction} (hη : ContDiff ℝ ∞ η)
    (h : ℝ) (n : ℕ) (x : Plane) :
    ‖iteratedFDeriv ℝ n (componentSource p h η 1) x‖ =
      ((h ^ 2)⁻¹ * p.ε) * ‖iteratedFDeriv ℝ n (fun y => p.cuspPlus y • η y) x‖ := by
  have hprod : ContDiff ℝ ∞ (fun y : Plane => p.cuspPlus y • η y) :=
    (cuspPlus_contDiff hp).smul hη
  rw [componentSource_plus_eq, iteratedFDeriv_const_smul_apply' (a := (h ^ 2)⁻¹ * p.ε)
    (f := fun y : Plane => p.cuspPlus y • η y) (contDiff_infty.mp hprod n).contDiffAt,
    norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (sq_nonneg h)) hp.ε_pos.le)]

theorem norm_iteratedFDeriv_componentSource_minus {p : CuspParameters}
    (hp : p.BasicConditions) {η : Wavefunction} (hη : ContDiff ℝ ∞ η)
    (h : ℝ) (n : ℕ) (x : Plane) :
    ‖iteratedFDeriv ℝ n (componentSource p h η 2) x‖ =
      ((h ^ 2)⁻¹ * p.ε) * ‖iteratedFDeriv ℝ n (fun y => p.cuspMinus y • η y) x‖ := by
  have hprod : ContDiff ℝ ∞ (fun y : Plane => p.cuspMinus y • η y) :=
    (cuspMinus_contDiff hp).smul hη
  rw [componentSource_minus_eq, iteratedFDeriv_const_smul_apply' (a := (h ^ 2)⁻¹ * p.ε)
    (f := fun y : Plane => p.cuspMinus y • η y) (contDiff_infty.mp hprod n).contDiffAt,
    norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (sq_nonneg h)) hp.ε_pos.le)]

end CuspParameters
end InfiniteZero
