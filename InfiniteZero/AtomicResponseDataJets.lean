import InfiniteZero.AtomicResponseWavefunction
import InfiniteZero.WeightedSemiclassicalJets
import InfiniteZero.ConstructionSmooth

/-!
# The two terms of the actual semiclassical response data

The energy shift is the difference of the true core and full ground energies.
Jet estimates retain one coefficient of that shift, independently of the
radial derivative estimate subsequently supplied.
-/

noncomputable section
open scoped ContDiff

namespace InfiniteZero.CuspParameters

def atomicScaledEnergyShift (p : CuspParameters) (coupling : ℝ) : ℝ :=
  (coupling⁻¹) ^ 2 * (atomicGroundEnergy p.b p.potential coupling -
    atomicGroundEnergy p.b p.core coupling)

def atomicScaledResponseSource (p : CuspParameters) (coupling c : ℝ)
    (φ : Wavefunction) : Wavefunction :=
  fun x => -(c : ℂ) * (p.atomicPerturbation x : ℂ) * φ x +
    (c * p.atomicScaledEnergyShift coupling : ℂ) * φ x

theorem atomicScaledResponseSource_contDiff {p : CuspParameters}
    (hp : p.BasicConditions) (coupling c : ℝ) {φ : Wavefunction}
    (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (p.atomicScaledResponseSource coupling c φ) := by
  have hW := (potential_contDiff hp).sub (core_contDiff hp.r₀_pos)
  have hF : ContDiff ℝ ∞ (fun y => (p.atomicPerturbation y : ℂ) * φ y) := by
    simpa only [Complex.real_smul] using hW.smul hφ
  have hleft : ContDiff ℝ ∞
      (fun x => -(c : ℂ) * ((p.atomicPerturbation x : ℂ) * φ x)) :=
    contDiff_const.mul hF
  have hright : ContDiff ℝ ∞
      (fun x => (c * p.atomicScaledEnergyShift coupling : ℂ) * φ x) :=
    contDiff_const.mul hφ
  unfold atomicScaledResponseSource
  convert hleft.add hright using 1
  funext x
  ring

theorem norm_atomicScaledResponseSource_jet_le {p : CuspParameters}
    (hp : p.BasicConditions) (coupling : ℝ) {c : ℝ} (hc : 0 ≤ c)
    {φ : Wavefunction} (hφ : ContDiff ℝ ∞ φ) (n : ℕ) (x : Plane) :
    ‖iteratedFDeriv ℝ n (p.atomicScaledResponseSource coupling c φ) x‖ ≤
      c * ‖iteratedFDeriv ℝ n (fun y => (p.atomicPerturbation y : ℂ) * φ y) x‖ +
      c * |p.atomicScaledEnergyShift coupling| * ‖iteratedFDeriv ℝ n φ x‖ := by
  let F : Wavefunction := fun y => (p.atomicPerturbation y : ℂ) * φ y
  have hW := (potential_contDiff hp).sub (core_contDiff hp.r₀_pos)
  have hF : ContDiff ℝ ∞ F := by simpa only [F, Complex.real_smul] using hW.smul hφ
  have heq : p.atomicScaledResponseSource coupling c φ =
      fun y => (-(c : ℂ)) • F y + (c * p.atomicScaledEnergyShift coupling : ℂ) • φ y := by
    funext y
    simp only [atomicScaledResponseSource, smul_eq_mul, F]
    ring
  rw [heq, fun_iteratedFDeriv_add_apply
    (contDiff_infty.mp (hF.const_smul (-(c : ℂ))) n).contDiffAt
    (contDiff_infty.mp (hφ.const_smul (c * p.atomicScaledEnergyShift coupling : ℂ)) n).contDiffAt,
    iteratedFDeriv_const_smul_apply' (contDiff_infty.mp hF n).contDiffAt,
    iteratedFDeriv_const_smul_apply' (contDiff_infty.mp hφ n).contDiffAt]
  apply (norm_add_le _ _).trans_eq
  simp only [norm_smul, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hc, F]

theorem weighted_atomicScaledResponseSource_jet_le {p : CuspParameters}
    (hp : p.BasicConditions) (coupling : ℝ) {c : ℝ} (hc : 0 ≤ c)
    {φ : Wavefunction} (hφ : ContDiff ℝ ∞ φ) (n : ℕ) (x : Plane)
    (T : Plane → ℝ) {h κ F R D : ℝ} (hh : 0 ≤ h) (hR : 0 ≤ R)
    (hforce : Real.exp (κ / h * T x) * h ^ n *
      ‖iteratedFDeriv ℝ n (fun y => (p.atomicPerturbation y : ℂ) * φ y) x‖ ≤ F)
    (hradial : Real.exp (κ / h * T x) * h ^ n * ‖iteratedFDeriv ℝ n φ x‖ ≤ R)
    (hshift : |p.atomicScaledEnergyShift coupling| ≤ D) :
    Real.exp (κ / h * T x) * h ^ n *
      ‖iteratedFDeriv ℝ n (p.atomicScaledResponseSource coupling c φ) x‖ ≤
        c * F + c * D * R := by
  have hs := norm_atomicScaledResponseSource_jet_le hp coupling hc hφ n x
  calc
    _ ≤ Real.exp (κ / h * T x) * h ^ n *
        (c * ‖iteratedFDeriv ℝ n (fun y => (p.atomicPerturbation y : ℂ) * φ y) x‖ +
          c * |p.atomicScaledEnergyShift coupling| * ‖iteratedFDeriv ℝ n φ x‖) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = c * (Real.exp (κ / h * T x) * h ^ n *
          ‖iteratedFDeriv ℝ n (fun y => (p.atomicPerturbation y : ℂ) * φ y) x‖) +
        c * |p.atomicScaledEnergyShift coupling| *
          (Real.exp (κ / h * T x) * h ^ n * ‖iteratedFDeriv ℝ n φ x‖) := by ring
    _ ≤ c * F + c * |p.atomicScaledEnergyShift coupling| * R :=
      add_le_add (mul_le_mul_of_nonneg_left hforce hc)
        (mul_le_mul_of_nonneg_left hradial (mul_nonneg hc (abs_nonneg _)))
    _ ≤ _ := add_le_add_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hshift hc) hR) _

end InfiniteZero.CuspParameters
