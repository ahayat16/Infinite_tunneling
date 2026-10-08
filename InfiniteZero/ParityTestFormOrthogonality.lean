import InfiniteZero.MagneticParityNormalization

/-!
# Orthogonal energy splitting for opposite-parity tests

The double-well differential Hamiltonian preserves parity. Integration by
parts therefore removes both mixed energy terms between an even and an
odd test. Their span has the exact diagonal mass and energy formulas used
to compare its Rayleigh upper bound with the two parity infima.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace InfiniteZero

theorem waveInner_add_left {φ ψ χ : Wavefunction}
    (hφ : MemLp φ 2 volume) (hψ : MemLp ψ 2 volume) (hχ : MemLp χ 2 volume) :
    waveInner (φ + ψ) χ = waveInner φ χ + waveInner ψ χ := by
  rw [← inner_toLp_eq_waveInner (hφ.add hψ) hχ, MemLp.toLp_add hφ hψ,
    inner_add_left, inner_toLp_eq_waveInner hφ hχ, inner_toLp_eq_waveInner hψ hχ]

theorem waveInner_add_right {φ ψ χ : Wavefunction}
    (hφ : MemLp φ 2 volume) (hψ : MemLp ψ 2 volume) (hχ : MemLp χ 2 volume) :
    waveInner φ (ψ + χ) = waveInner φ ψ + waveInner φ χ := by
  rw [← inner_toLp_eq_waveInner hφ (hψ.add hχ), MemLp.toLp_add hψ hχ,
    inner_add_right, inner_toLp_eq_waveInner hφ hψ, inner_toLp_eq_waveInner hφ hχ]

theorem HasParity.doubleHamiltonian {even : Bool} {ψ : Wavefunction}
    (hp : HasParity even ψ) (hψ : ContDiff ℝ ∞ ψ) (b L coupling : ℝ) (v : Potential) :
    HasParity even (doubleHamiltonian b v L coupling ψ) := by
  have hJ := doubleHamiltonian_inversion b L coupling v hψ
  cases even
  · have hinv : (fun x => ψ (-x)) = (-1 : ℂ) • ψ := by
      funext x
      simpa only [Pi.smul_apply, neg_one_smul] using hp x
    change magneticHamiltonian b coupling (doubleWellPotential v L) (fun x => ψ (-x)) =
      (fun x => magneticHamiltonian b coupling (doubleWellPotential v L) ψ (-x)) at hJ
    rw [hinv, magneticHamiltonian_smul b coupling _ hψ] at hJ
    intro x
    simpa only [Pi.smul_apply, neg_one_smul, doubleHamiltonian] using (congrFun hJ x).symm
  · have hinv : (fun x => ψ (-x)) = ψ := funext hp
    rw [hinv] at hJ
    exact fun x => (congrFun hJ x).symm

theorem magneticForm_add_of_even_odd {b L coupling : ℝ} {v : Potential}
    (hV : Continuous (doubleWellPotential v L)) {φ ψ : Wavefunction}
    (hφ : IsTestFunction φ) (hψ : IsTestFunction ψ)
    (hpφ : HasParity true φ) (hpψ : HasParity false ψ) :
    magneticForm b coupling (doubleWellPotential v L) (φ + ψ) =
      magneticForm b coupling (doubleWellPotential v L) φ +
      magneticForm b coupling (doubleWellPotential v L) ψ := by
  have hHφ := hφ.memLp_magneticHamiltonian b coupling hV
  have hHψ := hψ.memLp_magneticHamiltonian b coupling hV
  have hcross₁ : waveInner φ (magneticHamiltonian b coupling (doubleWellPotential v L) ψ) = 0 :=
    waveInner_eq_zero_of_even_odd hpφ (hpψ.doubleHamiltonian hψ.1 b L coupling v)
  have hcross₂ : waveInner ψ (magneticHamiltonian b coupling (doubleWellPotential v L) φ) = 0 := by
    have hzero := waveInner_eq_zero_of_even_odd
      (hpφ.doubleHamiltonian hφ.1 b L coupling v) hpψ
    change waveInner (magneticHamiltonian b coupling (doubleWellPotential v L) φ) ψ = 0 at hzero
    have hs := waveInner_star_swap (magneticHamiltonian b coupling (doubleWellPotential v L) φ) ψ
    rw [hzero, star_zero] at hs
    exact hs.symm
  have hsum := waveInner_magneticHamiltonian_eq_magneticForm b coupling hV (hφ.add hψ)
  rw [magneticHamiltonian_add b coupling _ hφ.1 hψ.1,
    waveInner_add_left hφ.memLp hψ.memLp (hHφ.add hHψ),
    waveInner_add_right hφ.memLp hHφ hHψ,
    waveInner_add_right hψ.memLp hHφ hHψ, hcross₁, hcross₂,
    waveInner_magneticHamiltonian_eq_magneticForm b coupling hV hφ,
    waveInner_magneticHamiltonian_eq_magneticForm b coupling hV hψ,
    add_zero, zero_add] at hsum
  simpa only [Complex.add_re, Complex.ofReal_re] using (congrArg Complex.re hsum).symm

theorem mass_even_odd_combination {φ ψ : Wavefunction}
    (hφ : MemLp φ 2 volume) (hψ : MemLp ψ 2 volume)
    (hpφ : HasParity true φ) (hpψ : HasParity false ψ) (a c : ℂ) :
    mass (a • φ + c • ψ) = ‖a‖ ^ 2 * mass φ + ‖c‖ ^ 2 * mass ψ := by
  rw [mass_add_wavefunctions (hφ.const_smul a) (hψ.const_smul c),
    waveInner_eq_zero_of_even_odd (hpφ.smul a) (hpψ.smul c), Complex.zero_re,
    mul_zero, add_zero, mass_smul_wavefunction, mass_smul_wavefunction]

theorem magneticForm_even_odd_combination {b L coupling : ℝ} {v : Potential}
    (hV : Continuous (doubleWellPotential v L)) {φ ψ : Wavefunction}
    (hφ : IsTestFunction φ) (hψ : IsTestFunction ψ)
    (hpφ : HasParity true φ) (hpψ : HasParity false ψ) (a c : ℂ) :
    magneticForm b coupling (doubleWellPotential v L) (a • φ + c • ψ) =
      ‖a‖ ^ 2 * magneticForm b coupling (doubleWellPotential v L) φ +
      ‖c‖ ^ 2 * magneticForm b coupling (doubleWellPotential v L) ψ := by
  rw [magneticForm_add_of_even_odd hV (hφ.smul a) (hψ.smul c)
      (hpφ.smul a) (hpψ.smul c), magneticForm_smul b coupling _ hφ,
    magneticForm_smul b coupling _ hψ]

end InfiniteZero
