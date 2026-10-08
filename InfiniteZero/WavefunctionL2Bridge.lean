import InfiniteZero.OperatorBridge
import InfiniteZero.MagneticIntegrationByParts

/-!
# Wavefunctions and their actual L² classes

The scalar products and masses of chosen representatives agree with the
Hilbert-space scalar products and norms. All changes of representative are
made through almost-everywhere equality. On the test-function core, integration
by parts therefore identifies the operator energy with `magneticForm`.
-/

noncomputable section

open MeasureTheory

namespace InfiniteZero

/-- The representative used by `toLp` agrees almost everywhere with its input. -/
theorem represents_toLp {ψ : Wavefunction} (hψ : MemLp ψ 2 volume) :
    Represents (hψ.toLp ψ) ψ := hψ.coeFn_toLp

theorem Represents.memLp {u : L2Space} {ψ : Wavefunction} (hu : Represents u ψ) :
    MemLp ψ 2 volume := (Lp.memLp u).ae_eq hu

/-- An arbitrary `MemLp` witness gives the same represented Hilbert-space vector. -/
theorem Represents.toLp_eq {u : L2Space} {ψ : Wavefunction} (hu : Represents u ψ)
    (hψ : MemLp ψ 2 volume) : hψ.toLp ψ = u :=
  Lp.ext (hψ.coeFn_toLp.trans hu.symm)

/-- The physical integral is the complex Hilbert-space scalar product. -/
theorem Represents.inner_eq_waveInner {u v : L2Space} {ψ χ : Wavefunction}
    (hu : Represents u ψ) (hv : Represents v χ) :
    inner ℂ u v = waveInner ψ χ := by
  rw [L2.inner_def, waveInner]
  apply integral_congr_ae
  filter_upwards [hu, hv] with x hx hy
  simp [hx, hy, mul_comm]

/-- The product defining `waveInner` is integrable for L² representatives. -/
theorem Represents.integrable_star_mul {u v : L2Space} {ψ χ : Wavefunction}
    (hu : Represents u ψ) (hv : Represents v χ) :
    Integrable (fun x => star (ψ x) * χ x) := by
  apply (L2.integrable_inner (𝕜 := ℂ) u v).congr
  filter_upwards [hu, hv] with x hx hy
  simp [hx, hy, mul_comm]

theorem inner_toLp_eq_waveInner {ψ χ : Wavefunction}
    (hψ : MemLp ψ 2 volume) (hχ : MemLp χ 2 volume) :
    inner ℂ (hψ.toLp ψ) (hχ.toLp χ) = waveInner ψ χ :=
  (represents_toLp hψ).inner_eq_waveInner (represents_toLp hχ)

/-- Squared Hilbert-space norm equals the actual integral of the density. -/
theorem Represents.norm_sq_eq_mass {u : L2Space} {ψ : Wavefunction}
    (hu : Represents u ψ) : ‖u‖ ^ 2 = mass ψ := by
  calc
    ‖u‖ ^ 2 = (inner ℂ u u).re := norm_sq_eq_re_inner (𝕜 := ℂ) u
    _ = (waveInner ψ ψ).re := congrArg Complex.re (hu.inner_eq_waveInner hu)
    _ = mass ψ := by rw [waveInner_self_eq_mass, Complex.ofReal_re]

theorem norm_toLp_sq_eq_mass {ψ : Wavefunction} (hψ : MemLp ψ 2 volume) :
    ‖hψ.toLp ψ‖ ^ 2 = mass ψ := (represents_toLp hψ).norm_sq_eq_mass

/-- Test-function integration by parts, transported to arbitrary L² representatives. -/
theorem Represents.inner_magneticHamiltonian_eq_magneticForm (b coupling : ℝ)
    {V : Potential} {ψ : Wavefunction} {u v : L2Space}
    (hu : Represents u ψ) (hv : Represents v (magneticHamiltonian b coupling V ψ))
    (hV : Continuous V) (hψ : IsTestFunction ψ) :
    inner ℂ u v = (magneticForm b coupling V ψ : ℂ) := by
  rw [hu.inner_eq_waveInner hv]
  exact waveInner_magneticHamiltonian_eq_magneticForm b coupling hV hψ

theorem Represents.re_inner_magneticHamiltonian_eq_magneticForm (b coupling : ℝ)
    {V : Potential} {ψ : Wavefunction} {u v : L2Space}
    (hu : Represents u ψ) (hv : Represents v (magneticHamiltonian b coupling V ψ))
    (hV : Continuous V) (hψ : IsTestFunction ψ) :
    (inner ℂ u v).re = magneticForm b coupling V ψ := by
  rw [hu.inner_magneticHamiltonian_eq_magneticForm b coupling hv hV hψ,
    Complex.ofReal_re]

/-- Explicit `MemLp` witnesses avoid assuming any closed-domain realization. -/
theorem inner_toLp_magneticHamiltonian_eq_magneticForm (b coupling : ℝ)
    {V : Potential} {ψ : Wavefunction} (hV : Continuous V) (hψ : IsTestFunction ψ)
    (hψLp : MemLp ψ 2 volume) (hHLp : MemLp (magneticHamiltonian b coupling V ψ) 2 volume) :
    inner ℂ (hψLp.toLp ψ) (hHLp.toLp (magneticHamiltonian b coupling V ψ)) =
      (magneticForm b coupling V ψ : ℂ) :=
  (represents_toLp hψLp).inner_magneticHamiltonian_eq_magneticForm b coupling
    (represents_toLp hHLp) hV hψ

theorem re_inner_toLp_magneticHamiltonian_eq_magneticForm (b coupling : ℝ)
    {V : Potential} {ψ : Wavefunction} (hV : Continuous V) (hψ : IsTestFunction ψ)
    (hψLp : MemLp ψ 2 volume) (hHLp : MemLp (magneticHamiltonian b coupling V ψ) 2 volume) :
    (inner ℂ (hψLp.toLp ψ) (hHLp.toLp (magneticHamiltonian b coupling V ψ))).re =
      magneticForm b coupling V ψ := by
  rw [inner_toLp_magneticHamiltonian_eq_magneticForm b coupling hV hψ hψLp hHLp,
    Complex.ofReal_re]

end InfiniteZero
