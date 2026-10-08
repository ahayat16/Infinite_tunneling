import InfiniteZero.StandardLandauResolvent
import InfiniteZero.MagneticTestGraph
import InfiniteZero.WavefunctionL2Bridge

/-!
# Extending a resolvent identity from the test-function core

A left inverse on compact smooth functions, together with an `L²` bound
on differences of their images, determines the inverse on the closed
operator graph. The proof extends a continuous norm inequality from the
test graph to its closure. It does not require a separate construction of
the integral operator on all of `L²`, or any regularity of its output.

The magnetic realization certificate is an explicit hypothesis; no
admitted theorem is imported here.
-/

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace InfiniteZero

private theorem represents_sub_core {u v : L2Space} {f g : Wavefunction}
    (hf : Represents u f) (hg : Represents v g) :
    Represents (u - v) (f - g) := by
  filter_upwards [Lp.coeFn_sub u v, hf, hg] with x hx hfx hgx
  simpa only [Pi.sub_apply, hfx, hgx] using hx

private theorem represents_shifted_core {u v : L2Space} {f g : Wavefunction}
    (hf : Represents u f) (hg : Represents v g) (ρ : ℝ) :
    Represents (v + (ρ : ℂ) • u) (g + (ρ : ℂ) • f) := by
  filter_upwards [Lp.coeFn_add v ((ρ : ℂ) • u), Lp.coeFn_smul (ρ : ℂ) u,
    hf, hg] with x hx hs hfx hgx
  simpa only [Pi.add_apply, Pi.smul_apply, hfx, hgx, hs] using hx

/-- The free magnetic differential expression preserves compact smooth
functions, so its shifted source is again an admissible test function. -/
theorem IsTestFunction.shifted_free_magneticHamiltonian {φ : Wavefunction}
    (hφ : IsTestFunction φ) (B ρ : ℝ) :
    IsTestFunction (magneticHamiltonian B 1 0 φ + (ρ : ℂ) • φ) := by
  have hH : IsTestFunction (magneticHamiltonian B 1 0 φ) := by
    have hD (i : Fin 2) :=
      (hφ.covariantDerivative B 1 i).covariantDerivative B 1 i
    have hfun : magneticHamiltonian B 1 0 φ =
        InfiniteZero.covariantDerivative B 1 0 (InfiniteZero.covariantDerivative B 1 0 φ) +
        InfiniteZero.covariantDerivative B 1 1 (InfiniteZero.covariantDerivative B 1 1 φ) := by
      funext x
      simp [magneticHamiltonian, Fin.sum_univ_two]
    rw [hfun]
    exact (hD 0).add (hD 1)
  exact hH.add (hφ.smul (ρ : ℂ))

/-- A bounded left inverse on the test core extends to every point of the
prescribed closed free magnetic graph. The constant controls squared
norms, hence is the square of the usual operator-norm bound.

Only a bound for differences of test sources is required. In particular,
the map `T` need not already be packaged as a continuous operator on `L²`. -/
theorem magneticClosedGraph_inverse_of_testCore
    {B ρ C : ℝ} (T : Wavefunction → Wavefunction)
    (hLp : ∀ f, IsTestFunction f → MemLp (T f) 2 volume)
    (hDiff : ∀ f g, IsTestFunction f → IsTestFunction g →
      mass (T f - T g) ≤ C * mass (f - g))
    (hLeft : ∀ φ, IsTestFunction φ →
      T (magneticHamiltonian B 1 0 φ + (ρ : ℂ) • φ) =ᵐ[volume] φ)
    {f : Wavefunction} (hf : IsTestFunction f) {u w : L2Space}
    (hgraph : (u, w) ∈ magneticClosedGraph B 1 0)
    (hsource : Represents (w + (ρ : ℂ) • u) f) :
    Represents u (T f) := by
  let v : L2Space := (hLp f hf).toLp (T f)
  let F : L2Space := hf.memLp.toLp f
  have hv : Represents v (T f) := represents_toLp (hLp f hf)
  have hF : Represents F f := represents_toLp hf.memLp
  have hcore : ∀ z ∈ magneticTestGraph B 1 0,
      ‖v - z.1‖ ^ 2 ≤ C * ‖F - (z.2 + (ρ : ℂ) • z.1)‖ ^ 2 := by
    rintro z ⟨φ, hφ, hφL, hHφL, hz, hzH⟩
    have hφrep : Represents z.1 φ := by rw [hz]; exact represents_toLp hφL
    have hHrep : Represents z.2 (magneticHamiltonian B 1 0 φ) := by
      rw [hzH]
      exact represents_toLp hHφL
    have hTrep : Represents z.1
        (T (magneticHamiltonian B 1 0 φ + (ρ : ℂ) • φ)) :=
      hφrep.trans (hLeft φ hφ).symm
    calc
      ‖v - z.1‖ ^ 2 = mass (T f -
          T (magneticHamiltonian B 1 0 φ + (ρ : ℂ) • φ)) :=
        (represents_sub_core hv hTrep).norm_sq_eq_mass
      _ ≤ C * mass (f - (magneticHamiltonian B 1 0 φ + (ρ : ℂ) • φ)) :=
        hDiff f _ hf (hφ.shifted_free_magneticHamiltonian B ρ)
      _ = C * ‖F - (z.2 + (ρ : ℂ) • z.1)‖ ^ 2 :=
        congrArg (fun a : ℝ => C * a)
          (represents_sub_core hF (represents_shifted_core hφrep hHrep ρ)).norm_sq_eq_mass.symm
  have hclosed : IsClosed {z : L2Space × L2Space |
      ‖v - z.1‖ ^ 2 ≤ C * ‖F - (z.2 + (ρ : ℂ) • z.1)‖ ^ 2} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hbound : ‖v - u‖ ^ 2 ≤ C * ‖F - (w + (ρ : ℂ) • u)‖ ^ 2 := by
    have hclosure : (u, w) ∈ closure (magneticTestGraph B 1 0) := by
      rwa [← magneticClosedGraph_eq_closure B 1 0]
    have hsubset : closure (magneticTestGraph B 1 0) ⊆
        {z : L2Space × L2Space |
          ‖v - z.1‖ ^ 2 ≤ C * ‖F - (z.2 + (ρ : ℂ) • z.1)‖ ^ 2} :=
      closure_minimal (s := magneticTestGraph B 1 0)
        (t := {z : L2Space × L2Space |
          ‖v - z.1‖ ^ 2 ≤ C * ‖F - (z.2 + (ρ : ℂ) • z.1)‖ ^ 2}) hcore hclosed
    have hh := @hsubset (u, w) hclosure
    change ‖v - u‖ ^ 2 ≤ C * ‖F - (w + (ρ : ℂ) • u)‖ ^ 2 at hh
    exact hh
  have hF_eq : F = w + (ρ : ℂ) • u := hsource.toLp_eq hf.memLp
  rw [hF_eq, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero] at hbound
  have hvu : v = u := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (v - u)]
  rwa [hvu] at hv

/-- The test-core criterion for the standard Landau kernel formula. All
analytic input consists of a squared `L²` difference bound and the
left-inverse identity on compact smooth functions. Graph closure supplies
the domain extension. -/
theorem hasStandardLandauResolvent_of_testCore
    {B ρ C : ℝ} (hA : IsMagneticRealization B 1 0)
    (hLp : ∀ f : Wavefunction, IsTestFunction f →
      MemLp (fun x => ∫ y : Plane, freeLandauKernel B 1 ρ x y * f y) 2 volume)
    (hDiff : ∀ f g : Wavefunction, IsTestFunction f → IsTestFunction g →
      mass ((fun x => ∫ y : Plane, freeLandauKernel B 1 ρ x y * f y) -
        (fun x => ∫ y : Plane, freeLandauKernel B 1 ρ x y * g y)) ≤
      C * mass (f - g))
    (hLeft : ∀ φ : Wavefunction, IsTestFunction φ →
      (fun x => ∫ y : Plane, freeLandauKernel B 1 ρ x y *
        (magneticHamiltonian B 1 0 φ y + (ρ : ℂ) * φ y)) =ᵐ[volume] φ) :
    HasStandardLandauResolvent B ρ := by
  intro U f hf hsource
  apply magneticClosedGraph_inverse_of_testCore
    (fun f x => ∫ y : Plane, freeLandauKernel B 1 ρ x y * f y) hLp hDiff hLeft hf
      (u := (U : L2Space)) (w := magneticOperator B 1 0 U) _ hsource
  rw [← hA.graph_eq]
  exact LinearPMap.mem_graph _ U

end InfiniteZero
