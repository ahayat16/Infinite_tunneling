import InfiniteZero.StandardLandauResolvent
import InfiniteZero.LandauResolventScaling
import InfiniteZero.MagneticInhomogeneousDomain

/-!
# The physical resolvent representation from the standard kernel

The closed-operator kernel identity at Planck constant one implies the
existing physical interface. Integration by parts and self-adjointness
place the smooth solution in the operator domain; the proper-time change
of variables supplies the exact coupling factors. The realization and
kernel formula are explicit hypotheses of this module; the latter is
proved from the heat kernel in `ClassicalLandauResolvent.lean`.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace InfiniteZero

/-- Apply the standard closed-operator kernel formula to a smooth `L²`
solution of the inhomogeneous equation. Domain membership is proved from
the realization certificate, rather than included in the kernel input. -/
theorem HasStandardLandauResolvent.smooth_solution {B ρ : ℝ}
    (hK : HasStandardLandauResolvent B ρ)
    (hA : IsMagneticRealization B 1 0)
    {u f : Wavefunction} (hu : ContDiff ℝ ∞ u) (huL : MemLp u 2 volume)
    (hf : IsTestFunction f)
    (heq : ∀ x, magneticHamiltonian B 1 0 u x + (ρ : ℂ) * u x = f x) :
    ∀ᵐ x : Plane, u x = ∫ y : Plane, freeLandauKernel B 1 ρ x y * f y := by
  let U : L2Space := huL.toLp u
  let F : L2Space := hf.memLp.toLp f
  let G : L2Space := F - (ρ : ℂ) • U
  have hU : Represents U u := huL.coeFn_toLp
  have hF : Represents F f := hf.memLp.coeFn_toLp
  have hG : Represents G (magneticHamiltonian B 1 0 u) := by
    filter_upwards [Lp.coeFn_sub F ((ρ : ℂ) • U), Lp.coeFn_smul (ρ : ℂ) U,
      hF, hU] with x hx hs hfx hux
    change G x = _
    dsimp only [G]
    rw [hx]
    simp only [Pi.sub_apply, hs, Pi.smul_apply, smul_eq_mul, hfx, hux]
    exact (eq_sub_iff_add_eq.mpr (heq x)).symm
  have hgraph := hA.mem_graph_of_smooth continuous_const hu hU hG
  obtain ⟨W, hWU, hWG⟩ := (magneticOperator B 1 0).mem_graph_iff.mp hgraph
  have hsource : Represents (magneticOperator B 1 0 W + (ρ : ℂ) • (W : L2Space)) f := by
    rw [hWG, hWU]
    simpa only [G, sub_add_cancel] using hF
  have hrepr := hK W f hf hsource
  rw [hWU] at hrepr
  exact hU.symm.trans hrepr

/-- The standard resolvent at field `B = bλ` and shift `ρ = λ²E`
gives the original semiclassical kernel interface, with the same source
and the same almost-everywhere representative. -/
theorem freeLandauResolventKernel_of_standard {b coupling E : ℝ}
    (hc : 0 < coupling)
    (hA : IsMagneticRealization (b * coupling) 1 0)
    (hK : HasStandardLandauResolvent (b * coupling) (coupling ^ 2 * E)) :
    FreeLandauResolventKernel b coupling E := by
  intro u f hu huL hf heq
  have heq' : ∀ x, magneticHamiltonian (b * coupling) 1 0 u x +
      ((coupling ^ 2 * E : ℝ) : ℂ) * u x = f x := by
    intro x
    rw [← magneticHamiltonian_free_standard b coupling u]
    exact heq x
  have hrepr := hK.smooth_solution hA hu huL hf heq'
  filter_upwards [hrepr] with x hx
  rw [integral_freeLandauKernel_coupling_rescale b E hc x f]
  exact hx

end InfiniteZero
