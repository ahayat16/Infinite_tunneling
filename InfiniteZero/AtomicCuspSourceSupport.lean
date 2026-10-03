import InfiniteZero.AtomicCuspSource
import InfiniteZero.HoppingIntegrability

/-!
# Support and genuine L¹ norms of the cusp sources

Each component source vanishes wherever its own cusp potential vanishes.
On the closed cusp support, separation identifies the perturbation source
with that component, including at the cusp tip. The L¹ identity below uses
mathlib's actual quotient space and the given integrability witness.
-/

noncomputable section
open MeasureTheory Set

namespace InfiniteZero

/-- The norm of the actual L¹ class equals the integral of the norm of its
representative; no new source-norm convention is introduced. -/
theorem norm_toL1_eq_integral_norm {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ : Measure α} {f : α → F} (hf : Integrable f μ) :
    ‖hf.toL1 f‖ = ∫ x, ‖f x‖ ∂μ := by
  rw [hf.norm_toL1_eq_lintegral_enorm,
    integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable]

namespace CuspParameters

theorem componentSource_plus_support_subset (p : CuspParameters) (h : ℝ)
    (u : Wavefunction) :
    Function.support (componentSource p h u 1) ⊆ Function.support p.cuspPlus := by
  intro x hx
  change p.cuspPlus x ≠ 0
  intro hz
  apply hx
  simp [componentSource_plus_eq, hz]

theorem componentSource_minus_support_subset (p : CuspParameters) (h : ℝ)
    (u : Wavefunction) :
    Function.support (componentSource p h u 2) ⊆ Function.support p.cuspMinus := by
  intro x hx
  change p.cuspMinus x ≠ 0
  intro hz
  apply hx
  simp [componentSource_minus_eq, hz]

theorem atomicPerturbation_source_eq_plus {p : CuspParameters}
    (hp : p.BasicConditions) (h : ℝ) (u : Wavefunction) {x : Plane}
    (hx : x ∈ tsupport p.cuspPlus) :
    atomicSource h p.atomicPerturbation u x = componentSource p h u 1 x :=
  (atomicPerturbation_source_eventuallyEq_plus hp h u hx).self_of_nhds

theorem atomicPerturbation_source_eq_minus {p : CuspParameters}
    (hp : p.BasicConditions) (h : ℝ) (u : Wavefunction) {x : Plane}
    (hx : x ∈ tsupport p.cuspMinus) :
    atomicSource h p.atomicPerturbation u x = componentSource p h u 2 x :=
  (atomicPerturbation_source_eventuallyEq_minus hp h u hx).self_of_nhds

end CuspParameters
end InfiniteZero
