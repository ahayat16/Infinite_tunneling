import InfiniteZero.AtomicCuspSourceSupport

/-!
# Exact component-source decomposition and its L¹ bound

The same reference state, full state, and real coefficient occur in both
terms. Integrability follows from continuity and the compact support of
each actual component potential; no source profile estimate is assumed.
-/

noncomputable section
open MeasureTheory

namespace InfiniteZero.CuspParameters

theorem componentSource_eq_incoming_add_scattered (p : CuspParameters)
    (h c : ℝ) (φ ψ : Wavefunction) (i : Fin 3) :
    componentSource p h ψ i =
      componentSource p h (fun x => (c : ℂ) * φ x) i +
        componentSource p h (fun x => ψ x - (c : ℂ) * φ x) i := by
  funext x
  simp only [componentSource, atomicSource, Pi.add_apply]
  ring

theorem componentSource_integral_norm_le_incoming_add_scattered
    {p : CuspParameters} (hp : p.BasicConditions) (h c : ℝ)
    {φ ψ : Wavefunction} (hφ : Continuous φ) (hψ : Continuous ψ) (i : Fin 3) :
    (∫ x, ‖componentSource p h ψ i x‖) ≤
      (∫ x, ‖componentSource p h (fun y => (c : ℂ) * φ y) i x‖) +
        ∫ x, ‖componentSource p h (fun y => ψ y - (c : ℂ) * φ y) i x‖ := by
  have hcφ : Continuous (fun x => (c : ℂ) * φ x) := continuous_const.mul hφ
  have hi := componentSource_integrable hp h hcφ i
  have hs := componentSource_integrable hp h (hψ.sub hcφ) i
  have hf := componentSource_integrable hp h hψ i
  calc
    _ ≤ ∫ x, ‖componentSource p h (fun y => (c : ℂ) * φ y) i x‖ +
        ‖componentSource p h (fun y => ψ y - (c : ℂ) * φ y) i x‖ := by
      apply integral_mono hf.norm (hi.norm.add hs.norm)
      intro x
      dsimp only [Pi.add_apply]
      rw [congrFun (componentSource_eq_incoming_add_scattered p h c φ ψ i) x,
        Pi.add_apply]
      exact norm_add_le _ _
    _ = _ := integral_add hi.norm hs.norm

end InfiniteZero.CuspParameters
