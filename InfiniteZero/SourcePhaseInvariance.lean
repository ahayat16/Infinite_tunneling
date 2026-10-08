import InfiniteZero.AtomicCuspSource
import InfiniteZero.HoppingPhase

/-!
# Unit-phase invariance of the genuine source cells

The same phase multiplies both sources in a pairing, and cancels pointwise
with its complex conjugate. No integrability hypothesis is needed for
these exact identities. The canonical-cell identification retains the
full atomic energy and the semiclassical parameter `coupling⁻¹`.
-/

noncomputable section
open MeasureTheory

namespace InfiniteZero

theorem componentSource_smul (p : CuspParameters) (h : ℝ) (z : ℂ)
    (φ : Wavefunction) (i : Fin 3) :
    componentSource p h (z • φ) i = z • componentSource p h φ i :=
  atomicSource_smul h (componentPotential p i) z φ

theorem norm_componentSource_smul_unit (p : CuspParameters) (h : ℝ)
    (z : ℂ) (hz : ‖z‖ = 1) (φ : Wavefunction) (i : Fin 3) (x : Plane) :
    ‖componentSource p h (z • φ) i x‖ = ‖componentSource p h φ i x‖ := by
  rw [componentSource_smul, Pi.smul_apply, norm_smul, hz, one_mul]

theorem integral_norm_componentSource_smul_unit (p : CuspParameters) (h : ℝ)
    (z : ℂ) (hz : ‖z‖ = 1) (φ : Wavefunction) (i : Fin 3) :
    (∫ x : Plane, ‖componentSource p h (z • φ) i x‖) =
      ∫ x : Plane, ‖componentSource p h φ i x‖ := by
  simp only [norm_componentSource_smul_unit p h z hz φ i]

/-- A common unit phase cancels in the exact complex integrand, independently
of any convergence or spectral assumption. -/
theorem channelIntegrand_smul_unit (K : Plane → Plane → ℂ)
    (z : ℂ) (hz : ‖z‖ = 1) (F G : Wavefunction) :
    channelIntegrand K (z • F) (z • G) = channelIntegrand K F G := by
  have hzunit : star z * z = 1 := by
    simpa only [Complex.star_def, hz, one_pow, Complex.ofReal_one] using
      Complex.conj_mul' z
  funext q
  simp only [channelIntegrand, Pi.smul_apply, smul_eq_mul, star_mul']
  calc
    star z * star (F q.1) * K q.1 q.2 * (z * G q.2) =
        (star z * z) * (star (F q.1) * K q.1 q.2 * G q.2) := by ring
    _ = _ := by rw [hzunit, one_mul]

theorem sourcePairing_smul_unit (h : ℝ) (K : Plane → Plane → ℂ)
    (z : ℂ) (hz : ‖z‖ = 1) (F G : Wavefunction) :
    sourcePairing h K (z • F) (z • G) = sourcePairing h K F G := by
  simp only [sourcePairing, channelIntegrand_smul_unit K z hz F G]

theorem sourceCell_smul_unit (p : CuspParameters) (L h E : ℝ)
    (z : ℂ) (hz : ‖z‖ = 1) (φ : Wavefunction) (i j : Fin 3) :
    sourceCell p L h E (z • φ) i j = sourceCell p L h E φ i j := by
  simp only [sourceCell, componentSource_smul,
    sourcePairing_smul_unit h (sourceKernel p.b L h E) z hz]

/-- The cell of any genuine normalized full ground state is the canonical
cell when that ground state is simple. Both energies are the same actual
full atomic energy; the radial reference state is not rephased. -/
theorem canonicalSourceCell_eq_sourceCell (p : CuspParameters) (L coupling : ℝ)
    (hsimple : AtomicGroundSimple p.b p.potential coupling)
    (ψ : Wavefunction) (hψ : IsAtomicGroundState p.b p.potential coupling ψ)
    (i j : Fin 3) :
    canonicalSourceCell p L coupling i j =
      sourceCell p L coupling⁻¹ (scaledAtomicEnergy p coupling) ψ i j := by
  have hcanonical := canonicalAtomicState_spec p.b p.potential coupling ⟨ψ, hψ⟩
  obtain ⟨z, hz, hphase⟩ :=
    hsimple ψ (canonicalAtomicState p.b p.potential coupling) hψ hcanonical
  unfold canonicalSourceCell
  rw [hphase, sourceCell_smul_unit p L coupling⁻¹ (scaledAtomicEnergy p coupling) z hz]

end InfiniteZero
