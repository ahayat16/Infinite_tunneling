import InfiniteZero.MagneticCovariance
import InfiniteZero.HoppingSourceIdentity

/-!
# The classical free-Landau resolvent interface and its atomic application

`FreeLandauResolventKernel` is a universal classical analytic contract. It
contains neither tunneling nor an atomic spectral-existence assertion. The
classical theorem admitted in `Remaining.lean` assumes `b > 0`, `coupling > 0`,
`E > 0`; this module makes no such existence assertion or admission.

The application below proves all its concrete source and differential-equation
hypotheses. The factor `coupling⁻²` comes from the fact that the kernel is the
resolvent of the semiclassical operator, while `magneticHamiltonian` is unscaled.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace InfiniteZero

/-- Classical resolvent identification for arbitrary smooth `L²` solutions
and arbitrary smooth compactly supported sources. Positivity of the three
parameters belongs to the classical theorem supplying this contract.

The differential equation also places `u` in the maximal operator domain,
since its right-hand side and `u` are in `L²`. Essential self-adjointness of
the free operator identifies this domain with its closed realization. -/
def FreeLandauResolventKernel (b coupling E : ℝ) : Prop :=
  ∀ u f : Wavefunction,
    ContDiff ℝ ∞ u → MemLp u 2 volume → IsTestFunction f →
    (∀ x, magneticHamiltonian b coupling 0 u x +
      ((coupling ^ 2 * E : ℝ) : ℂ) * u x = f x) →
    ∀ᵐ x : Plane, u x = (((coupling⁻¹) ^ 2 : ℝ) : ℂ) *
      ∫ y : Plane, freeLandauKernel b coupling⁻¹ E x y * f y

/-- The universal positive-parameter kernel interface at one fixed magnetic
field. It contains no potential, atomic state, separation or source estimate. -/
def HasPositiveLandauResolvent (b : ℝ) : Prop :=
  ∀ coupling E : ℝ, 0 < coupling → 0 < E → FreeLandauResolventKernel b coupling E

/-- Multiplication by the compactly supported potential makes the physical
right source compactly supported, although the atomic state need not be. -/
theorem rightPhysicalSource_isTestFunction (b L coupling : ℝ) {v : Potential}
    (hv : ContDiff ℝ ∞ v) (hvCompact : HasCompactSupport v)
    {φ : Wavefunction} (hφ : ContDiff ℝ ∞ φ) :
    IsTestFunction (rightPhysicalSource b v L coupling φ) := by
  have hu : ContDiff ℝ ∞ (rightState b L coupling φ) :=
    (contDiff_magneticTranslation b coupling (-displacement L) hφ).comp contDiff_id.neg
  have hvR : ContDiff ℝ ∞ (fun x => v (displacement L - x)) :=
    hv.comp (contDiff_const.sub contDiff_id)
  have hcR : HasCompactSupport (fun x => v (displacement L - x)) :=
    hvCompact.comp_homeomorph (Homeomorph.subLeft (displacement L))
  refine ⟨?_, ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul hvR)).mul hu
  · apply HasCompactSupport.intro hcR
    intro x hx
    have hz := image_eq_zero_of_notMem_tsupport (f := fun y => v (displacement L - y)) hx
    simp [rightPhysicalSource, atomicSource, hz]

/-- Covariance and the physical scaling give the precise free equation
needed by `FreeLandauResolventKernel`, with source `-rightPhysicalSource`. -/
theorem IsAtomicGroundState.rightState_resolvent_equation
    {b coupling E : ℝ} {v : Potential} {φ : Wavefunction}
    (hφ : IsAtomicGroundState b v coupling φ) (hCoupling : 0 < coupling)
    (hE : E = -(coupling⁻¹) ^ 2 * atomicGroundEnergy b v coupling)
    (L : ℝ) (x : Plane) :
    magneticHamiltonian b coupling 0 (rightState b L coupling φ) x +
      ((coupling ^ 2 * E : ℝ) : ℂ) * rightState b L coupling φ x =
        -rightPhysicalSource b v L coupling φ x := by
  have hscale : coupling ^ 2 * E = -atomicGroundEnergy b v coupling := by
    rw [hE]
    field_simp
  rw [hscale, Complex.ofReal_neg]
  have he := hφ.rightState_free_equation L x
  simpa only [rightPhysicalSource, atomicSource, inv_pow, inv_inv,
    neg_mul, ← sub_eq_add_neg] using he

/-- The only remaining input is the universal classical kernel contract;
all atomic translation, support, regularity, sign and scaling steps are proved. -/
theorem rightResolventRepresentation_of_freeLandauResolventKernel
    {b coupling E : ℝ} {v : Potential} {φ : Wavefunction}
    (hKernel : FreeLandauResolventKernel b coupling E)
    (hv : ContDiff ℝ ∞ v) (hvCompact : HasCompactSupport v)
    (hφ : IsAtomicGroundState b v coupling φ) (hCoupling : 0 < coupling)
    (hE : E = -(coupling⁻¹) ^ 2 * atomicGroundEnergy b v coupling) (L : ℝ) :
    RightResolventRepresentation b v L coupling E φ := by
  have hR := (hφ.rightState_eigenfunction L).1
  have hsource := rightPhysicalSource_isTestFunction b L coupling hv hvCompact hφ.1.1
  have hrepr := hKernel (rightState b L coupling φ) (-rightPhysicalSource b v L coupling φ)
    hR.1 hR.2.1 ⟨hsource.1.neg, hsource.2.neg⟩
    (hφ.rightState_resolvent_equation hCoupling hE L)
  filter_upwards [hrepr] with x hx
  simpa only [Pi.neg_apply, mul_neg, integral_neg, neg_mul] using hx

end InfiniteZero
