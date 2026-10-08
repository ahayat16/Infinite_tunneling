import InfiniteZero.HoppingChannels
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# From the free resolvent equation to the two-source identity

The analytic input is the free Landau integral equation for the right atomic
state. All source normalizations, magnetic phases, changes of variables, and
the passage to the product integral are proved here. In particular the input
does not assume an identity for the hopping coefficient.
-/

noncomputable section
open MeasureTheory

namespace InfiniteZero

/-- The symmetric-gauge free Green kernel, with its explicit proper-time
radial part. The positive spectral parameter is supplied separately. -/
def freeLandauKernel (b h E : ℝ) (x y : Plane) : ℂ :=
  (landauKernel b h E ‖x - y‖ : ℂ) *
    Complex.exp (-Complex.I * ((b / (2 * h) * wedge x y : ℝ) : ℂ))

def leftPhysicalSource (b : ℝ) (v : Potential) (L coupling : ℝ)
    (φ : Wavefunction) : Wavefunction :=
  atomicSource coupling⁻¹ (fun x => v (x + displacement L))
    (leftState b L coupling φ)

def rightPhysicalSource (b : ℝ) (v : Potential) (L coupling : ℝ)
    (φ : Wavefunction) : Wavefunction :=
  atomicSource coupling⁻¹ (fun y => v (displacement L - y))
    (rightState b L coupling φ)

/-- The sole resolvent hypothesis: an almost-everywhere integral
representation of the right state by its physical source. -/
def RightResolventRepresentation (b : ℝ) (v : Potential) (L coupling E : ℝ)
    (φ : Wavefunction) : Prop :=
  ∀ᵐ x : Plane, rightState b L coupling φ x =
    -(((coupling⁻¹) ^ 2 : ℝ) : ℂ) *
      ∫ y : Plane, freeLandauKernel b coupling⁻¹ E x y *
        rightPhysicalSource b v L coupling φ y

theorem leftPhysicalSource_gauge (b : ℝ) (v : Potential) (L coupling : ℝ)
    (φ : Wavefunction) (x : Plane) :
    leftPhysicalSource b v L coupling φ x =
      Complex.exp (Complex.I * ((b * coupling / 2 * wedge x (displacement L) : ℝ) : ℂ)) *
        atomicSource coupling⁻¹ v φ (x + displacement L) := by
  have hw : wedge x (-displacement L) = -wedge x (displacement L) := by
    simp only [wedge, PiLp.neg_apply]
    ring
  simp only [leftPhysicalSource, atomicSource, leftState, magneticTranslation,
    hw, mul_neg, Complex.ofReal_neg, sub_neg_eq_add]
  ring_nf

theorem rightPhysicalSource_gauge (b : ℝ) (v : Potential) (L coupling : ℝ)
    (φ : Wavefunction) (y : Plane) :
    rightPhysicalSource b v L coupling φ y =
      Complex.exp (-Complex.I * ((b * coupling / 2 * wedge y (displacement L) : ℝ) : ℂ)) *
        atomicSource coupling⁻¹ v φ (displacement L - y) := by
  simp only [rightPhysicalSource, atomicSource, rightState, leftState, magneticTranslation,
    wedge, PiLp.neg_apply, neg_mul_neg, sub_neg_eq_add]
  rw [neg_add_eq_sub]
  ring

/-- The affine substitution reproduces precisely the geometric phase. -/
theorem sourcePhase_affine (b L : ℝ) (z w : Plane) :
    -(b / 2) * (wedge (z - displacement L) (displacement L) +
      wedge (displacement L - w) (displacement L) +
      wedge (z - displacement L) (displacement L - w)) = sourcePhase b L z w := by
  simp [wedge, displacement, coordinateVector, sourcePhase, PiLp.sub_apply]
  ring

theorem source_displacement_affine (L : ℝ) (z w : Plane) :
    (z - displacement L) - (displacement L - w) = z + w - 2 • displacement L := by
  module

theorem physical_source_integrand_affine (b : ℝ) (v : Potential) (L coupling E : ℝ)
    (φ : Wavefunction) (z w : Plane) :
    star (leftPhysicalSource b v L coupling φ (z - displacement L)) *
      freeLandauKernel b coupling⁻¹ E (z - displacement L) (displacement L - w) *
      rightPhysicalSource b v L coupling φ (displacement L - w) =
    channelIntegrand (sourceKernel b L coupling⁻¹ E)
      (atomicSource coupling⁻¹ v φ) (atomicSource coupling⁻¹ v φ) (z, w) := by
  rw [leftPhysicalSource_gauge, rightPhysicalSource_gauge]
  simp only [sub_add_cancel, sub_sub_cancel]
  simp only [freeLandauKernel, channelIntegrand, sourceKernel, source_displacement_affine,
    star_mul', Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_I,
    Complex.conj_ofReal]
  have hp :
      -(Complex.I * ((b * coupling / 2 * wedge (z - displacement L) (displacement L) : ℝ) : ℂ)) +
      (-Complex.I * ((b / (2 * coupling⁻¹) *
        wedge (z - displacement L) (displacement L - w) : ℝ) : ℂ)) +
      (-Complex.I * ((b * coupling / 2 * wedge (displacement L - w) (displacement L) : ℝ) : ℂ)) =
      ((sourcePhase b L z w / coupling⁻¹ : ℝ) : ℂ) * Complex.I := by
    have hr := sourcePhase_affine b L z w
    simp only [div_mul_eq_div_div, div_inv_eq_mul]
    push_cast
    rw [← hr]
    push_cast
    ring
  calc
    _ = star (atomicSource coupling⁻¹ v φ z) *
        (landauKernel b coupling⁻¹ E ‖z + w - 2 • displacement L‖ : ℂ) *
        (Complex.exp (-(Complex.I * ((b * coupling / 2 *
          wedge (z - displacement L) (displacement L) : ℝ) : ℂ))) *
        Complex.exp (-Complex.I * ((b / (2 * coupling⁻¹) *
          wedge (z - displacement L) (displacement L - w) : ℝ) : ℂ)) *
        Complex.exp (-Complex.I * ((b * coupling / 2 *
          wedge (displacement L - w) (displacement L) : ℝ) : ℂ))) *
        atomicSource coupling⁻¹ v φ w := by simp only [Complex.star_def]; ring_nf
    _ = _ := by
      rw [← Complex.exp_add, ← Complex.exp_add, hp]
      simp only [Complex.star_def]
      ring

theorem hopping_eq_source_inner (b : ℝ) (v : Potential) (L coupling : ℝ)
    (φ : Wavefunction) :
    hopping b v L coupling φ =
      ∫ x : Plane, star (leftPhysicalSource b v L coupling φ x) * rightState b L coupling φ x := by
  unfold hopping
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [leftPhysicalSource, atomicSource, inv_pow, inv_inv, Complex.ofReal_mul,
    star_mul', Complex.star_def, Complex.conj_ofReal]
  ring

/-- The exact two-source identity follows from the one-state free resolvent
equation. Its only integrability hypothesis is for the final source pairing. -/
theorem hopping_eq_sourcePairing_of_resolvent (b : ℝ) (v : Potential) (L coupling E : ℝ)
    (φ : Wavefunction)
    (hR : RightResolventRepresentation b v L coupling E φ)
    (hInt : Integrable (channelIntegrand (sourceKernel b L coupling⁻¹ E)
      (atomicSource coupling⁻¹ v φ) (atomicSource coupling⁻¹ v φ)) (volume.prod volume)) :
    hopping b v L coupling φ = sourcePairing coupling⁻¹ (sourceKernel b L coupling⁻¹ E)
      (atomicSource coupling⁻¹ v φ) (atomicSource coupling⁻¹ v φ) := by
  rw [hopping_eq_source_inner]
  let f : Plane → Plane → ℂ := fun x y =>
    star (leftPhysicalSource b v L coupling φ x) * freeLandauKernel b coupling⁻¹ E x y *
      rightPhysicalSource b v L coupling φ y
  have hrep :
      (∫ x : Plane, star (leftPhysicalSource b v L coupling φ x) * rightState b L coupling φ x) =
      -(((coupling⁻¹) ^ 2 : ℝ) : ℂ) * ∫ x : Plane, ∫ y : Plane, f x y := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hR] with x hx
    rw [hx]
    simp only [f, mul_assoc, integral_const_mul]
    ring
  rw [hrep]
  unfold sourcePairing
  congr 1
  calc
    (∫ x : Plane, ∫ y : Plane, f x y) =
        ∫ z : Plane, ∫ y : Plane, f (z - displacement L) y :=
      (integral_sub_right_eq_self (fun x : Plane => ∫ y : Plane, f x y) (displacement L)).symm
    _ = ∫ z : Plane, ∫ w : Plane, f (z - displacement L) (displacement L - w) := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact (integral_sub_left_eq_self (fun y : Plane => f (z - displacement L) y)
        volume (displacement L)).symm
    _ = ∫ z : Plane, ∫ w : Plane,
        channelIntegrand (sourceKernel b L coupling⁻¹ E)
          (atomicSource coupling⁻¹ v φ) (atomicSource coupling⁻¹ v φ) (z, w) := by
      simp only [f, physical_source_integrand_affine]
    _ = _ := integral_integral hInt

/-- The nine existing integrability conditions imply exactly the Fubini
hypothesis used by the source-identity theorem. -/
theorem CellsIntegrable.total {p : CuspParameters} {L h E : ℝ} {φ : Wavefunction}
    (hInt : CellsIntegrable p L h E φ) :
    Integrable (channelIntegrand (sourceKernel p.b L h E)
      (atomicSource h p.potential φ) (atomicSource h p.potential φ)) (volume.prod volume) := by
  rw [← componentSource_sum p h φ]
  have he : channelIntegrand (sourceKernel p.b L h E)
      (fun x => ∑ i, componentSource p h φ i x) (fun x => ∑ i, componentSource p h φ i x) =
      (fun q => ∑ i : Fin 3, ∑ j : Fin 3,
        channelIntegrand (sourceKernel p.b L h E)
          (componentSource p h φ i) (componentSource p h φ j) q) := by
    funext q
    simp only [channelIntegrand, Complex.star_def, map_sum, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  rw [he]
  exact integrable_finsetSum Finset.univ fun i _ =>
    integrable_finsetSum Finset.univ fun j _ => hInt i j

theorem canonicalHopping_eq_source_of_resolvent (p : CuspParameters) (L coupling : ℝ)
    (hR : RightResolventRepresentation p.b p.potential L coupling (scaledAtomicEnergy p coupling)
      (canonicalAtomicState p.b p.potential coupling))
    (hInt : CellsIntegrable p L coupling⁻¹ (scaledAtomicEnergy p coupling)
      (canonicalAtomicState p.b p.potential coupling)) :
    canonicalHopping p.b p.potential L coupling = canonicalTotalSourcePairing p L coupling :=
  hopping_eq_sourcePairing_of_resolvent p.b p.potential L coupling (scaledAtomicEnergy p coupling)
    (canonicalAtomicState p.b p.potential coupling) hR hInt.total

/-- Direct entry point to the oscillation pipeline from the free-resolvent
equation and the two complex active-channel estimates. -/
def canonicalHopping_linearCosine_of_resolvent (p : CuspParameters) (L slope : ℝ)
    (h : ChannelAsymptotics (canonicalSourceCell p L) slope)
    (hInt : ∀ x, h.threshold ≤ x → CellsIntegrable p L x⁻¹ (scaledAtomicEnergy p x)
      (canonicalAtomicState p.b p.potential x))
    (hR : ∀ x, h.threshold ≤ x →
      RightResolventRepresentation p.b p.potential L x (scaledAtomicEnergy p x)
        (canonicalAtomicState p.b p.potential x)) :
    LinearCosineAsymptotic (fun x => -(canonicalHopping p.b p.potential L x).re) slope :=
  canonicalHopping_linearCosine_of_channels p L slope h hInt fun x hx =>
    canonicalHopping_eq_source_of_resolvent p L x (hR x hx) (hInt x hx)

theorem canonicalHopping_real_of_resolvent (p : CuspParameters) (L coupling : ℝ)
    (hR : RightResolventRepresentation p.b p.potential L coupling (scaledAtomicEnergy p coupling)
      (canonicalAtomicState p.b p.potential coupling))
    (hInt : CellsIntegrable p L coupling⁻¹ (scaledAtomicEnergy p coupling)
      (canonicalAtomicState p.b p.potential coupling)) :
    (canonicalHopping p.b p.potential L coupling).im = 0 :=
  canonicalHopping_real_of_source_identity p L coupling
    (canonicalHopping_eq_source_of_resolvent p L coupling hR hInt)

end InfiniteZero
