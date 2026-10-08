import InfiniteZero.CuspSourcePairingFubini
import InfiniteZero.AtomicCuspKernelProfile
import InfiniteZero.ComplexLogFlatChange

/-!
# Exact normalization of the incoming physical cusp density

The two chart Jacobians become the powers in the two scalar log-flat
integrands. This is before the logarithmic changes of variables: there
is no tStar^6 factor here. The cell factor -h^2 and the source prefactors
remain outside the density. All identities are multiplicative, so no
nonvanishing premise on a kernel or leading coefficient is necessary.
-/

noncomputable section

namespace InfiniteZero

/-- On the positive real axis the complex scalar model splits into the
real log-flat factor, its power, and the complex linear exponential. -/
theorem complexLogFlatIntegrand_eq_logFlat_mul
    (β tStar h : ℝ) (c : ℂ) (m : ℕ) {t : ℝ} (ht : 0 < t) :
    complexLogFlatIntegrand β tStar h c m t =
      ((t ^ m * logFlat β tStar t : ℝ) : ℂ) *
        Complex.exp (-(c * (t : ℂ) / (h : ℂ))) := by
  rw [complexLogFlatIntegrand, logFlat_of_pos _ _ ht, sub_eq_add_neg, Complex.exp_add]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_exp,
    Complex.ofReal_neg]
  ring

namespace CuspParameters

/-- Baseline normalization only. The core and full energies remain distinct,
and no source strength or cell sign is included. -/
def incomingCuspNormalization (p : CuspParameters) (L h Ecore Efull : ℝ) : ℂ :=
  ((h ^ (3 / 2 : ℝ) : ℝ) : ℂ) ^ 3 /
    ((landauLeadingCoefficient p.b Ecore p.R : ℂ) ^ 2 *
      (landauLeadingCoefficient p.b Efull (Geometry.activeDistance p.R L) : ℂ)) *
    Complex.exp ((((p.activeReferenceAction L Efull Ecore : ℝ) : ℂ) -
      Complex.I * (Geometry.phaseStar p.b p.R L : ℂ)) / (h : ℂ))

/-- Exact passage from the physical chart density to the two scalar normal
models and the true normalized multiplier. Only the positivity of the two
normal coordinates is needed; the normalization is never divided out. -/
theorem incomingCuspNormalization_mul_density
    (p : CuspParameters) (L h Ecore Efull s r : ℝ) {t u : ℝ}
    (ht : 0 < t) (hu : 0 < u) :
    p.incomingCuspNormalization L h Ecore Efull *
        p.incomingCuspDensity L h Ecore Efull t u s r =
      ((p.χa t * p.χa u * p.χb s * p.χb r : ℝ) : ℂ) *
        complexLogFlatIntegrand p.β p.tStar h (p.activeSaddleSlope L) 2 t *
        complexLogFlatIntegrand p.β p.tStar h (p.activeSaddleSlope L) 2 u *
        p.frozenCuspKernelPhaseProfile L h Ecore Efull s r (t : ℂ) (u : ℂ) := by
  have he :
      Complex.exp (-(p.activeSaddleSlope L * (t : ℂ) / (h : ℂ))) *
        Complex.exp (-(p.activeSaddleSlope L * (u : ℂ) / (h : ℂ))) *
        Complex.exp (((p.activeReferenceAction L Efull Ecore : ℝ) : ℂ) / (h : ℂ) +
          (p.activeSaddleSlope L * ((t : ℂ) + (u : ℂ)) -
            Complex.I * (Geometry.phaseStar p.b p.R L : ℂ)) / (h : ℂ)) =
      Complex.exp ((((p.activeReferenceAction L Efull Ecore : ℝ) : ℂ) -
        Complex.I * (Geometry.phaseStar p.b p.R L : ℂ)) / (h : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  unfold incomingCuspNormalization
  rw [← he, incomingCuspDensity_eq_complex,
    complexLogFlatIntegrand_eq_logFlat_mul _ _ _ _ _ ht,
    complexLogFlatIntegrand_eq_logFlat_mul _ _ _ _ _ hu,
    frozenCuspKernelPhaseProfile_eq_normalized_product]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Geometry.complexCuspKernelProduct]
  ring

end CuspParameters
end InfiniteZero
