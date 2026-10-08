import InfiniteZero.RadialSingleWell
import InfiniteZero.RealRadialState
import InfiniteZero.SemiclassicalOperator
import InfiniteZero.RadialOscillatorLevels

/-!
# Classical radial ground state and the first two semiclassical levels

The input is stated in the semiclassical convention of Helffer--Kachmar,
arXiv:2208.13030v5, Theorem 1.1(1--2) and Proposition 2.1. The limiting
levels are the ordered values of the magnetic oscillator modes from
Section 2.2; the full mode formula is also stated by
Drigho-Filho--Kuru--Negro--Nieto, arXiv:1703.06634, equation (2.27).
Their ordering and difference are proved in
`RadialOscillatorLevels`; the oscillator spectral decomposition itself
remains part of this classical input.

No complement inequality, ground-state certificate, unscaled gap limit,
or threshold conversion is included here.
-/

noncomputable section
open Filter
open scoped Topology ContDiff
namespace InfiniteZero

/-- The first semiclassical level, defined by the actual operator-domain
Rayleigh infimum of `(-ih∇-A)²+V`. -/
def radialFirstSemiclassicalLevel (V : Potential) (h : ℝ) : ℝ :=
  operatorVariationalBottom (semiclassicalMagneticOperator V h)

/-- The second semiclassical min-max, using two-dimensional subspaces of
the same operator domain. -/
def radialSecondSemiclassicalLevel (V : Potential) (h : ℝ) : ℝ :=
  operatorSecondMinmax (semiclassicalMagneticOperator V h)

/-- The two instances `j=1,2` of harmonic approximation, together with the
positive normalized radial ground state. The limits use the full classical
oscillator mode family, before computing its first two ordered values.
The operator and its domain are fixed by `semiclassicalMagneticOperator`.
-/
structure RadialLowLevelData (V : Potential) where
  h₀ : ℝ
  h₀_pos : 0 < h₀
  errorBound : ℝ
  errorBound_pos : 0 < errorBound
  first_error : ∀ h : ℝ, 0 < h → h ≤ h₀ →
    |radialFirstSemiclassicalLevel V h - V 0 - h * radialOscillatorGroundLevel
      (iteratedDeriv 2 (fun r : ℝ => V (r • coordinateVector 0)) 0)| ≤
      errorBound * h * Real.sqrt h
  second_error : ∀ h : ℝ, 0 < h → h ≤ h₀ →
    |radialSecondSemiclassicalLevel V h - V 0 - h * radialOscillatorSecondLevel
      (iteratedDeriv 2 (fun r : ℝ => V (r • coordinateVector 0)) 0)| ≤
      errorBound * h * Real.sqrt h
  ground : ∀ h : ℝ, 0 < h → h ≤ h₀ →
    ∃ φ : Wavefunction, ContDiff ℝ ∞ φ ∧ IsPositiveRadial φ ∧
      ∃ u : (semiclassicalMagneticOperator V h).domain,
        ‖(u : L2Space)‖ = 1 ∧
        semiclassicalMagneticOperator V h u =
          (radialFirstSemiclassicalLevel V h : ℂ) • (u : L2Space) ∧
        Represents (u : L2Space) φ

/-- A004: the positive radial ground state and the first two harmonic
level asymptotics, in the source's semiclassical normalization. These are
Helffer--Kachmar, Theorem 1.1(1--2), Proposition 2.1, and the classical
oscillator mode decomposition in Section 2.2 and
Drigho-Filho--Kuru--Negro--Nieto, arXiv:1703.06634, equation (2.27).
The `h * sqrt h` error is the source's `O(h^(3/2))` remainder.
The project-specific
operator-certificate and coupling conversions are proved separately.
See `docs/RADIAL_HARMONIC_CONTRACT.md` for the exact correspondence.
-/
theorem classical_radial_low_levels (V : Potential) (hV : RadialSingleWell V) :
    Nonempty (RadialLowLevelData V) := by
  sorry

end InfiniteZero
