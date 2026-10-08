import InfiniteZero.RadialSingleWell
import InfiniteZero.GroundStateCertificate
import InfiniteZero.RealRadialState

/-!
# Unit-field radial harmonic certificate

This is the intermediate certificate used by the radial-core assembly.
Its existence follows from the semiclassical level input A004 and realization
A002 through `RadialHarmonicAssembly`. The complement inequality, coupling
conversion and oscillator-gap calculation are proved in Lean.
-/

noncomputable section
open Filter
open scoped Topology ContDiff
namespace InfiniteZero

/-- Difference between the first two unit-field oscillator levels associated
with the radial Hessian of the well; Helffer--Kachmar, Section 2.2. -/
def radialOscillatorGap (V : Potential) : ℝ :=
  Real.sqrt (1 + 2 * iteratedDeriv 2 (fun r : ℝ => V (r • coordinateVector 0)) 0) - 1

theorem RadialSingleWell.oscillatorGap_pos {V : Potential} (hV : RadialSingleWell V) :
    0 < radialOscillatorGap V := by
  have hd := hV.radial_second_pos
  unfold radialOscillatorGap
  have hs := Real.sq_sqrt (show 0 ≤ 1 + 2 *
    iteratedDeriv 2 (fun r : ℝ => V (r • coordinateVector 0)) 0 by linarith)
  have hn := Real.sqrt_nonneg (1 + 2 *
    iteratedDeriv 2 (fun r : ℝ => V (r • coordinateVector 0)) 0)
  nlinarith

/-- The operator-form consequence of radial harmonic approximation.
`gapRatio` is the certified gap divided by the unscaled coupling.
`RadialHarmonicAssembly` derives this structure from the two level
asymptotics using the proved min-max complement inequality.
The positive representative is specified for the same normalized vector.
-/
structure RadialHarmonicData (V : Potential) where
  threshold : ℝ
  threshold_pos : 0 < threshold
  gapRatio : ℝ → ℝ
  gapRatio_tendsto : Tendsto gapRatio atTop (𝓝 (radialOscillatorGap V))
  ground : ∀ coupling : ℝ, threshold ≤ coupling →
    ∃ E : ℝ, ∃ q : GroundStateCertificate (magneticOperator 1 coupling V) E,
      q.gap = gapRatio coupling * coupling ∧
      ∃ φ : Wavefunction, ContDiff ℝ ∞ φ ∧ IsPositiveRadial φ ∧
        Represents (q.normalizedVector : L2Space) φ

end InfiniteZero
