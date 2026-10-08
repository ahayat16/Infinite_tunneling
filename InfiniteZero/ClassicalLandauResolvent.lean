import InfiniteZero.LandauHeatTestInverse
import InfiniteZero.LandauResolventL2
import InfiniteZero.LandauResolventActionLinearity
import InfiniteZero.LandauResolventCoreExtension

/-!
# The standard Landau resolvent kernel

The kernel identity, formerly admission A003, is proved from the explicit
Gaussian heat kernel. Spatial integration, the heat equation, its initial
limit, and the Laplace transform give a left inverse on compact smooth
functions. Schur's estimate supplies the `L²` bound; closure of the test
graph then extends the identity to the given operator domain. The
realization certificate is an explicit hypothesis.

Cornean--Fournais--Frank--Helffer, *Sharp trace asymptotics for a class of
2D-magnetic operators*, Ann. Inst. Fourier 63 (2013), (B.21), p.2508,
gives the heat kernel in precisely this symmetric gauge. Its Laplace
transform gives the resolvent at negative spectral parameter. The direct
resolvent time-integral also appears in Helffer--Pankrashkin,
*Semiclassical reduction for magnetic Schrödinger operator with periodic
zero-range potentials and applications*, (5.1)--(5.2), in Landau gauge.
The Lean proof and its natural-language derivation are described in
`docs/CLASSICAL_LANDAU_RESOLVENT.md`.
-/

namespace InfiniteZero

/-- The standard Landau resolvent has the explicit proper-time kernel.
The proof uses the realization certificate only to identify the operator
graph with the closure of its compact smooth core. Every heat-kernel and
integral estimate is proved in Lean. This discharges the former A003;
the physical wrapper supplies `hA` from A002. -/
theorem classical_standard_landau_resolvent {B ρ : ℝ}
    (hB : 0 < B) (hρ : 0 < ρ) (hA : IsMagneticRealization B 1 0) :
    HasStandardLandauResolvent B ρ := by
  apply hasStandardLandauResolvent_of_testCore (C := ρ⁻¹ ^ 2) hA
  · intro f hf
    exact (standardLandauResolventAction_memLp_mass_le hB hρ hf).1
  · intro f g hf hg
    exact standardLandauResolventAction_mass_sub_le hB hρ
      (fun f hf => (standardLandauResolventAction_memLp_mass_le hB hρ hf).2) hf hg
  · intro φ hφ
    exact Filter.Eventually.of_forall fun x =>
      standardLandauResolventAction_shifted_test hB hρ hφ x

end InfiniteZero
