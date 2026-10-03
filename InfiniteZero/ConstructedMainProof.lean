import InfiniteZero.CanonicalParityRelativeErrors
import InfiniteZero.ConstructedMainAssembly

/-!
# Main conclusion for the constructed potential from classical interfaces

Every original estimate is constructed here through the preceding modules.
The same channel witnesses supply the hopping envelope and the little-o
Schur errors. Only the universal realization, radial-core, resolvent and
elliptic interfaces are external inputs; no tunneling or double-well
spectral hypothesis is assumed.
-/

noncomputable section
namespace InfiniteZero.CuspParameters

theorem operatorMainConclusion_of_radialData
    (hInterior : HasInteriorEllipticEstimate)
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (hAleft : ∀ coupling L,
      IsMagneticRealization p.b coupling (fun x => p.potential (x + displacement L)))
    (hAright : ∀ coupling L,
      IsMagneticRealization p.b coupling (fun x => p.potential (displacement L - x)))
    (hAdouble : ∀ coupling L,
      IsMagneticRealization p.b coupling (doubleWellPotential p.potential L))
    (hKernel : HasPositiveLandauResolvent p.b)
    (χ : CuspWeightCutoffs p) (cert : p.SeparationCertificate)
    {L : ℝ} (hL : cert.L₀ ≤ L) : OperatorMainConclusion p.b p.potential L := by
  obtain ⟨W, H, _, hamp, _, hreal⟩ := exists_canonicalHopping_asymptotic_of_radialData
    hInterior hp hRad hAcore hApot hKernel χ cert hL
  obtain ⟨S⟩ := nonempty_canonicalParitySchurData_of_radialData
    hInterior hp hRad hAcore hApot hAleft hAright hAdouble hKernel χ cert hL W
  have hSchur : CanonicalParitySchurData p.b p.potential L H.amplitude := by
    rw [hamp]
    exact S
  exact operatorMainConclusion_of_hopping_schur hp cert hRad hAcore hApot
    hAleft hAright hAdouble hL H hreal hSchur

theorem exists_main_separation_of_radialData
    (hInterior : HasInteriorEllipticEstimate)
    {p : CuspParameters} (hp : p.BasicConditions) (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (hAleft : ∀ coupling L,
      IsMagneticRealization p.b coupling (fun x => p.potential (x + displacement L)))
    (hAright : ∀ coupling L,
      IsMagneticRealization p.b coupling (fun x => p.potential (displacement L - x)))
    (hAdouble : ∀ coupling L,
      IsMagneticRealization p.b coupling (doubleWellPotential p.potential L))
    (hKernel : HasPositiveLandauResolvent p.b) :
    ∃ L₀ : ℝ, p.R < L₀ ∧ ∀ L : ℝ, L₀ ≤ L → OperatorMainConclusion p.b p.potential L := by
  obtain ⟨χ⟩ := exists_cuspWeightCutoffs hp
  obtain ⟨cert⟩ := exists_separationCertificate hp
  refine ⟨cert.L₀, (le_max_right _ _).trans_lt cert.separation, ?_⟩
  intro L hL
  exact operatorMainConclusion_of_radialData hInterior hp hRad hAcore hApot
    hAleft hAright hAdouble hKernel χ cert hL

end InfiniteZero.CuspParameters
