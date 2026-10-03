import InfiniteZero.CanonicalParityFineBound
import InfiniteZero.AtomicOppositeSupportFineBounds
import InfiniteZero.ConcreteChannelWitnesses
import InfiniteZero.CanonicalChannelAsymptotics

/-!
# Fine errors for the same physical witnesses as the hopping asymptotic

The universal opposite-support estimate is applied to the actual canonical
full ground state and to the core coefficient already fixed by the channel
witnesses. Both physical Schur corrections and the diagonal defect are
little-o of that very same positive tunneling envelope.
-/

noncomputable section
open Filter Set Asymptotics
open scoped Topology
namespace InfiniteZero.CuspParameters

theorem canonicalParity_errors_isLittleO_of_radialData
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
    {L : ℝ} (hL : cert.L₀ ≤ L) (W : ConcreteChannelWitnesses p L) :
    canonicalDefect p.b p.potential L =o[atTop]
      (fun coupling => p.activeSaddleTexEnvelope L coupling (W.c coupling) (W.Γ coupling)) ∧
    ∀ even : Bool, (fun coupling => canonicalParityCorrection p.b p.potential L coupling even)
      =o[atTop] (fun coupling =>
        p.activeSaddleTexEnvelope L coupling (W.c coupling) (W.Γ coupling)) := by
  obtain ⟨C, hC, Tm, _, hmass⟩ := exists_atomic_oppositeSupport_mass_fine_bound_of_radialData
    hInterior hp hRad hAcore hApot hKernel χ cert hL
  obtain ⟨Ts, _, hσ⟩ := exists_canonicalParityCorrection_mass_bounds_of_radialData
    hp cert hRad hAcore hApot hAdouble
  have hRL : p.R < L := ((le_max_right _ _).trans_lt cert.separation).trans_le hL
  have hcpos : ∀ᶠ coupling in atTop, 0 < W.c coupling := by
    filter_upwards [eventually_ge_atTop W.threshold] with coupling hc
    exact lt_of_lt_of_le (by norm_num) (W.c_range coupling hc).1
  have hΓpos : ∀ᶠ coupling in atTop, 0 < W.Γ coupling := by
    filter_upwards [eventually_ge_atTop W.threshold] with coupling hc
    exact W.Γ_pos coupling hc
  have hfine (K : ℝ) (hK : 0 ≤ K) :=
    oppositeSupportFineBound_isLittleO_activeSaddleTexEnvelope_of_radialData
      hp hRad hAcore hApot hRL hK hcpos hΓpos
  have hδbound : canonicalDefect p.b p.potential L =O[atTop]
      (fun coupling => p.oppositeSupportFineBound L C coupling (W.c coupling) (W.Γ coupling)) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop Tm, eventually_ge_atTop W.threshold,
      eventually_ge_atTop (1 : ℝ)] with coupling hcm hcw hc1
    have hψ := canonicalAtomicState_spec p.b p.potential coupling
      ⟨W.ψ coupling, W.full_ground coupling hcw⟩
    obtain ⟨_, hI, _⟩ := hmass coupling hcm (W.φ coupling) (W.core_ground coupling hcw)
      (W.core_positive coupling hcw) (W.Γ coupling) (W.tail coupling hcw)
      (W.c coupling) (W.c_range coupling hcw).1 _ hψ
    have hb := canonicalDefect_le_oppositeSupportFineBound hc1 hC.le hI
    simpa only [one_mul, Real.norm_eq_abs] using hb.trans (le_abs_self _)
  refine ⟨hδbound.trans_isLittleO (hfine C hC.le), ?_⟩
  intro even
  have hσbound : (fun coupling => canonicalParityCorrection p.b p.potential L coupling even)
      =O[atTop] (fun coupling =>
        p.oppositeSupportFineBound L ((32 / hRad.gap) * C) coupling (W.c coupling) (W.Γ coupling)) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop Tm, eventually_ge_atTop W.threshold,
      eventually_ge_atTop Ts, eventually_ge_atTop (1 : ℝ)] with coupling hcm hcw hcs hc1
    have hψ := canonicalAtomicState_spec p.b p.potential coupling
      ⟨W.ψ coupling, W.full_ground coupling hcw⟩
    obtain ⟨_, _, hM⟩ := hmass coupling hcm (W.φ coupling) (W.core_ground coupling hcw)
      (W.core_positive coupling hcw) (W.Γ coupling) (W.tail coupling hcw)
      (W.c coupling) (W.c_range coupling hcw).1 _ hψ
    obtain ⟨hnonneg, hbound⟩ := hσ coupling hcs L hL
      (hAleft coupling L) (hAright coupling L) even
    have hb := canonicalParityCorrection_le_oppositeSupportFineBound
      (zero_le_one.trans hc1) hRad.gap_pos even hbound hM
    simpa only [one_mul, Real.norm_eq_abs, abs_of_nonneg hnonneg]
      using hb.trans (le_abs_self _)
  exact hσbound.trans_isLittleO (hfine ((32 / hRad.gap) * C)
    (mul_nonneg (div_nonneg (by norm_num) hRad.gap_pos.le) hC.le))

theorem nonempty_canonicalParitySchurData_of_radialData
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
    {L : ℝ} (hL : cert.L₀ ≤ L) (W : ConcreteChannelWitnesses p L) :
    Nonempty (CanonicalParitySchurData p.b p.potential L (fun coupling =>
      2 * (p.activeTangentialLeadingCoefficient L *
        p.activeSaddleTexEnvelope L coupling (W.c coupling) (W.Γ coupling)))) := by
  obtain ⟨hδ, hσ⟩ := canonicalParity_errors_isLittleO_of_radialData
    hInterior hp hRad hAcore hApot hAleft hAright hAdouble hKernel χ cert hL W
  have hRL : p.R < L := ((le_max_right _ _).trans_lt cert.separation).trans_le hL
  have hsep : p.R < 2 * L := by linarith [hp.radius_pos]
  have hK : 0 < 2 * p.activeTangentialLeadingCoefficient L :=
    mul_pos (by norm_num) (activeTangentialLeadingCoefficient_pos hp hsep)
  have hfour : 4 * p.r₀ ≤ L := by linarith [hp.radius_large, hp.r₀_pos]
  refine ⟨canonicalParitySchurDataOfSmallErrors
    (tendsto_canonicalOverlap_of_radialData hp hRad hAcore hApot hfour) ?_ ?_⟩
  · simpa only [mul_assoc] using hδ.const_mul_right hK.ne'
  · intro even
    simpa only [mul_assoc] using (hσ even).const_mul_right hK.ne'

end InfiniteZero.CuspParameters
