import InfiniteZero.ClassicalRadialHarmonic
import InfiniteZero.RadialCoreSpectralData
import InfiniteZero.RadialCoreVariationalBound
import InfiniteZero.MagneticFieldScaling
import InfiniteZero.MagneticGapThreshold
import InfiniteZero.RadialGroundCertificate
import InfiniteZero.AtomicLocalizationOverlap

/-!
# Radial-core spectral data from unit-field harmonic approximation

The classical input supplies the ground certificate and asymptotic gap for
`core / b²`. The explicit core hypotheses, variational energy bound, field
conversion, uniform gap threshold and test-function inequality are proved
in Lean. This assembles the unchanged interface used by the tunneling proof.
-/

noncomputable section
namespace InfiniteZero.CuspParameters

/-- Reconstruct the radial-core interface from unit-field harmonic data and
the magnetic realization. Both inputs are explicit hypotheses here, so this
assembly itself has no admitted proof step. The energy bound is independent
of both inputs. -/
theorem radialCoreSpectralData_of_harmonicData {p : CuspParameters} {b : ℝ}
    (hb : 0 < b) (hr : 0 < p.r₀)
    (h : RadialHarmonicData (fun x => p.core x / b ^ 2))
    (hA : ∀ coupling : ℝ,
      IsMagneticRealization 1 (b * coupling) (fun x => p.core x / b ^ 2)) :
    Nonempty (RadialCoreSpectralData b p) := by
  let δ := radialOscillatorGap (fun x => p.core x / b ^ 2)
  have hδ : 0 < δ := (core_div_sq_radialSingleWell hb hr).oscillatorGap_pos
  obtain ⟨B, hB, henergy⟩ := exists_core_scaledAtomicGroundEnergy_upper b hr
  obtain ⟨T, hT, hgap⟩ :=
    exists_pos_threshold_unitField_linear_gap hδ h.gapRatio_tendsto hb
  let S := max T (h.threshold / b)
  have hS : 0 < S := hT.trans_le (le_max_left _ _)
  have hground : ∀ coupling : ℝ, S ≤ coupling → ∃ φ : Wavefunction,
      IsAtomicGroundState b p.core coupling φ ∧ IsPositiveRadial φ ∧
      ∀ u : Wavefunction, IsTestFunction u →
        ((b * δ / 2) * coupling) * (mass u - ‖waveInner φ u‖ ^ 2) ≤
          magneticForm b coupling p.core u - atomicGroundEnergy b p.core coupling * mass u := by
    intro coupling hc
    have hunit : h.threshold ≤ b * coupling := by
      have hdiv : h.threshold / b ≤ coupling := (le_max_right _ _).trans hc
      simpa only [mul_comm] using (div_le_iff₀ hb).mp hdiv
    obtain ⟨E, q, hqgap, φ, hφsmooth, hφpos, hrep⟩ := h.ground (b * coupling) hunit
    have hφunit := q.isAtomicGroundState_of_smooth_representative (hA coupling) hφsmooth hrep
    have hφ := (isAtomicGroundState_unitField_iff hb.ne' coupling p.core φ).mpr hφunit
    refine ⟨φ, hφ, hφpos, fun u hu => ?_⟩
    have hproj : 0 ≤ mass u - ‖waveInner φ u‖ ^ 2 := by
      have hov := norm_waveInner_sq_le_mass_mul hφ.1.2.1 hu.memLp
      rw [hφ.2, one_mul] at hov
      exact sub_nonneg.mpr hov
    have hq := q.atomic_test_rankOne_lower_bound_of_smooth_representative
      (hA coupling) (core_div_sq_radialSingleWell hb hr).smooth.continuous hφsmooth hrep hu
    rw [← magneticForm_unitField hb.ne' coupling p.core u,
      ← atomicGroundEnergy_unitField hb.ne' coupling p.core] at hq
    have hgap' : (b * δ / 2) * coupling ≤ q.gap := by
      rw [hqgap]
      exact hgap coupling ((le_max_left _ _).trans hc)
    exact (mul_le_mul_of_nonneg_right hgap' hproj).trans hq
  refine ⟨{
    gap := b * δ / 2
    gap_pos := by positivity
    energyBound := B
    energyBound_pos := hB
    threshold := S
    threshold_pos := hS
    ground := ?_
    positive_radial_ground := ?_ }⟩
  · intro coupling hc
    have hcpos := hS.trans_le hc
    obtain ⟨φ, hφ, _, hφgap⟩ := hground coupling hc
    refine ⟨φ, hφ, henergy coupling hcpos, fun u hu => ?_⟩
    have hcancel : coupling ^ 2 * ((coupling⁻¹) ^ 2 *
        atomicGroundEnergy b p.core coupling) = atomicGroundEnergy b p.core coupling := by
      field_simp
    rw [hcancel]
    exact hφgap u hu
  · intro coupling hc
    obtain ⟨φ, hφ, hφpos, _⟩ := hground coupling hc
    exact ⟨φ, hφ, hφpos⟩

end InfiniteZero.CuspParameters
