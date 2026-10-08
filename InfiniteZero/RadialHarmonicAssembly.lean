import InfiniteZero.ClassicalRadialHarmonic
import InfiniteZero.ClassicalRadialLowLevels
import InfiniteZero.RadialHarmonicLimits
import InfiniteZero.MagneticGapThreshold

/-!
# From semiclassical levels to the radial ground-state certificate

The first two mode values, subtraction of the harmonic limits, change of
coupling and energy units, and min-max complement inequality are proved
here or in the imported modules. The classical level data and magnetic
realization are explicit hypotheses of this assembly.
-/

noncomputable section
open Filter
open scoped Topology ContDiff
namespace InfiniteZero

/-- The first source remainder bound yields the first oscillator coefficient. -/
theorem RadialLowLevelData.first_limit {V : Potential} (h : RadialLowLevelData V) :
    Tendsto (fun t => (radialFirstSemiclassicalLevel V t - V 0) / t)
      (𝓝[>] (0 : ℝ))
      (𝓝 (radialOscillatorGroundLevel
        (iteratedDeriv 2 (fun r : ℝ => V (r • coordinateVector 0)) 0))) :=
  tendsto_firstOrder_of_harmonic_remainder h.h₀_pos h.errorBound_pos.le h.first_error

/-- The second source remainder bound yields the second oscillator coefficient. -/
theorem RadialLowLevelData.second_limit {V : Potential} (h : RadialLowLevelData V) :
    Tendsto (fun t => (radialSecondSemiclassicalLevel V t - V 0) / t)
      (𝓝[>] (0 : ℝ))
      (𝓝 (radialOscillatorSecondLevel
        (iteratedDeriv 2 (fun r : ℝ => V (r • coordinateVector 0)) 0))) :=
  tendsto_firstOrder_of_harmonic_remainder h.h₀_pos h.errorBound_pos.le h.second_error

/-- The two source-format harmonic asymptotics imply the unscaled gap
ratio, with the oscillator gap computed from its ordered mode values. -/
theorem RadialLowLevelData.gapRatio_tendsto {V : Potential}
    (h : RadialLowLevelData V) (hV : RadialSingleWell V) :
    Tendsto (fun k : ℝ => k *
      (radialSecondSemiclassicalLevel V k⁻¹ - radialFirstSemiclassicalLevel V k⁻¹))
      atTop (𝓝 (radialOscillatorGap V)) := by
  have ht := tendsto_coupling_gap_of_harmonic_levels h.first_limit h.second_limit
  rwa [radialOscillatorLevel_gap hV.radial_second_pos] at ht

/-- At positive coupling, the rescaled difference is exactly the
unscaled second min-max minus the first Rayleigh infimum. -/
theorem coupling_mul_radial_semiclassical_gap {V : Potential} {k : ℝ} (hk : 0 < k) :
    (k * (radialSecondSemiclassicalLevel V k⁻¹ -
      radialFirstSemiclassicalLevel V k⁻¹)) * k =
      operatorSecondMinmax (magneticOperator 1 k V) -
        operatorVariationalBottom (magneticOperator 1 k V) := by
  rw [radialSecondSemiclassicalLevel, radialFirstSemiclassicalLevel,
    semiclassicalMagneticOperator_secondMinmax V (inv_ne_zero hk.ne'),
    semiclassicalMagneticOperator_variationalBottom, inv_inv]
  field_simp

/-- Construct the previous radial harmonic interface from the published
level asymptotics and positive radial state. The spectral min-max passage
to the complement bound is a Lean theorem, not an input field. -/
theorem radialHarmonicData_of_lowLevels {V : Potential} (hV : RadialSingleWell V)
    (h : RadialLowLevelData V)
    (hA : ∀ k : ℝ, IsMagneticRealization 1 k V) :
    Nonempty (RadialHarmonicData V) := by
  let g : ℝ → ℝ := fun k => k *
    (radialSecondSemiclassicalLevel V k⁻¹ - radialFirstSemiclassicalLevel V k⁻¹)
  have hg : Tendsto g atTop (𝓝 (radialOscillatorGap V)) := h.gapRatio_tendsto hV
  obtain ⟨T, hT, hbound⟩ := exists_pos_threshold_unitField_lower
    hV.oscillatorGap_pos hg (show (0 : ℝ) < 1 by norm_num)
  let S := max T h.h₀⁻¹
  have hS : 0 < S := hT.trans_le (le_max_left _ _)
  refine ⟨⟨S, hS, g, hg, ?_⟩⟩
  intro k hk
  have hkpos : 0 < k := hS.trans_le hk
  have hkh : k⁻¹ ≤ h.h₀ := (inv_le_comm₀ hkpos h.h₀_pos).mpr
    ((le_max_right _ _).trans hk)
  have hsource := h.ground k⁻¹ (inv_pos.mpr hkpos) hkh
  simp only [semiclassicalMagneticOperator] at hsource
  rw [inv_inv] at hsource
  obtain ⟨φ, hφ, hφpos, v, hv, heig, hrep⟩ := hsource
  let A := magneticOperator 1 k V
  have heig' : A v = (operatorVariationalBottom A : ℂ) • (v : L2Space) := by
    apply operatorVariationalBottom_eigenvector_of_real_smul A
      (sq_pos_of_pos (inv_pos.mpr hkpos)) v
    simpa only [radialFirstSemiclassicalLevel, semiclassicalMagneticOperator, inv_inv] using heig
  have hlo : ∀ u : A.domain, operatorVariationalBottom A * ‖(u : L2Space)‖ ^ 2 ≤
      (inner ℂ (u : L2Space) (A u)).re := by
    intro u
    rw [(hA k).bottom_eq]
    exact (hA k).lower_bound u
  have hgpos : 0 < g k := by
    have hb := hbound k ((le_max_left _ _).trans hk)
    simp only [one_mul] at hb
    exact (half_pos hV.oscillatorGap_pos).trans_le hb
  have hgap : operatorVariationalBottom A < operatorSecondMinmax A := by
    have heq := coupling_mul_radial_semiclassical_gap (V := V) hkpos
    have hp := mul_pos hgpos hkpos
    change 0 < (k * (radialSecondSemiclassicalLevel V k⁻¹ -
      radialFirstSemiclassicalLevel V k⁻¹)) * k at hp
    rw [heq] at hp
    exact sub_pos.mp hp
  let q := groundStateCertificate_of_secondMinmax (hA k).selfAdjoint v hv heig' hlo hgap
  refine ⟨operatorVariationalBottom A, q, ?_, φ, hφ, hφpos, ?_⟩
  · exact (coupling_mul_radial_semiclassical_gap (V := V) hkpos).symm
  · have hn : (q.normalizedVector : L2Space) = (v : L2Space) := by
      simp only [GroundStateCertificate.normalizedVector, q,
        groundStateCertificate_of_secondMinmax, hv, inv_one, Complex.ofReal_one,
        one_smul]
    rwa [hn]

end InfiniteZero
