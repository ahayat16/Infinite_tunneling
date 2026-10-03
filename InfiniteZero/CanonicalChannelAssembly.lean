import InfiniteZero.HoppingChannels

/-!
# Assembling the canonical channels from relative errors

The amplitude is preserved exactly. No regularity of this amplitude or of
the witnesses used to define it is required. The incoming identity retains
its negative sign and its complex phase; only relative error bounds are
used to replace the incoming channel by the canonical active cell.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace InfiniteZero

/-- A pointwise bound relative to a positive, possibly irregular amplitude
gives convergence of the normalized complex error. -/
theorem tendsto_complex_div_of_eventual_norm_bound
    {ι : Type*} {l : Filter ι} {F : ι → ℂ} {amplitude error : ι → ℝ}
    (ha : ∀ᶠ x in l, 0 < amplitude x) (he : Tendsto error l (𝓝 0))
    (hbound : ∀ᶠ x in l, ‖F x‖ ≤ amplitude x * error x) :
    Tendsto (fun x => F x / (amplitude x : ℂ)) l (𝓝 0) := by
  apply squeeze_zero_norm' _ he
  filter_upwards [ha, hbound] with x hx hb
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
  apply (div_le_iff₀ hx).mpr
  simpa only [mul_comm] using hb

/-- An incoming relative identity gives the required signed complex channel
limit even when the phase itself has no limit. -/
theorem tendsto_incoming_channel_of_relative_identity
    {ι : Type*} {l : Filter ι} {incoming error : ι → ℂ}
    {amplitude phase : ι → ℝ}
    (ha : ∀ᶠ x in l, 0 < amplitude x) (he : Tendsto error l (𝓝 0))
    (hidentity : ∀ᶠ x in l, incoming x = -(amplitude x : ℂ) *
      Complex.exp ((phase x : ℂ) * Complex.I) * (1 + error x)) :
    Tendsto (fun x => incoming x / (amplitude x : ℂ) +
      Complex.exp ((phase x : ℂ) * Complex.I)) l (𝓝 0) := by
  apply squeeze_zero_norm' _ (by simpa only [norm_zero] using he.norm)
  filter_upwards [ha, hidentity] with x hx hid
  have hane : (amplitude x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have heq : incoming x / (amplitude x : ℂ) +
      Complex.exp ((phase x : ℂ) * Complex.I) =
        -(Complex.exp ((phase x : ℂ) * Complex.I) * error x) := by
    rw [hid]
    field_simp
    ring
  rw [heq, norm_neg, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Assembly from the incoming channel limit and vanishing relative bounds
for the canonical active replacement and each inactive cell. -/
def canonicalChannelAsymptotics_of_relative_limits
    (p : CuspParameters) (L slope threshold : ℝ)
    (amplitude phase : ℝ → ℝ) (incoming : ℝ → ℂ)
    (activeError inactiveError : ℝ → ℝ)
    (ha : ∀ x, threshold ≤ x → 0 < amplitude x)
    (hphase : ContinuousOn phase (Ici threshold))
    (hphaseRatio : Tendsto (fun x => phase x / x) atTop (𝓝 slope))
    (hincoming : Tendsto (fun x => incoming x / (amplitude x : ℂ) +
      Complex.exp ((phase x : ℂ) * Complex.I)) atTop (𝓝 0))
    (hactive : Tendsto activeError atTop (𝓝 0))
    (hactiveBound : ∀ᶠ x in atTop,
      ‖canonicalSourceCell p L x 1 2 - incoming x‖ ≤ amplitude x * activeError x)
    (hinactive : Tendsto inactiveError atTop (𝓝 0))
    (hinactiveBound : ∀ i j : Fin 3, (i, j) ≠ (1, 2) → (i, j) ≠ (2, 1) →
      ∀ᶠ x in atTop, ‖canonicalSourceCell p L x i j‖ ≤ amplitude x * inactiveError x) :
    ChannelAsymptotics (canonicalSourceCell p L) slope where
  threshold := threshold
  amplitude := amplitude
  phase := phase
  amplitude_pos := ha
  phase_continuous := hphase
  phase_ratio := hphaseRatio
  active_tendsto := by
    have hpos : ∀ᶠ x in atTop, 0 < amplitude x :=
      (eventually_ge_atTop threshold).mono (fun x hx => ha x hx)
    have hdiff := tendsto_complex_div_of_eventual_norm_bound hpos hactive hactiveBound
    convert hdiff.add hincoming using 1
    · ext x
      simp only [sub_div]
      ring
    · simp only [add_zero]
  inactive_tendsto := by
    intro i j h₁ h₂
    exact tendsto_complex_div_of_eventual_norm_bound
      ((eventually_ge_atTop threshold).mono (fun x hx => ha x hx))
      hinactive (hinactiveBound i j h₁ h₂)

/-- The incoming hypothesis can be the exact relative-error identity rather
than a preassembled channel limit. Amplitude and phase remain definitionally
the functions supplied by the caller. -/
def canonicalChannelAsymptotics_of_relative_errors
    (p : CuspParameters) (L slope threshold : ℝ)
    (amplitude phase : ℝ → ℝ) (incoming incomingError : ℝ → ℂ)
    (activeError inactiveError : ℝ → ℝ)
    (ha : ∀ x, threshold ≤ x → 0 < amplitude x)
    (hphase : ContinuousOn phase (Ici threshold))
    (hphaseRatio : Tendsto (fun x => phase x / x) atTop (𝓝 slope))
    (hincoming : Tendsto incomingError atTop (𝓝 0))
    (hincomingIdentity : ∀ᶠ x in atTop, incoming x = -(amplitude x : ℂ) *
      Complex.exp ((phase x : ℂ) * Complex.I) * (1 + incomingError x))
    (hactive : Tendsto activeError atTop (𝓝 0))
    (hactiveBound : ∀ᶠ x in atTop,
      ‖canonicalSourceCell p L x 1 2 - incoming x‖ ≤ amplitude x * activeError x)
    (hinactive : Tendsto inactiveError atTop (𝓝 0))
    (hinactiveBound : ∀ i j : Fin 3, (i, j) ≠ (1, 2) → (i, j) ≠ (2, 1) →
      ∀ᶠ x in atTop, ‖canonicalSourceCell p L x i j‖ ≤ amplitude x * inactiveError x) :
    ChannelAsymptotics (canonicalSourceCell p L) slope :=
  canonicalChannelAsymptotics_of_relative_limits p L slope threshold
    amplitude phase incoming activeError inactiveError ha hphase hphaseRatio
    (tendsto_incoming_channel_of_relative_identity
      ((eventually_ge_atTop threshold).mono (fun x hx => ha x hx))
      hincoming hincomingIdentity)
    hactive hactiveBound hinactive hinactiveBound

/-- Only eventual positivity and eventual phase continuity are necessary.
The resulting positive threshold may be enlarged without changing either
of the prescribed functions. -/
theorem exists_canonicalChannelAsymptotics_of_eventual_relative_errors
    (p : CuspParameters) (L slope : ℝ)
    (amplitude phase : ℝ → ℝ) (incoming incomingError : ℝ → ℂ)
    (activeError inactiveError : ℝ → ℝ)
    (ha : ∀ᶠ x in atTop, 0 < amplitude x)
    (hphase : ∃ T : ℝ, ContinuousOn phase (Ici T))
    (hphaseRatio : Tendsto (fun x => phase x / x) atTop (𝓝 slope))
    (hincoming : Tendsto incomingError atTop (𝓝 0))
    (hincomingIdentity : ∀ᶠ x in atTop, incoming x = -(amplitude x : ℂ) *
      Complex.exp ((phase x : ℂ) * Complex.I) * (1 + incomingError x))
    (hactive : Tendsto activeError atTop (𝓝 0))
    (hactiveBound : ∀ᶠ x in atTop,
      ‖canonicalSourceCell p L x 1 2 - incoming x‖ ≤ amplitude x * activeError x)
    (hinactive : Tendsto inactiveError atTop (𝓝 0))
    (hinactiveBound : ∀ i j : Fin 3, (i, j) ≠ (1, 2) → (i, j) ≠ (2, 1) →
      ∀ᶠ x in atTop, ‖canonicalSourceCell p L x i j‖ ≤ amplitude x * inactiveError x) :
    ∃ H : ChannelAsymptotics (canonicalSourceCell p L) slope,
      0 < H.threshold ∧ H.amplitude = amplitude ∧ H.phase = phase := by
  obtain ⟨Ta, hTa⟩ := eventually_atTop.mp ha
  obtain ⟨Tp, hTp⟩ := hphase
  let T := max 1 (max Ta Tp)
  have hTpos : 0 < T := zero_lt_one.trans_le (le_max_left _ _)
  have hTaT : Ta ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hTpT : Tp ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  let H := canonicalChannelAsymptotics_of_relative_errors p L slope T
    amplitude phase incoming incomingError activeError inactiveError
    (fun x hx => hTa x (hTaT.trans hx))
    (hTp.mono (fun x hx => hTpT.trans hx)) hphaseRatio
    hincoming hincomingIdentity hactive hactiveBound hinactive hinactiveBound
  exact ⟨H, hTpos, rfl, rfl⟩

end InfiniteZero
