import InfiniteZero.AtomicSourceRegime

/-!
# The physical hopping asymptotic from canonical source channels

The atomic source facts provide the actual resolvent representation and
integrability at a common large-coupling threshold. Enlarging the channel
threshold therefore gives the hopping cosine asymptotic with exactly twice
the channel amplitude and the same phase. This file proves neither hopping
continuity nor the existence of its zeros.
-/

noncomputable section

open Set

namespace InfiniteZero

/-- Enlarge the validity threshold without changing amplitude, phase or
either asymptotic channel limit. -/
def ChannelAsymptotics.rebase {I : ℝ → Fin 3 → Fin 3 → ℂ} {slope : ℝ}
    (h : ChannelAsymptotics I slope) (T : ℝ) : ChannelAsymptotics I slope where
  threshold := max h.threshold T
  amplitude := h.amplitude
  phase := h.phase
  amplitude_pos := fun x hx => h.amplitude_pos x ((le_max_left _ _).trans hx)
  phase_continuous := h.phase_continuous.mono
    (show Ici (max h.threshold T) ⊆ Ici h.threshold from
      fun _ hx => (le_max_left h.threshold T).trans hx)
  phase_ratio := h.phase_ratio
  active_tendsto := h.active_tendsto
  inactive_tendsto := h.inactive_tendsto

@[simp]
theorem ChannelAsymptotics.rebase_threshold {I : ℝ → Fin 3 → Fin 3 → ℂ} {slope : ℝ}
    (h : ChannelAsymptotics I slope) (T : ℝ) :
    (h.rebase T).threshold = max h.threshold T := rfl

@[simp]
theorem ChannelAsymptotics.rebase_amplitude {I : ℝ → Fin 3 → Fin 3 → ℂ} {slope : ℝ}
    (h : ChannelAsymptotics I slope) (T : ℝ) :
    (h.rebase T).amplitude = h.amplitude := rfl

@[simp]
theorem ChannelAsymptotics.rebase_phase {I : ℝ → Fin 3 → Fin 3 → ℂ} {slope : ℝ}
    (h : ChannelAsymptotics I slope) (T : ℝ) :
    (h.rebase T).phase = h.phase := rfl

/-- Canonical channel estimates imply the physical hopping cosine formula
and eventual reality. The source identity is derived from the universal
kernel interface and the established atomic ground-state facts. -/
theorem exists_canonicalHopping_linearCosine_of_channels_of_radialData
    {p : CuspParameters} (hp : p.BasicConditions)
    (hRad : RadialCoreSpectralData p.b p)
    (hAcore : ∀ coupling, IsMagneticRealization p.b coupling p.core)
    (hApot : ∀ coupling, IsMagneticRealization p.b coupling p.potential)
    (hKernel : HasPositiveLandauResolvent p.b)
    {L slope : ℝ} (hL : p.R < 2 * L)
    (h : ChannelAsymptotics (canonicalSourceCell p L) slope) :
    ∃ H : LinearCosineAsymptotic
        (fun coupling => -(canonicalHopping p.b p.potential L coupling).re) slope,
      H.amplitude = (fun coupling => 2 * h.amplitude coupling) ∧
      H.phase = h.phase ∧ 0 < H.threshold ∧ h.threshold ≤ H.threshold ∧
      ∀ coupling : ℝ, H.threshold ≤ coupling →
        (canonicalHopping p.b p.potential L coupling).im = 0 := by
  obtain ⟨T, hT, hfacts⟩ :=
    CuspParameters.exists_atomicSourceFacts_of_radialData hp hRad hAcore hApot hKernel
  let hc := h.rebase T
  have hsourceThreshold {coupling : ℝ} (hx : hc.threshold ≤ coupling) : T ≤ coupling :=
    (le_max_right _ _).trans hx
  let H := canonicalHopping_linearCosine_of_resolvent p L slope hc
    (fun coupling hx => (hfacts coupling (hsourceThreshold hx)).cells_integrable L hL)
    (fun coupling hx => (hfacts coupling (hsourceThreshold hx)).representation L)
  refine ⟨H, rfl, rfl, hT.trans_le (le_max_right _ _), le_max_left _ _, ?_⟩
  intro coupling hx
  exact (hfacts coupling (hsourceThreshold hx)).hopping_real hL

end InfiniteZero
