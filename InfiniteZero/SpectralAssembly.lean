import InfiniteZero.Oscillation

/-!
# From the hopping asymptotic to exact scalar crossings

The analytic inputs in this file are hypotheses, not admissions.  The two scalar
sector energies are connected to the physical Hamiltonian in the separate
spectral model.  The transfer error is normalized by a positive envelope, never
by the hopping coefficient.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace InfiniteZero

/-- Difference between the ordered pair of sector energies. -/
def lowGap (Ee Eo : ℝ → ℝ) (x : ℝ) : ℝ :=
  max (Ee x) (Eo x) - min (Ee x) (Eo x)

theorem lowGap_eq_abs (Ee Eo : ℝ → ℝ) (x : ℝ) :
    lowGap Ee Eo x = |Eo x - Ee x| :=
  max_sub_min_eq_abs (Ee x) (Eo x)

theorem lowGap_eq_zero_iff (Ee Eo : ℝ → ℝ) (x : ℝ) :
    lowGap Ee Eo x = 0 ↔ Ee x = Eo x := by
  rw [lowGap_eq_abs, abs_eq_zero, sub_eq_zero]
  exact eq_comm

/-- The real-variable interface supplied by hopping asymptotics, the Schur
transfer estimate, and continuity of the two scalar quantities. -/
structure SpectralAsymptotics (Ee Eo rho : ℝ → ℝ) where
  hopping : CosineAsymptotic (fun x => -rho x)
  transfer : Tendsto
    (fun x => (Eo x - Ee x + 2 * rho x) / (2 * hopping.amplitude x)) atTop (𝓝 0)
  threshold : ℝ
  splitting_continuous : ContinuousOn (fun x => Eo x - Ee x) (Ici threshold)
  hopping_continuous : ContinuousOn rho (Ici threshold)

/-- The conclusion has separate sequences for exact gaps and for hopping zeros.
The last field records actual interlacing, and hence repeated changes of which
sector energy is lower. -/
structure SpectralOscillationResult (Ee Eo rho : ℝ → ℝ) : Prop where
  gap_zeros : ∃ z : ℕ → ℝ,
    StrictMono z ∧ Tendsto z atTop atTop ∧ ∀ n, lowGap Ee Eo (z n) = 0
  hopping_zeros : ∃ z : ℕ → ℝ,
    StrictMono z ∧ Tendsto z atTop atTop ∧ ∀ n, rho (z n) = 0
  interlaced_signs : ∃ p q : ℕ → ℝ,
    Tendsto p atTop atTop ∧ Tendsto q atTop atTop ∧
      ∀ n, p n < q n ∧ q n < p (n + 1) ∧
        0 < Eo (p n) - Ee (p n) ∧ Eo (q n) - Ee (q n) < 0

/-- The same conclusions, with every sample beyond a specified threshold. -/
structure SpectralOscillationResultAbove (Ee Eo rho : ℝ → ℝ) (T : ℝ) : Prop where
  gap_zeros : ∃ z : ℕ → ℝ,
    StrictMono z ∧ Tendsto z atTop atTop ∧
      ∀ n, T < z n ∧ lowGap Ee Eo (z n) = 0
  hopping_zeros : ∃ z : ℕ → ℝ,
    StrictMono z ∧ Tendsto z atTop atTop ∧
      ∀ n, T < z n ∧ rho (z n) = 0
  interlaced_signs : ∃ p q : ℕ → ℝ,
    Tendsto p atTop atTop ∧ Tendsto q atTop atTop ∧
      ∀ n, T < p n ∧ p n < q n ∧ q n < p (n + 1) ∧
        0 < Eo (p n) - Ee (p n) ∧ Eo (q n) - Ee (q n) < 0

namespace SpectralAsymptotics

/-- The spectral transfer estimate preserves the cosine phase. -/
def splitting {Ee Eo rho : ℝ → ℝ} (h : SpectralAsymptotics Ee Eo rho) :
    CosineAsymptotic (fun x => Eo x - Ee x) := by
  apply (h.hopping.pos_mul (show (0 : ℝ) < 2 by norm_num)).add_relative_error
  simpa only [CosineAsymptotic.pos_mul, mul_neg, sub_neg_eq_add] using h.transfer

theorem unbounded_gap_zeros {Ee Eo rho : ℝ → ℝ}
    (h : SpectralAsymptotics Ee Eo rho) : HasUnboundedZeros (lowGap Ee Eo) := by
  intro R
  obtain ⟨x, hx, hzero⟩ := h.splitting.unboundedZeros h.splitting_continuous R
  change Eo x - Ee x = 0 at hzero
  refine ⟨x, hx, ?_⟩
  rw [lowGap_eq_abs, hzero, abs_zero]

theorem unbounded_hopping_zeros {Ee Eo rho : ℝ → ℝ}
    (h : SpectralAsymptotics Ee Eo rho) : HasUnboundedZeros rho := by
  have hs : HasUnboundedSigns rho := by
    simpa only [neg_neg] using h.hopping.unboundedSigns.neg
  exact hs.unboundedZeros h.hopping_continuous

theorem result {Ee Eo rho : ℝ → ℝ} (h : SpectralAsymptotics Ee Eo rho) :
    SpectralOscillationResult Ee Eo rho where
  gap_zeros := h.unbounded_gap_zeros.exists_strictMono_sequence
  hopping_zeros := h.unbounded_hopping_zeros.exists_strictMono_sequence
  interlaced_signs := h.splitting.unboundedSigns.exists_interlaced_sequences

theorem result_above {Ee Eo rho : ℝ → ℝ} (h : SpectralAsymptotics Ee Eo rho) (T : ℝ) :
    SpectralOscillationResultAbove Ee Eo rho T where
  gap_zeros := h.unbounded_gap_zeros.exists_strictMono_sequence_above T
  hopping_zeros := h.unbounded_hopping_zeros.exists_strictMono_sequence_above T
  interlaced_signs := h.splitting.unboundedSigns.exists_interlaced_sequences_above T

end SpectralAsymptotics

end InfiniteZero
