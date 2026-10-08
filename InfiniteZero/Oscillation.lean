import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The real-variable end of the argument

This file contains no spectral or semiclassical assumptions.  In particular,
the zeros constructed here are zeros of the function supplied as an argument;
zeros of the hopping coefficient are never identified with spectral crossings.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace InfiniteZero

/-- Both strict signs occur arbitrarily far to the right. -/
def HasUnboundedSigns (f : ℝ → ℝ) : Prop :=
  ∀ R : ℝ, (∃ x, R < x ∧ 0 < f x) ∧ (∃ x, R < x ∧ f x < 0)

/-- The zero set is unbounded above. -/
def HasUnboundedZeros (f : ℝ → ℝ) : Prop :=
  ∀ R : ℝ, ∃ x, R < x ∧ f x = 0

theorem HasUnboundedSigns.neg {f : ℝ → ℝ} (h : HasUnboundedSigns f) :
    HasUnboundedSigns (fun x => -f x) := by
  intro R
  obtain ⟨⟨p, hpR, hp⟩, ⟨n, hnR, hn⟩⟩ := h R
  constructor
  · exact ⟨n, hnR, neg_pos.mpr hn⟩
  · exact ⟨p, hpR, neg_neg_of_pos hp⟩

/-- The two signs can be sampled along interlaced sequences escaping to infinity. -/
theorem HasUnboundedSigns.exists_interlaced_sequences {f : ℝ → ℝ}
    (h : HasUnboundedSigns f) :
    ∃ p q : ℕ → ℝ,
      Tendsto p atTop atTop ∧ Tendsto q atTop atTop ∧
      (∀ n, p n < q n ∧ q n < p (n + 1) ∧ 0 < f (p n) ∧ f (q n) < 0) := by
  classical
  choose a ha hfa using fun R => (h R).1
  choose b hb hfb using fun R => (h R).2
  let p : ℕ → ℝ := Nat.rec (a 0) (fun n x => a (max (b x) (n + 1)))
  let q : ℕ → ℝ := fun n => b (p n)
  have hs (n : ℕ) : max (q n) ((n : ℝ) + 1) < p (n + 1) := ha _
  have hn (n : ℕ) : (n : ℝ) ≤ p n := by
    cases n with
    | zero => simpa [p] using (ha 0).le
    | succ n =>
        simpa only [Nat.cast_add, Nat.cast_one] using
          le_trans (le_max_right (q n) ((n : ℝ) + 1)) (hs n).le
  have hp : Tendsto p atTop atTop := by
    apply tendsto_atTop.2
    intro c
    obtain ⟨N, hN⟩ := exists_nat_gt c
    filter_upwards [eventually_ge_atTop N] with n hnN
    exact le_trans hN.le (le_trans (Nat.cast_le.mpr hnN) (hn n))
  refine ⟨p, q, hp, ?_, ?_⟩
  · apply tendsto_atTop.2
    intro c
    filter_upwards [(tendsto_atTop.1 hp) c] with n hn
    exact le_trans hn (hb (p n)).le
  · intro n
    refine ⟨hb (p n), lt_of_le_of_lt (le_max_left _ _) (hs n), ?_, hfb (p n)⟩
    cases n with
    | zero => exact hfa 0
    | succ n => exact hfa _

/-- Interlaced sign samples may all be chosen in any prescribed final half-line. -/
theorem HasUnboundedSigns.exists_interlaced_sequences_above {f : ℝ → ℝ}
    (h : HasUnboundedSigns f) (T : ℝ) :
    ∃ p q : ℕ → ℝ,
      Tendsto p atTop atTop ∧ Tendsto q atTop atTop ∧
      ∀ n, T < p n ∧ p n < q n ∧ q n < p (n + 1) ∧
        0 < f (p n) ∧ f (q n) < 0 := by
  obtain ⟨p, q, hp, hq, hs⟩ := h.exists_interlaced_sequences
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hp.eventually (eventually_gt_atTop T))
  have hshift : Tendsto (fun n : ℕ => N + n) atTop atTop := by
    apply tendsto_atTop.2
    intro M
    filter_upwards [eventually_ge_atTop M] with n hn
    exact le_trans hn (Nat.le_add_left n N)
  refine ⟨fun n => p (N + n), fun n => q (N + n), hp.comp hshift, hq.comp hshift, ?_⟩
  intro n
  refine ⟨hN (N + n) (Nat.le_add_right N n), (hs (N + n)).1, ?_,
    (hs (N + n)).2.2.1, (hs (N + n)).2.2.2⟩
  simpa only [Nat.add_assoc] using (hs (N + n)).2.1

/-- The intermediate value theorem is used only beyond the continuity threshold. -/
theorem HasUnboundedSigns.unboundedZeros {f : ℝ → ℝ} {T : ℝ}
    (h : HasUnboundedSigns f) (hc : ContinuousOn f (Ici T)) :
    HasUnboundedZeros f := by
  intro R
  obtain ⟨p, hp, hfp⟩ := (h (max R T)).1
  obtain ⟨q, hpq, hfq⟩ := (h p).2
  have hpT : T ≤ p := le_trans (le_max_right R T) hp.le
  have hc' : ContinuousOn f (Icc p q) :=
    hc.mono (fun x hx => le_trans hpT hx.1)
  obtain ⟨z, hz, hfz⟩ :=
    intermediate_value_Icc' hpq.le hc' ⟨hfq.le, hfp.le⟩
  exact ⟨z, lt_of_lt_of_le (lt_of_le_of_lt (le_max_left R T) hp) hz.1, hfz⟩

/-- Unboundedness gives an actual sequence of distinct zeros tending to infinity. -/
theorem HasUnboundedZeros.exists_strictMono_sequence {f : ℝ → ℝ}
    (h : HasUnboundedZeros f) :
    ∃ z : ℕ → ℝ, StrictMono z ∧ Tendsto z atTop atTop ∧ ∀ n, f (z n) = 0 := by
  classical
  choose g hgR hgf using h
  let z : ℕ → ℝ := Nat.rec (g 0) (fun n x => g (max x (n + 1)))
  have hzs (n : ℕ) : max (z n) ((n : ℝ) + 1) < z (n + 1) := by
    exact hgR _
  have hzn (n : ℕ) : (n : ℝ) ≤ z n := by
    cases n with
    | zero => simpa [z] using (hgR 0).le
    | succ n =>
        simpa only [Nat.cast_add, Nat.cast_one] using
          le_trans (le_max_right (z n) ((n : ℝ) + 1)) (hzs n).le
  refine ⟨z, strictMono_nat_of_lt_succ (fun n => ?_), ?_, ?_⟩
  · exact lt_of_le_of_lt (le_max_left _ _) (hzs n)
  · apply tendsto_atTop.2
    intro b
    obtain ⟨N, hN⟩ := exists_nat_gt b
    filter_upwards [eventually_ge_atTop N] with n hn
    exact le_trans hN.le (le_trans (Nat.cast_le.mpr hn) (hzn n))
  · intro n
    cases n with
    | zero => exact hgf 0
    | succ n => exact hgf _

/-- A zero sequence can be confined to the region where all analytic and
spectral hypotheses apply; in particular every coupling can be positive. -/
theorem HasUnboundedZeros.exists_strictMono_sequence_above {f : ℝ → ℝ}
    (h : HasUnboundedZeros f) (T : ℝ) :
    ∃ z : ℕ → ℝ, StrictMono z ∧ Tendsto z atTop atTop ∧
      ∀ n, T < z n ∧ f (z n) = 0 := by
  obtain ⟨z, hm, ht, hz⟩ := h.exists_strictMono_sequence
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually (eventually_gt_atTop T))
  have hshift : Tendsto (fun n : ℕ => N + n) atTop atTop := by
    apply tendsto_atTop.2
    intro M
    filter_upwards [eventually_ge_atTop M] with n hn
    exact le_trans hn (Nat.le_add_left n N)
  refine ⟨fun n => z (N + n), ?_, ht.comp hshift, ?_⟩
  · exact fun _ _ hab => hm (Nat.add_lt_add_left hab N)
  · intro n
    exact ⟨hN (N + n) (Nat.le_add_right N n), hz (N + n)⟩

theorem HasUnboundedZeros.infinite {f : ℝ → ℝ} (h : HasUnboundedZeros f) :
    Set.Infinite {x | f x = 0} := by
  by_contra hf
  obtain ⟨b, hb⟩ := (Set.not_infinite.mp hf).bddAbove
  obtain ⟨x, hx, hfx⟩ := h b
  exact (not_lt_of_ge (hb hfx)) hx

/-- The only real-variable data needed from the oscillatory asymptotic.

No regularity of the error or amplitude is requested.  In applications the
bound `O(1 / log x)` implies the recorded convergence of the error.  Eventual
strict monotonicity of the phase is stronger than the assumptions here.
-/
structure CosineAsymptotic (f : ℝ → ℝ) where
  threshold : ℝ
  amplitude : ℝ → ℝ
  phase : ℝ → ℝ
  error : ℝ → ℝ
  amplitude_pos : ∀ x, threshold ≤ x → 0 < amplitude x
  phase_continuous : ContinuousOn phase (Ici threshold)
  phase_tendsto : Tendsto phase atTop atTop
  error_tendsto : Tendsto error atTop (𝓝 0)
  formula : ∀ x, threshold ≤ x →
    f x = amplitude x * (Real.cos (phase x) + error x)

namespace CosineAsymptotic

/-- Multiplying by a positive constant does not change the phase or the error. -/
def pos_mul {f : ℝ → ℝ} (h : CosineAsymptotic f) {c : ℝ} (hc : 0 < c) :
    CosineAsymptotic (fun x => c * f x) where
  threshold := h.threshold
  amplitude := fun x => c * h.amplitude x
  phase := h.phase
  error := h.error
  amplitude_pos x hx := mul_pos hc (h.amplitude_pos x hx)
  phase_continuous := h.phase_continuous
  phase_tendsto := h.phase_tendsto
  error_tendsto := h.error_tendsto
  formula x hx := by rw [h.formula x hx]; ring

/-- Stability under an error small relative to the strictly positive envelope.
There is deliberately no division by the oscillating function `f`. -/
def add_relative_error {f g : ℝ → ℝ} (h : CosineAsymptotic f)
    (he : Tendsto (fun x => (g x - f x) / h.amplitude x) atTop (𝓝 0)) :
    CosineAsymptotic g where
  threshold := h.threshold
  amplitude := h.amplitude
  phase := h.phase
  error := fun x => h.error x + (g x - f x) / h.amplitude x
  amplitude_pos := h.amplitude_pos
  phase_continuous := h.phase_continuous
  phase_tendsto := h.phase_tendsto
  error_tendsto := by simpa only [add_zero] using h.error_tendsto.add he
  formula x hx := by
    have hne : h.amplitude x ≠ 0 := ne_of_gt (h.amplitude_pos x hx)
    have hdiv : h.amplitude x * ((g x - f x) / h.amplitude x) = g x - f x := by
      field_simp [hne]
    calc
      g x = f x + (g x - f x) := by ring
      _ = h.amplitude x * (Real.cos (h.phase x) + h.error x) +
          h.amplitude x * ((g x - f x) / h.amplitude x) := by
            rw [hdiv, h.formula x hx]
      _ = h.amplitude x *
          (Real.cos (h.phase x) + (h.error x + (g x - f x) / h.amplitude x)) := by ring

/-- Every phase level above the value at a chosen base point is attained later.
Strict monotonicity, and hence uniqueness of the phase point, is unnecessary. -/
theorem exists_phase {f : ℝ → ℝ} (h : CosineAsymptotic f)
    {B t : ℝ} (hB : h.threshold ≤ B) (ht : h.phase B ≤ t) :
    ∃ x, B ≤ x ∧ h.phase x = t := by
  have he : ∀ᶠ x in atTop, t ≤ h.phase x :=
    h.phase_tendsto.eventually (eventually_ge_atTop t)
  obtain ⟨y, hyB, hyt⟩ := ((eventually_ge_atTop B).and he).exists
  have hc : ContinuousOn h.phase (Icc B y) :=
    h.phase_continuous.mono (fun x hx => le_trans hB hx.1)
  obtain ⟨x, hx, hxt⟩ := intermediate_value_Icc hyB hc ⟨ht, hyt⟩
  exact ⟨x, hx.1, hxt⟩

/-- Small absolute errors preserve the signs at cosine extrema. -/
theorem unboundedSigns {f : ℝ → ℝ} (h : CosineAsymptotic f) :
    HasUnboundedSigns f := by
  have he : ∀ᶠ x in atTop, |h.error x| < 1 := by
    simpa only [Real.dist_eq, sub_zero] using
      (Metric.tendsto_nhds.mp h.error_tendsto 1 zero_lt_one)
  obtain ⟨E, hE⟩ := eventually_atTop.1 he
  intro R
  let B := max h.threshold (max E (R + 1))
  have hBT : h.threshold ≤ B := le_max_left _ _
  have hBE : E ≤ B := le_trans (le_max_left _ _) (le_max_right _ _)
  have hBR : R < B := by
    have : R + 1 ≤ B := le_trans (le_max_right _ _) (le_max_right _ _)
    linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (h.phase B / (2 * Real.pi))
  let t : ℝ := (n : ℝ) * (2 * Real.pi)
  have ht : h.phase B < t :=
    (div_lt_iff₀ (mul_pos (by norm_num) Real.pi_pos)).mp hn
  have hcos : Real.cos t = 1 := by
    simpa only [t, mul_assoc] using Real.cos_nat_mul_two_pi n
  obtain ⟨p, hp, hphasep⟩ := h.exists_phase hBT ht.le
  obtain ⟨q, hq, hphaseq⟩ := h.exists_phase hBT
    (show h.phase B ≤ t + Real.pi by linarith [Real.pi_pos])
  have hep := abs_lt.mp (hE p (le_trans hBE hp))
  have heq := abs_lt.mp (hE q (le_trans hBE hq))
  constructor
  · refine ⟨p, lt_of_lt_of_le hBR hp, ?_⟩
    rw [h.formula p (le_trans hBT hp), hphasep, hcos]
    exact mul_pos (h.amplitude_pos p (le_trans hBT hp)) (by linarith)
  · refine ⟨q, lt_of_lt_of_le hBR hq, ?_⟩
    rw [h.formula q (le_trans hBT hq), hphaseq, Real.cos_add_pi, hcos]
    exact mul_neg_of_pos_of_neg (h.amplitude_pos q (le_trans hBT hq)) (by linarith)

theorem unboundedZeros {f : ℝ → ℝ} (h : CosineAsymptotic f)
    {T : ℝ} (hc : ContinuousOn f (Ici T)) : HasUnboundedZeros f :=
  h.unboundedSigns.unboundedZeros hc

end CosineAsymptotic

end InfiniteZero
