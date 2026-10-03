import InfiniteZero.Construction
import InfiniteZero.LandauKernel
import InfiniteZero.LinearPhase
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Concrete source channels and their exact nine-cell assembly

Labels `0,1,2 : Fin 3` mean core, upper cusp, lower cusp. The scalar kernel is
the explicit proper-time Landau integral. The sources contain the actual
potential components and an actual atomic wavefunction. No integral is an
unconstrained field. The operator identity required for their use as
the physical hopping coefficient is the free-resolvent source formula P5.1;
that identity is proved from the classical resolvent interface in the later
source-representation modules, and remains an explicit hypothesis here.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace InfiniteZero

def sourcePhase (b L : ℝ) (z w : Plane) : ℝ :=
  b * (L * (z 1 - w 1) + (z 0 * w 1 - z 1 * w 0) / 2)

theorem sourcePhase_swap (b L : ℝ) (z w : Plane) :
    sourcePhase b L w z = -sourcePhase b L z w := by
  unfold sourcePhase
  ring

def sourceKernel (b L h E : ℝ) (z w : Plane) : ℂ :=
  (landauKernel b h E ‖z + w - 2 • displacement L‖ : ℂ) *
    Complex.exp (((sourcePhase b L z w / h : ℝ) : ℂ) * Complex.I)

theorem sourceKernel_swap (b L h E : ℝ) (z w : Plane) :
    sourceKernel b L h E w z = star (sourceKernel b L h E z w) := by
  unfold sourceKernel
  rw [sourcePhase_swap, add_comm w z]
  simp only [neg_div,
    Complex.ofReal_neg, star_mul', Complex.star_def, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp

def componentPotential (p : CuspParameters) (i : Fin 3) : Potential :=
  ![p.core, fun x => p.ε * p.cuspPlus x, fun x => p.ε * p.cuspMinus x] i

theorem componentPotential_sum (p : CuspParameters) (x : Plane) :
    ∑ i : Fin 3, componentPotential p i x = p.potential x := by
  simp [componentPotential, Fin.sum_univ_succ, CuspParameters.potential]
  ring

def atomicSource (h : ℝ) (v : Potential) (φ : Wavefunction) : Wavefunction :=
  fun x => (((h ^ 2)⁻¹ * v x : ℝ) : ℂ) * φ x

def componentSource (p : CuspParameters) (h : ℝ) (φ : Wavefunction) (i : Fin 3) : Wavefunction :=
  atomicSource h (componentPotential p i) φ

theorem componentSource_sum (p : CuspParameters) (h : ℝ) (φ : Wavefunction) :
    (fun x => ∑ i : Fin 3, componentSource p h φ i x) = atomicSource h p.potential φ := by
  funext x
  simp only [componentSource, atomicSource, Complex.ofReal_mul, ← Finset.sum_mul,
    ← Finset.mul_sum, ← Complex.ofReal_sum, componentPotential_sum]

def channelIntegrand (K : Plane → Plane → ℂ) (F G : Wavefunction) (q : Plane × Plane) : ℂ :=
  star (F q.1) * K q.1 q.2 * G q.2

def sourcePairing (h : ℝ) (K : Plane → Plane → ℂ) (F G : Wavefunction) : ℂ :=
  -((h ^ 2 : ℝ) : ℂ) * ∫ q : Plane × Plane, channelIntegrand K F G q ∂volume.prod volume

theorem sourcePairing_swap (h : ℝ) (K : Plane → Plane → ℂ)
    (hK : ∀ z w, K w z = star (K z w)) (F G : Wavefunction) :
    sourcePairing h K G F = star (sourcePairing h K F G) := by
  have he : (fun q : Plane × Plane => channelIntegrand K G F q.swap) =
      (fun q => star (channelIntegrand K F G q)) := by
    funext q
    dsimp only [channelIntegrand, Prod.fst_swap, Prod.snd_swap]
    rw [hK q.1 q.2]
    simp only [star_mul', star_star]
    ring
  unfold sourcePairing
  rw [← integral_prod_swap (channelIntegrand K G F), he]
  simp only [Complex.star_def, integral_conj, map_mul, map_neg, Complex.conj_ofReal]

theorem sourcePairing_sum (h : ℝ) (K : Plane → Plane → ℂ) (F : Fin 3 → Wavefunction)
    (hInt : ∀ i j, Integrable (channelIntegrand K (F i) (F j)) (volume.prod volume)) :
    sourcePairing h K (fun x => ∑ i, F i x) (fun x => ∑ i, F i x) =
      ∑ i : Fin 3, ∑ j : Fin 3, sourcePairing h K (F i) (F j) := by
  have he : channelIntegrand K (fun x => ∑ i, F i x) (fun x => ∑ i, F i x) =
      (fun q => ∑ i : Fin 3, ∑ j : Fin 3, channelIntegrand K (F i) (F j) q) := by
    funext q
    simp only [channelIntegrand, Complex.star_def, map_sum, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  unfold sourcePairing
  rw [he, integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hInt i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hInt _ j)]
  simp only [Finset.mul_sum]

def sourceCell (p : CuspParameters) (L h E : ℝ) (φ : Wavefunction) (i j : Fin 3) : ℂ :=
  sourcePairing h (sourceKernel p.b L h E) (componentSource p h φ i) (componentSource p h φ j)

def totalSourcePairing (p : CuspParameters) (L h E : ℝ) (φ : Wavefunction) : ℂ :=
  sourcePairing h (sourceKernel p.b L h E)
    (atomicSource h p.potential φ) (atomicSource h p.potential φ)

def CellsIntegrable (p : CuspParameters) (L h E : ℝ) (φ : Wavefunction) : Prop :=
  ∀ i j, Integrable (channelIntegrand (sourceKernel p.b L h E)
    (componentSource p h φ i) (componentSource p h φ j)) (volume.prod volume)

theorem totalSourcePairing_eq_nine_cells (p : CuspParameters) (L h E : ℝ) (φ : Wavefunction)
    (hInt : CellsIntegrable p L h E φ) :
    totalSourcePairing p L h E φ = ∑ i : Fin 3, ∑ j : Fin 3, sourceCell p L h E φ i j := by
  unfold totalSourcePairing
  rw [← componentSource_sum p h φ]
  exact sourcePairing_sum h (sourceKernel p.b L h E) (componentSource p h φ) hInt

theorem sourceCell_swap (p : CuspParameters) (L h E : ℝ) (φ : Wavefunction) (i j : Fin 3) :
    sourceCell p L h E φ j i = star (sourceCell p L h E φ i j) :=
  sourcePairing_swap h _ (sourceKernel_swap p.b L h E) _ _

/-- The exact scaled positive-energy parameter `−h² e₀(λ)`; positivity is
a separate atomic spectral result, not built into the definition. -/
def scaledAtomicEnergy (p : CuspParameters) (coupling : ℝ) : ℝ :=
  -(coupling⁻¹) ^ 2 * atomicGroundEnergy p.b p.potential coupling

def canonicalSourceCell (p : CuspParameters) (L coupling : ℝ) (i j : Fin 3) : ℂ :=
  sourceCell p L coupling⁻¹ (scaledAtomicEnergy p coupling)
    (canonicalAtomicState p.b p.potential coupling) i j

def canonicalTotalSourcePairing (p : CuspParameters) (L coupling : ℝ) : ℂ :=
  totalSourcePairing p L coupling⁻¹ (scaledAtomicEnergy p coupling)
    (canonicalAtomicState p.b p.potential coupling)

theorem canonicalSourceCell_swap (p : CuspParameters) (L coupling : ℝ) (i j : Fin 3) :
    canonicalSourceCell p L coupling j i = star (canonicalSourceCell p L coupling i j) :=
  sourceCell_swap p L coupling⁻¹ _ _ i j

/-- The seven inactive ordered cells, with the two cross cells omitted. -/
def inactiveCells (I : Fin 3 → Fin 3 → ℂ) : ℂ :=
  I 0 0 + I 0 1 + I 0 2 + I 1 0 + I 1 1 + I 2 0 + I 2 2

theorem nine_cells_split (I : Fin 3 → Fin 3 → ℂ) :
    (∑ i : Fin 3, ∑ j : Fin 3, I i j) = I 1 2 + I 2 1 + inactiveCells I := by
  simp [Fin.sum_univ_succ, inactiveCells]
  ring

/-- The full source pairing is real by exchange symmetry, without a
pointwise-real assumption on the atomic state. -/
theorem totalSourcePairing_im (p : CuspParameters) (L h E : ℝ) (φ : Wavefunction) :
    (totalSourcePairing p L h E φ).im = 0 := by
  have he := sourcePairing_swap h (sourceKernel p.b L h E) (sourceKernel_swap p.b L h E)
    (atomicSource h p.potential φ) (atomicSource h p.potential φ)
  have hi := congrArg Complex.im he
  simp only [Complex.star_def, Complex.conj_im] at hi
  change (sourcePairing h (sourceKernel p.b L h E)
    (atomicSource h p.potential φ) (atomicSource h p.potential φ)).im = 0
  linarith

/-- Precise analytic input at the channel level. The active estimate is the
complex statement `I₊₋/a + exp(iΘ) → 0`. Each of the seven inactive cells is
negligible relative to `a`; no cosine approximation is assumed. -/
structure ChannelAsymptotics (I : ℝ → Fin 3 → Fin 3 → ℂ) (slope : ℝ) where
  threshold : ℝ
  amplitude : ℝ → ℝ
  phase : ℝ → ℝ
  amplitude_pos : ∀ x, threshold ≤ x → 0 < amplitude x
  phase_continuous : ContinuousOn phase (Ici threshold)
  phase_ratio : Tendsto (fun x => phase x / x) atTop (𝓝 slope)
  active_tendsto : Tendsto (fun x => I x 1 2 / (amplitude x : ℂ) +
    Complex.exp ((phase x : ℂ) * Complex.I)) atTop (𝓝 0)
  inactive_tendsto : ∀ i j, (i, j) ≠ ((1 : Fin 3), (2 : Fin 3)) →
    (i, j) ≠ ((2 : Fin 3), (1 : Fin 3)) →
    Tendsto (fun x => I x i j / (amplitude x : ℂ)) atTop (𝓝 0)

theorem ChannelAsymptotics.inactive_sum_tendsto {I : ℝ → Fin 3 → Fin 3 → ℂ} {slope : ℝ}
    (h : ChannelAsymptotics I slope) :
    Tendsto (fun x => inactiveCells (I x) / (h.amplitude x : ℂ)) atTop (𝓝 0) := by
  have hh := ((((((h.inactive_tendsto 0 0 (by decide) (by decide)).add
    (h.inactive_tendsto 0 1 (by decide) (by decide))).add
    (h.inactive_tendsto 0 2 (by decide) (by decide))).add
    (h.inactive_tendsto 1 0 (by decide) (by decide))).add
    (h.inactive_tendsto 1 1 (by decide) (by decide))).add
    (h.inactive_tendsto 2 0 (by decide) (by decide))).add
    (h.inactive_tendsto 2 2 (by decide) (by decide))
  simpa only [inactiveCells, add_div, zero_add] using hh

def ChannelAsymptotics.cosineError {I : ℝ → Fin 3 → Fin 3 → ℂ} {slope : ℝ}
    (h : ChannelAsymptotics I slope) (x : ℝ) : ℝ :=
  -(I x 1 2 / (h.amplitude x : ℂ) + Complex.exp ((h.phase x : ℂ) * Complex.I)).re -
    (inactiveCells (I x) / (h.amplitude x : ℂ)).re / 2

theorem ChannelAsymptotics.cosineError_tendsto {I : ℝ → Fin 3 → Fin 3 → ℂ} {slope : ℝ}
    (h : ChannelAsymptotics I slope) : Tendsto h.cosineError atTop (𝓝 0) := by
  have ha := Complex.continuous_re.continuousAt.tendsto.comp h.active_tendsto
  have hi := Complex.continuous_re.continuousAt.tendsto.comp h.inactive_sum_tendsto
  simpa only [cosineError, Complex.zero_re, neg_zero, zero_div, sub_zero] using ha.neg.sub (hi.div_const 2)

/-- The cosine comes from exact conjugation of the two active channels, even
at zeros of the leading cosine. The denominator is always the positive envelope. -/
def ChannelAsymptotics.toLinearCosine {I : ℝ → Fin 3 → Fin 3 → ℂ} {slope : ℝ}
    (h : ChannelAsymptotics I slope)
    (hconj : ∀ x, I x 2 1 = star (I x 1 2)) :
    LinearCosineAsymptotic (fun x => -(∑ i : Fin 3, ∑ j : Fin 3, I x i j).re) slope where
  threshold := h.threshold
  amplitude := fun x => 2 * h.amplitude x
  phase := h.phase
  error := h.cosineError
  amplitude_pos := fun x hx => mul_pos (by norm_num) (h.amplitude_pos x hx)
  phase_continuous := h.phase_continuous
  phase_ratio := h.phase_ratio
  error_tendsto := h.cosineError_tendsto
  formula := by
    intro x hx
    rw [nine_cells_split, hconj x]
    have ha : h.amplitude x ≠ 0 := (h.amplitude_pos x hx).ne'
    simp only [cosineError, Complex.add_re, Complex.star_def, Complex.conj_re,
      Complex.div_ofReal_re, Complex.exp_ofReal_mul_I_re]
    field_simp
    ring

/-- Fully checked conversion from the concrete source-channel estimates to
the cosine input consumed by the spectral assembly. `hSource` is exactly the
resolvent/source representation P5.1 for the original hopping, supplied by
the later proved resolvent bridge. -/
def canonicalHopping_linearCosine_of_channels (p : CuspParameters) (L slope : ℝ)
    (h : ChannelAsymptotics (canonicalSourceCell p L) slope)
    (hInt : ∀ x, h.threshold ≤ x → CellsIntegrable p L x⁻¹ (scaledAtomicEnergy p x)
      (canonicalAtomicState p.b p.potential x))
    (hSource : ∀ x, h.threshold ≤ x →
      canonicalHopping p.b p.potential L x = canonicalTotalSourcePairing p L x) :
    LinearCosineAsymptotic (fun x => -(canonicalHopping p.b p.potential L x).re) slope := by
  let hc := h.toLinearCosine (fun x => canonicalSourceCell_swap p L x 1 2)
  refine { hc with formula := ?_ }
  intro x hx
  rw [hSource x hx]
  change -(totalSourcePairing p L x⁻¹ (scaledAtomicEnergy p x)
    (canonicalAtomicState p.b p.potential x)).re = _
  rw [totalSourcePairing_eq_nine_cells p L x⁻¹ _ _ (hInt x hx)]
  exact hc.formula x hx

theorem canonicalHopping_real_of_source_identity (p : CuspParameters) (L x : ℝ)
    (hSource : canonicalHopping p.b p.potential L x = canonicalTotalSourcePairing p L x) :
    (canonicalHopping p.b p.potential L x).im = 0 := by
  rw [hSource]
  exact totalSourcePairing_im p L x⁻¹ _ _

end InfiniteZero
