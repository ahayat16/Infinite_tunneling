import InfiniteZero.AtomicLocalizationRankOne
import InfiniteZero.MagneticGraphLowerBound

/-!
# Coercivity for the constructed potential on its actual operator domain

Only the displayed data about the radial reference core are inputs. The
localization, exterior mass estimate and passage to the closed graph for the
nonradial constructed potential have all been proved in Lean.
-/

noncomputable section
open MeasureTheory

namespace InfiniteZero.CuspParameters

/-- The rank-one bound for the full potential, on the domain of its actual
operator. The threshold is independent of the coupling and the reference state. -/
theorem exists_atomic_operator_rankOne_threshold {p : CuspParameters}
    (hp : p.BasicConditions) {γ : ℝ} (hγ : 0 < γ) (B : ℝ) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      IsMagneticRealization p.b coupling p.potential → ∀ (e : ℝ) (φ : Wavefunction),
      ∀ hφ : MemLp φ 2 volume, mass φ = 1 →
      Integrable (magneticEnergyDensity p.b coupling p.core φ) →
      magneticForm p.b coupling p.core φ = coupling ^ 2 * e →
      e ≤ -1 + B / coupling →
      (∀ u : Wavefunction, IsTestFunction u →
        (γ * coupling) * (mass u - ‖waveInner φ u‖ ^ 2) ≤
          magneticForm p.b coupling p.core u - coupling ^ 2 * e * mass u) →
      ∀ u : (magneticOperator p.b coupling p.potential).domain,
        (γ / 2 * coupling) * ‖(u : L2Space)‖ ^ 2 -
          2 * (γ * coupling) * ‖inner ℂ (hφ.toLp φ) (u : L2Space)‖ ^ 2 ≤
        (inner ℂ (u : L2Space) (magneticOperator p.b coupling p.potential u)).re -
          coupling ^ 2 * e * ‖(u : L2Space)‖ ^ 2 := by
  obtain ⟨T, hT, hbound⟩ := exists_atomic_test_rankOne_threshold hp hγ B
  refine ⟨T, hT, ?_⟩
  intro coupling hc hA e φ hφ hm hi he hupper hgap u
  exact hA.rankOne_lower (potential_contDiff hp).continuous hφ
    (hbound coupling hc e φ hφ hm hi he hupper hgap) u

/-- Quantitative complement coercivity for the actual nonradial operator.
This does not yet assert existence of its ground state: orthogonality is
to the radial reference state, whose data are explicit arguments. -/
theorem exists_atomic_operator_complement_threshold {p : CuspParameters}
    (hp : p.BasicConditions) {γ : ℝ} (hγ : 0 < γ) (B : ℝ) :
    ∃ T > 0, ∀ coupling : ℝ, T ≤ coupling →
      IsMagneticRealization p.b coupling p.potential → ∀ (e : ℝ) (φ : Wavefunction),
      ∀ hφ : MemLp φ 2 volume, mass φ = 1 →
      Integrable (magneticEnergyDensity p.b coupling p.core φ) →
      magneticForm p.b coupling p.core φ = coupling ^ 2 * e →
      e ≤ -1 + B / coupling →
      (∀ u : Wavefunction, IsTestFunction u →
        (γ * coupling) * (mass u - ‖waveInner φ u‖ ^ 2) ≤
          magneticForm p.b coupling p.core u - coupling ^ 2 * e * mass u) →
      ∀ u : (magneticOperator p.b coupling p.potential).domain,
        inner ℂ (hφ.toLp φ) (u : L2Space) = 0 →
        (coupling ^ 2 * e + γ / 2 * coupling) * ‖(u : L2Space)‖ ^ 2 ≤
          (inner ℂ (u : L2Space) (magneticOperator p.b coupling p.potential u)).re := by
  obtain ⟨T, hT, hbound⟩ := exists_atomic_test_rankOne_threshold hp hγ B
  refine ⟨T, hT, ?_⟩
  intro coupling hc hA e φ hφ hm hi he hupper hgap u horth
  exact hA.complement_lower (potential_contDiff hp).continuous hφ
    (hbound coupling hc e φ hφ hm hi he hupper hgap) u horth

end InfiniteZero.CuspParameters
