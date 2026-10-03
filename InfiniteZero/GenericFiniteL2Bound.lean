import InfiniteZero.GenericCompactL2Bound

/-!
# From mass bounds to finite sums of genuine L² norms

The square mass is identified with the Hilbert norm of `MemLp.toLp`.
A uniform mass bound therefore controls the sum of norms for any finite
family, with its cardinality as the only additional factor.
-/

noncomputable section
open MeasureTheory

namespace InfiniteZero

/-- A nonnegative square bound on the physical mass bounds the norm of
the corresponding genuine L² vector. -/
theorem norm_toLp_le_of_mass_le_sq {F : Wavefunction}
    (hF : MemLp F 2 volume) {B : ℝ} (hB : 0 ≤ B) (hmass : mass F ≤ B ^ 2) :
    ‖hF.toLp F‖ ≤ B := by
  apply (sq_le_sq₀ (norm_nonneg _) hB).mp
  rw [(represents_toLp hF).norm_sq_eq_mass]
  exact hmass

/-- The same mass bound on a finite list of wavefunctions controls the
sum of their Hilbert norms. No support or smoothness hypothesis is needed. -/
theorem sum_norm_toLp_le_card_mul_of_mass_le_sq {ι : Type*} [Fintype ι]
    (F : ι → Wavefunction) (hF : ∀ i, MemLp (F i) 2 volume)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ i, mass (F i) ≤ B ^ 2) :
    (∑ i, ‖(hF i).toLp (F i)‖) ≤ (Fintype.card ι : ℝ) * B := by
  calc
    _ ≤ ∑ _i : ι, B :=
      Finset.sum_le_sum (fun i _ => norm_toLp_le_of_mass_le_sq (hF i) hB (hbound i))
    _ = _ := by simp

/-- A finite-set variant allows a bound only on the selected indices. -/
theorem sum_norm_toLp_le_card_mul_of_mass_le_sq_finset {ι : Type*}
    (s : Finset ι) (F : ι → Wavefunction) (hF : ∀ i, MemLp (F i) 2 volume)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ i ∈ s, mass (F i) ≤ B ^ 2) :
    (∑ i ∈ s, ‖(hF i).toLp (F i)‖) ≤ (s.card : ℝ) * B := by
  calc
    _ ≤ ∑ _i ∈ s, B :=
      Finset.sum_le_sum (fun i hi => norm_toLp_le_of_mass_le_sq (hF i) hB (hbound i hi))
    _ = _ := by simp

end InfiniteZero
