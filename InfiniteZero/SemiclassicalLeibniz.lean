import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Semiclassical Leibniz estimates with every power retained

Multiplying the ordinary higher-derivative product estimate by `h^n`
distributes exactly as `h^i * h^(n-i)` in every binomial summand.
The statements concern derivatives of the factors before any external
weight is applied. No differentiability of such a weight is assumed.
-/

noncomputable section
open scoped ContDiff

namespace InfiniteZero

/-- Exact redistribution of the semiclassical factor, including `h = 0`. -/
theorem semiclassical_binomial_sum (h : ℝ) (n : ℕ) (a b : ℕ → ℝ) :
    h ^ n * (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * a i * b (n - i)) =
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * (h ^ i * a i) * (h ^ (n - i) * b (n - i)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hpow : h ^ n = h ^ i * h ^ (n - i) := by
    rw [← pow_add, Nat.add_sub_of_le hin]
  rw [hpow]
  ring

section RealScalar

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Real scalar multiplication: each derivative factor keeps its own power
of the semiclassical parameter. -/
theorem semiclassical_norm_iteratedFDeriv_smul_le {h : ℝ} (hh : 0 ≤ h)
    {f : E → ℝ} {g : E → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (x : E) :
    h ^ n * ‖iteratedFDeriv ℝ n (fun y => f y • g y) x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (h ^ i * ‖iteratedFDeriv ℝ i f x‖) *
        (h ^ (n - i) * ‖iteratedFDeriv ℝ (n - i) g x‖) := by
  calc
    _ ≤ h ^ n * (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖) :=
      mul_le_mul_of_nonneg_left
        (norm_iteratedFDeriv_smul_le (contDiff_infty.mp hf n)
          (contDiff_infty.mp hg n) x le_rfl) (pow_nonneg hh n)
    _ = _ := semiclassical_binomial_sum h n
      (fun i => ‖iteratedFDeriv ℝ i f x‖) (fun i => ‖iteratedFDeriv ℝ i g x‖)

/-- Evaluating a Fréchet jet on vectors of norm at most one loses no
semiclassical factor. This includes ordered coordinate derivatives. -/
theorem semiclassical_norm_iteratedFDeriv_apply_le {h : ℝ} (hh : 0 ≤ h)
    (g : E → F) (n : ℕ) (x : E) (v : Fin n → E) (hv : ∀ i, ‖v i‖ ≤ 1) :
    h ^ n * ‖iteratedFDeriv ℝ n g x v‖ ≤ h ^ n * ‖iteratedFDeriv ℝ n g x‖ := by
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hh n)
  simpa using (iteratedFDeriv ℝ n g x).le_opNorm_mul_prod_of_le hv

end RealScalar

section Product

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]

/-- The same estimate for products in a normed real algebra, in particular
for complex-valued wavefunctions. -/
theorem semiclassical_norm_iteratedFDeriv_mul_le {h : ℝ} (hh : 0 ≤ h)
    {f g : E → A} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (x : E) :
    h ^ n * ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (h ^ i * ‖iteratedFDeriv ℝ i f x‖) *
        (h ^ (n - i) * ‖iteratedFDeriv ℝ (n - i) g x‖) := by
  calc
    _ ≤ h ^ n * (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖) :=
      mul_le_mul_of_nonneg_left
        (norm_iteratedFDeriv_mul_le (contDiff_infty.mp hf n)
          (contDiff_infty.mp hg n) x le_rfl) (pow_nonneg hh n)
    _ = _ := semiclassical_binomial_sum h n
      (fun i => ‖iteratedFDeriv ℝ i f x‖) (fun i => ‖iteratedFDeriv ℝ i g x‖)

end Product
end InfiniteZero
