import InfiniteZero.ComplexLogFlatChange
import InfiniteZero.Construction

/-!
# Removing the normal cutoff near the log-flat saddle

The difference between the cutoff integral and its exact plateau integral
is an integral over a fixed interval bounded away from zero. Its norm has
an explicit `exp (-Re(c) * t₂ / h)` bound, uniform in `h > 0`.
-/

noncomputable section
open Set MeasureTheory Filter

namespace InfiniteZero

theorem integrableOn_cutoff_complexLogFlatIntegrand {β tStar t₀ M : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) {χ : ℝ → ℝ}
    (hχ : Continuous χ) (hbound : ∀ t ∈ Ioo 0 t₀, |χ t| ≤ M)
    (h : ℝ) (c : ℂ) (m : ℕ) :
    IntegrableOn (fun t : ℝ => (χ t : ℂ) * complexLogFlatIntegrand β tStar h c m t)
      (Ioo 0 t₀) := by
  apply (integrableOn_complexLogFlatIntegrand hβ hStar t₀ h c m).bdd_mul
    (c := M) (show AEStronglyMeasurable (fun t : ℝ => (χ t : ℂ))
      (volume.restrict (Ioo 0 t₀)) from (Complex.continuous_ofReal.comp hχ).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hbound t ht

/-- Exact decomposition at the end of the plateau. The half-open tail
assigns the splitting endpoint once, so no improper-integral argument is needed. -/
theorem cutoff_complexLogFlatIntegral_sub_eq {β tStar t₀ t₂ M : ℝ}
    (hβ : 0 < β) (hStar : 0 < tStar) (ht₂ : 0 < t₂) (ht₂₀ : t₂ < t₀)
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hbound : ∀ t ∈ Ioo 0 t₀, |χ t| ≤ M)
    (hone : ∀ t ∈ Ioo 0 t₂, χ t = 1) (h : ℝ) (c : ℂ) (m : ℕ) :
    (∫ t in Ioo 0 t₀, (χ t : ℂ) * complexLogFlatIntegrand β tStar h c m t) -
        (∫ t in Ioo 0 t₂, complexLogFlatIntegrand β tStar h c m t) =
      ∫ t in Ico t₂ t₀, (χ t : ℂ) * complexLogFlatIntegrand β tStar h c m t := by
  have hi := integrableOn_cutoff_complexLogFlatIntegrand hβ hStar hχ hbound h c m
  have hs : Ioo 0 t₂ ⊆ Ioo 0 t₀ := fun t ht => ⟨ht.1, ht.2.trans ht₂₀⟩
  have ht : Ico t₂ t₀ ⊆ Ioo 0 t₀ := fun t ht => ⟨ht₂.trans_le ht.1, ht.2⟩
  have hdisj : Disjoint (Ioo 0 t₂) (Ico t₂ t₀) := by
    apply Set.disjoint_left.2
    intro t hs ht
    exact (not_lt_of_ge ht.1) hs.2
  have he : (∫ t in Ioo 0 t₂, (χ t : ℂ) * complexLogFlatIntegrand β tStar h c m t) =
      ∫ t in Ioo 0 t₂, complexLogFlatIntegrand β tStar h c m t := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    simp only [hone t ht, Complex.ofReal_one, one_mul]
  rw [← Ioo_union_Ico_eq_Ioo ht₂ ht₂₀.le,
    setIntegral_union hdisj measurableSet_Ico (hi.mono_set hs) (hi.mono_set ht), he,
    add_sub_cancel_left]

/-- The cutoff error is exponentially small with an explicit constant
`M * t₀^m * (t₀-t₂)` independent of the semiclassical parameter. -/
theorem norm_cutoff_complexLogFlatIntegral_sub_le {β tStar t₀ t₂ M h : ℝ} {c : ℂ}
    (hβ : 0 < β) (hStar : 0 < tStar) (ht₂ : 0 < t₂) (ht₂₀ : t₂ < t₀)
    (hh : 0 < h) (hc : 0 < c.re) {χ : ℝ → ℝ}
    (hχ : Continuous χ) (hbound : ∀ t ∈ Ioo 0 t₀, |χ t| ≤ M)
    (hone : ∀ t ∈ Ioo 0 t₂, χ t = 1) (m : ℕ) :
    ‖(∫ t in Ioo 0 t₀, (χ t : ℂ) * complexLogFlatIntegrand β tStar h c m t) -
        (∫ t in Ioo 0 t₂, complexLogFlatIntegrand β tStar h c m t)‖ ≤
      (M * t₀ ^ m * (t₀ - t₂)) * Real.exp (-c.re * t₂ / h) := by
  have ht₀ : 0 < t₀ := ht₂.trans ht₂₀
  have hM : 0 ≤ M := (abs_nonneg (χ t₂)).trans (hbound t₂ ⟨ht₂, ht₂₀⟩)
  rw [cutoff_complexLogFlatIntegral_sub_eq hβ hStar ht₂ ht₂₀ hχ hbound hone h c m]
  let K := M * t₀ ^ m * Real.exp (-c.re * t₂ / h)
  have hnorm : ∀ t ∈ Ico t₂ t₀,
      ‖(χ t : ℂ) * complexLogFlatIntegrand β tStar h c m t‖ ≤ K := by
    intro t ht
    have htpos : 0 < t := ht₂.trans_le ht.1
    have hexp : Real.exp (-β * (Real.log (tStar / t)) ^ 2 - c.re * t / h) ≤
        Real.exp (-c.re * t₂ / h) := by
      apply Real.exp_le_exp.mpr
      have hct : c.re * t₂ / h ≤ c.re * t / h := by gcongr; exact ht.1
      have hs := mul_nonneg hβ.le (sq_nonneg (Real.log (tStar / t)))
      simp only [neg_mul, neg_div]
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      norm_complexLogFlatIntegrand β tStar h c m htpos.le]
    calc
      _ ≤ M * (t₀ ^ m * Real.exp (-c.re * t₂ / h)) :=
        mul_le_mul (hbound t ⟨htpos, ht.2⟩)
          (mul_le_mul (pow_le_pow_left₀ htpos.le ht.2.le m) hexp
            (Real.exp_pos _).le (pow_nonneg ht₀.le m))
          (by positivity) hM
      _ = K := by dsimp [K]; ring
  have hi : IntegrableOn (fun _ : ℝ => K) (Ico t₂ t₀) :=
    (continuous_const.continuousOn.integrableOn_Icc (a := t₂) (b := t₀)).mono_set
      Ico_subset_Icc_self
  calc
    _ ≤ ∫ _t in Ico t₂ t₀, K := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
      exact hnorm t ht
    _ = _ := by
      rw [setIntegral_const, Real.volume_real_Ico, max_eq_left (sub_nonneg.2 ht₂₀.le),
        smul_eq_mul]
      dsimp [K]
      ring

/-- The concrete construction provides the required plateau and bound `M=1`. -/
theorem CuspParameters.exists_normalCutoff_error_bound {p : CuspParameters}
    (hp : p.BasicConditions) (m : ℕ) :
    ∃ t₂ : ℝ, 0 < t₂ ∧ t₂ < p.t₀ ∧ ∀ (c : ℂ) (h : ℝ), 0 < c.re → 0 < h →
      ‖(∫ t in Ioo 0 p.t₀, (p.χa t : ℂ) * complexLogFlatIntegrand p.β p.tStar h c m t) -
          (∫ t in Ioo 0 t₂, complexLogFlatIntegrand p.β p.tStar h c m t)‖ ≤
        (p.t₀ ^ m * (p.t₀ - t₂)) * Real.exp (-c.re * t₂ / h) := by
  obtain ⟨t₂, ht₂, ht₂₀, hone⟩ := hp.χa_one
  refine ⟨t₂, ht₂, ht₂₀, fun c h hc hh => ?_⟩
  simpa only [one_mul] using norm_cutoff_complexLogFlatIntegral_sub_le hp.β_pos
    (hp.t₀_pos.trans hp.t₀_lt) ht₂ ht₂₀ hh hc hp.χa_smooth.continuous
    (M := 1) (fun t _ => by rw [abs_of_nonneg (hp.χa_range t).1]; exact (hp.χa_range t).2)
    (fun t ht => hone t ⟨ht.1.le, ht.2.le⟩) m

end InfiniteZero
