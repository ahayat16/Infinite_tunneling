import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Monotonicity of positive radial ground profiles

A positive radial L² profile satisfying `(r f')' = r q f` is decreasing
when `q` is increasing. The flux vanishes at the origin by its explicit
factor `r`; no boundary condition on `f' 0` is required.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace InfiniteZero

/-- A positive radial L² solution with increasing coefficient has nonpositive
radial derivative. -/
theorem deriv_nonpos_of_radial_flux {f q : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < f r)
    (hq : MonotoneOn q (Ici 0))
    (hflux : ∀ r > 0, HasDerivAt (fun s => s * deriv f s) (r * q r * f r) r)
    (hfi : IntegrableOn (fun r => r * f r ^ 2) (Ioi 0))
    {r : ℝ} (hr : 0 < r) : deriv f r ≤ 0 := by
  have hfc : Continuous (fun s => s * deriv f s) :=
    continuous_id.mul (hf.continuous_deriv (by simp))
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  by_cases hqr : q r ≤ 0
  · have hanti : AntitoneOn (fun s => s * deriv f s) (Icc 0 r) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 r) hfc.continuousOn
      · intro s hs
        have hs' : s ∈ Ioo 0 r := by simpa only [interior_Icc] using hs
        exact (hflux s hs'.1).differentiableAt.differentiableWithinAt
      · intro s hs
        have hs' : s ∈ Ioo 0 r := by simpa only [interior_Icc] using hs
        rw [(hflux s hs'.1).deriv]
        have hqs : q s ≤ 0 := (hq hs'.1.le hr.le hs'.2.le).trans hqr
        exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos hs'.1.le hqs) (hpos s hs'.1.le).le
    have h := hanti (show (0 : ℝ) ∈ Icc 0 r from ⟨le_rfl, hr.le⟩)
      (show r ∈ Icc 0 r from ⟨hr.le, le_rfl⟩) hr.le
    simp only [zero_mul] at h
    nlinarith
  · have hqr' : 0 < q r := lt_of_not_ge hqr
    by_contra hderiv
    have hdr : 0 < deriv f r := lt_of_not_ge hderiv
    have hmonoFlux : MonotoneOn (fun s => s * deriv f s) (Ici r) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici r) hfc.continuousOn
      · intro s hs
        have hrs : r < s := by simpa only [interior_Ici, mem_Ioi] using hs
        exact (hflux s (hr.trans hrs)).differentiableAt.differentiableWithinAt
      · intro s hs
        have hrs : r < s := by simpa only [interior_Ici, mem_Ioi] using hs
        have hs0 : 0 < s := hr.trans hrs
        rw [(hflux s hs0).deriv]
        exact mul_nonneg (mul_nonneg hs0.le
          (hqr'.le.trans (hq hr.le hs0.le hrs.le))) (hpos s hs0.le).le
    have hderivNonneg (s : ℝ) (hrs : r ≤ s) : 0 ≤ deriv f s := by
      have hs0 : 0 < s := hr.trans_le hrs
      have h := hmonoFlux (show r ∈ Ici r by simp) hrs hrs
      have hfluxpos : 0 < s * deriv f s := (mul_pos hr hdr).trans_le h
      exact ((mul_pos_iff_of_pos_left hs0).mp hfluxpos).le
    have hmono : MonotoneOn f (Ici r) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici r) hf.continuous.continuousOn
        hfd.differentiableOn
      intro s hs
      exact hderivNonneg s (interior_subset hs)
    have hconst : IntegrableOn (fun _ : ℝ => f r ^ 2) (Ioi (max r 1)) := by
      apply (hfi.mono_set (Ioi_subset_Ioi (hr.le.trans (le_max_left r 1)))).mono'
        aestronglyMeasurable_const
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hrs : r ≤ s := (le_max_left r 1).trans hs.le
      have hs1 : 1 ≤ s := (le_max_right r 1).trans hs.le
      have hfs : f r ≤ f s := hmono (show r ∈ Ici r by simp) hrs hrs
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hsq : f r ^ 2 ≤ f s ^ 2 := by
        nlinarith [hpos r hr.le, hpos s (hr.le.trans hrs)]
      exact hsq.trans (le_mul_of_one_le_left (sq_nonneg _) hs1)
    have hz : f r ^ 2 = 0 := by
      simpa [integrableOn_const_iff, Real.volume_Ioi] using hconst
    have hp := hpos r hr.le
    nlinarith

/-- The monotonicity includes the origin by continuity. -/
theorem antitoneOn_of_radial_flux {f q : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < f r)
    (hq : MonotoneOn q (Ici 0))
    (hflux : ∀ r > 0, HasDerivAt (fun s => s * deriv f s) (r * q r * f r) r)
    (hfi : IntegrableOn (fun r => r * f r ^ 2) (Ioi 0)) :
    AntitoneOn f (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hf.continuous.continuousOn
    (hf.differentiable (by simp)).differentiableOn
  intro r hr
  exact deriv_nonpos_of_radial_flux hf hpos hq hflux hfi
    (by simpa only [interior_Ici, mem_Ioi] using hr)

end InfiniteZero
