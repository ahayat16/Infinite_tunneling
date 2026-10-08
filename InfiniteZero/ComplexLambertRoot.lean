import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Constructing the large complex Lambert root

The branch needed for the log-flat saddle is constructed by contraction,
rather than postulated as a special function. Quantitative assumptions here
involve only the input L and its ordinary principal logarithm.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace InfiniteZero

theorem norm_complex_log_sub_le_of_re_ge {a : ℝ} (ha : 0 < a) {z w : ℂ}
    (hz : a ≤ z.re) (hw : a ≤ w.re) :
    ‖Complex.log z - Complex.log w‖ ≤ a⁻¹ * ‖z - w‖ := by
  let s : Set ℂ := {u | a ≤ u.re}
  have hs : Convex ℝ s := by
    intro u hu v hv c d hc hd hcd
    change a ≤ (c • u + d • v).re
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    have h₁ := mul_le_mul_of_nonneg_left hu hc
    have h₂ := mul_le_mul_of_nonneg_left hv hd
    nlinarith
  apply hs.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (Complex.hasDerivAt_log (by
      apply Complex.mem_slitPlane_iff.mpr
      exact Or.inl (ha.trans_le hu))).hasDerivWithinAt)
    (fun u hu => ?_) hw hz
  rw [norm_inv]
  have hle : a ≤ ‖u‖ := hu.trans (Complex.re_le_norm u)
  exact (inv_le_inv₀ (ha.trans_le hle) ha).mpr hle

def lambertIteration (L w : ℂ) : ℂ := L - Complex.log w

theorem re_ge_of_mem_lambert_disc {L w : ℂ} {R : ℝ}
    (hw : w ∈ Metric.closedBall L R) : L.re - R ≤ w.re := by
  have hnorm : ‖w - L‖ ≤ R := by simpa [dist_eq_norm] using hw
  have hreal := (neg_le_abs (w - L).re).trans (Complex.abs_re_le_norm (w - L))
  simp only [Complex.sub_re] at hreal
  linarith

theorem lambertIteration_mapsTo {L : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hL : R + 2 ≤ L.re) (hlog : ‖Complex.log L‖ ≤ R / 2) :
    MapsTo (lambertIteration L) (Metric.closedBall L R) (Metric.closedBall L R) := by
  intro w hw
  have hwre : (2 : ℝ) ≤ w.re := by linarith [re_ge_of_mem_lambert_disc hw]
  have hLre : (2 : ℝ) ≤ L.re := by linarith
  have hb := norm_complex_log_sub_le_of_re_ge (by norm_num : (0 : ℝ) < 2) hwre hLre
  have hn : ‖w - L‖ ≤ R := by simpa [dist_eq_norm] using hw
  have hlogw : ‖Complex.log w‖ ≤ R := by
    have ht := norm_add_le (Complex.log w - Complex.log L) (Complex.log L)
    simp only [sub_add_cancel] at ht
    norm_num at hb
    nlinarith
  simpa [lambertIteration, Metric.mem_closedBall, dist_eq_norm] using hlogw

theorem lambertIteration_lipschitzOn {L : ℂ} {R : ℝ}
    (hL : R + 2 ≤ L.re) :
    LipschitzOnWith (1 / 2 : NNReal) (lambertIteration L) (Metric.closedBall L R) := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro z hz w hw
  have hzre : (2 : ℝ) ≤ z.re := by linarith [re_ge_of_mem_lambert_disc hz]
  have hwre : (2 : ℝ) ≤ w.re := by linarith [re_ge_of_mem_lambert_disc hw]
  have hb := norm_complex_log_sub_le_of_re_ge (by norm_num : (0 : ℝ) < 2) hzre hwre
  simpa [lambertIteration, sub_sub_sub_cancel_left, norm_sub_rev] using hb

/-- A genuine existence theorem with elementary quantitative input bounds.
The second-order localization measures the error in L - log L. -/
theorem exists_large_complex_lambert_root {L : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hL : R + 2 ≤ L.re) (hlog : ‖Complex.log L‖ ≤ R / 2) :
    ∃ w : ℂ, w ∈ Metric.closedBall L R ∧ 2 ≤ w.re ∧
      w + Complex.log w = L ∧ w * Complex.exp w = Complex.exp L ∧
      ‖w - (L - Complex.log L)‖ ≤ R / (L.re - R) := by
  let T := lambertIteration L
  have hmaps := lambertIteration_mapsTo hR hL hlog
  have hlip := lambertIteration_lipschitzOn hL
  have hcontr : ContractingWith (1 / 2 : NNReal) (hmaps.restrict T _ _) := by
    refine ⟨by norm_num, ?_⟩
    intro z w
    exact hlip z.property w.property
  obtain ⟨w, hw, hfix, _, _⟩ := ContractingWith.exists_fixedPoint'
    Metric.isClosed_closedBall.isComplete hmaps hcontr
    (Metric.mem_closedBall_self hR) (edist_ne_top L (T L))
  have hwre : (2 : ℝ) ≤ w.re := by linarith [re_ge_of_mem_lambert_disc hw]
  have hweq : w + Complex.log w = L := by
    change L - Complex.log w = w at hfix
    linear_combination -hfix
  have hwne : w ≠ 0 := by
    intro hzero
    norm_num [hzero] at hwre
  have hexp := congrArg Complex.exp hweq
  rw [Complex.exp_add, Complex.exp_log hwne, mul_comm] at hexp
  refine ⟨w, hw, hwre, hweq, hexp, ?_⟩
  have ha : 0 < L.re - R := by linarith
  have hnorm : ‖w - L‖ ≤ R := by simpa [dist_eq_norm] using hw
  have hb := norm_complex_log_sub_le_of_re_ge ha (re_ge_of_mem_lambert_disc hw)
    (show L.re - R ≤ L.re by linarith)
  have he : w - (L - Complex.log L) = -(Complex.log w - Complex.log L) := by
    linear_combination hweq
  rw [he, norm_neg]
  exact hb.trans (by rw [div_eq_mul_inv, mul_comm R]; gcongr)

theorem large_complex_lambert_root_unique {L w z : ℂ}
    (hw : 2 ≤ w.re) (hz : 2 ≤ z.re)
    (hew : w + Complex.log w = L) (hez : z + Complex.log z = L) : w = z := by
  have he : w - z = -(Complex.log w - Complex.log z) := by
    linear_combination hew - hez
  have hn : ‖w - z‖ = ‖Complex.log w - Complex.log z‖ := by rw [he, norm_neg]
  have hb := norm_complex_log_sub_le_of_re_ge (by norm_num : (0 : ℝ) < 2) hw hz
  norm_num at hb
  rw [← hn] at hb
  exact sub_eq_zero.mp (norm_eq_zero.mp (by linarith [norm_nonneg (w - z)]))

/-- The nonvacuous regime is certified by the existence theorem above.
The value zero outside that regime is not used in any saddle assertion. -/
def largeLambertRoot (L : ℂ) : ℂ := by
  classical
  exact if h : ∃ w : ℂ, 2 ≤ w.re ∧ w + Complex.log w = L then Classical.choose h else 0

theorem largeLambertRoot_spec {L : ℂ}
    (h : ∃ w : ℂ, 2 ≤ w.re ∧ w + Complex.log w = L) :
    2 ≤ (largeLambertRoot L).re ∧ largeLambertRoot L + Complex.log (largeLambertRoot L) = L := by
  classical
  simpa only [largeLambertRoot, dif_pos h] using Classical.choose_spec h

theorem largeLambertRoot_eq {L w : ℂ} (hw : 2 ≤ w.re) (he : w + Complex.log w = L) :
    largeLambertRoot L = w :=
  large_complex_lambert_root_unique (largeLambertRoot_spec ⟨w, hw, he⟩).1 hw
    (largeLambertRoot_spec ⟨w, hw, he⟩).2 he

theorem largeLambertRoot_estimates {L : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hL : R + 2 ≤ L.re) (hlog : ‖Complex.log L‖ ≤ R / 2) :
    largeLambertRoot L ∈ Metric.closedBall L R ∧ 2 ≤ (largeLambertRoot L).re ∧
      largeLambertRoot L + Complex.log (largeLambertRoot L) = L ∧
      largeLambertRoot L * Complex.exp (largeLambertRoot L) = Complex.exp L ∧
      ‖largeLambertRoot L - (L - Complex.log L)‖ ≤ R / (L.re - R) := by
  obtain ⟨w, hw, hre, he, hexp, herr⟩ := exists_large_complex_lambert_root hR hL hlog
  rw [largeLambertRoot_eq hre he]
  exact ⟨hw, hre, he, hexp, herr⟩

theorem large_complex_lambert_roots_lipschitz {L M w z : ℂ}
    (hw : 2 ≤ w.re) (hz : 2 ≤ z.re)
    (hew : w + Complex.log w = L) (hez : z + Complex.log z = M) :
    ‖w - z‖ ≤ 2 * ‖L - M‖ := by
  have he : w - z = (L - M) - (Complex.log w - Complex.log z) := by
    linear_combination hew - hez
  have ht := norm_sub_le (L - M) (Complex.log w - Complex.log z)
  rw [← he] at ht
  have hb := norm_complex_log_sub_le_of_re_ge (by norm_num : (0 : ℝ) < 2) hw hz
  norm_num at hb
  linarith

theorem large_complex_lambert_im_bound {L w : ℂ} (he : w + Complex.log w = L) :
    |w.im| ≤ |L.im| + Real.pi := by
  have him := congrArg Complex.im he
  simp only [Complex.add_im, Complex.log_im] at him
  have ha : |w.arg| ≤ Real.pi := abs_le.mpr ⟨(Complex.neg_pi_lt_arg w).le, Complex.arg_le_pi w⟩
  have hid : w.im = L.im - w.arg := by linarith
  rw [hid]
  exact (abs_sub _ _).trans (add_le_add le_rfl ha)

end InfiniteZero
