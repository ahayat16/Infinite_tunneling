import InfiniteZero.ComplexLogFlatSaddle

/-! Principal argument control for the actual log-flat saddle. -/

noncomputable section
open Set Filter
open scoped Topology

namespace InfiniteZero

theorem logFlatLambertDisplacement_im {β tStar : ℝ} (hβ : 0 < β) (ht : 0 < tStar)
    (k : ℝ) (c : ℂ) : (logFlatLambertDisplacement β k tStar c).im = c.arg := by
  simp only [logFlatLambertDisplacement, Complex.add_im, Complex.ofReal_im, add_zero,
    Complex.log_im]
  have he : c * (tStar : ℂ) / (2 * (β : ℂ)) = c * ((tStar / (2 * β) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he, Complex.arg_mul_real (by positivity)]

theorem im_mem_uIcc_of_im_add_arg_eq {w : ℂ} {θ : ℝ}
    (he : w.im + w.arg = θ) : w.im ∈ uIcc 0 θ := by
  by_cases hi : 0 ≤ w.im
  · have ha : 0 ≤ w.arg := Complex.arg_nonneg_iff.mpr hi
    have hθ : 0 ≤ θ := by linarith
    rw [uIcc_of_le hθ]
    exact ⟨hi, by linarith⟩
  · have hi' : w.im < 0 := lt_of_not_ge hi
    have ha : w.arg < 0 := Complex.arg_neg_iff.mpr hi'
    have hθ : θ ≤ 0 := by linarith
    rw [uIcc_of_ge hθ]
    exact ⟨by linarith, hi'.le⟩

theorem abs_im_le_of_im_add_arg_eq {w : ℂ} {θ : ℝ}
    (he : w.im + w.arg = θ) : |w.im| ≤ |θ| := by
  have hm := im_mem_uIcc_of_im_add_arg_eq he
  rcases le_total 0 θ with hθ | hθ
  · rw [uIcc_of_le hθ] at hm
    rw [abs_of_nonneg hm.1, abs_of_nonneg hθ]
    exact hm.2
  · rw [uIcc_of_ge hθ] at hm
    rw [abs_of_nonpos hm.2, abs_of_nonpos hθ]
    exact neg_le_neg hm.1

theorem abs_sub_le_of_mem_uIcc_zero {θ v η : ℝ}
    (hv : v ∈ uIcc 0 θ) (hη : η ∈ uIcc 0 v) : |θ - η| ≤ |θ| := by
  rcases le_total 0 θ with hθ | hθ
  · rw [uIcc_of_le hθ] at hv
    rw [uIcc_of_le hv.1] at hη
    simp only [mem_Icc] at hv hη
    rw [abs_of_nonneg hθ, abs_of_nonneg (by linarith : 0 ≤ θ - η)]
    linarith
  · rw [uIcc_of_ge hθ] at hv
    rw [uIcc_of_ge hv.2] at hη
    simp only [mem_Icc] at hv hη
    rw [abs_of_nonpos hθ, abs_of_nonpos (by linarith : θ - η ≤ 0)]
    linarith

theorem eventually_logFlatSaddleRoot_arg {β k tStar : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hc : c ≠ 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      (logFlatSaddleRoot β k tStar c h).im + (logFlatSaddleRoot β k tStar c h).arg = c.arg ∧
      (logFlatSaddleRoot β k tStar c h).im ∈ uIcc 0 c.arg ∧
      |(logFlatSaddleRoot β k tStar c h).im| ≤ |c.arg| := by
  filter_upwards [eventually_logFlatSaddleRoot_log_eq β k tStar c,
    eventually_logFlatSaddleRoot_equation (k := k) hβ.ne' ht.ne' hc] with h he hs
  have him := congrArg Complex.im he
  simp only [Complex.add_im, Complex.log_im, Complex.ofReal_im, zero_add,
    logFlatLambertDisplacement_im hβ ht] at him
  exact ⟨him, im_mem_uIcc_of_im_add_arg_eq him, abs_im_le_of_im_add_arg_eq him⟩

/-- The whole connector stays in the same right-half-plane angular sector. -/
theorem eventually_logFlatSaddleRoot_connector_angle {β k tStar : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hc : 0 < c.re) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ η ∈ uIcc 0 (logFlatSaddleRoot β k tStar c h).im,
      |c.arg - η| ≤ |c.arg| ∧ |c.arg - η| < Real.pi / 2 := by
  have hcne : c ≠ 0 := by intro h; simp [h] at hc
  have hcarg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hc)
  filter_upwards [eventually_logFlatSaddleRoot_arg (k := k) hβ ht hcne] with h hs
  intro η hη
  have ha := abs_sub_le_of_mem_uIcc_zero hs.2.1 hη
  exact ⟨ha, ha.trans_lt hcarg⟩

theorem re_mul_exp_neg_I (c : ℂ) (η : ℝ) :
    (c * Complex.exp (-(η : ℂ) * Complex.I)).re = ‖c‖ * Real.cos (c.arg - η) := by
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
  rw [Real.cos_sub, mul_add, ← mul_assoc, ← mul_assoc,
    Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg]

theorem re_mul_exp_neg_I_ge_of_angle {c : ℂ} {η : ℝ}
    (hangle : |c.arg - η| ≤ |c.arg|) :
    c.re ≤ (c * Complex.exp (-(η : ℂ) * Complex.I)).re := by
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (c.arg - η))
    (Complex.abs_arg_le_pi c) hangle
  simp only [Real.cos_abs] at hcos
  rw [re_mul_exp_neg_I, ← Complex.norm_mul_cos_arg c]
  exact mul_le_mul_of_nonneg_left hcos (norm_nonneg c)

/-- A uniform positive lower bound on the connector is the original real part of c. -/
theorem eventually_logFlatSaddleRoot_connector_re {β k tStar : ℝ} {c : ℂ}
    (hβ : 0 < β) (ht : 0 < tStar) (hc : 0 < c.re) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ η ∈ uIcc 0 (logFlatSaddleRoot β k tStar c h).im,
      c.re ≤ (c * Complex.exp (-(η : ℂ) * Complex.I)).re := by
  filter_upwards [eventually_logFlatSaddleRoot_connector_angle (k := k) hβ ht hc] with h hs
  exact fun η hη => re_mul_exp_neg_I_ge_of_angle (hs η hη).1

end InfiniteZero
