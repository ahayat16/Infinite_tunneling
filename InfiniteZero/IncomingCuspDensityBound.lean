import InfiniteZero.CuspSourcePairingFubini
import InfiniteZero.LandauKernelExactActionUpper
import InfiniteZero.InactiveSupportGaps

/-!
# An exact-action majorant of the true incoming chart density

The estimate holds on the entire closed coordinate rectangle, independently
of where the cutoffs vanish. Each radial source action gains `t/8`; the
bridge keeps its full action at `2L-R`. The three exact-action kernel bounds
cost `h⁻⁶`, with a constant fixed before all energies and coordinates.
-/

noncomputable section
open Set

namespace InfiniteZero.CuspParameters

theorem cuspChart_rectangle_bounds {p : CuspParameters} (hp : p.BasicConditions)
    {t s : ℝ} (ht : t ∈ Icc 0 p.t₀) (hs : |s| ≤ p.s₀) :
    (p.cuspChart (t, s)) 0 ≤ p.R / 2 - t / 4 ∧
      p.R + t / 4 ≤ ‖p.cuspChart (t, s)‖ ∧
        ‖p.cuspChart (t, s)‖ ≤ p.cuspSupportRadius := by
  have hnormal : 0 ≤ p.normalCoordinate (p.cuspChart (t, s)) := by
    simpa only [normalCoordinate_cuspChart] using ht.1
  have hnormalMax : p.normalCoordinate (p.cuspChart (t, s)) ≤ p.t₀ := by
    simpa only [normalCoordinate_cuspChart] using ht.2
  have htan : |p.tangentCoordinate (p.cuspChart (t, s))| ≤
      p.s₀ * p.normalCoordinate (p.cuspChart (t, s)) ^ 2 := by
    rw [tangentCoordinate_cuspChart, normalCoordinate_cuspChart, abs_mul, abs_sq]
    exact mul_le_mul_of_nonneg_right hs (sq_nonneg t)
  have hb := cusp_horizontal_radial_bounds hp hnormal hnormalMax htan
  simp only [normalCoordinate_cuspChart] at hb
  refine ⟨hb.1, hb.2, ?_⟩
  have hn := norm_le_cusp_coordinates p (p.cuspChart (t, s))
  simp only [normalCoordinate_cuspChart, tangentCoordinate_cuspChart, abs_mul, abs_sq,
    abs_of_nonneg ht.1] at hn
  have htsq := pow_le_pow_left₀ ht.1 ht.2 2
  have hprod := mul_le_mul hs htsq (sq_nonneg t) hp.s₀_pos.le
  unfold cuspSupportRadius
  linarith [ht.2]

theorem cuspChart_radial_action_gain_eighth {p : CuspParameters} (hp : p.BasicConditions)
    {E t s : ℝ} (hE : E ∈ Icc (1 / 2 : ℝ) 1)
    (ht : t ∈ Icc 0 p.t₀) (hs : |s| ≤ p.s₀) :
    bridgeAction p.b E p.R + t / 8 ≤ bridgeAction p.b E ‖p.cuspChart (t, s)‖ := by
  have hEp : 0 < E := lt_of_lt_of_le (by norm_num) hE.1
  have hrad := (cuspChart_rectangle_bounds hp ht hs).2.1
  have hR : p.R ≤ ‖p.cuspChart (t, s)‖ := by linarith [ht.1]
  have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt E := by
    nlinarith [Real.sq_sqrt hEp.le, Real.sqrt_nonneg E, hE.1]
  have hg := bridgeAction_sub_ge hp.b_pos.ne' hEp hR
  have hm := mul_le_mul_of_nonneg_left
    (show t / 4 ≤ ‖p.cuspChart (t, s)‖ - p.R by linarith) (Real.sqrt_nonneg E)
  have htq := mul_le_mul_of_nonneg_right hsqrt ht.1
  nlinarith

theorem cuspChart_bridge_rectangle_bounds {p : CuspParameters} (hp : p.BasicConditions)
    {L t u s r : ℝ} (hL : p.R < 2 * L)
    (ht : t ∈ Icc 0 p.t₀) (hu : u ∈ Icc 0 p.t₀)
    (hs : |s| ≤ p.s₀) (hr : |r| ≤ p.s₀) :
    ‖p.cuspChart (t, s) + reflection (p.cuspChart (u, r)) - 2 • displacement L‖ ∈
      Icc (Geometry.activeDistance p.R L) (2 * (L + p.cuspSupportRadius)) := by
  have hb₁ := cuspChart_rectangle_bounds hp ht hs
  have hb₂ := cuspChart_rectangle_bounds hp hu hr
  have hb := bridge_distance_ge_horizontal (p.cuspChart (t, s))
    (reflection (p.cuspChart (u, r))) L
  have href : (reflection (p.cuspChart (u, r))) 0 = (p.cuspChart (u, r)) 0 := by
    simp [reflection]
  rw [href] at hb
  constructor
  · dsimp [Geometry.activeDistance]
    linarith [ht.1, hu.1]
  · exact (bridge_distance_annulus (by linarith [hp.radius_pos] : 0 ≤ L) hb₁.2.2
      (by simpa only [norm_reflection] using hb₂.2.2)).2

theorem exists_incomingCuspDensity_bound {p : CuspParameters} (hp : p.BasicConditions)
    {L : ℝ} (hL : p.R < 2 * L) :
    ∃ C > 0, ∀ Ecore ∈ Icc (1 / 2 : ℝ) 1, ∀ Efull ∈ Icc (1 / 2 : ℝ) 1,
      ∀ h > 0, h ≤ 1 → ∀ t ∈ Icc 0 p.t₀, ∀ u ∈ Icc 0 p.t₀,
      ∀ s r : ℝ, |s| ≤ p.s₀ → |r| ≤ p.s₀ →
      ‖p.incomingCuspDensity L h Ecore Efull t u s r‖ ≤
        C * (h ^ 6)⁻¹ * Real.exp (-p.activeReferenceAction L Efull Ecore / h) *
          (t ^ 2 * logFlat p.β p.tStar t * Real.exp (-t / (8 * h))) *
          (u ^ 2 * logFlat p.β p.tStar u * Real.exp (-u / (8 * h))) := by
  let D := Geometry.activeDistance p.R L
  let rmin := min p.R D
  let rmax := max p.R (max p.cuspSupportRadius (2 * (L + p.cuspSupportRadius)))
  have hD : 0 < D := Geometry.activeDistance_pos hL
  have hrmin : 0 < rmin := lt_min hp.radius_pos hD
  have hrr : rmin ≤ rmax := (min_le_left _ _).trans (le_max_left _ _)
  obtain ⟨C, hC, hK⟩ := exists_uniform_landauKernel_exact_action_upper hp.b_pos
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) hrmin hrr
  refine ⟨C ^ 3, by positivity, ?_⟩
  intro Ec hEc Ef hEf h hh hh1 t ht u hu s r hs hr
  have hEcp : 0 < Ec := lt_of_lt_of_le (by norm_num) hEc.1
  have hEfp : 0 < Ef := lt_of_lt_of_le (by norm_num) hEf.1
  have hsdata := cuspChart_rectangle_bounds hp ht hs
  have hrdata := cuspChart_rectangle_bounds hp hu hr
  have hbdata := cuspChart_bridge_rectangle_bounds hp hL ht hu hs hr
  have hsource (v a : ℝ) (hv : v ∈ Icc 0 p.t₀) (ha : |a| ≤ p.s₀) :
      landauKernel p.b h Ec ‖p.cuspChart (v, a)‖ ≤
        C * (h ^ 2)⁻¹ * Real.exp (-bridgeAction p.b Ec p.R / h) *
          Real.exp (-v / (8 * h)) := by
    have hdata := cuspChart_rectangle_bounds hp hv ha
    have hlow : p.R ≤ ‖p.cuspChart (v, a)‖ := by linarith [hv.1]
    have hhigh : ‖p.cuspChart (v, a)‖ ≤ rmax :=
      hdata.2.2.trans ((le_max_left _ _).trans (le_max_right _ _))
    have hk := hK Ec hEc _ ⟨(min_le_left _ _).trans hlow, hhigh⟩ h hh hh1
    have hg := cuspChart_radial_action_gain_eighth hp hEc hv ha
    calc
      _ ≤ C * (h ^ 2)⁻¹ * Real.exp (-(bridgeAction p.b Ec p.R + v / 8) / h) := by
        apply hk.trans
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg hg) hh.le)
      _ = _ := by
        rw [show -(bridgeAction p.b Ec p.R + v / 8) / h =
          -bridgeAction p.b Ec p.R / h + -v / (8 * h) by ring, Real.exp_add]
        ring
  have hbridge : landauKernel p.b h Ef
      ‖p.cuspChart (t, s) + reflection (p.cuspChart (u, r)) - 2 • displacement L‖ ≤
      C * (h ^ 2)⁻¹ * Real.exp (-bridgeAction p.b Ef D / h) := by
    have hhigh : ‖p.cuspChart (t, s) + reflection (p.cuspChart (u, r)) -
        2 • displacement L‖ ≤ rmax :=
      hbdata.2.trans ((le_max_right _ _).trans (le_max_right _ _))
    apply (hK Ef hEf _ ⟨(min_le_right _ _).trans hbdata.1, hhigh⟩ h hh hh1).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
      (neg_le_neg ((strictMono_bridgeAction hp.b_pos.ne' hEfp).monotone hbdata.1)) hh.le)
  have hKt : 0 ≤ landauKernel p.b h Ec ‖p.cuspChart (t, s)‖ :=
    (landauKernel_pos hp.b_pos hh hEcp
      (by linarith [hp.radius_pos, hsdata.2.1, ht.1])).le
  have hKu : 0 ≤ landauKernel p.b h Ec ‖p.cuspChart (u, r)‖ :=
    (landauKernel_pos hp.b_pos hh hEcp
      (by linarith [hp.radius_pos, hrdata.2.1, hu.1])).le
  have hKb := (landauKernel_pos hp.b_pos hh hEfp (hD.trans_le hbdata.1)).le
  have hflat (v : ℝ) : 0 ≤ logFlat p.β p.tStar v := by
    unfold logFlat
    split_ifs <;> positivity
  have hft := hflat t
  have hfu := hflat u
  have hcut (v a : ℝ) : logFlat p.β p.tStar v * p.χa v * p.χb a ≤
      logFlat p.β p.tStar v := by
    have h₁ := mul_le_mul_of_nonneg_left (hp.χa_range v).2 (hflat v)
    have h₂ := mul_le_mul_of_nonneg_left (hp.χb_range a).2
      (mul_nonneg (hflat v) (hp.χa_range v).1)
    simp only [mul_one] at h₁ h₂
    exact h₂.trans h₁
  have hscalar : 0 ≤ t ^ 2 * u ^ 2 *
      (logFlat p.β p.tStar t * p.χa t * p.χb s) *
      (logFlat p.β p.tStar u * p.χa u * p.χb r) *
      landauKernel p.b h Ec ‖p.cuspChart (t, s)‖ *
      landauKernel p.b h Ec ‖p.cuspChart (u, r)‖ := by
    have hat := (hp.χa_range t).1
    have hau := (hp.χa_range u).1
    have hbs := (hp.χb_range s).1
    have hbr := (hp.χb_range r).1
    positivity
  have he : Real.exp (-bridgeAction p.b Ec p.R / h) *
      Real.exp (-bridgeAction p.b Ec p.R / h) * Real.exp (-bridgeAction p.b Ef D / h) =
      Real.exp (-p.activeReferenceAction L Ef Ec / h) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [activeReferenceAction, D]
    ring
  calc
    _ = (t ^ 2 * u ^ 2 * (logFlat p.β p.tStar t * p.χa t * p.χb s) *
        (logFlat p.β p.tStar u * p.χa u * p.χb r) *
        landauKernel p.b h Ec ‖p.cuspChart (t, s)‖ *
        landauKernel p.b h Ec ‖p.cuspChart (u, r)‖) *
        landauKernel p.b h Ef
          ‖p.cuspChart (t, s) + reflection (p.cuspChart (u, r)) - 2 • displacement L‖ := by
      rw [incomingCuspDensity, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hscalar, norm_sourceKernel hp.b_pos hh hEfp L _ _ (hD.trans_le hbdata.1)]
    _ ≤ t ^ 2 * u ^ 2 * logFlat p.β p.tStar t * logFlat p.β p.tStar u *
        (C * (h ^ 2)⁻¹ * Real.exp (-bridgeAction p.b Ec p.R / h) * Real.exp (-t / (8 * h))) *
        (C * (h ^ 2)⁻¹ * Real.exp (-bridgeAction p.b Ec p.R / h) * Real.exp (-u / (8 * h))) *
        (C * (h ^ 2)⁻¹ * Real.exp (-bridgeAction p.b Ef D / h)) := by
      gcongr
      · exact mul_nonneg (mul_nonneg hfu (hp.χa_range u).1) (hp.χb_range r).1
      · exact hcut t s
      · exact hcut u r
      · exact hsource t s ht hs
      · exact hsource u r hu hr
    _ = C ^ 3 * (h ^ 6)⁻¹ *
        (Real.exp (-bridgeAction p.b Ec p.R / h) *
          Real.exp (-bridgeAction p.b Ec p.R / h) * Real.exp (-bridgeAction p.b Ef D / h)) *
        (t ^ 2 * logFlat p.β p.tStar t * Real.exp (-t / (8 * h))) *
        (u ^ 2 * logFlat p.β p.tStar u * Real.exp (-u / (8 * h))) := by
      field_simp
    _ = _ := by rw [he]

end InfiniteZero.CuspParameters
