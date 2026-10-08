import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

/-!
# Positivity and monotonicity of a regular radial solution on a finite interval

For `(r f')' = r q f` with `q ≥ 0`, continuity of the derivative at the
origin makes the initial radial flux zero. A positive central value then
precludes a first nonpositive point. This local argument uses no behavior
beyond the closed interval and no differentiability of the coefficient.
-/

noncomputable section
open Set

namespace InfiniteZero

variable {a : ℝ} {f df q : ℝ → ℝ}

private theorem radial_regular_monotoneOn_of_nonneg (ha : 0 ≤ a)
    (hf : ContinuousOn f (Icc 0 a)) (hdf : ContinuousOn df (Icc 0 a))
    (hder : ∀ r ∈ Ioo 0 a, HasDerivAt f (df r) r)
    (hflux : ∀ r ∈ Ioo 0 a,
      HasDerivAt (fun s => s * df s) (r * q r * f r) r)
    (hq : ∀ r ∈ Ioo 0 a, 0 ≤ q r)
    (hf_nonneg : ∀ r ∈ Ioo 0 a, 0 ≤ f r) : MonotoneOn f (Icc 0 a) := by
  have hmono_flux : MonotoneOn (fun r => r * df r) (Icc 0 a) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 a)
      (continuousOn_id.mul hdf)
    · intro r hr
      rw [interior_Icc] at hr
      exact (hflux r hr).hasDerivWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      exact mul_nonneg (mul_nonneg hr.1.le (hq r hr)) (hf_nonneg r hr)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 a) hf
  · intro r hr
    rw [interior_Icc] at hr
    exact (hder r hr).hasDerivWithinAt
  · intro r hr
    rw [interior_Icc] at hr
    have hflux_nonneg := hmono_flux (show 0 ∈ Icc (0 : ℝ) a from ⟨le_rfl, ha⟩)
      (show r ∈ Icc (0 : ℝ) a from ⟨hr.1.le, hr.2.le⟩) hr.1.le
    simp only [zero_mul] at hflux_nonneg
    exact nonneg_of_mul_nonneg_right hflux_nonneg hr.1

/-- A regular radial solution positive at the origin cannot first become
nonpositive when its coefficient is nonnegative. -/
theorem radial_regular_pos (_ha : 0 ≤ a)
    (hf : ContinuousOn f (Icc 0 a)) (hdf : ContinuousOn df (Icc 0 a))
    (hder : ∀ r ∈ Ioo 0 a, HasDerivAt f (df r) r)
    (hflux : ∀ r ∈ Ioo 0 a,
      HasDerivAt (fun s => s * df s) (r * q r * f r) r)
    (hq : ∀ r ∈ Ioo 0 a, 0 ≤ q r) (hf0 : 0 < f 0) :
    ∀ r ∈ Icc 0 a, 0 < f r := by
  intro x hx
  by_contra hfx
  let S : Set ℝ := {r ∈ Icc 0 a | f r ≤ 0}
  have hS : IsCompact S :=
    isCompact_Icc.of_isClosed_subset
      (isClosed_Icc.isClosed_le hf continuousOn_const) (fun _ hr => hr.1)
  obtain ⟨r, hr⟩ := hS.exists_isLeast ⟨x, hx, not_lt.mp hfx⟩
  have hrange : r ∈ Icc 0 a := hr.1.1
  have hfr : f r ≤ 0 := hr.1.2
  have hrpos : 0 < r := by
    by_contra h
    have hzero : r = 0 := le_antisymm (not_lt.mp h) hrange.1
    rw [hzero] at hfr
    exact (not_le_of_gt hf0) hfr
  have hpositive : ∀ s ∈ Ioo 0 r, 0 < f s := by
    intro s hs
    by_contra hfs
    have hsS : s ∈ S := ⟨⟨hs.1.le, hs.2.le.trans hrange.2⟩, not_lt.mp hfs⟩
    exact (not_le_of_gt hs.2) (hr.2 hsS)
  have hsub : Icc (0 : ℝ) r ⊆ Icc 0 a := Icc_subset_Icc_right hrange.2
  have hsub_open : Ioo (0 : ℝ) r ⊆ Ioo 0 a :=
    fun s hs => ⟨hs.1, hs.2.trans_le hrange.2⟩
  have hmono : MonotoneOn f (Icc 0 r) :=
    radial_regular_monotoneOn_of_nonneg hrpos.le (hf.mono hsub) (hdf.mono hsub)
      (fun s hs => hder s (hsub_open hs)) (fun s hs => hflux s (hsub_open hs))
      (fun s hs => hq s (hsub_open hs)) (fun s hs => (hpositive s hs).le)
  have hle := hmono (show 0 ∈ Icc (0 : ℝ) r from ⟨le_rfl, hrpos.le⟩)
    (show r ∈ Icc (0 : ℝ) r from ⟨hrpos.le, le_rfl⟩) hrpos.le
  linarith

/-- Positivity is proved from the central value, rather than assumed on
the interval, before applying the nonnegative-flux comparison. -/
theorem radial_regular_monotoneOn (ha : 0 ≤ a)
    (hf : ContinuousOn f (Icc 0 a)) (hdf : ContinuousOn df (Icc 0 a))
    (hder : ∀ r ∈ Ioo 0 a, HasDerivAt f (df r) r)
    (hflux : ∀ r ∈ Ioo 0 a,
      HasDerivAt (fun s => s * df s) (r * q r * f r) r)
    (hq : ∀ r ∈ Ioo 0 a, 0 ≤ q r) (hf0 : 0 < f 0) :
    MonotoneOn f (Icc 0 a) := by
  apply radial_regular_monotoneOn_of_nonneg ha hf hdf hder hflux hq
  intro r hr
  exact (radial_regular_pos ha hf hdf hder hflux hq hf0 r ⟨hr.1.le, hr.2.le⟩).le

/-- The positive central value is a lower bound on the entire closed interval. -/
theorem radial_regular_center_le (ha : 0 ≤ a)
    (hf : ContinuousOn f (Icc 0 a)) (hdf : ContinuousOn df (Icc 0 a))
    (hder : ∀ r ∈ Ioo 0 a, HasDerivAt f (df r) r)
    (hflux : ∀ r ∈ Ioo 0 a,
      HasDerivAt (fun s => s * df s) (r * q r * f r) r)
    (hq : ∀ r ∈ Ioo 0 a, 0 ≤ q r) (hf0 : 0 < f 0) :
    ∀ r ∈ Icc 0 a, f 0 ≤ f r := by
  intro r hr
  exact radial_regular_monotoneOn ha hf hdf hder hflux hq hf0 ⟨le_rfl, ha⟩ hr hr.1

end InfiniteZero
