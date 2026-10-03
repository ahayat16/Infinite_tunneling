import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exterior radial Wronskians and uniqueness with finite energy

Two solutions of `f'' = q f - f'/r` have constant weighted Wronskian.
If their values and first derivatives have finite radial L² integrals,
that constant is integrable on an interval of infinite measure, hence zero.
A strictly positive comparison solution then gives proportionality.

The four energy integrability assumptions are explicit inputs. Deriving
the derivative bounds from the equation and L² alone is a separate
Caccioppoli argument, not an assumption hidden in these results.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero

/-- The first-order formulation of the radial exterior second-order equation. -/
structure IsRadialODESolutionOn (q f df : ℝ → ℝ) (a : ℝ) : Prop where
  deriv : ∀ r ∈ Ioi a, HasDerivAt f (df r) r
  second : ∀ r ∈ Ioi a, HasDerivAt df (q r * f r - r⁻¹ * df r) r

def radialWronskian (f df g dg : ℝ → ℝ) (r : ℝ) : ℝ :=
  r * (f r * dg r - df r * g r)

variable {a : ℝ} {q f df g dg : ℝ → ℝ}

theorem IsRadialODESolutionOn.mono (hf : IsRadialODESolutionOn q f df a)
    {R : ℝ} (hR : a ≤ R) : IsRadialODESolutionOn q f df R :=
  ⟨fun r hr => hf.deriv r (hR.trans_lt hr),
    fun r hr => hf.second r (hR.trans_lt hr)⟩

theorem hasDerivAt_radialWronskian_zero (ha : 0 < a)
    (hf : IsRadialODESolutionOn q f df a) (hg : IsRadialODESolutionOn q g dg a)
    {r : ℝ} (hr : r ∈ Ioi a) :
    HasDerivAt (radialWronskian f df g dg) 0 r := by
  have hrpos : 0 < r := ha.trans hr
  have hd := (hasDerivAt_id r).mul
    (((hf.deriv r hr).mul (hg.second r hr)).sub
      ((hf.second r hr).mul (hg.deriv r hr)))
  convert hd using 1
  simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
  field_simp [hrpos.ne']
  ring

theorem radialWronskian_constant (ha : 0 < a)
    (hf : IsRadialODESolutionOn q f df a) (hg : IsRadialODESolutionOn q g dg a) :
    ∃ C : ℝ, ∀ r ∈ Ioi a, radialWronskian f df g dg r = C := by
  apply isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi
  · intro r hr
    exact (hasDerivAt_radialWronskian_zero ha hf hg hr).differentiableAt.differentiableWithinAt
  · intro r hr
    exact (hasDerivAt_radialWronskian_zero ha hf hg hr).deriv

/-- The weighted Wronskian is dominated by the four radial energy densities. -/
theorem abs_radialWronskian_le {r : ℝ} (hr : 0 ≤ r) (f df g dg : ℝ → ℝ) :
    |radialWronskian f df g dg r| ≤
      ((r * f r ^ 2 + r * df r ^ 2) + (r * g r ^ 2 + r * dg r ^ 2)) / 2 := by
  have hp : |f r * dg r| ≤ (f r ^ 2 + dg r ^ 2) / 2 := by
    apply abs_le.mpr
    constructor
    · nlinarith [sq_nonneg (f r + dg r)]
    · nlinarith [sq_nonneg (f r - dg r)]
  have hq : |df r * g r| ≤ (df r ^ 2 + g r ^ 2) / 2 := by
    apply abs_le.mpr
    constructor
    · nlinarith [sq_nonneg (df r + g r)]
    · nlinarith [sq_nonneg (df r - g r)]
  calc
    |radialWronskian f df g dg r| = r * |f r * dg r - df r * g r| := by
      rw [radialWronskian, abs_mul, abs_of_nonneg hr]
    _ ≤ r * (|f r * dg r| + |df r * g r|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) hr
    _ ≤ r * ((f r ^ 2 + dg r ^ 2) / 2 + (df r ^ 2 + g r ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hp hq) hr
    _ = _ := by ring

theorem radialWronskian_zero_of_integrable (ha : 0 < a)
    (hf : IsRadialODESolutionOn q f df a) (hg : IsRadialODESolutionOn q g dg a)
    (hfi : IntegrableOn (fun r => r * f r ^ 2) (Ioi a))
    (hdfi : IntegrableOn (fun r => r * df r ^ 2) (Ioi a))
    (hgi : IntegrableOn (fun r => r * g r ^ 2) (Ioi a))
    (hdgi : IntegrableOn (fun r => r * dg r ^ 2) (Ioi a)) :
    ∀ r ∈ Ioi a, radialWronskian f df g dg r = 0 := by
  obtain ⟨C, hC⟩ := radialWronskian_constant ha hf hg
  have hmajor := ((hfi.add hdfi).add (hgi.add hdgi)).div_const 2
  have hCi : IntegrableOn (fun _ : ℝ => C) (Ioi a) := by
    apply hmajor.mono' aestronglyMeasurable_const
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [← hC r hr, Real.norm_eq_abs]
    exact abs_radialWronskian_le (ha.trans hr).le f df g dg
  have hCzero : C = 0 := by
    simpa [integrableOn_const_iff, Real.volume_Ioi] using hCi
  exact fun r hr => (hC r hr).trans hCzero

/-- Integrability only on a smaller exterior tail suffices to force the
Wronskian to vanish on the whole interval of definition. -/
theorem radialWronskian_eq_zero_of_integrable_tail (ha : 0 < a)
    (hf : IsRadialODESolutionOn q f df a) (hg : IsRadialODESolutionOn q g dg a)
    {R : ℝ} (hR : a ≤ R)
    (hfi : IntegrableOn (fun r => r * f r ^ 2) (Ioi R))
    (hdfi : IntegrableOn (fun r => r * df r ^ 2) (Ioi R))
    (hgi : IntegrableOn (fun r => r * g r ^ 2) (Ioi R))
    (hdgi : IntegrableOn (fun r => r * dg r ^ 2) (Ioi R)) :
    ∀ r ∈ Ioi a, radialWronskian f df g dg r = 0 := by
  have htail := radialWronskian_zero_of_integrable (ha.trans_le hR)
    (hf.mono hR) (hg.mono hR) hfi hdfi hgi hdgi
  obtain ⟨C, hC⟩ := radialWronskian_constant ha hf hg
  have hCzero : C = 0 :=
    (hC (R + 1) (hR.trans_lt (lt_add_one R))).symm.trans (htail (R + 1) (lt_add_one R))
  exact fun r hr => (hC r hr).trans hCzero

/-- A zero Wronskian and a positive comparison solution fix the ratio on the
entire exterior interval. -/
theorem exists_eq_mul_of_radialWronskian_zero (ha : 0 < a)
    (hf : ∀ r ∈ Ioi a, HasDerivAt f (df r) r)
    (hg : ∀ r ∈ Ioi a, HasDerivAt g (dg r) r)
    (hzero : ∀ r ∈ Ioi a, radialWronskian f df g dg r = 0)
    (hgpos : ∀ r ∈ Ioi a, 0 < g r) :
    ∃ Γ : ℝ, ∀ r ∈ Ioi a, f r = Γ * g r := by
  have hratio : ∀ r ∈ Ioi a, HasDerivAt (fun x => f x / g x) 0 r := by
    intro r hr
    have hrne : r ≠ 0 := (ha.trans hr).ne'
    have hw : f r * dg r - df r * g r = 0 :=
      (mul_eq_zero.mp (hzero r hr)).resolve_left hrne
    have hn : df r * g r - f r * dg r = 0 := by linarith
    simpa only [hn, zero_div] using (hf r hr).div (hg r hr) (hgpos r hr).ne'
  obtain ⟨Γ, hΓ⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun r hr => (hratio r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hratio r hr).deriv)
  refine ⟨Γ, fun r hr => ?_⟩
  exact (div_eq_iff (hgpos r hr).ne').mp (hΓ r hr)

/-- Proportionality of two radial solutions with finite exterior energy. -/
theorem exists_eq_mul_of_radialODE_of_integrable (ha : 0 < a)
    (hf : IsRadialODESolutionOn q f df a) (hg : IsRadialODESolutionOn q g dg a)
    (hfi : IntegrableOn (fun r => r * f r ^ 2) (Ioi a))
    (hdfi : IntegrableOn (fun r => r * df r ^ 2) (Ioi a))
    (hgi : IntegrableOn (fun r => r * g r ^ 2) (Ioi a))
    (hdgi : IntegrableOn (fun r => r * dg r ^ 2) (Ioi a))
    (hgpos : ∀ r ∈ Ioi a, 0 < g r) :
    ∃ Γ : ℝ, ∀ r ∈ Ioi a, f r = Γ * g r :=
  exists_eq_mul_of_radialWronskian_zero ha hf.deriv hg.deriv
    (radialWronskian_zero_of_integrable ha hf hg hfi hdfi hgi hdgi) hgpos

/-- Exterior energy bounds away from the endpoint determine the ratio on
the original, larger interval. -/
theorem exists_eq_mul_of_radialODE_of_integrable_tail (ha : 0 < a)
    (hf : IsRadialODESolutionOn q f df a) (hg : IsRadialODESolutionOn q g dg a)
    {R : ℝ} (hR : a ≤ R)
    (hfi : IntegrableOn (fun r => r * f r ^ 2) (Ioi R))
    (hdfi : IntegrableOn (fun r => r * df r ^ 2) (Ioi R))
    (hgi : IntegrableOn (fun r => r * g r ^ 2) (Ioi R))
    (hdgi : IntegrableOn (fun r => r * dg r ^ 2) (Ioi R))
    (hgpos : ∀ r ∈ Ioi a, 0 < g r) :
    ∃ Γ : ℝ, ∀ r ∈ Ioi a, f r = Γ * g r :=
  exists_eq_mul_of_radialWronskian_zero ha hf.deriv hg.deriv
    (radialWronskian_eq_zero_of_integrable_tail ha hf hg hR hfi hdfi hgi hdgi) hgpos

end InfiniteZero
