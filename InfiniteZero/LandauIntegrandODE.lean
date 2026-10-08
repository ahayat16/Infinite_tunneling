import InfiniteZero.LandauKernel

/-! Exact radial and proper-time derivatives of the actual Landau integrand.
The radial differential expression is a total proper-time derivative. -/

noncomputable section
namespace InfiniteZero

def landauRadialSlope (b h τ : ℝ) : ℝ :=
  b / (2 * h) * (Real.cosh (b * τ) / Real.sinh (b * τ))

def landauIntegrandRadialDeriv (b h E r τ : ℝ) : ℝ :=
  -(landauRadialSlope b h τ * r) * landauIntegrand b h E r τ

def landauIntegrandRadialSecond (b h E r τ : ℝ) : ℝ :=
  ((landauRadialSlope b h τ * r) ^ 2 - landauRadialSlope b h τ) *
    landauIntegrand b h E r τ

theorem hasDerivAt_landauIntegrand_radius (b h E τ r : ℝ) :
    HasDerivAt (fun s => landauIntegrand b h E s τ)
      (landauIntegrandRadialDeriv b h E r τ) r := by
  have hp := ((((hasDerivAt_id r).pow 2).const_mul (b / 4)).mul_const
    (Real.cosh (b * τ) / Real.sinh (b * τ))).const_add (E * τ)
  have hd := ((hp.neg.div_const h).exp).const_mul (Real.sinh (b * τ))⁻¹
  dsimp only [Pi.neg_apply, Pi.pow_apply, id_eq] at hd
  convert hd using 1
  · ext s
    simp only [landauIntegrand, properTimePhase]
    congr 2
    ring
  · simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    unfold landauIntegrandRadialDeriv landauRadialSlope landauIntegrand properTimePhase
    ring_nf

theorem hasDerivAt_landauIntegrandRadialDeriv_radius (b h E τ r : ℝ) :
    HasDerivAt (fun s => landauIntegrandRadialDeriv b h E s τ)
      (landauIntegrandRadialSecond b h E r τ) r := by
  have hd := (((hasDerivAt_id r).const_mul (landauRadialSlope b h τ)).neg).mul
    (hasDerivAt_landauIntegrand_radius b h E τ r)
  dsimp only [Pi.neg_apply, Pi.mul_apply, id_eq] at hd
  convert hd using 1
  unfold landauIntegrandRadialSecond landauIntegrandRadialDeriv
  ring

theorem deriv_landauIntegrand_radius (b h E τ r : ℝ) :
    deriv (fun s => landauIntegrand b h E s τ) r =
      landauIntegrandRadialDeriv b h E r τ :=
  (hasDerivAt_landauIntegrand_radius b h E τ r).deriv

theorem deriv2_landauIntegrand_radius (b h E τ r : ℝ) :
    deriv (deriv (fun s => landauIntegrand b h E s τ)) r =
      landauIntegrandRadialSecond b h E r τ := by
  have heq : deriv (fun s => landauIntegrand b h E s τ) =
      fun s => landauIntegrandRadialDeriv b h E s τ :=
    funext (deriv_landauIntegrand_radius b h E τ)
  rw [heq]
  exact (hasDerivAt_landauIntegrandRadialDeriv_radius b h E τ r).deriv

/-- Exact derivative in the integration variable, away from its singular endpoint. -/
theorem hasDerivAt_landauIntegrand_time {b τ : ℝ} (hb : 0 < b) (hτ : 0 < τ)
    (h E r : ℝ) :
    HasDerivAt (landauIntegrand b h E r)
      ((-b * (Real.cosh (b * τ) / Real.sinh (b * τ)) -
        (E - b ^ 2 * r ^ 2 / (4 * Real.sinh (b * τ) ^ 2)) / h) *
          landauIntegrand b h E r τ) τ := by
  have hs : Real.sinh (b * τ) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos hb hτ)).ne'
  have hi := (((hasDerivAt_id τ).const_mul b).sinh).inv hs
  have he := (((hasDerivAt_properTimePhase hb hτ E r).neg).div_const h).exp
  dsimp only [Pi.inv_apply, Pi.neg_apply, id_eq] at hi he
  convert hi.mul he using 1
  simp only [Pi.inv_apply, mul_one]
  unfold landauIntegrand
  field_simp
  ring

/-- The radial magnetic differential expression is exactly minus h times
the proper-time derivative, before any exchange of derivatives and integrals. -/
theorem landauIntegrand_radial_ode {b h r τ : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hr : 0 < r) (hτ : 0 < τ) (E : ℝ) :
    -h ^ 2 * (landauIntegrandRadialSecond b h E r τ +
        r⁻¹ * landauIntegrandRadialDeriv b h E r τ) +
      (b ^ 2 * r ^ 2 / 4 + E) * landauIntegrand b h E r τ =
        -h * deriv (landauIntegrand b h E r) τ := by
  rw [(hasDerivAt_landauIntegrand_time hb hτ h E r).deriv]
  have hs : Real.sinh (b * τ) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos hb hτ)).ne'
  have hyp := Real.cosh_sq_sub_sinh_sq (b * τ)
  unfold landauIntegrandRadialSecond landauIntegrandRadialDeriv landauRadialSlope
  field_simp
  nlinarith [congrArg (fun t : ℝ =>
    b ^ 2 * r ^ 2 * landauIntegrand b h E r τ * t) hyp]

end InfiniteZero
