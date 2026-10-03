import InfiniteZero.RadialCoreProfileEstimates

/-!
# A pointwise upper bound for normalized decreasing radial states

Inside a ball of radius `r`, positivity and radial monotonicity make the
density at least the squared profile value at `r`. The exact planar ball
volume and unit mass therefore bound that value by `1 / (sqrt π * r)`.
For the actual core ground state, monotonicity is supplied by its proved
radial equation. No energy or asymptotic estimate is an additional input.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero

/-- The value at a positive radius controls the mass of the whole smaller
ball from below. No continuity or differentiability hypothesis is needed. -/
theorem realRadialProfile_sq_mul_ball_volume_le_mass_ball {r : ℝ} (hr : 0 < r)
    {φ : Wavefunction} (hφ : MemLp φ 2 volume) (hpos : IsPositiveRadial φ)
    (hmono : AntitoneOn (realRadialProfile φ) (Ici 0)) :
    Real.pi * r ^ 2 * (realRadialProfile φ r) ^ 2 ≤
      ∫ x in Metric.ball (0 : Plane) r, ‖φ x‖ ^ 2 := by
  have hbound (x : Plane) (hx : x ∈ Metric.ball (0 : Plane) r) :
      (realRadialProfile φ r) ^ 2 ≤ ‖φ x‖ ^ 2 := by
    have hxr : ‖x‖ ≤ r := by
      exact (by simpa only [Metric.mem_ball, dist_zero_right] using hx : ‖x‖ < r).le
    rw [hpos.radial x, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    apply (sq_le_sq₀ (hpos.profile_pos r).le (hpos.profile_pos ‖x‖).le).mpr
    exact hmono (norm_nonneg x) hr.le hxr
  have hvol : volume.real (Metric.ball (0 : Plane) r) = Real.pi * r ^ 2 := by
    simp [Measure.real, EuclideanSpace.volume_ball_fin_two, hr.le,
      Real.pi_pos.le, mul_comm]
  calc
    _ = ∫ _x in Metric.ball (0 : Plane) r, (realRadialProfile φ r) ^ 2 := by
      rw [setIntegral_const, smul_eq_mul, hvol]
    _ ≤ _ := setIntegral_mono_on
      (integrableOn_const measure_ball_lt_top.ne)
      hφ.norm.integrable_sq.integrableOn measurableSet_ball hbound

/-- A normalized positive decreasing radial state is bounded at every
strictly positive radius, uniformly in the state itself. -/
theorem realRadialProfile_le_inv_sqrt_pi_mul_radius {r : ℝ} (hr : 0 < r)
    {φ : Wavefunction} (hφ : MemLp φ 2 volume) (hmass : mass φ = 1)
    (hpos : IsPositiveRadial φ) (hmono : AntitoneOn (realRadialProfile φ) (Ici 0)) :
    realRadialProfile φ r ≤ 1 / (Real.sqrt Real.pi * r) := by
  have hball := realRadialProfile_sq_mul_ball_volume_le_mass_ball hr hφ hpos hmono
  have htotal : (∫ x in Metric.ball (0 : Plane) r, ‖φ x‖ ^ 2) ≤ mass φ :=
    setIntegral_le_integral hφ.norm.integrable_sq
      (Filter.Eventually.of_forall fun x => sq_nonneg ‖φ x‖)
  have hsq : Real.pi * r ^ 2 * (realRadialProfile φ r) ^ 2 ≤ 1 := by
    simpa only [hmass] using hball.trans htotal
  have hden : 0 < Real.sqrt Real.pi * r := mul_pos (Real.sqrt_pos.mpr Real.pi_pos) hr
  apply (le_div_iff₀ hden).mpr
  apply (sq_le_sq₀ (mul_nonneg (hpos.profile_pos r).le hden.le) zero_le_one).mp
  calc
    (realRadialProfile φ r * (Real.sqrt Real.pi * r)) ^ 2 =
        Real.pi * r ^ 2 * (realRadialProfile φ r) ^ 2 := by
      simp only [mul_pow, Real.sq_sqrt Real.pi_pos.le]
      ring
    _ ≤ 1 := hsq
    _ = 1 ^ 2 := by norm_num

/-- The same estimate expressed directly for the wavefunction on the plane. -/
theorem norm_le_inv_sqrt_pi_mul_norm_of_positive_radial
    {φ : Wavefunction} (hφ : MemLp φ 2 volume) (hmass : mass φ = 1)
    (hpos : IsPositiveRadial φ) (hmono : AntitoneOn (realRadialProfile φ) (Ici 0))
    {x : Plane} (hx : 0 < ‖x‖) :
    ‖φ x‖ ≤ 1 / (Real.sqrt Real.pi * ‖x‖) := by
  rw [hpos.radial x, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (hpos.profile_pos ‖x‖)]
  exact realRadialProfile_le_inv_sqrt_pi_mul_radius hx hφ hmass hpos hmono

/-- The actual positive radial core ground state has the pointwise bound.
Its radial monotonicity follows from the concrete core ODE. -/
theorem IsAtomicGroundState.core_profile_le_inv_sqrt_pi_mul_radius
    {b coupling : ℝ} {p : CuspParameters} {φ : Wavefunction}
    (hr₀ : 0 < p.r₀) (hφ : IsAtomicGroundState b p.core coupling φ)
    (hpos : IsPositiveRadial φ) {r : ℝ} (hr : 0 < r) :
    realRadialProfile φ r ≤ 1 / (Real.sqrt Real.pi * r) :=
  realRadialProfile_le_inv_sqrt_pi_mul_radius hr hφ.1.2.1 hφ.2 hpos
    (hφ.core_profile_antitone hr₀ hpos)

/-- A bound on every nonzero point, with no condition on the coupling or
the ground energy beyond the true normalized ground-state hypotheses. -/
theorem IsAtomicGroundState.core_norm_le_inv_sqrt_pi_mul_norm
    {b coupling : ℝ} {p : CuspParameters} {φ : Wavefunction}
    (hr₀ : 0 < p.r₀) (hφ : IsAtomicGroundState b p.core coupling φ)
    (hpos : IsPositiveRadial φ) {x : Plane} (hx : 0 < ‖x‖) :
    ‖φ x‖ ≤ 1 / (Real.sqrt Real.pi * ‖x‖) :=
  norm_le_inv_sqrt_pi_mul_norm_of_positive_radial hφ.1.2.1 hφ.2 hpos
    (hφ.core_profile_antitone hr₀ hpos) hx

end InfiniteZero
