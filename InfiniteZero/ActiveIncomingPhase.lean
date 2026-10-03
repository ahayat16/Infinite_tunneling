import InfiniteZero.ActiveSaddleEnvelope

/-!
# The continuous real phase of the incoming active cell

The Gaussian leading factor has a positive real prefactor. Its two
critical phases therefore add to the magnetic geometric phase without
an argument choice. No active-cell asymptotic is assumed here.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace InfiniteZero.CuspParameters

def activeIncomingPhase (p : CuspParameters) (L coupling : ℝ) : ℝ :=
  coupling * Geometry.phaseStar p.b p.R L +
    2 * logFlatSaddlePhase p.β 2 p.tStar (p.activeSaddleSlope L) coupling⁻¹

theorem exists_continuousOn_activeIncomingPhase (p : CuspParameters) (L : ℝ) :
    ∃ T > 0, ContinuousOn (p.activeIncomingPhase L) (Ici T) := by
  obtain ⟨T, hT, hs⟩ :=
    exists_continuousOn_logFlatSaddlePhase_inv p.β 2 p.tStar (p.activeSaddleSlope L)
  refine ⟨T, hT, ?_⟩
  exact (continuousOn_id.mul continuousOn_const).add (continuousOn_const.mul hs)

theorem tendsto_activeIncomingPhase_div
    {p : CuspParameters} (hp : p.BasicConditions) (L : ℝ) :
    Tendsto (fun coupling : ℝ => p.activeIncomingPhase L coupling / coupling)
      atTop (𝓝 (Geometry.phaseStar p.b p.R L)) := by
  have hs := (tendsto_logFlatSaddlePhase_inv_div (k := (2 : ℝ)) hp.β_pos
    (hp.t₀_pos.trans hp.t₀_lt) (activeSaddleSlope_ne_zero hp L)).const_mul 2
  have ht := (tendsto_const_nhds (x := Geometry.phaseStar p.b p.R L)).add hs
  simp only [mul_zero, add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with coupling hc
  dsimp only [activeIncomingPhase]
  field_simp

theorem norm_exp_activeIncomingPhase (p : CuspParameters) (L coupling : ℝ) :
    ‖Complex.exp ((p.activeIncomingPhase L coupling : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem exp_geometric_mul_logFlatSaddleLeading_sq
    (p : CuspParameters) (L coupling : ℝ) :
    Complex.exp (((coupling * Geometry.phaseStar p.b p.R L : ℝ) : ℂ) * Complex.I) *
      logFlatSaddleLeading p.β 2 p.tStar (p.activeSaddleSlope L) coupling⁻¹ ^ 2 =
        ((logFlatSaddleLeadingSize p.β 2 p.tStar (p.activeSaddleSlope L) coupling⁻¹ ^ 2 : ℝ) : ℂ) *
          Complex.exp ((p.activeIncomingPhase L coupling : ℂ) * Complex.I) := by
  rw [logFlatSaddleLeading_eq_size_mul_phase, mul_pow]
  rw [pow_two (Complex.exp _), ← Complex.exp_add]
  rw [mul_left_comm, ← Complex.exp_add]
  simp only [Complex.ofReal_pow, activeIncomingPhase, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  congr 2
  ring

end InfiniteZero.CuspParameters
