import InfiniteZero.AtomicCuspDoubleRayShift
import InfiniteZero.CuspSaddleMultiplier

/-!
# Exact centering of the double atomic contour at its saddle

A real translation in each logarithmic coordinate preserves the product
measure. Its preimage of the two truncated rays is precisely the active
saddle product domain. This identity does not require integrability or
positivity hypotheses and does not perform a complex contour deformation.
-/

noncomputable section

open MeasureTheory Set Filter

namespace InfiniteZero.CuspParameters

/-- The logarithmic integrand on the two saddle rays, after centering their
real coordinates, is exactly the saddle product times the physical multiplier. -/
theorem atomicCuspLogProduct_translate_saddle (p : CuspParameters)
    (L h s r : ℝ) (q : ℝ × ℝ) :
    let c := p.activeSaddleSlope L
    let w := logFlatSaddleRoot p.β 2 p.tStar c h
    let z := logFlatComplexCritical p.β 2 w
    p.atomicCuspLogProduct L h s r w.im w.im (q.1 + z.re, q.2 + z.re) =
      logFlatSaddleProductIntegrand p.β 2 p.tStar c c h q *
        p.atomicCuspSaddleMultiplier L h s r q := by
  dsimp only
  let w := logFlatSaddleRoot p.β 2 p.tStar (p.activeSaddleSlope L) h
  let z := logFlatComplexCritical p.β 2 w
  have he (t : ℝ) : ((t + z.re : ℝ) : ℂ) + (w.im : ℂ) * Complex.I =
      z + (t : ℂ) := by
    have hi : z.im = w.im := by
      simp only [z, logFlatComplexCritical, Complex.sub_im, Complex.ofReal_im, sub_zero]
    apply Complex.ext <;> simp [hi, add_comm]
  change p.atomicCuspLogProduct L h s r w.im w.im
    (q.1 + z.re, q.2 + z.re) = _
  simp only [atomicCuspLogProduct, he, logFlatContourFunction,
    logFlatSaddleProductIntegrand, logFlatSaddleContourIntegrand,
    atomicCuspSaddleMultiplier, saddleNormalPoint, w, z]

/-- Exact transport of the two shifted logarithmic rays to the active
product domain centered at the same critical point. -/
theorem atomicCuspLogDoubleIntegral_saddle_eq (p : CuspParameters)
    (L h s r : ℝ) :
    let c := p.activeSaddleSlope L
    let w := logFlatSaddleRoot p.β 2 p.tStar c h
    p.atomicCuspLogDoubleIntegral L h s r w.im w.im =
      ∫ q in activeSaddleProductDomain p.β 2 p.tStar c h,
        logFlatSaddleProductIntegrand p.β 2 p.tStar c c h q *
          p.atomicCuspSaddleMultiplier L h s r q
          ∂(volume : Measure ℝ).prod volume := by
  dsimp only
  let w := logFlatSaddleRoot p.β 2 p.tStar (p.activeSaddleSlope L) h
  let z := logFlatComplexCritical p.β 2 w
  let f := p.atomicCuspLogProduct L h s r w.im w.im
  let shift := Prod.map (fun x : ℝ => x + z.re) (fun y : ℝ => y + z.re)
  have hpre : shift ⁻¹'
      (Ioi (logFlatActiveLogCut h) ×ˢ Ioi (logFlatActiveLogCut h)) =
      activeSaddleProductDomain p.β 2 p.tStar (p.activeSaddleSlope L) h := by
    ext q
    simp only [shift, mem_preimage, mem_prod, mem_Ioi, Prod.map_fst, Prod.map_snd,
      activeSaddleProductDomain]
    change (_ < q.1 + z.re ∧ _ < q.2 + z.re) ↔
      (_ - z.re < q.1 ∧ _ - z.re < q.2)
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hmp := (measurePreserving_add_right (volume : Measure ℝ) z.re).prod
    (measurePreserving_add_right (volume : Measure ℝ) z.re)
  have hi := hmp.setIntegral_preimage_emb
    ((MeasurableEquiv.addRight z.re).prodCongr
      (MeasurableEquiv.addRight z.re)).measurableEmbedding
    f (Ioi (logFlatActiveLogCut h) ×ˢ Ioi (logFlatActiveLogCut h))
  change (∫ q in shift ⁻¹'
      (Ioi (logFlatActiveLogCut h) ×ˢ Ioi (logFlatActiveLogCut h)), f (shift q)
        ∂(volume : Measure ℝ).prod volume) = _ at hi
  rw [hpre] at hi
  change (∫ q in Ioi (logFlatActiveLogCut h) ×ˢ Ioi (logFlatActiveLogCut h),
    f q ∂(volume : Measure ℝ).prod volume) = _
  rw [← hi]
  apply integral_congr_ae
  filter_upwards [] with q
  exact atomicCuspLogProduct_translate_saddle p L h s r q

end InfiniteZero.CuspParameters
