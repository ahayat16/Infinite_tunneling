import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The two-cusp geometric certificate

These are the coordinate calculations in Proposition 2.6 and its formalisation
addition P2.6. All declarations in this file are proved without admissions.

`Point` is used only for coordinates. In particular, `sqNorm` and `length` below
are the Euclidean squared norm and length, not the norm of the product type.
The analytic action estimates are deliberately separate from these calculations.
-/

namespace InfiniteZero.Geometry

noncomputable section

abbrev Point := ℝ × ℝ

def reflect (p : Point) : Point := (p.1, -p.2)

def tipPlus (R : ℝ) : Point := (R / 2, Real.sqrt 3 * R / 2)

def tipMinus (R : ℝ) : Point := (R / 2, -(Real.sqrt 3 * R / 2))

def normalPlus : Point := (-1 / 2, Real.sqrt 3 / 2)

def normalMinus : Point := (-1 / 2, -(Real.sqrt 3 / 2))

def tangentPlus : Point := (-(Real.sqrt 3 / 2), -1 / 2)

def tangentMinus : Point := (-(Real.sqrt 3 / 2), 1 / 2)

def dot (p q : Point) : ℝ := p.1 * q.1 + p.2 * q.2

def wedge (p q : Point) : ℝ := p.1 * q.2 - p.2 * q.1

def sqNorm (p : Point) : ℝ := p.1 ^ 2 + p.2 ^ 2

def length (p : Point) : ℝ := Real.sqrt (sqNorm p)

/-- The bridge vector is the difference of the physical right and left tips,
up to an immaterial overall sign. The two wells have centers `(±L, 0)`. -/
def bridge (L : ℝ) (z w : Point) : Point := (z.1 + w.1 - 2 * L, z.2 + w.2)

def activeDistance (R L : ℝ) : ℝ := 2 * L - R

/-- Magnetic phase, equation (Phi). -/
def phase (b L : ℝ) (z w : Point) : ℝ :=
  b * (L * (z.2 - w.2) + wedge z w / 2)

/-- The positive coefficient of the leading oscillatory phase. -/
def phaseStar (b R L : ℝ) : ℝ := Real.sqrt 3 * b * R * (L - R / 4)

/-- Either outgoing normal derivative of the magnetic phase at the cross pair. -/
def phaseSlope (b L : ℝ) : ℝ := Real.sqrt 3 * b * L / 2

def normalLine (p n : Point) (t : ℝ) : Point := (p.1 + t * n.1, p.2 + t * n.2)

private theorem sqrtThree_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
  Real.sq_sqrt (by norm_num)

@[simp] theorem reflect_tipPlus (R : ℝ) : reflect (tipPlus R) = tipMinus R := rfl

@[simp] theorem reflect_normalPlus : reflect normalPlus = normalMinus := rfl

@[simp] theorem reflect_tangentPlus : reflect tangentPlus = tangentMinus := by
  norm_num [reflect, tangentPlus, tangentMinus]

theorem sqNorm_tipPlus (R : ℝ) : sqNorm (tipPlus R) = R ^ 2 := by
  dsimp [sqNorm, tipPlus]
  ring_nf
  rw [sqrtThree_sq]
  ring

theorem sqNorm_tipMinus (R : ℝ) : sqNorm (tipMinus R) = R ^ 2 := by
  dsimp [sqNorm, tipMinus]
  ring_nf
  rw [sqrtThree_sq]
  ring

theorem length_tipPlus {R : ℝ} (hR : 0 ≤ R) : length (tipPlus R) = R := by
  rw [length, sqNorm_tipPlus, Real.sqrt_sq hR]

theorem length_tipMinus {R : ℝ} (hR : 0 ≤ R) : length (tipMinus R) = R := by
  rw [length, sqNorm_tipMinus, Real.sqrt_sq hR]

theorem normalPlus_unit : sqNorm normalPlus = 1 := by
  norm_num [sqNorm, normalPlus, div_pow, sqrtThree_sq]

theorem normalMinus_unit : sqNorm normalMinus = 1 := by
  norm_num [sqNorm, normalMinus, div_pow, sqrtThree_sq]

theorem tangentPlus_unit : sqNorm tangentPlus = 1 := by
  norm_num [sqNorm, tangentPlus, div_pow, sqrtThree_sq]

theorem tangentMinus_unit : sqNorm tangentMinus = 1 := by
  norm_num [sqNorm, tangentMinus, div_pow, sqrtThree_sq]

theorem normalPlus_dot_tangentPlus : dot normalPlus tangentPlus = 0 := by
  dsimp [dot, normalPlus, tangentPlus]
  ring

theorem normalMinus_dot_tangentMinus : dot normalMinus tangentMinus = 0 := by
  dsimp [dot, normalMinus, tangentMinus]
  ring

theorem normalPlus_wedge_tangentPlus : wedge normalPlus tangentPlus = 1 := by
  dsimp [wedge, normalPlus, tangentPlus]
  nlinarith [sqrtThree_sq]

theorem normalMinus_wedge_tangentMinus : wedge normalMinus tangentMinus = -1 := by
  dsimp [wedge, normalMinus, tangentMinus]
  nlinarith [sqrtThree_sq]

theorem tipPlus_dot_normalPlus (R : ℝ) : dot (tipPlus R) normalPlus = R / 2 := by
  dsimp [dot, tipPlus, normalPlus]
  ring_nf
  rw [sqrtThree_sq]
  ring

theorem tipMinus_dot_normalMinus (R : ℝ) : dot (tipMinus R) normalMinus = R / 2 := by
  dsimp [dot, tipMinus, normalMinus]
  ring_nf
  rw [sqrtThree_sq]
  ring

theorem bridge_cross (R L : ℝ) :
    bridge L (tipPlus R) (tipMinus R) = (-activeDistance R L, 0) := by
  ext <;> dsimp [bridge, tipPlus, tipMinus, activeDistance] <;> ring

theorem bridge_same_plus (R L : ℝ) :
    bridge L (tipPlus R) (tipPlus R) = (-activeDistance R L, Real.sqrt 3 * R) := by
  ext <;> dsimp [bridge, tipPlus, activeDistance] <;> ring

theorem bridge_same_minus (R L : ℝ) :
    bridge L (tipMinus R) (tipMinus R) = (-activeDistance R L, -(Real.sqrt 3 * R)) := by
  ext <;> dsimp [bridge, tipMinus, activeDistance] <;> ring

theorem sqNorm_bridge_cross (R L : ℝ) :
    sqNorm (bridge L (tipPlus R) (tipMinus R)) = activeDistance R L ^ 2 := by
  rw [bridge_cross]
  simp [sqNorm]

theorem sqNorm_bridge_same_plus (R L : ℝ) :
    sqNorm (bridge L (tipPlus R) (tipPlus R)) =
      activeDistance R L ^ 2 + 3 * R ^ 2 := by
  rw [bridge_same_plus]
  simp [sqNorm, mul_pow]

theorem sqNorm_bridge_same_minus (R L : ℝ) :
    sqNorm (bridge L (tipMinus R) (tipMinus R)) =
      activeDistance R L ^ 2 + 3 * R ^ 2 := by
  rw [bridge_same_minus]
  simp [sqNorm, mul_pow]

theorem activeDistance_pos {R L : ℝ} (hL : R < 2 * L) : 0 < activeDistance R L :=
  sub_pos.mpr hL

theorem length_bridge_cross {R L : ℝ} (hL : R < 2 * L) :
    length (bridge L (tipPlus R) (tipMinus R)) = activeDistance R L := by
  rw [length, sqNorm_bridge_cross, Real.sqrt_sq (activeDistance_pos hL).le]

theorem same_cusp_sq_gap (R L : ℝ) :
    sqNorm (bridge L (tipPlus R) (tipPlus R)) -
      sqNorm (bridge L (tipPlus R) (tipMinus R)) = 3 * R ^ 2 := by
  rw [sqNorm_bridge_same_plus, sqNorm_bridge_cross]
  ring

theorem same_cusp_sq_gap_pos {R : ℝ} (hR : 0 < R) (L : ℝ) :
    0 < sqNorm (bridge L (tipPlus R) (tipPlus R)) -
      sqNorm (bridge L (tipPlus R) (tipMinus R)) := by
  rw [same_cusp_sq_gap]
  positivity

theorem phase_at_tips (b R L : ℝ) :
    phase b L (tipPlus R) (tipMinus R) = phaseStar b R L := by
  dsimp [phase, wedge, tipPlus, tipMinus, phaseStar]
  ring

theorem phase_reflect (b L : ℝ) (z w : Point) :
    phase b L (reflect z) (reflect w) = -phase b L z w := by
  dsimp [phase, reflect, wedge]
  ring

theorem phaseStar_pos {b R L : ℝ} (hb : 0 < b) (hR : 0 < R) (hL : R < 2 * L) :
    0 < phaseStar b R L := by
  have h : 0 < L - R / 4 := by linarith
  unfold phaseStar
  positivity

theorem phaseSlope_pos {b L : ℝ} (hb : 0 < b) (hL : 0 < L) :
    0 < phaseSlope b L := by
  unfold phaseSlope
  positivity

theorem phase_normalLine_plus (b R L t : ℝ) :
    phase b L (normalLine (tipPlus R) normalPlus t) (tipMinus R) =
      phaseStar b R L + t * phaseSlope b L := by
  dsimp [phase, wedge, normalLine, tipPlus, tipMinus, normalPlus, phaseStar, phaseSlope]
  ring

theorem phase_normalLine_minus (b R L t : ℝ) :
    phase b L (tipPlus R) (normalLine (tipMinus R) normalMinus t) =
      phaseStar b R L + t * phaseSlope b L := by
  dsimp [phase, wedge, normalLine, tipPlus, tipMinus, normalMinus, phaseStar, phaseSlope]
  ring

theorem hasDerivAt_phase_normal_plus (b R L t : ℝ) :
    HasDerivAt (fun s => phase b L (normalLine (tipPlus R) normalPlus s) (tipMinus R))
      (phaseSlope b L) t := by
  simp_rw [phase_normalLine_plus]
  simpa using ((hasDerivAt_id t).mul_const (phaseSlope b L)).const_add (phaseStar b R L)

theorem hasDerivAt_phase_normal_minus (b R L t : ℝ) :
    HasDerivAt (fun s => phase b L (tipPlus R) (normalLine (tipMinus R) normalMinus s))
      (phaseSlope b L) t := by
  simp_rw [phase_normalLine_minus]
  simpa using ((hasDerivAt_id t).mul_const (phaseSlope b L)).const_add (phaseStar b R L)

end

end InfiniteZero.Geometry
