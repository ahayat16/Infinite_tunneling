import InfiniteZero.MagneticFormPotentialComparison
import InfiniteZero.MagneticLocalizedForm

/-!
# Continuity of the concrete parity energies at positive coupling

The infimum is bounded below by comparison with the nonnegative free form.
A unitary global dilation places all couplings on the same normalized
parity test set at fixed magnetic field. The uniform potential comparison
then makes the dilated infimum Lipschitz. No spectral attainment or
identification with a sector eigenvalue is assumed.
-/

noncomputable section
open Set
open scoped ContDiff

namespace InfiniteZero

def parityTestFormValues (b coupling : ℝ) (V : Potential) (even : Bool) : Set ℝ :=
  {E | ∃ ψ : Wavefunction, IsNormalizedTest ψ ∧ HasParity even ψ ∧
    magneticForm b coupling V ψ = E}

def parityTestEnergy (b coupling : ℝ) (V : Potential) (even : Bool) : ℝ :=
  sInf (parityTestFormValues b coupling V even)

theorem parityTestFormValues_nonempty (b coupling : ℝ) (V : Potential) (even : Bool)
    (hne : ∃ ψ : Wavefunction, IsNormalizedTest ψ ∧ HasParity even ψ) :
    (parityTestFormValues b coupling V even).Nonempty := by
  obtain ⟨ψ, hψ, hp⟩ := hne
  exact ⟨magneticForm b coupling V ψ, ψ, hψ, hp, rfl⟩

/-- Lower boundedness is obtained from the actual free form, not from spectral data. -/
theorem parityTestFormValues_bddBelow (b coupling : ℝ) (even : Bool) {V : Potential}
    (hV : Continuous V) {B : ℝ} (hB : ∀ x, |V x| ≤ B) :
    BddBelow (parityTestFormValues b coupling V even) := by
  refine ⟨-(coupling ^ 2 * B), ?_⟩
  rintro E ⟨ψ, hψ, hp, rfl⟩
  have h := abs_magneticForm_sub_le (W := 0) b coupling hV continuous_const
    hψ.1 (δ := B) (fun x => by simpa only [Pi.zero_apply, sub_zero] using hB x)
  rw [hψ.2, mul_one] at h
  have hfree := magneticForm_zero_potential_nonneg b coupling ψ
  have hlo := (abs_le.mp h).1
  linarith

private theorem bounded_magneticDilationPotential {V : Potential} {B c : ℝ}
    (hB : ∀ x, |V x| ≤ B) (hc : 0 < c) (x : Plane) :
    |magneticDilationPotential V c x| ≤ c * B := by
  rw [magneticDilationPotential, abs_mul, abs_of_pos hc]
  exact mul_le_mul_of_nonneg_left (hB _) hc.le

/-- Exact relation between the original test infimum and its fixed-field dilation. -/
theorem parityTestEnergy_eq_mul_dilated (b : ℝ) (even : Bool) {V : Potential}
    (hV : Continuous V) {B : ℝ} (hB : ∀ x, |V x| ≤ B)
    (hne : ∃ ψ : Wavefunction, IsNormalizedTest ψ ∧ HasParity even ψ)
    {c : ℝ} (hc : 0 < c) :
    parityTestEnergy b c V even =
      c * parityTestEnergy b 1 (magneticDilationPotential V c) even := by
  have hD : BddBelow (parityTestFormValues b 1 (magneticDilationPotential V c) even) :=
    parityTestFormValues_bddBelow b 1 even (continuous_magneticDilationPotential hV c)
      (bounded_magneticDilationPotential hB hc)
  have hO := parityTestFormValues_bddBelow b c even hV hB
  apply le_antisymm
  · have hl : c⁻¹ * parityTestEnergy b c V even ≤
        parityTestEnergy b 1 (magneticDilationPotential V c) even := by
      apply le_csInf (parityTestFormValues_nonempty b 1 _ even hne)
      rintro E ⟨ψ, hψ, hp, rfl⟩
      let u := magneticDilation c⁻¹ ψ
      have hu : IsNormalizedTest u := hψ.magneticDilation (inv_pos.mpr hc)
      have hup : HasParity even u := hp.magneticDilation c⁻¹
      have hinf : parityTestEnergy b c V even ≤ magneticForm b c V u :=
        csInf_le hO ⟨u, hu, hup, rfl⟩
      have hf := magneticForm_magneticDilation b V hc hu.1
      change magneticForm b 1 (magneticDilationPotential V c) (magneticDilation c u) = _ at hf
      have hcancel : magneticDilation c u = ψ := magneticDilation_cancel_inv hc ψ
      rw [hcancel] at hf
      rw [hf]
      exact mul_le_mul_of_nonneg_left hinf (inv_nonneg.mpr hc.le)
    have hm := mul_le_mul_of_nonneg_left hl hc.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] using hm
  · apply le_csInf (parityTestFormValues_nonempty b c V even hne)
    rintro E ⟨ψ, hψ, hp, rfl⟩
    have hinf : parityTestEnergy b 1 (magneticDilationPotential V c) even ≤
        magneticForm b 1 (magneticDilationPotential V c) (magneticDilation c ψ) :=
      csInf_le hD ⟨magneticDilation c ψ, hψ.magneticDilation hc,
        hp.magneticDilation c, rfl⟩
    have hf := magneticForm_magneticDilation b V hc hψ.1
    change magneticForm b 1 (magneticDilationPotential V c) (magneticDilation c ψ) = _ at hf
    rw [hf] at hinf
    have hm := mul_le_mul_of_nonneg_left hinf hc.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] using hm

/-- Uniform test bounds pass to the two nonempty, lower-bounded infima. -/
theorem parityTestEnergy_le_add_of_form_le (b coupling : ℝ) (even : Bool)
    {V W : Potential}
    (hV : BddBelow (parityTestFormValues b coupling V even))
    (hne : ∃ ψ : Wavefunction, IsNormalizedTest ψ ∧ HasParity even ψ)
    {δ : ℝ}
    (hbound : ∀ ψ : Wavefunction, IsNormalizedTest ψ → HasParity even ψ →
      magneticForm b coupling V ψ ≤ magneticForm b coupling W ψ + δ) :
    parityTestEnergy b coupling V even ≤ parityTestEnergy b coupling W even + δ := by
  have hl : parityTestEnergy b coupling V even - δ ≤ parityTestEnergy b coupling W even := by
    apply le_csInf (parityTestFormValues_nonempty b coupling W even hne)
    rintro E ⟨ψ, hψ, hp, rfl⟩
    have hinf : parityTestEnergy b coupling V even ≤ magneticForm b coupling V ψ :=
      csInf_le hV ⟨ψ, hψ, hp, rfl⟩
    have h := hbound ψ hψ hp
    linarith
  linarith

theorem exists_dilated_parityTestEnergy_lipschitz {V : Potential}
    (hV : ContDiff ℝ ∞ V) (hcompact : HasCompactSupport V) (even : Bool)
    (hne : ∃ ψ : Wavefunction, IsNormalizedTest ψ ∧ HasParity even ψ) :
    ∃ C > 0, ∀ (b c μ : ℝ), 0 < c → 0 < μ →
      |parityTestEnergy b 1 (magneticDilationPotential V c) even -
        parityTestEnergy b 1 (magneticDilationPotential V μ) even| ≤ C * |c - μ| := by
  obtain ⟨C, hC, hform⟩ := exists_magneticForm_dilationPotential_lipschitz hV hcompact
  obtain ⟨B, _, hb⟩ := (hcompact.isCompact_range hV.continuous).isBounded.exists_pos_norm_le
  have hB (x : Plane) : |V x| ≤ B := hb _ ⟨x, rfl⟩
  have hle (b c μ : ℝ) (hc : 0 < c) (hμ : 0 < μ) :
      parityTestEnergy b 1 (magneticDilationPotential V c) even ≤
        parityTestEnergy b 1 (magneticDilationPotential V μ) even + C * |c - μ| := by
    apply parityTestEnergy_le_add_of_form_le b 1 even
      (parityTestFormValues_bddBelow b 1 even (continuous_magneticDilationPotential hV.continuous c)
        (bounded_magneticDilationPotential hB hc)) hne
    intro ψ hψ _
    have h := (abs_le.mp (hform b c μ hc hμ ψ hψ)).2
    linarith
  refine ⟨C, hC, fun b c μ hc hμ => abs_le.mpr ⟨?_, ?_⟩⟩
  · have h := hle b μ c hμ hc
    rw [abs_sub_comm μ c] at h
    linarith
  · have h := hle b c μ hc hμ
    linarith

theorem continuousOn_parityTestEnergy (b : ℝ) {V : Potential}
    (hV : ContDiff ℝ ∞ V) (hcompact : HasCompactSupport V) (even : Bool)
    (hne : ∃ ψ : Wavefunction, IsNormalizedTest ψ ∧ HasParity even ψ) :
    ContinuousOn (fun c : ℝ => parityTestEnergy b c V even) (Ioi 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_dilated_parityTestEnergy_lipschitz hV hcompact even hne
  have hLip : LipschitzOnWith ⟨C, hC.le⟩
      (fun c : ℝ => parityTestEnergy b 1 (magneticDilationPotential V c) even) (Ioi 0) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro c hc μ hμ
    simpa only [Real.dist_eq] using hbound b c μ hc hμ
  obtain ⟨B, _, hb⟩ := (hcompact.isCompact_range hV.continuous).isBounded.exists_pos_norm_le
  have hEq : EqOn (fun c : ℝ => parityTestEnergy b c V even)
      (fun c : ℝ => c * parityTestEnergy b 1 (magneticDilationPotential V c) even) (Ioi 0) := by
    intro c hc
    exact parityTestEnergy_eq_mul_dilated b even hV.continuous (fun x => hb _ ⟨x, rfl⟩) hne hc
  exact (continuousOn_id.mul hLip.continuousOn).congr hEq

/-- Continuity of the actual parity energies, with nonemptiness as the only test input. -/
theorem continuousOn_parityEnergy (b L : ℝ) (even : Bool) {v : Potential}
    (hv : ContDiff ℝ ∞ v) (hcompact : HasCompactSupport v)
    (hne : ∃ ψ : Wavefunction, IsNormalizedTest ψ ∧ HasParity even ψ) :
    ContinuousOn (fun coupling : ℝ => parityEnergy b v L coupling even) (Ioi 0) := by
  have hV : ContDiff ℝ ∞ (doubleWellPotential v L) :=
    (hv.comp (contDiff_id.add contDiff_const)).add
      (hv.comp (contDiff_id.neg.add contDiff_const))
  have hL : HasCompactSupport (fun x : Plane => v (x + displacement L)) :=
    hcompact.comp_homeomorph (Homeomorph.addRight (displacement L))
  have hR : HasCompactSupport (fun x : Plane => v (-x + displacement L)) :=
    hL.comp_homeomorph (Homeomorph.neg Plane)
  exact continuousOn_parityTestEnergy b hV (hL.add hR) even hne

end InfiniteZero
