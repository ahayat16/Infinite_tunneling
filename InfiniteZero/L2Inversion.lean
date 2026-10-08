import InfiniteZero.OperatorBridge

/-!
# Spatial inversion on the physical Hilbert space

Pullback by `x ↦ -x` preserves planar volume and defines a complex-linear
isometric involution on the actual `L²` classes. Its two eigenspace equations
agree with the existing almost-everywhere definition of parity.
-/

noncomputable section
open MeasureTheory

namespace InfiniteZero

private def l2InversionMap : L2Space →ₗᵢ[ℂ] L2Space :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : Plane => -x) volume.measurePreserving_neg

private theorem l2InversionMap_involutive : Function.Involutive l2InversionMap := by
  intro u
  change Lp.compMeasurePreserving (fun x : Plane => -x) volume.measurePreserving_neg
    (Lp.compMeasurePreserving (fun x : Plane => -x) volume.measurePreserving_neg u) = u
  rw [← Lp.compMeasurePreserving_comp_apply]
  simpa only [Function.comp_def, neg_neg] using Lp.compMeasurePreserving_id_apply u

def l2Inversion : L2Space ≃ₗᵢ[ℂ] L2Space where
  toFun := l2InversionMap
  invFun := l2InversionMap
  left_inv := l2InversionMap_involutive
  right_inv := l2InversionMap_involutive
  map_add' := l2InversionMap.map_add
  map_smul' := l2InversionMap.map_smul
  norm_map' := l2InversionMap.norm_map

@[simp] theorem l2Inversion_apply_twice (u : L2Space) :
    l2Inversion (l2Inversion u) = u := l2InversionMap_involutive u

@[simp] theorem l2Inversion_symm_apply (u : L2Space) :
    l2Inversion.symm u = l2Inversion u := rfl

theorem l2Inversion_coeFn (u : L2Space) :
    (l2Inversion u : Plane → ℂ) =ᵐ[volume] fun x => u (-x) :=
  Lp.coeFn_compMeasurePreserving u volume.measurePreserving_neg

theorem Represents.inversion {u : L2Space} {ψ : Wavefunction}
    (hu : Represents u ψ) : Represents (l2Inversion u) (fun x => ψ (-x)) :=
  (l2Inversion_coeFn u).trans (volume.measurePreserving_neg.quasiMeasurePreserving.ae hu)

theorem l2Inversion_eq_iff_hasL2Parity (even : Bool) (u : L2Space) :
    l2Inversion u = (if even then u else -u) ↔ HasL2Parity even u := by
  cases even
  · change l2Inversion u = -u ↔ ∀ᵐ x : Plane, u (-x) = -u x
    constructor
    · intro h
      have hinv := l2Inversion_coeFn u
      rw [h] at hinv
      filter_upwards [hinv, Lp.coeFn_neg u] with x hx hn
      exact hx.symm.trans hn
    · intro h
      apply Lp.ext
      filter_upwards [l2Inversion_coeFn u, h, Lp.coeFn_neg u] with x hx hp hn
      exact (hx.trans hp).trans hn.symm
  · change l2Inversion u = u ↔ ∀ᵐ x : Plane, u (-x) = u x
    constructor
    · intro h
      have hinv := l2Inversion_coeFn u
      rw [h] at hinv
      exact hinv.symm
    · intro h
      exact Lp.ext ((l2Inversion_coeFn u).trans h)

@[simp] theorem norm_l2Inversion (u : L2Space) : ‖l2Inversion u‖ = ‖u‖ :=
  l2Inversion.norm_map u

@[simp] theorem inner_l2Inversion (u v : L2Space) :
    inner ℂ (l2Inversion u) (l2Inversion v) = inner ℂ u v :=
  l2Inversion.inner_map_map u v

end InfiniteZero
