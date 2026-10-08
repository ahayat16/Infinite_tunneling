import InfiniteZero.Construction
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Reflection preserves planar volume and exchanges the cusp supports

The existing coordinate reflection is promoted to a linear isometry
equivalence. Its change-of-variables identities concern the actual Euclidean
volume on `Plane`, with no parameter assumptions or integrability premises
needed for the Bochner integral equalities.
-/

noncomputable section
open Set MeasureTheory

namespace InfiniteZero.CuspParameters

def reflectionLinearIsometryEquiv : Plane ≃ₗᵢ[ℝ] Plane where
  toFun := reflection
  invFun := reflection
  left_inv := reflection_involutive
  right_inv := reflection_involutive
  map_add' x y := by
    ext i
    fin_cases i <;> simp [reflection, add_comm]
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [reflection]
  norm_map' := norm_reflection

@[simp] theorem reflectionLinearIsometryEquiv_apply (x : Plane) :
    reflectionLinearIsometryEquiv x = reflection x := rfl

@[simp] theorem reflectionLinearIsometryEquiv_symm_apply (x : Plane) :
    reflectionLinearIsometryEquiv.symm x = reflection x := rfl

theorem reflection_measurePreserving :
    MeasurePreserving reflection (volume : Measure Plane) volume :=
  reflectionLinearIsometryEquiv.measurePreserving

theorem reflection_measurableEmbedding : MeasurableEmbedding reflection :=
  reflectionLinearIsometryEquiv.toHomeomorph.toMeasurableEquiv.measurableEmbedding

theorem integral_comp_reflection {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : Plane → F) :
    (∫ x : Plane, g (reflection x)) = ∫ x : Plane, g x :=
  reflection_measurePreserving.integral_comp reflection_measurableEmbedding g

theorem integrable_comp_reflection_iff {F : Type*} [NormedAddCommGroup F]
    (g : Plane → F) : Integrable (g ∘ reflection) volume ↔ Integrable g volume :=
  reflection_measurePreserving.integrable_comp_emb reflection_measurableEmbedding

theorem setIntegral_comp_reflection {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : Plane → F) (s : Set Plane) :
    (∫ x in reflection ⁻¹' s, g (reflection x)) = ∫ x in s, g x :=
  reflection_measurePreserving.setIntegral_preimage_emb reflection_measurableEmbedding g s

theorem integrableOn_comp_reflection_iff {F : Type*} [NormedAddCommGroup F]
    (g : Plane → F) (s : Set Plane) :
    IntegrableOn (g ∘ reflection) (reflection ⁻¹' s) volume ↔ IntegrableOn g s volume :=
  (reflection_measurePreserving.restrict_preimage_emb reflection_measurableEmbedding s).integrable_comp_emb
    reflection_measurableEmbedding

theorem cuspMinus_tsupport_eq_preimage (p : CuspParameters) :
    tsupport p.cuspMinus = reflection ⁻¹' tsupport p.cuspPlus :=
  tsupport_comp_eq_preimage p.cuspPlus reflectionLinearIsometryEquiv.toHomeomorph

@[simp] theorem reflection_mem_cuspMinus_tsupport_iff (p : CuspParameters) (x : Plane) :
    reflection x ∈ tsupport p.cuspMinus ↔ x ∈ tsupport p.cuspPlus := by
  rw [cuspMinus_tsupport_eq_preimage]
  simp only [mem_preimage, reflection_involutive]

@[simp] theorem reflection_mem_cuspPlus_tsupport_iff (p : CuspParameters) (x : Plane) :
    reflection x ∈ tsupport p.cuspPlus ↔ x ∈ tsupport p.cuspMinus := by
  rw [cuspMinus_tsupport_eq_preimage]
  rfl

theorem cuspPlus_tsupport_eq_preimage (p : CuspParameters) :
    tsupport p.cuspPlus = reflection ⁻¹' tsupport p.cuspMinus := by
  ext x
  exact (reflection_mem_cuspMinus_tsupport_iff p x).symm

@[simp] theorem reflection_mem_cuspMinus_support_iff (p : CuspParameters) (x : Plane) :
    reflection x ∈ Function.support p.cuspMinus ↔ x ∈ Function.support p.cuspPlus := by
  simp only [Function.mem_support, cuspMinus_reflection]

@[simp] theorem reflection_mem_cuspPlus_support_iff (p : CuspParameters) (x : Plane) :
    reflection x ∈ Function.support p.cuspPlus ↔ x ∈ Function.support p.cuspMinus := Iff.rfl

theorem integral_cuspMinus_eq_reflection_cuspPlus {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (p : CuspParameters) (g : Plane → F) :
    (∫ x in tsupport p.cuspMinus, g x) =
      ∫ x in tsupport p.cuspPlus, g (reflection x) := by
  rw [cuspPlus_tsupport_eq_preimage]
  exact (setIntegral_comp_reflection g (tsupport p.cuspMinus)).symm

end InfiniteZero.CuspParameters
