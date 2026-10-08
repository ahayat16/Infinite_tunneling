import InfiniteZero.OperatorBridge
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Exact scalar Schur reduction

The complement block is an actual linear equivalence between the complement
domain and range. Eliminating it proves the dimension of the full kernel;
no simplicity assumption on that kernel is used.
-/

noncomputable section

namespace InfiniteZero

variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- The scalar Schur complement of an invertible complement block. -/
def schurScalar (a : ℂ) (A : V ≃ₗ[ℂ] W) (B : W) (C : V →ₗ[ℂ] ℂ) : ℂ :=
  a - C (A.symm B)

/-- The full block map, allowing distinct complement domain and range. -/
def schurBlock (a : ℂ) (A : V ≃ₗ[ℂ] W) (B : W) (C : V →ₗ[ℂ] ℂ) :
    (ℂ × V) →ₗ[ℂ] (ℂ × W) where
  toFun u := (a * u.1 + C u.2, u.1 • B + A u.2)
  map_add' u v := by
    ext <;> simp [mul_add, add_smul] <;> abel
  map_smul' c u := by
    ext <;> simp [smul_add, smul_smul]
    ring

@[simp] theorem schurBlock_apply (a : ℂ) (A : V ≃ₗ[ℂ] W) (B : W)
    (C : V →ₗ[ℂ] ℂ) (c : ℂ) (η : V) :
    schurBlock a A B C (c, η) = (a * c + C η, c • B + A η) := rfl

/-- Exact elimination of the complement coordinate. -/
theorem schurBlock_eq_zero_iff (a : ℂ) (A : V ≃ₗ[ℂ] W) (B : W)
    (C : V →ₗ[ℂ] ℂ) (c : ℂ) (η : V) :
    schurBlock a A B C (c, η) = 0 ↔
      η = -(c • A.symm B) ∧ schurScalar a A B C * c = 0 := by
  constructor
  · intro h
    have hfirst : a * c + C η = 0 := congrArg Prod.fst h
    have hsecond : c • B + A η = 0 := congrArg Prod.snd h
    have hη : η = -(c • A.symm B) := by
      have hh := congrArg A.symm hsecond
      simp only [map_add, map_smul, A.symm_apply_apply, map_zero] at hh
      exact eq_neg_of_add_eq_zero_right hh
    refine ⟨hη, ?_⟩
    rw [hη] at hfirst
    simp only [map_neg, map_smul, smul_eq_mul] at hfirst
    dsimp [schurScalar]
    linear_combination hfirst
  · rintro ⟨rfl, hscalar⟩
    ext
    · simp only [schurBlock_apply, Prod.fst_zero, map_neg,
        map_smul, smul_eq_mul]
      dsimp [schurScalar] at hscalar
      linear_combination hscalar
    · simp

/-- The spanning vector has first coordinate one, hence never vanishes. -/
def schurKernelVector (A : V ≃ₗ[ℂ] W) (B : W) : ℂ × V := (1, -A.symm B)

theorem schurKernelVector_ne_zero (A : V ≃ₗ[ℂ] W) (B : W) :
    schurKernelVector A B ≠ 0 := by
  intro h
  have hh := congrArg Prod.fst h
  norm_num [schurKernelVector] at hh

theorem schurBlock_ker_eq_span (a : ℂ) (A : V ≃ₗ[ℂ] W) (B : W)
    (C : V →ₗ[ℂ] ℂ) (hscalar : schurScalar a A B C = 0) :
    LinearMap.ker (schurBlock a A B C) =
      Submodule.span ℂ {schurKernelVector A B} := by
  ext u
  rcases u with ⟨c, η⟩
  rw [LinearMap.mem_ker, schurBlock_eq_zero_iff, hscalar, zero_mul,
    eq_self_iff_true, and_true,
    Submodule.mem_span_singleton]
  constructor
  · intro hη
    refine ⟨c, ?_⟩
    ext <;> simp [schurKernelVector, hη]
  · rintro ⟨z, hz⟩
    have hc : z = c := by simpa [schurKernelVector] using congrArg Prod.fst hz
    simpa [schurKernelVector, hc] using (congrArg Prod.snd hz).symm

theorem schurBlock_ker_finrank (a : ℂ) (A : V ≃ₗ[ℂ] W) (B : W)
    (C : V →ₗ[ℂ] ℂ) (hscalar : schurScalar a A B C = 0) :
    Module.finrank ℂ (LinearMap.ker (schurBlock a A B C)) = 1 := by
  rw [schurBlock_ker_eq_span a A B C hscalar]
  exact finrank_span_singleton (schurKernelVector_ne_zero A B)

theorem schurBlock_ker_eq_bot (a : ℂ) (A : V ≃ₗ[ℂ] W) (B : W)
    (C : V →ₗ[ℂ] ℂ) (hscalar : schurScalar a A B C ≠ 0) :
    LinearMap.ker (schurBlock a A B C) = ⊥ := by
  apply le_antisymm _ bot_le
  rintro ⟨c, η⟩ h
  obtain ⟨hη, hc⟩ := (schurBlock_eq_zero_iff a A B C c η).mp h
  have hc0 : c = 0 := (mul_eq_zero.mp hc).resolve_left hscalar
  simpa [hc0] using hη

/-- A nonzero kernel vector exists exactly when the scalar equation vanishes. -/
theorem schurBlock_exists_nonzero_iff (a : ℂ) (A : V ≃ₗ[ℂ] W) (B : W)
    (C : V →ₗ[ℂ] ℂ) :
    (∃ u : ℂ × V, u ≠ 0 ∧ schurBlock a A B C u = 0) ↔
      schurScalar a A B C = 0 := by
  constructor
  · rintro ⟨⟨c, η⟩, hne, hu⟩
    obtain ⟨hη, hc⟩ := (schurBlock_eq_zero_iff a A B C c η).mp hu
    rcases mul_eq_zero.mp hc with h | h
    · exact h
    · exfalso
      apply hne
      simp [h, hη]
  · intro hscalar
    refine ⟨schurKernelVector A B, schurKernelVector_ne_zero A B, ?_⟩
    rw [schurKernelVector, schurBlock_eq_zero_iff]
    simp [hscalar]

section Coordinates

variable {U X : Type*} [AddCommGroup U] [Module ℂ U]
  [AddCommGroup X] [Module ℂ X]

/-- An exact coordinate identity for a linear map. In operator applications,
`U` is the operator domain, while `X` is its ambient range space. In particular
these coordinates need not identify the operator domain with all of `X`. -/
structure SchurCoordinates (F : U →ₗ[ℂ] X) (V W : Type*)
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] where
  diagonal : ℂ
  complement : V ≃ₗ[ℂ] W
  column : W
  row : V →ₗ[ℂ] ℂ
  domainCoords : U ≃ₗ[ℂ] (ℂ × V)
  rangeCoords : X ≃ₗ[ℂ] (ℂ × W)
  block_identity : ∀ u, rangeCoords (F u) =
    schurBlock diagonal complement column row (domainCoords u)

namespace SchurCoordinates

variable {F : U →ₗ[ℂ] X} (h : SchurCoordinates F V W)

def scalar : ℂ := schurScalar h.diagonal h.complement h.column h.row

theorem ker_eq_comap : LinearMap.ker F =
    (LinearMap.ker (schurBlock h.diagonal h.complement h.column h.row)).comap
      h.domainCoords.toLinearMap := by
  ext u
  change F u = 0 ↔ schurBlock h.diagonal h.complement h.column h.row (h.domainCoords u) = 0
  rw [← h.block_identity]
  exact h.rangeCoords.map_eq_zero_iff.symm

/-- The coordinate identity induces an equivalence of the exact kernels. -/
def kernelEquiv : LinearMap.ker F ≃ₗ[ℂ]
    LinearMap.ker (schurBlock h.diagonal h.complement h.column h.row) :=
  (LinearEquiv.ofEq _ _ h.ker_eq_comap).trans
    (h.domainCoords.ofSubmodule' _)

theorem ker_finrank (hscalar : h.scalar = 0) : Module.finrank ℂ (LinearMap.ker F) = 1 := by
  rw [h.kernelEquiv.finrank_eq]
  exact schurBlock_ker_finrank h.diagonal h.complement h.column h.row hscalar

theorem ker_eq_bot (hscalar : h.scalar ≠ 0) : LinearMap.ker F = ⊥ := by
  rw [h.ker_eq_comap,
    schurBlock_ker_eq_bot h.diagonal h.complement h.column h.row hscalar]
  ext u
  simp

theorem exists_nonzero_iff : (∃ u : U, u ≠ 0 ∧ F u = 0) ↔ h.scalar = 0 := by
  unfold scalar
  rw [← schurBlock_exists_nonzero_iff h.diagonal h.complement h.column h.row]
  constructor
  · rintro ⟨u, hne, hu⟩
    refine ⟨h.domainCoords u, ?_, ?_⟩
    · simpa using hne
    · rw [← h.block_identity, hu, map_zero]
  · rintro ⟨u, hne, hu⟩
    refine ⟨h.domainCoords.symm u, ?_, ?_⟩
    · simpa using hne
    · apply h.rangeCoords.injective
      rw [map_zero, h.block_identity, h.domainCoords.apply_symm_apply]
      exact hu

end SchurCoordinates

end Coordinates

/-- The eigenvalue equation as a linear map on the genuine operator domain. -/
def operatorShift (T : L2Space →ₗ.[ℂ] L2Space) (E : ℝ) : T.domain →ₗ[ℂ] L2Space :=
  T.toFun - (E : ℂ) • T.domain.subtype

@[simp] theorem operatorShift_apply (T : L2Space →ₗ.[ℂ] L2Space) (E : ℝ)
    (u : T.domain) : operatorShift T E u = T u - (E : ℂ) • (u : L2Space) := rfl

theorem operatorShift_ker_map (T : L2Space →ₗ.[ℂ] L2Space) (E : ℝ) :
    (LinearMap.ker (operatorShift T E)).map T.domain.subtype = operatorEigenspace T E := by
  ext x
  rw [Submodule.mem_map, mem_operatorEigenspace, LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u, rfl, ?_⟩
    exact sub_eq_zero.mp hu
  · rintro ⟨u, rfl, hu⟩
    refine ⟨u, ?_, rfl⟩
    exact sub_eq_zero.mpr hu

/-- Passing from domain elements to their ambient L² values loses no
eigenvectors and does not change the eigenspace dimension. -/
def operatorShift_kernelEquiv (T : L2Space →ₗ.[ℂ] L2Space) (E : ℝ) :
    LinearMap.ker (operatorShift T E) ≃ₗ[ℂ] operatorEigenspace T E :=
  (T.domain.equivSubtypeMap _).trans (LinearEquiv.ofEq _ _ (operatorShift_ker_map T E))

theorem SchurCoordinates.operator_eigenspace_finrank
    {T : L2Space →ₗ.[ℂ] L2Space} {E : ℝ}
    (h : SchurCoordinates (operatorShift T E) V W) (hscalar : h.scalar = 0) :
    Module.finrank ℂ (operatorEigenspace T E) = 1 := by
  rw [← (operatorShift_kernelEquiv T E).finrank_eq]
  exact h.ker_finrank hscalar

theorem SchurCoordinates.operator_eigenspace_eq_bot
    {T : L2Space →ₗ.[ℂ] L2Space} {E : ℝ}
    (h : SchurCoordinates (operatorShift T E) V W) (hscalar : h.scalar ≠ 0) :
    operatorEigenspace T E = ⊥ := by
  rw [← operatorShift_ker_map, h.ker_eq_bot hscalar, Submodule.map_bot]

theorem SchurCoordinates.operator_eigenvalue_iff
    {T : L2Space →ₗ.[ℂ] L2Space} {E : ℝ}
    (h : SchurCoordinates (operatorShift T E) V W) :
    (∃ u : L2Space, u ≠ 0 ∧ u ∈ operatorEigenspace T E) ↔ h.scalar = 0 := by
  rw [← h.exists_nonzero_iff]
  constructor
  · rintro ⟨u, hne, hu⟩
    obtain ⟨v, hv, heig⟩ := (LinearPMap.mem_graph_iff T).mp hu
    change (v : L2Space) = u at hv
    change T v = (E : ℂ) • u at heig
    refine ⟨v, ?_, ?_⟩
    · intro hv0
      apply hne
      rw [← hv, hv0]
      rfl
    · simp only [operatorShift_apply, sub_eq_zero]
      simpa only [hv] using heig
  · rintro ⟨u, hne, hu⟩
    refine ⟨u, ?_, ?_⟩
    · intro hu0
      exact hne (Subtype.ext hu0)
    · apply (LinearPMap.mem_graph_iff T).mpr
      exact ⟨u, rfl, sub_eq_zero.mp hu⟩

end InfiniteZero
