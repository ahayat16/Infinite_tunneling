# Global dilation, continuity of parity energies and hopping

The four modules [MagneticDilation](../InfiniteZero/MagneticDilation.lean), [MagneticDilationPotential](../InfiniteZero/MagneticDilationPotential.lean), [MagneticFormPotentialComparison](../InfiniteZero/MagneticFormPotentialComparison.lean), and [ParityEnergyContinuity](../InfiniteZero/ParityEnergyContinuity.lean) compile without warnings and are audited: only `propext`, `Classical.choice`, and `Quot.sound` occur. They prove continuity of the variational parity energies at strictly positive couplings under the elementary hypothesis that each test class considered is nonempty. No identification with an eigenmode enters this proof.

## Global change of scale

For `λ > 0`, the dilation is

\[
 (U_\lambda\psi)(y)=\lambda^{-1/2}\psi(\lambda^{-1/2}y).
\]

The planar change of measure gives `mass(Uλψ) = mass ψ`. The map preserves smooth compactly supported functions and parity, and its inverse is exactly U_(λ⁻¹). It thus bijectively permutes normalized tests of each parity. These conclusions are the lemmas `mass_magneticDilation`, `IsTestFunction.magneticDilation`, `IsNormalizedTest.magneticDilation`, `HasParity.magneticDilation`, and the two cancellation identities in `MagneticDilation`.

Define the transformed potential

\[
 W_\lambda(y)=\lambda V(\lambda^{-1/2}y).
\]

With the repository convention `D_(b,λ) = −i∇ − bλ y⊥/2`, the covariant-derivative calculation gives a factor λ⁻¹ in front of D_(b,λ)ψ(λ⁻¹ᐟ²y). After integration, the exact identity is

\[
 \mathfrak q_{b,1,W_\lambda}(U_\lambda\psi)
   =\lambda^{-1}\mathfrak q_{b,\lambda,V}(\psi).
\tag{1}
\]

This is `magneticForm_magneticDilation`. The field in the transformed form is fixed; all remaining coupling dependence is in Wλ.

## Uniform control of the transformed potential

Assume `V : Plane → ℝ` is smooth and compactly supported. For z=λ⁻¹ᐟ²y, the chain rule gives exactly

\[
 \partial_\lambda W_\lambda(y)=V(z)-\tfrac12 DV(z)[z].
\tag{2}
\]

The derivative DV has compact support, as does z ↦ DV(z)[z]. The right-hand side of (2) is therefore a continuous compactly supported function of z. Its norm is bounded by a constant C>0, chosen before λ and y. The mean value theorem on `(0,∞)` gives

\[
 |W_\lambda(y)-W_\mu(y)|\le C|\lambda-\mu|
 \quad(\lambda,\mu>0,\ y\in\mathbb R^2).
\tag{3}
\]

`exists_magneticDilationPotential_lipschitz` expresses this uniformity on the entire positive half-line, with no additional threshold. This is not a uniform bound on Wλ itself as λ grows.

## From potentials to forms, then infima

At fixed field and coupling, kinetic terms cancel:

\[
 \mathfrak q_{b,\lambda,V}(\psi)-\mathfrak q_{b,\lambda,W}(\psi)
 =\lambda^2\int(V-W)|\psi|^2.
\]

Continuity of the potentials and compact support of the test justify integrability and this subtraction. If |V−W|≤δ, `abs_magneticForm_sub_le` bounds the absolute difference by λ² δ mass ψ. In particular, (3) gives, at fixed field, control C|λ−μ| common to all normalized tests, also independently of b.

Fix parity σ and assume only `∃ ψ, IsNormalizedTest ψ ∧ HasParity σ ψ`. The set of form values on these tests is then nonempty. It is also bounded below: for |V|≤B, comparison with the nonnegative free form gives q_(b,λ,V)(ψ)≥−λ²B on normalized tests. `parityTestFormValues_bddBelow` proves this bound; no spectral lower bound is added as a hypothesis.

Let eσ(λ) be the infimum of q_(b,1,Wλ) over this same test set. The uniform form inequality in both directions passes to nonempty, bounded-below real infima: |eσ(λ)−eσ(μ)|≤C|λ−μ|. The test bijection and (1) then give

\[
 E_\sigma(\lambda)=\lambda e_\sigma(\lambda).
\]

Thus `continuousOn_parityTestEnergy` proves continuity on `(0,∞)`. Taking V(x)=v(x+d)+v(d−x) preserves smoothness and compact support, and `continuousOn_parityEnergy` concerns exactly the magnetic model's definition `parityEnergy`, for any fixed separation.

## Connection to the constructed potential and limitations

The assembly in [ConstructedParityEnergyContinuity](../InfiniteZero/ConstructedParityEnergyContinuity.lean) compiles without warnings; its three results pass `assert_no_sorry` guards and their audit finds only the three standard axioms already listed. It discharges nonemptiness for the constructed potential by choosing a large coupling where an actual atomic ground state exists and the even/odd trials provide unit vectors in the double-well domain, using [AtomicGroundAgmon](../InfiniteZero/AtomicGroundAgmon.lean) and [ParityTrialEnergyBound](../InfiniteZero/ParityTrialEnergyBound.lean). The result `IsMagneticRealization.exists_normalized_parity_test_of_domain_vector` in [MagneticParityNormalization](../InfiniteZero/MagneticParityNormalization.lean) then produces a normalized test of each parity. Its proof uses density of the actual parity-test graph: if no normalized test existed, every form lower bound would hold on tests and hence on the domain, contradicting the existence of a nonzero vector.

The assembly's hypotheses are explicit: `BasicConditions`, a `SeparationCertificate`, `RadialCoreSpectralData`, core and atomic-potential realizations, and left-, right-, and double-well realizations. For each L≥cert.L₀, the three theorems are:

- `exists_normalized_parity_test_of_radialData`: nonemptiness of both normalized test classes;
- `continuousOn_parityEnergy_of_radialData`: continuity of each parity energy on `(0,∞)`;
- `continuousOn_signedSplitting_of_radialData`: continuity of their difference, odd energy minus even energy.

The auxiliary coupling is chosen above both the atomic-existence and trial-validity thresholds, before the separation L. The tests are used only for nonemptiness of the variational class, which is coupling-independent. The continuity conclusion therefore covers **all** positive couplings, without a final threshold. The module imports no admission and keeps the radial data and realizations as arguments; no new classical result is postulated.

The compiled wrappers in [ClassicalDoubleWellParityGround](../InfiniteZero/ClassicalDoubleWellParityGround.lean), `doubleWell_parityEnergy_continuous` and `doubleWell_signedSplitting_continuous`, give these conclusions from hp, cert, and L≥cert.L₀ alone. They obtain the normalized test from actual sector ground-state certificates. Instantiation uses classical results A002 and A004; their named dependencies were verified by the global audit `scripts/check.sh`: exactly A002 and A004, without A003, A005, or use of `thm_main`.

The generic proof requires neither continuity of a choice of eigenfunctions, realization of self-adjoint sectors, nor attainment of the infimum. Continuity of canonical hopping is proved separately below from the atomic gap and a comparison of states modulo phase. Identification of the first two min–max levels and eigenspaces is now established separately in the [global doublet](GLOBAL_PARITY_DOUBLET.md).

## Comparing actual atomic states modulo phase

[MagneticDilationL2.lean](../InfiniteZero/MagneticDilationL2.lean) extends dilation identities to L² functions: linearity, preservation of the inner product and mass, and identities transporting just one inner-product argument. The Hilbert-space lemma [UnitPhaseDistance.lean](../InfiniteZero/UnitPhaseDistance.lean) proves that for two unit vectors u,v there is a scalar z of norm one with `‖u−zv‖² ≤ 2(1−|⟨v,u⟩|²)`.

[AtomicGroundDilationComparison.lean](../InfiniteZero/AtomicGroundDilationComparison.lean) applies these facts to actual states of the constructed potential. The uniform bound on Wλ−Wμ first controls the reduced energies Eatom(λ)/λ. The rank-one atomic gap on tests is then transported by dilation and extended through closure of the original operator graph. For ρ=Uλ⁻¹Uμ φμ, we obtain

\[
 \gamma\bigl(1-|\langle\rho,\varphi_\lambda\rangle|^2\bigr)
 \le 2C_0|\lambda-\mu|.
\]

Phase alignment therefore gives a constant C and threshold T, chosen before both couplings and eigenfunctions, such that

\[
 \forall\lambda,\mu\ge T,\quad
 \exists |z|=1:\quad
 \operatorname{mass}(\varphi_\lambda-zU_\lambda^{-1}U_\mu\varphi_\mu)
 \le C|\lambda-\mu|.
\]

The theorem `exists_atomicGround_phase_dilation_comparison_of_radialData` takes only hp, radial data, and core and full-potential realizations. No new realization of a dilated operator or continuity of a phase choice is admitted.

## Continuity of actual canonical hopping

[HoppingContinuity.lean](../InfiniteZero/HoppingContinuity.lean) compiles without warnings. Its three results pass `assert_no_sorry` guards and depend only on `propext`, `Classical.choice`, and `Quot.sound`. The final result is exactly

```lean
hp → hRad → hAcore → hApot →
  ∃ T > 0, ∀ L : ℝ,
    ContinuousOn (canonicalHopping p.b p.potential L) (Ici T)
```

Here `hRad : RadialCoreSpectralData p.b p` and both realizations hAcore, hApot cover all couplings. The threshold precedes L; no separation condition is needed for this continuity. The real part is therefore continuous on the same half-line. The wrapper `CuspParameters.canonicalHopping_continuous hp`, in [ClassicalHoppingContinuity.lean](../InfiniteZero/ClassicalHoppingContinuity.lean), also compiles. It supplies the same conclusion from `BasicConditions` alone by instantiating A002 and A004; no new admission is added. At this milestone, the global check of this stage was still in progress.

The proof has three steps:

1. `norm_hopping_sub_le_of_mass_one` controls a change of state. For two L² functions of mass one and a continuous potential with |V|≤B, bilinearity and Cauchy–Schwarz give
   \[
    |\rho_\lambda(\varphi)-\rho_\lambda(\psi)|
      \le 2\lambda^2 B\sqrt{\operatorname{mass}(\varphi-\psi)}.
   \]
   Magnetic translations preserve the L² norm; all integrability statements follow from these hypotheses.
2. `continuous_hopping_magneticDilation_inv` fixes a continuous function χ and proves continuity of `λ ↦ hopping b V L λ (U_(λ⁻¹) χ)` for continuous compactly supported V. The identity U_(λ⁻¹)χ(x)=sqrt λ · χ(sqrt λ • x) makes the integrand jointly continuous; the potential factor gives it fixed compact support. This step also handles the λ-dependent magnetic phase.
3. `exists_canonicalHopping_continuous_of_radialData` fixes μ≥T and takes χ=Uμ φμ, where φμ is the actual canonical ground state. The previous comparison supplies, for each λ≥T, a unit phase z such that `mass(φλ−z U_(λ⁻¹)χ) ≤ C|λ−μ|`. Hopping is invariant under this phase: the conjugated factor in the left argument cancels the right factor. Since |p.potential|≤1, its difference from reference hopping is at most 2λ² sqrt(C|λ−μ|), which tends to zero. At λ=μ, the reference is exactly φμ by the dilation inverse identity.

This proof constructs neither a continuous canonical phase nor graph transport by dilation. It completes continuity of the physical scalar under explicit radial data and realizations; relative spectral errors and final parameter assembly remain separate.
