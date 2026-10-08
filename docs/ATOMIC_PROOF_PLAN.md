# Verifiable plan for the atomic block

**The final theorem is proved and compiled modulo three classical admissions.** [ConstructedMainProof](../InfiniteZero/ConstructedMainProof.lean) assembles the channels, spectral doublet, continuity results, and relative Schur errors. [Remaining.lean](../InfiniteZero/Remaining.lean) deduces `thm_main` with the explicit witness `elementaryParameters`; its only admissions are the three classical admissions A002–A004.

This plan retains the historical order of steps and approaches considered. Forward-looking wording describes their strategy; it does not indicate a gap in the final theorem. Stronger limits not claimed, notably B.1 and the literal power of B.2, remain indicated. The completed final assembly is recalled at the end.
**Passage from radial spectral data to a simple full-potential ground state and its gap is now proved. The radial core data are assembled from the classical unit-field theorem A004 and realization A002, with an independent variational energy bound. No nonradial, source, or tunneling result is admitted in this assembly.** The first useful external result is **radial magnetic** harmonic approximation, applied to the explicit core. For the full potential, the first project-specific step is coercivity on the radial ground state's orthogonal complement. This now constructs the simple ground state and gap by an actual self-adjoint compression, Schur complement, and intermediate value theorem, without assuming these nonradial conclusions.

A shortcut is available: initial coercivity only needs radial ground-state exterior mass of order h, obtained from its energy. Absolute Agmon decay and exponential comparison of energies and actual ground states in L² norm are now proved separately. The weighted response of the same full ground state is also constructed, with a positive radial reference, exact equation, and c∈[1/2,1]. The [k=0 weighted forcing and fine L² response](CUSP_FINE_FORCING.md) now retain the actual core action, Γ, and log-flat cost. [Forcing derivatives](CUSP_FORCING_DERIVATIVES.md) are also proved, with a threshold and Γ common to the required orders. The [full PDE data](ATOMIC_FINE_RESPONSE_DATA.md) are now controlled on a fixed neighborhood: normalized radial jets handle the energy-shift term without producing Γ². Pointwise scattered-source amplitudes and the active integral are now controlled through the actual hopping asymptotic. The [physical double-well spectral reduction](GLOBAL_PARITY_DOUBLET.md) and [relative corrections](../InfiniteZero/CanonicalParityRelativeErrors.lean) are also proved.
Radial normalization now has a direct ODE/Wronskian route, giving the sufficient power h² without pointwise harmonic convergence. Its assembly compiles; it does not replace literal Lemma B.1. See [RADIAL_NORMALIZATION.md](RADIAL_NORMALIZATION.md).

## 1. Objects and quantifiers to preserve

Fix `p : CuspParameters` and `hp : p.BasicConditions` once and for all. Set `b = p.b > 0`, `v₀ = p.core`, `W = p.ε * (p.cuspPlus + p.cuspMinus)`, and `v = p.potential = v₀ + W`. For h>0, write

\[
 H_h(V)=(hP-bx^\perp/2)^2+V,\qquad
 q_{h,V}(u)=\|(hP-bx^\perp/2)u\|_2^2+\int V|u|^2.
\]

The thresholds and constants below depend on this fixed p, not the well separation L. No potential choice after h or L is allowed. Atomic results and the final assembly hold for every p satisfying these elementary conditions: `CuspParameters.mainConclusion` gives a separation threshold, then the conclusion for every L beyond it. The final witness for the existential potential is the explicit choice `elementaryParameters`.

In the [TeX](../article/Infinite_Zero_Tunneling_Lean_oriented_V2.tex), the corresponding chain is `lem:radial-spectral`, then `lem:complement-coercivity`, `prop:Feshbach`, and `lem:exact-one-well-gap`. `prop:Feshbach` is the first proposition in this chain concluding existence and simplicity of the full-potential ground state; its full version also contains exponential estimates that are useful to separate from these two conclusions.

The package to obtain for the full potential has exactly the form

\[
 \exists h_0,c,C>0\;\forall h\in(0,h_0),\quad
 \begin{cases}
 H_h(v)\phi_h=e_h\phi_h,\quad \|\phi_h\|_2=1,\\
 e_h=\inf q_{h,v}\text{ over normalized test functions},\\
 -1\le e_h\le-1+Ch,\\
 \ker(H_h(v)-e_h)=\mathbb C\phi_h,\\
 q_{h,v}(u)\ge(e_h+ch)\|u\|_2^2\quad(u\perp\phi_h).
 \end{cases}
\]

The last inequality is formulated at least on the operator domain. IMS localizations are proved here on tests, then the required bounds pass to graph closure; a general IMS identity on the form domain is not used in the results already obtained. The full-potential ground state is not assumed real, positive, or radial.

Exact code correspondence:

| Object | Current Lean definition | Connection and status |
| --- | --- | --- |
| Unscaled Hamiltonian | `magneticHamiltonian` in [MagneticModel.lean](../InfiniteZero/MagneticModel.lean) | For λ=h⁻¹, H_h(V)=h² magneticOperator b λ V, with domains identified. |
| Atomic energy | `atomicGroundEnergy b V λ`, real infimum over normalized tests | Identification and existence proved under `RadialCoreSpectralData` and realizations in `AtomicGroundConstruction`. |
| Normalized ground state | `IsAtomicGroundState b V λ φ` | Smoothness, membership in L², **pointwise** equation at the preceding energy, and `mass φ = 1`. |
| Simplicity | `AtomicGroundSimple` in [HoppingPhase.lean](../InfiniteZero/HoppingPhase.lean) | All normalized ground states differ by a complex constant of norm one. This predicate alone is vacuously true if no ground state exists. |
| Realization | `IsMagneticRealization` in [OperatorBridge.lean](../InfiniteZero/OperatorBridge.lean) | A002 supplies self-adjointness, infimum, and smooth eigenvector representatives; neither existence nor a gap. |
| Gap | `HasGapAboveGround` in [OperatorBridge.lean](../InfiniteZero/OperatorBridge.lean) | The type requires a positive gap; separately retain the quantitative bound c h, or c λ before rescaling. |
| Resolvent energy | `scaledAtomicEnergy p λ` in [HoppingChannels.lean](../InfiniteZero/HoppingChannels.lean) | Equals −e_h; limit one and eventual bound [1/2,1] proved in `AtomicGroundEnergyBounds` under the classical data. |

In [Main.lean](../InfiniteZero/Main.lean), `LocalChannelAnalyticData.atomic_exists` and `scaled_energy_pos` are required from `channels.threshold`; `atomic_simple` from `threshold`. Choose both thresholds accordingly. The conclusion data's `ground_gap` field concerns the **double** well: proving the atomic gap does not automatically fill it.

`canonicalAtomicState` is a conditional choice, zero outside the existence regime. This choice does not solve the spectral problem or supply a phase continuous in λ.

## 2. Geometric hypotheses already proved

Smoothness, compact support, and full-potential bounds are proved by `CuspParameters.admissiblePotential` in [ConstructionSmooth.lean](../InfiniteZero/ConstructionSmooth.lean). More precise useful facts are:

- `core_contDiff`, `core_hasCompactSupport`, `core_range`, `core_zero`, and `core_gt_neg_one`: a smooth compactly supported core valued in [−1,0], with unique minimum −1 at the origin; radiality is explicit in the definition.
- `potential_unique_minimum`, `potential_eventuallyEq_core`, `potential_fderiv_zero`, and `potential_second_directional_derivative` in [ConstructionMinimum.lean](../InfiniteZero/ConstructionMinimum.lean): the full potential equals the core near zero, and its second derivative in direction u is 2 ‖u‖² / p.r₀².
- `core_cuspPlus_tsupport_disjoint`, `core_cuspMinus_tsupport_disjoint`, and `cuspPlus_cuspMinus_tsupport_disjoint` in [ConstructionSupportSeparation.lean](../InfiniteZero/ConstructionSupportSeparation.lean).
- `elementaryParameters_basicConditions` and `exists_basicConditions` in [ConstructionParameters.lean](../InfiniteZero/ConstructionParameters.lean): the elementary constraints have an actual witness.

The bound −εa≤W≤0 follows from individual bounds and disjointness of the two cusps. For the first spectral argument, the coarser −2εa≤W≤0, with 2εa<1/2, already suffices. The IMS partition is now constructed in `AtomicLocalizationCutoffs`: a bump equals one on the ball of radius 2r₀ and zero outside radius 3r₀, then χ₀=sin(π bump/2) and χ₁=cos(π bump/2). The separation 3r₀<R/2 places all of supp χ₀ before the cusps. The IMS error has a global coupling-independent bound; the core vanishes on the exterior part. The uniform expansion v₀(x)=−1+|x|²/r₀²+O(|x|⁴) and its use after dilation remain to be assembled separately; the verified second directional derivative alone must not be presented as a complete Taylor-remainder theorem.

## 3. First external spectral input: the radial core

Primary reference consulted directly: Bernard Helffer and Ayman Kachmar, *Quantum tunneling in deep potential wells and strong magnetic field revisited*, [arXiv:2208.13030v5](https://arxiv.org/pdf/2208.13030v5), September 5, 2023. In **this version**, the assumptions are (1.1), p. 1; Theorem 1.1, pp. 3–4, establishes simplicity, radial positivity, and the ground-energy expansion; Proposition 2.1, p. 11, treats the first eigenvalues by harmonic approximation. The following proof discusses the rescaled profile. These results concern a radial well in the relevant magnetic regime and do not directly cover our nonradial potential. No tunneling result from this reference is imported here.

Application to check in our conventions, without copying normalization factors from a profile formula:

\[
 H_h(v_0)=b^2\mathcal L^{\mathrm{sw}}_{h/b}(v_0/b^2),\qquad
 (V_h f)(y)=h^{1/2}f(\sqrt h\,y).
\]

The second transformation is unitary in dimension two since dx=h dy. The normalized potential v₀/b² satisfies the radial assumptions above. Direct calculation gives

\[
 V_h(H_h(v_0)+1)V_h^{-1}/h
 =(P-by^\perp/2)^2+|y|^2/r_0^2+O(h|y|^4).
\]

With ν=√(b²/4+1/r₀²), the limiting oscillator has ground state ψ₀(y)=√(ν/π) exp(−ν|y|²/2), energy μ₀=2ν, and gap δ₀=2ν−b>0. These formulas can be checked by applying the operator to the Gaussian and integrating its square. Completeness of the oscillator mode expansion, needed to identify the second level, is a spectral statement distinct from this eigenfunction calculation alone.

The **radial contract**, defined in `RadialCoreSpectralData` and constructed by `radial_core_spectral_data` from A002+A004, concerns the actual self-adjoint operator H_h(v₀): for sufficiently small h, a normalized ground state φ₀,h exists with energy e₀,h and

\[
 -1\le e_{0,h}\le-1+Ch,\qquad
 q_{h,v_0}(u)-e_{0,h}\|u\|^2
 \ge\gamma h\bigl(\|u\|^2-|\langle\phi_{0,h},u\rangle|^2\bigr).
\]

To reproduce B.1 literally, one would separately need local L² convergence of h^{1/2} φ₀,h(√h ·) to the correctly normalized Gaussian. The Wronskian route to Γ≳h² avoids this need. The O(h^(3/2)) energy remainder from the reference is included in the semiclassical-level input A004; Lean derives the weaker limits used for the simplicity transfer from it. The independent variational proof of the core energy upper bound does not use this admission.

A004 is `classical_radial_low_levels`: it supplies a positive normalized radial ground state and O(h^(3/2)) harmonic-approximation bounds for the first two semiclassical levels of a general radial single well. Lean proves the oscillator-level ordering, the large-coupling gap limit and the two-dimensional min-max argument giving the operator complement bound. The `classical_radial_harmonic` interface is a proved wrapper using A002 and A004. `RadialCoreSpectralAssembly` proves the application to the core, using b>0 and r₀>0 without cusp hypotheses, the field conversion, a uniform gap constant, and its transfer to tests. `RadialCoreVariationalBound` proves the core energy upper bound independently of A002 and A004. The [classical radial contract](RADIAL_HARMONIC_CONTRACT.md) gives the exact remaining input, checked references, and natural-language proof. The derived `RadialCoreSpectralData` requires no energy-density integrability for the noncompact ground state. Its `positive_radial_ground` field supplies a real, radial, strictly positive witness at the same threshold; it assumes no continuous choice.
`RadialCoreSpectralData.positive_ground_with_gap`, in `RadialCoreGroundChoice`, resolves this witness issue: under realization A002, the test gap extends to the graph and forces simplicity. Both states differ only by a unit phase; the same positive witness therefore satisfies the initial gap and energy bounds, without loss of constants or modification of A004.

## 4. First original step: coercivity with only a polynomial loss

Fix h, write φ₀=φ₀,h and e₀=e₀,h, and assume the preceding radial contract. Positivity of the kinetic term immediately gives

\[
 \int_{|x|\ge r_0}|\phi_0|^2
 \le q_{h,v_0}(\phi_0)+1=e_0+1\le Ch.
\]

Indeed, 1+v₀≥0 everywhere and equals one outside the core. The Lean proof avoids assuming an integral form identity for the eigenvector: the inequality proved on tests passes to graph closure by continuity of exterior L² restriction. `AtomicExteriorGraph` thus gives M_ext≤B/λ for the actual radial ground state, using only its energy and operator realization.

Choose smooth real functions 0≤χⱼ≤1, with χ₀²+χ₁²=1, such that χ₀=1 near the entire core support, supp χ₀ is disjoint from supp W, and v₀=0 on supp χ₁. Sine and cosine of a radial transition in a fixed annulus separating the supports suffice. Their gradients are bounded. For u⊥φ₀, Cauchy–Schwarz gives

\[
 |\langle\phi_0,\chi_0u\rangle|^2
 =|\langle(\chi_0-1)\phi_0,u\rangle|^2\le Ch\|u\|^2.
\]

Applying the radial gap to χ₀u therefore gives

\[
 q_{h,v_0}(\chi_0u)-e_0\|\chi_0u\|^2
 \ge\gamma h\|\chi_0u\|^2-C\gamma h^2\|u\|^2.
\]

On the exterior part, W−e₀≥c₁>0 for sufficiently small h, since W's fixed depth is strictly below one and e₀→−1. Hence q_{h,v}(χ₁u)−e₀‖χ₁u‖²≥c₁‖χ₁u‖².

Finally expand D_h(χⱼu)=χⱼD_hu−ih(∇χⱼ)u. Cross terms cancel by Σχⱼ∇χⱼ=0, and IMS gives a negative error bounded by C_IMS h²‖u‖². After absorption,

\[
 q_{h,v}(u)-e_0\|u\|^2\ge ch\|u\|^2
 \qquad(u\perp\phi_0).
\]

This is `lem:complement-coercivity` / `sublemma:L3-1-exterior` in the TeX, with a shorter initial proof than the Agmon route. IMS is proved pointwise in [MagneticIMS.lean](../InfiniteZero/MagneticIMS.lean), then integrated on tests in [MagneticIMSIntegrated.lean](../InfiniteZero/MagneticIMSIntegrated.lean), with integrability deduced from compact supports. Localized functions remain tests.

`AtomicLocalizationEnergy.core_exteriorMass_le` proves, in unscaled variables, λ²M_ext(u)≤q_{λ,v₀}(u)+λ²mass(u). It applies to L² states with integrable energy density; for tests, this integrability is deduced. Energy at most −λ²+Bλ for a normalized state thus gives M_ext≤B/λ. `AtomicLocalizationOverlap` proves the orthogonality defect using this actual exterior mass, and its variant without orthogonality.

A first test-level assembly is proved in `CuspParameters.exists_atomic_test_coercivity_threshold` ([AtomicLocalizationForms.lean](../InfiniteZero/AtomicLocalizationForms.lean)). For each fixed p, γ>0, and B, it chooses T before λ. For λ≥T, the only spectral inputs concern the core: a state φ∈L² of mass one, integrable energy density, q_{λ,v₀}(φ)=λ²e, e≤−1+B/λ, and

\[
 q_{\lambda,v_0}(u)-\lambda^2 e\,\mathrm{mass}(u)
 \ge\gamma\lambda\bigl(\mathrm{mass}(u)-|\langle\phi,u\rangle|^2\bigr)
 \quad(u\in C_c^\infty).
\]

It concludes for the **full potential** and all tests u⊥φ:

\[
 q_{\lambda,v}(u)-\lambda^2e\,\mathrm{mass}(u)
 \ge \frac{\gamma\lambda}{2}\,\mathrm{mass}(u).
\]

Multiplication by h², with λ=1/h, gives coercivity of order h. The proof uses exterior margin 1/4, sufficient under the coarse bound W>−1/2, and absorbs errors γB+C_IMS in the unscaled regime. The threshold is max(1,4B,4γ,2(γB+C_IMS)/γ). No field assumes the nonradial coercivity to be established. The following spectral version uses exactly the radial data now supplied by A004.

`MagneticIntegrationByParts` now supplies the exact complex identity `waveInner ψ (magneticHamiltonian b λ V ψ) = (magneticForm b λ V ψ : ℂ)` on test functions for continuous V. Covariant derivatives are symmetric on these tests by integration by parts; all integrability is proved. This is the first connection to the operator graph, with no additional assertion about noncompact eigenfunctions.

**Transfer of coercivity to the operator domain is now proved.** `AtomicLocalizationRankOne` retains the overlap for all tests:

\[
 q_{\lambda,v}(u)-\lambda^2e\,\mathrm{mass}(u)
 \ge \frac{\gamma\lambda}{2}\mathrm{mass}(u)
       -2\gamma\lambda|\langle\phi,u\rangle|^2.
\]

This variant uses threshold max(1,4B,4γ,2(2γB+C_IMS)/γ). `MagneticTestGraph` proves the test graph is already a complex subspace: its closure is therefore exactly the project's closed graph, with no points added by a linear span. `WavefunctionL2Bridge` identifies function masses and inner products with those of their L² classes, then test-graph energy with the magnetic form. Finally, `MagneticGraphLowerBound` uses continuity of

\[
 (u,v)\longmapsto \operatorname{Re}\langle u,v\rangle
 -\lambda^2e\|u\|^2-\frac{\gamma\lambda}{2}\|u\|^2
 +2\gamma\lambda|\langle\phi,u\rangle|^2
\]

to preserve positivity on graph closure. `AtomicLocalizationOperator.exists_atomic_operator_complement_threshold` thus concludes coercivity on all operator-domain vectors orthogonal to the radial reference. Neither density of orthogonal tests nor preservation of the closed domain by cutoffs needs to be assumed. Realization A002 is an explicit argument in this admission-free proof. The current version `AtomicSpectralCoercivity` replaces integrable-density and energy-identity hypotheses with only the actual radial ground state: `AtomicExteriorGraph` supplies exterior mass. The theorem `exists_atomic_spectral_operator_complement_threshold` therefore uses exactly the fields of `RadialCoreSpectralData`, now supplied by A004. No general IMS identity on a noncompact form domain is claimed here.

## 5. Existence, simplicity, and gap by Schur, without a global spectral projection

The following abstract statement is now proved and applied after step 4. Let H₀ be self-adjoint and bounded below, H=H₀+W with W bounded, self-adjoint, and negative, H₀φ₀=e₀φ₀, ‖φ₀‖=1, and Q(H−e₀)Q≥g>0 on Q=φ₀⊥. Then H has a simple ground state E≤e₀ and gap at least g.

**Domains and inverse.** The projection Q preserves D(H₀)=D(H) because φ₀ belongs to it. Set B=QWφ₀. Subtracting the bounded self-adjoint operator |φ₀⟩⟨B|+|B⟩⟨φ₀| from H leaves an operator reducing ℂφ₀⊕Q. Thus A_E=Q(H−E)Q, on D(H)∩Q, is self-adjoint and A_E≥g for every real E≤e₀.

Domain equality is now proved for our potential in `AtomicPerturbationDomain.atomicOperator_domain_eq_core`. Multiplication by W=p.potential−p.core is constructed as an actual bounded operator on L². `MagneticBoundedPerturbation` transports test graphs and their closures by the continuous equivalence (u,v)↦(u,v+λ²Wu). `atomicOperator_graph_of_core_eigenvector` gives the exact residual Hφ₀=e₀φ₀+λ²Wφ₀ in unscaled variables under both realization certificates. `OrthogonalCompression` constructs QH on {u∈Q | u∈D(H)}, proves domain preservation by Q, density, and self-adjointness of the compression. The formal proof directly uses the adjoint domain; it does not assume H preserves Q.

A self-adjoint operator A≥g>0 is bijective: ‖Au‖≥g‖u‖ and closedness give closed range; its orthogonal complement is ker A*=ker A={0}, so the range is dense and hence surjective. Its bounded inverse satisfies ‖A⁻¹‖≤g⁻¹ and is positive. This general proof is now formalized for actual `LinearPMap` operators in `CoerciveOperator.exists_coerciveSelfAdjoint_inverse`, with positivity and self-adjointness of the inverse. Closed range follows from graph completeness and a lower bound on its second projection; its orthogonal complement vanishes by the actual definition of adjoint. No spectral theorem or admitted external result is used in this module. The tool is now applied to the actual shifted compression, with ‖A_E⁻¹‖≤g⁻¹.

**Scalar root.** Set `w₀₀=⟨φ₀,Wφ₀⟩≤0` and

\[
 F(E)=e_0+w_{00}-E-\langle B,A_E^{-1}B\rangle\in\mathbb R.
\]

The resolvent identity A_E⁻¹−A_F⁻¹=(E−F)A_E⁻¹A_F⁻¹ proves norm continuity for E,F≤e₀. We have F(e₀)≤0. For E_low=e₀−|w₀₀|−‖B‖²/g−1, inverse bounds give F(E_low)≥1. The intermediate value theorem gives E*≤e₀ with F(E*)=0. Set ζ=A_E*⁻¹B. The nonzero vector φ₀−ζ solves H(φ₀−ζ)=E*(φ₀−ζ).

**Minimum and gap.** For u=aφ₀+η in the domain, the exact identity is

\[
 \langle u,(H-E_*)u\rangle
 =\langle\eta+a\zeta,A_{E_*}(\eta+a\zeta)\rangle
 \ge g\|\eta+a\zeta\|^2.
\]

It establishes that E* is the minimum and the kernel is the line spanned by φ₀−ζ. If u⊥φ₀−ζ, our inner product, linear in the second argument, gives a=⟨ζ,η⟩, hence

\[
 \|\eta+a\zeta\|^2
 =\|\eta\|^2+(2+\|\zeta\|^2)|a|^2
 \ge\|\eta\|^2+|a|^2=\|u\|^2.
\]

The gap is therefore at least g. Normalization by √(1+‖ζ‖²) gives the choice with positive overlap with φ₀. Conclusions about the test infimum then use the fact that tests form an operator core.

The purely algebraic kernel argument already exists in [SchurBlock.lean](../InfiniteZero/SchurBlock.lean), notably `schurBlock_ker_finrank` and `SchurCoordinates.operator_eigenspace_finrank`. The operator chain is now assembled: `SchurScalarRoot` produces the root with actual resolvents, `SchurEigenvector` reconstructs a graph vector, and `SchurGroundState.exists_groundVector_of_complement_coercive` proves the global lower bound and gap. Its only inputs are self-adjointness, a unit domain vector with Rayleigh quotient ≤E₀, and coercivity E₀+g on its orthogonal complement. No eigenvector is assumed. `GroundStateCertificate` then identifies the variational infimum and proves the eigenspace is the line spanned by this vector.

Applying this lemma with g=ch gives atomic existence, simplicity, and gap. Since v≥−1 and W≤0, it also gives −1≤E*≤e₀≤−1+Ch. These bounds alone do not suffice for exponential comparison, which now uses the core's Agmon tail.

Quantitative controls are now proved in `SchurGroundEstimates`: ‖ζ‖≤‖B‖/g, 0≤a−E≤‖B‖²/g, and 1−c≤‖ζ‖² for the normalization coefficient. `SchurResidualBounds` identifies the coupling with the projected residual and bounds coupling and diagonal shift by the actual residual λ²(p.potential−p.core)φ₀. `AtomicPerturbationTail` supplies ‖λ²Wφ₀‖²≤(2λ²εa)² ∫_{‖x‖≥4r₀}|φ₀|² for the actual multiplier, with integrability deduced from φ₀∈L².

`AtomicResidualDecay` applies Agmon and obtains ‖λ²Wφ₀‖₂≤Kλ exp(−dλ). `AtomicSchurReference` retains this same radial state in the full domain, its residual, and complement coercivity. `SchurGroundQuantitative` constructs the certificate and ζ from **one** scalar root, with exact vector φ₀−ζ. The certified energy and quantitative bounds thus do not concern independent choices.

`AtomicGroundComparison` concludes, for unscaled energies, 0≤Ecore−Efull≤C exp(−dλ). It constructs normalized ground vectors u,v∈L² for both actual operators, with ‖v−u‖₂≤C exp(−dλ), Re⟨u,v⟩>0, and Im⟨u,v⟩=0. The energy shift includes both Ecore−a and a−Efull; the first is controlled by the residual, the second by its square divided by the gap. The wrappers `atomicGroundEnergy_exponential_comparison` and `atomicGroundVectors_exponential_comparison` require only `BasicConditions`, modulo A002+A004, with constants and threshold before λ. See [ATOMIC_COMPARISON.md](ATOMIC_COMPARISON.md).

The abstract coefficient c=(1+‖ζ‖²)⁻¹ᐟ² is now connected exactly to the constructed normalized vector. Positive overlap fixes the relative phase of the two actual vectors. No separate c_h→1 theorem, coupling-continuous choice, canonical-phase alignment, or pointwise amplitude control is claimed by this comparison.

## 6. Connection to Lean predicates and the role of Appendix B

By A002, an L² eigenvector has a smooth representative satisfying the pointwise equation. The identity mass ψ=‖u‖² for representatives of the same L² vector transfers normalization. `bottom_eq` identifies its minimum energy with `atomicGroundEnergy`. This produces `∃ φ, IsAtomicGroundState b v λ φ`.

A one-dimensional eigenline implies that two normalized representatives are equal almost everywhere up to a scalar. Their continuity and the full support of Lebesgue measure strengthen this to pointwise equality; unit masses force the scalar to have norm one. This actually gives `AtomicGroundSimple`. Neither merely almost-everywhere equality nor `finrank = 1` without identifying the eigenspace replaces this step.

Both connections are now proved in `AtomicGroundTransfer`: `IsMagneticRealization.exists_atomicGroundState_of_eigenvector` first normalizes the L² vector in its eigenspace, then chooses a smooth representative; `atomicGroundSimple_of_finrank_one` deduces the norm-one factor and pointwise equality. Their existence and dimension hypotheses are now produced by `SchurGroundCertificate`, then `AtomicGroundConstruction.exists_atomicGroundCertificate_of_radialData`. Under `BasicConditions`, `RadialCoreSpectralData p.b p`, and core/full-potential operator realizations, the latter proves for sufficiently large λ a certificate at E≤atomicGroundEnergy p.b p.core λ, with gap exactly γλ/2. `eventual_atomicGround_properties_of_radialData` deduces normalized existence, `AtomicGroundSimple`, `HasGapAboveGround`, and energy comparison. The radial contract is assembled from A004 and A002; A002 also supplies the full-potential realization. Thus `CuspParameters.eventual_atomicGround_properties`, in `Remaining.lean`, requires only `BasicConditions` and gives those four conclusions. This wrapper does not remove classical dependencies: A004's radial content and A002's realization remain admitted. No nonradial spectral conclusion is directly admitted.

The positive factor h² does not change eigenvectors. It turns semiclassical energy E* into unscaled energy h⁻²E* and gap ch into c/h. `AtomicGroundEnergyBounds` now establishes

\[
 -\lambda^2\le E_{\rm atom}(\lambda)\le-\lambda^2+B\lambda,
 \qquad 1-B/\lambda\le\operatorname{scaledAtomicEnergy}(\lambda)\le1.
\]

Positivity at all sufficiently large couplings, eventual bound [1/2,1], and limit one are therefore proved, without admissions in this module. Radial and realization inputs remain explicit.

`CuspParameters.exists_atomicSourceFacts_of_radialData`, in `AtomicSourceRegime`, combines these results with the universal free-kernel contract. It chooses a threshold before L and supplies `AtomicSourceFacts` at every later coupling: a normalized canonical ground state, simplicity, gap, energy in [1/2,1], right representation for every L, and cell integrability if R<2L. The methods `hopping_eq_source` and `hopping_real` give exact identity with the source pairing and reality of hopping. `CuspParameters.atomic_source_regime` fills all three interfaces using A002+A003+A004 in `Remaining.lean`. It assumes no cell asymptotic and supplies neither their fine size nor hopping continuity.

The first local weighted estimates are also proved. `magneticForm_cutoff_eigenfunction`, in `MagneticLocalEnergy`, gives, for a smooth real compactly supported cutoff χ and actual eigenfunction φ,

\[
 q_{\lambda,V}(\chi\phi)-E\|\chi\phi\|_2^2
   =\int |\nabla\chi|^2|\phi|^2.
\]

`magnetic_agmon_weighted`, in `MagneticAgmonWeighted`, deduces, for smooth compactly supported η and smooth real F,

\[
 \int(\lambda^2V-E-2|\nabla F|^2)(\eta e^F)^2|\phi|^2
 \le2\int e^{2F}|\nabla\eta|^2|\phi|^2.
\]

All integrability follows from supports of η and its derivatives; neither globally integrable energy of φ nor a global bound on F is assumed. `AtomicAgmonRegion` eventually supplies λ²p.potential−Eatom≥λ²/4 outside the core. Consequently, a compact cutoff outside the core satisfies (λ²/4)mass(χφ)≤∫ cutoffGradientSq χ · ‖φ‖². This margin also holds on the cusps. `MagneticAgmonBounded` now removes spatial cutoffs by dominated convergence, bounding densities by a constant times |φ|² at each fixed coupling. `AtomicAgmonWeight` supplies a bounded smooth weight, zero up to 3r₀ and equal to dλ from 4r₀ onward, with |∇F|²≤λ²/16. The margin becomes λ²/8 and the weight vanishes on the exterior cutoff gradient's support.

[`AtomicAgmonGlobal`](../InfiniteZero/AtomicAgmonGlobal.lean) deduces, for the core and full potential, ∫_{‖x‖≥4r₀}|φ|²≤(C/λ²)exp(−2dλ) for λ>0 and every normalized eigenstate with E≤−3λ²/4. C,d>0 are fixed before λ, without globally integrable energy assumptions. The [detailed proof](AGMON_DECAY.md) gives C=16C_IMS. `AtomicGroundAgmon` now applies E≤−λ²+Bλ to supply the energy regime and ground-state tail from a fixed threshold. `CuspParameters.canonicalAtomicState_agmon_tail`, in `Remaining.lean`, gives the canonical-state version under `BasicConditions`, modulo A002+A004. This absolute decay supplies neither the weighted inverse nor fine action rates.

Appendix B must be distinguished from the sufficient variant now compiled:

1. **Literal B.1 remains open.** Rescaled-profile convergence in H²_loc and C⁰_loc requires local harmonic convergence, the difference equation, an interior elliptic estimate, and Sobolev embedding. A002 and A004 do not include this quantitative package.
2. **Exact radial tail proved.** `RadialCoreExteriorState` proves φ₀(r)=Γ_h K_h^(-e₀)(r), r>r₀, for the actual normalized positive state, by computing its ODE and applying real L² uniqueness through the Wronskian.
3. **Polynomial bound by comparison.** `RadialCoreProfileEstimates` gives f(r)≥c₀>0 on [0,h] from the full ODE and mass. `RadialCoreKernelComparison` gives f≤ΓK at all positive radii. At r=h, K(h)≤1/(πE_hh²) and E_h≥1/2 give Γ≥ch², then Γ⁻¹≤Ch⁻². The assembly `RadialCoreNormalizationLower` compiles. It uses neither A003 nor pointwise harmonic convergence.
4. **Auxiliary integral identity proved.** The A003 representation for a smooth compactly supported source becomes pointwise outside the core by `LandauExteriorConvolution`. Polar coordinates and real parts give the exact formula of `RadialCoreNormalization`, with normalized angular-average profile equal to 1 at zero. Neither positivity nor identification with the TeX regular Green factor is assumed.

The power h² is weaker than h^(3/2) in B.2, but suffices for uses L7.1 and L8.2: the polynomial exponent is free and their action margins are strict. The [proof and exact losses](RADIAL_NORMALIZATION.md) explain this justified departure. B.1 and the literal B.2 bound must not be marked proved.

## 7. Suggested order and boundary of the classical interfaces

```text
construction and support separation [proved]
       + A002 [classical realization already recorded]
       + A004 [unit-field radial spectral theorem and operator complement bound]
       + core energy bound, field conversion, and test-gap transfer [proved]
          ↓
core: ground state, e₀=−1+O(h), gap γh
          ↓
exterior mass O(h) → IMS → complement coercivity [proved]
          ↓
self-adjoint compression and inverse + Schur + intermediate value theorem [proved]
          ↓
full potential: existence + simplicity + gap ch [deduced, modulo A002+A004]
          ↓
energy ≤ radial energy [proved]
          ↓
IsAtomicGroundState / AtomicGroundSimple [deduced, modulo A002+A004]
resolvent energy → 1, eventually in [1/2,1] [proved under radial data]
          + A003 [standard closed-operator kernel, with proved domain/scaling bridges]
          ↓
representation ∀L, cells integrable for R<2L, hopping identity/reality [deduced]

radial branch: full ODE + mass → decreasing profile and f≥c on [0,h] [proved]
             + Wronskian comparison f≤ΓK → Γ≥c h², Γ⁻¹≤C h⁻² [proved under radial data and realization]
separate open branch: local harmonic convergence + ellipticity → literal B.1
Agmon branch: cutoff identity + bounded smooth weight + L² dominated convergence [proved]
            → global tail (C/λ²)exp(−2dλ), E≤−3λ²/4 [proved for core and full potential]
            → tail for actual ground states and canonical state [deduced under A002+A004]
            → exponential residual + quantitative certificate from the same root [proved]
            → exponential energy and L² comparison with fixed relative phase [deduced under A002+A004]
weighted branch: exact cusp weight + uniform smooth approximation + graph closure [proved]
               → exponential residual/defect + controlled projection → inverse ≤12/(γλ), E≤Ecore [proved]
               → same positive reference and certificate → response equation and actual weighted-forcing bound [proved]
               → coarse weighted residual → ‖exp(κλT)η‖₂≤Cexp(−dλ), c∈[1/2,1] [proved]
               + exact tail ΓK + exact kernel action + weighted gain + log-flat cost
               → k=0 forcing ≤ CΓλ²exp(−λJ−β₁log²λ) [proved]
               + Cauchy at radius h + log-flat jets + Leibniz → same bound for every j≤k [proved]
               → same actual φcore, energy, and Γ; sums of L² norms [proved]
               → L² response ≤ CcΓλ³exp(−λJ−β₁log²λ) [proved]
               + scalar equation and c≥1/2 → energy difference controlled by a single forcing factor [proved]
               + radial mass and upper bound on Γ → weighted radial jets without Γ [proved]
               → data f=−cWφ+cδφ: jets and local L² sums ≤CcΓλ²exp(−λJ−β₁log²λ) [proved]
               → same states and exact scaled PDE [assembled]
subsequent branch: pointwise elliptic propagation of η → fine scattered sources
```

The classical interfaces remain distinct: A002 for realization, justified in [CLASSICAL_OPERATOR_REALIZATION.md](CLASSICAL_OPERATOR_REALIZATION.md), and A004 for radial harmonic data, justified in [RADIAL_HARMONIC_CONTRACT.md](RADIAL_HARMONIC_CONTRACT.md). Coercive inversion, test-level IMS, domain transfer under bounded perturbation, actual compression, and nonradial spectral assembly are proved without additional admissions.

Quantitative elliptic estimates are not included in A004. The interior estimate used for correction jets is proved in Lean, without an additional admission. The fine harmonic profile of B.1 remains unclaimed; correction jets and pointwise source profiles, however, are proved via this explicit contract. The weighted L² response and its locally differentiated data retain the exact action and log-flat cost, beyond Agmon and exponential comparison.

The search in the Mathlib version used here finds adjoints and partially defined operators in `Analysis/InnerProductSpace/LinearPMap`, and a Lax–Milgram theorem for bounded coercive forms. It does not find a ready-made interface combining a closed magnetic form, self-adjoint compression, harmonic approximation, and the discrete spectrum of our operator. `InnerProductSpace/Rayleigh` does not prove existence of our unbounded minimizer; `InnerProductSpace/Spectrum` alone does not supply the general spectral calculus needed by the manuscript's projection proof. The now formalized Schur route avoids that need; the domain issues required for its construction were handled directly.

Cusp coercivity and nonradial atomic assembly are not admitted: they are proved with the radial input explicitly displayed. Forcing derivatives, elliptic propagation, pointwise scattered-source profiles, the active cell, and physical double-well Schur analysis are now proved in the steps below. B.1 and the literal power of B.2 remain unclaimed; Γ≳h² suffices for B.2's polynomial role in the identified uses. Smooth compact admissibility alone does not supply these analytic contracts; the proofs use the precise potential construction.

### Inverse, k=0 forcing, and fine weighted response established

`AtomicCuspWeightedInverse.exists_atomic_cusp_weighted_inverse_of_radialData` now proves a variant of `lem:weighted-inverse` (TeX lines 6950–7266) for every E≤Ecore. It therefore covers the actual ground energy, as needed by `sublemma:T3-4-weighted-response` (3396–3413), without claiming the upper part of the TeX symmetric window. For weight wλ=exp(κλT), the norm of the actual operator wλ ι (A_Q−E)⁻¹ Q wλ⁻¹ is ≤12/(γλ) in our convention. Constants precede λ, the radial reference precedes E,κ, and the resolvent precedes κ. `CuspWeight` constructs the nonnegative Lipschitz weight, zero up to 4r₀ and equal to normal coordinate t on closed cusp supports, including tips.

The assembly is proved without extending A002. `MagneticWeightedTest` gives the exact coefficient-one identity on tests. Gradient cost is absorbed in the IMS exterior margin; the inequality passes to the closed graph because it uses only bounded multipliers applied to both graph coordinates. `CuspWeightApproximation` supplies smooth weights converging to T with uniformly bounded gradients; strong multiplier convergence transfers the inequality to the exact weight. The Agmon tail makes the radial ground state's weighted defect small, and `AtomicResidualDecay` controls the compressed equation's rank-one term. Absorption retains γλ/4; projection adds at most a factor three. Neither operator-domain preservation by a Lipschitz weight nor an extra global form identity is assumed. See the [detailed natural-language proof](CUSP_WEIGHTED_INVERSE.md).

`AtomicGroundWeightedResponse` now applies this inverse to the correction of the same quantitative certificate q, for the same positive radial reference s. The identity ζ=(A_Q−Efull)⁻¹Q(λ²Wu) is proved in `WeightedSchurCorrection`. With c=(1+‖ζ‖²)⁻¹ᐟ² and η=v−cu=−cζ, one obtains ‖exp(κλT)η‖₂≤(12cλ/γ)‖exp(κλT)Wu‖₂. W is the actual perturbation, including ε. `SchurResponseEquation` simultaneously retains the uncompressed equation (A−Efull)η=−cλ²Wu+c(Efull−Ecore)u in the actual domain.

`AtomicWeightedResidual` bounds the actual weighted forcing by Kλ exp(−dλ) after a fixed reduction of κ₀, using Agmon and bounded height of T. `AtomicGroundWeightedDecay` concludes for the same s,q that ‖exp(κλT)η‖₂≤C exp(−dλ) and c∈[1/2,1]. Constants and thresholds precede λ; the positive reference and full vector precede κ. This first absolute bound is now strengthened by `LandauKernelExactActionUpper`, `CuspWeightedActionGain`, and `CuspFineForcingPointwise`. The weight leaves normal margin t/16; the log-flat majorant gives, for every 0<β₁<β, a pointwise bound CΓλ²exp(−λJ)exp(−β₁log²λ) on exp(κλT)Wφcore, with J=bridgeAction p.b (−λ⁻²Ecore) p.R. `AtomicCuspFineForcing` integrates this on the actual multiplier's fixed support, retaining β₁ in L² norm. The unscaled residual's factor λ² is distinct from this forcing Wφcore.

`AtomicGroundFineResponse` applies the preceding forcing bound to the same certificate: ‖exp(κλT)η‖₂≤CcΓλ³exp(−λJ)exp(−β₁log²λ). The same positive state's exact tail supplies Γ; `RadialCoreEnergyBounds` places Ecore,h=−λ⁻²Ecore in [1/2,1]. Constants and threshold precede λ, and states, c, and Γ precede κ. The correction has the full energy; that energy is not substituted for the core energy in J. These results close `sublemma:T3-4-weighted-forcing` for k=0 and `sublemma:T3-4-weighted-response`, modulo A002+A004 only. The [natural-language proof](CUSP_FINE_FORCING.md) explains why the nonoptimal power λ³ suffices for the manuscript's free polynomial.

`AtomicEnergyShiftForcing` adds the single-forcing-factor bound: the exact scalar equation gives |Efull−Ecore|≤(1+‖ζ‖)‖λ²Wφcore‖₂. Then c≥1/2 implies ‖ζ‖²≤3, hence ‖ζ‖≤2 and |λ⁻²(Efull−Ecore)|≤3‖exp(κλT)Wφcore‖₂. This version of `sublemma:T3-4-energy-forcing` assumes no new smallness or second Γ estimate. Forcing derivatives are now established. `AtomicFineResponseData` also handles the PDE data's second term using normalized radial jets without Γ; the full data are locally controlled with a single Γ factor. [Elliptic propagation](ATOMIC_RESPONSE_JETS.md) is then proved using the proved interior estimate; the [full scattered-source profile](CUSP_SCATTERED_SOURCE.md) is also established for the same states.

The physical assembly also compiles: `AtomicResponseWavefunction` chooses the smooth representative of the same certified vector and proves the response PDE pointwise. `WeightedWavefunctionL2` identifies its weighted norm with the actual integrated mass. `AtomicGroundWeightedDecomposition` assembles actual ground states φcore,ψfull, positive radial φcore, c∈[1/2,1], η=ψfull−cφcore, orthogonality, and mass(exp(κλT)η)≤C²exp(−2dλ), with the same states chosen before κ. The pointwise equation adds no elliptic or source bound. The compiled wrapper `CuspParameters.atomicGround_weighted_decomposition` requires only `BasicConditions` and also supplies cutoffs chosen before λ, via A002+A004 alone. A003 does not enter this assembly.
`AtomicGroundFineDecomposition`, also compiled, adds for the same wavefunctions their exact-tail coefficient Γ and weighted mass bounded by (CcΓλ³exp(−λJ)exp(−β₁log²λ))². Orthogonality and the pointwise PDE are retained, without converting this norm to a pointwise estimate. The wrapper `CuspParameters.atomicGround_fine_weighted_decomposition` requires only `BasicConditions` and 0<β₁<β, via A002+A004. New locally differentiated data are assembled separately in `AtomicFineResponseDecomposition`; this paragraph does not report the global-check result for that later stage.

An essential independent branch is `prop:exact-radial-tail` (1702–1775): identifying the actual core tail with a positive multiple of the radial kernel. The assembly from A002+A004 supplies a positive radial choice, using Helffer–Kachmar's classical Theorem 1.1(2). The integral kernel's ODE and uniqueness of its real radial L² branch are now proved in `LandauRadialEquation` and `LandauExteriorUniqueness`. Two differentiations under the integral are justified by Cauchy bounds; proper-time integration has no boundary term. Derivative energy is deduced from Caccioppoli before the Wronskian argument. The [detailed proof](RADIAL_EXTERIOR_KERNEL.md) leaves no derivative-decay hypothesis in final uniqueness.

`MagneticRadialReduction` and `RadialPlaneL2` prove the differential and polar connections. `RadialCoreExteriorState` applies uniqueness to the actual core state and obtains φcore=ΓK, Γ>0, for r>r₀. The threshold is chosen before coupling and a single coefficient holds throughout the exterior. This identity was not added to A004. The quantitative assembly avoids a new admission: `RadialEigenfunctionEquation` proves the actual profile's full ODE and `CoreRadialMonotonicity` proves monotonicity of the effective potential. Radial integrability and positivity imply f′≤0. Exterior mass O(h) gives f(0)≥sqrt(1/(2πr₀²)), then flux comparison gives f(r)≥f(0)(1−r²/(4h²)), hence f≥c₀>0 on [0,h].

The Wronskian W=r(fK′−f′K) satisfies W′=−λ²r vcore fK≥0 and vanishes in the exterior, where f=ΓK. Hence (f/K)′≥0 and f≤ΓK on r>0. The kernel bound at r=h concludes Γ≥ch²; the reciprocal bound follows. `RadialCoreNormalizationLower` assembles these facts, retaining Γ from the same exterior identity. Its build status is tracked in [RADIAL_NORMALIZATION.md](RADIAL_NORMALIZATION.md), with constants chosen before coupling and no dependence on A003.

The angular-average convolution formula is also proved with an explicit free-kernel interface, supplied by A002+A003, but its positivity or Green factorization is no longer needed on this route. The variant costs h⁻⁴ in L7.1 and h⁻² in L8.2. Strict exponential margins absorb these powers after increasing the free polynomial exponent M. Physical applications are assembled in [inactive cells](INACTIVE_CELLS.md) and [opposite-support estimates](OPPOSITE_SUPPORT_ESTIMATES.md), then relative parity errors.

### Full differentiated data and interior propagation

The [derivative block](CUSP_FORCING_DERIVATIVES.md) closes the content of `sublemma:T3-4-weighted-forcing` at every fixed maximum order. Cusp jets retain a strict log-flat margin, while Cauchy on discs of radius h supplies kernel jets with the exact action. After Leibniz, hⁿ leaves power h⁻². The L² passage and finite sums concern actual jets of Wφcore. `RadialCoreFineForcingDerivatives` keeps the same state, energy, and single Γ for all required orders. The wrapper `radialCore_fine_forcing_derivatives` supplies A002+A004 inputs without assuming an exterior tail or source estimate.

Full data are now controlled: f=−cWφcore+cδφcore, with δ=h²(Efull−Ecore). The energy-shift bound contains one Γ, so weighted jets of the radial factor are bounded **without adding Γ**. This route is formalized in [RADIAL_WEIGHTED_JETS.md](RADIAL_WEIGHTED_JETS.md):

1. `RadialCorePointwiseBound` compares normalized mass on a ball with the decreasing positive profile and gives φcore(rref)≤1/(√π rref).
2. `RadialCoreNormalizationUpper` applies the uniform kernel lower bound at rref=2r₀ and the actual core energy to obtain Γ≤Ch²exp((J(E,rref)+εact)/h), for every fixed loss εact>0. This holds for each Γ representing the same state's tail.
3. With rmin=R/2, the margin Δ=(rmin−rref)/2>0 permits fixing εact=Δ/4 and small κ₀ before coupling. The action absorbs the weight, normalization, and jet powers. After polynomial absorption, `RadialCoreWeightedJetBounds` gives, for every j≤n, exp(κT/h)hʲ‖Dʲφcore‖≤Cexp(−Δ/(4h)) on the fixed annulus.

`AtomicResponseDataJets` expresses both terms of f and linearity of their jets exactly. `AtomicFineResponseData` combines these with scalar control to obtain exp(κT/h)hʲ‖Dʲf‖≤CcΓh⁻²exp(−J/h)exp(−β₁log²(1/h)) on this annulus. The global weighted norm of η retains prefactor cΓh⁻³.

`CuspPacketNeighborhood` constructs fixed open sets U′ and U, with closed cusp supports in U′, closure U′ compact in U, and balls of radius 2h uniformly contained in U. `AtomicFineResponseDecomposition` assembles the same states, c and Γ, the scaled PDE throughout the plane, global mass of η, and masses and finite sums of L² norms of f's jets restricted to U. Constants precede λ and the finite family; states and coefficients precede κ. Weights and indicators are applied after differentiation. The term δφcore is not assumed compactly supported.

The compiled wrapper `CuspParameters.atomicGround_fine_response_data`, in `ClassicalAtomicFineResponseData`, chooses cutoffs and supplies A002+A004 inputs from `BasicConditions`, 0<β₁<β, and the maximum order. The [natural-language proof of the full data](ATOMIC_FINE_RESPONSE_DATA.md) specifies quantifiers and the single Γ factor. This block closes `sublemma:T3-4-forcing-derivatives`, with the allowed polynomial losses.

Interior propagation is now assembled in `AtomicFineResponseJets`, using the proved interior estimate. Rescaling, the Jacobian, uniform coefficient jets, and weight comparison are proved. The result retains the same states and gives exp(κλT)λ^-j‖Dʲη‖≤CcΓλ⁴exp(−λJ)exp(−β₁log²λ) on the closure of the inner neighborhood, for every j≤n. The wrapper `atomicGround_fine_response_jets` supplies inputs via A002+A004. See [the proof and its scope](ATOMIC_RESPONSE_JETS.md). Multiplication by λ²W and the scattered source's local log-flat factor are treated below; cells and the hopping asymptotic are also assembled in the [canonical channels](ACTIVE_CHANNEL_ASYMPTOTIC.md).

### Proved connection: scattered source with both log-flat factors

For the same states, define Fsc=λ²Wη. On each closed cusp support, use T=t and the local jets of W, controlled by C logFlat βlocal tStar t for every 0<βlocal<β. The local log-flat margin absorbs chart-change factors; it must not use the response's global coefficient β₁.

Apply `semiclassical_norm_iteratedFDeriv_mul_le` to Wη, keeping the weight after differentiation. Each term has a power h^k on W, bounded by one for 0<h≤1, and an already controlled weighted jet of η. The source's extra λ² leaves a bound with prefactor CcΓλ⁶: same action, global cost exp(−β₁log²λ), local cost logFlat βlocal tStar t, and decay exp(−κλt). This bound is now formalized in `CuspScatteredSourceJets`, then applied to the same actual states in `AtomicScatteredSourceJets`. `AtomicCuspSource` proves equality of germs and all jets with the corresponding branch, including tips; λ² and ε are those of the existing `atomicSource` definition. The wrapper `atomicGround_scattered_source_jets` uses only A002+A004. See [the proof and margins needed later](CUSP_SCATTERED_SOURCE.md). L¹ bounds are assembled below and used in [mixed and scattered cells](ACTIVE_SCATTERED.md). The relative incoming–incoming cell formula does not follow from these upper bounds alone: it is proved by [physical saddle analysis](INCOMING_PHYSICAL_ASYMPTOTIC.md).

The local incoming bound now compiles in `CuspIncomingSourceJets`: the exact tail and exterior jets give h^(-(n+2)), then the physical factor h⁻² leaves h^(-(n+4)). The radial gain retains J(Ecore,R)+t/8, and local margin βin<β absorbs potential derivatives. `AtomicSourceProfiles` applies this estimate to the same states as the scattered source, enlarging only the threshold to place core energy in [1/2,1] and ensure h≤h₀. The wrapper `atomicGround_source_profiles` uses A002+A004, with three independent margins and common constants before λ. See [the simultaneous profiles and their scope](CUSP_SOURCE_PROFILES.md).

### Proved connection: actual L¹ norms of cusp sources

At order zero, work with the existing branches `componentSource p h (cφ) 1/2` and `componentSource p h η 1/2`. Their integrability follows from `componentSource_integrable` and continuity of the states; the germs in `AtomicCuspSource` transfer the established bounds. No ε or h⁻² factor should be added a second time.

The chart domain is `(0,t₀) × (−s₀,s₀)`; `BasicConditions` requires s₀>0, not s₀≤1. `integral_image_cuspChart` supplies the actual Jacobian t², and `cuspPlus_support_subset_chartImage` supplies support in the chart image. One must bound ∫x,‖F x‖, rather than merely ‖∫x,F x‖. Tangential integration contributes the fixed factor **2s₀**.

For local coefficient βlocal and loss β′<βlocal, the m=2 moment of `eventually_logFlatLaplaceIntegral_le_exp` gives

\[
 \int_0^{t_0}t^2\operatorname{logFlat}_{\beta_{\rm local}}(t)
 e^{-a\lambda t}\,dt\le e^{-\beta'\log^2\lambda},
 \qquad a\ge a_{\min}>0,
\]

after a threshold independent of a. `integrableOn_logFlat_laplace` justifies integrability. Restriction to the open rectangle is handled from the compact closed rectangle; the lower branch is transported by reflection, a measure-preserving linear isometry. These norm and reflection connections are now proved in `CuspProfileIntegral`, `PlaneReflectionMeasure`, and `CuspProfileIntegralReflection`.

Fix κ=κ₀/2>0 before λ for the scattered source; no uniform bound with the extra local gain is expected down to κ=0. The scattered L¹ bound then keeps global coefficient βglobal and gains β′ from the local profile without identifying the two contributions. Choosing all three margins sufficiently close to β before the small integration losses gives strict margins for mixed and scattered cells.

`AtomicSourceL1` applies these integrals to the same physical states, with an intermediate local margin chosen before the constants. The incoming source satisfies CI cΓλ⁴exp(−λJ−βin log²λ); the scattered source satisfies CS cΓλ⁶exp(−λJ−(βglobal+βlocal)log²λ). `AtomicCuspSourceSupport` proves actual component support and identifies ∫‖F‖ with the norm of their actual L¹ class. The wrapper `atomicGround_source_L1` supplies these results under `BasicConditions` and three margins in (0,β).

`ComponentSourceL1Assembly` then proves the exact decomposition of each full component and the integrated triangle inequality. `AtomicComponentSourceL1` uses c≤1, λ⁴≤λ⁶, and the scattered source's stronger log-flat decay to conclude ‖F+‖₁+‖F−‖₁≤CΓλ⁶exp(−λJ−β₁log²λ). Integrability of all three components and the bound ‖F0‖₁≤Ccoreλ² concern the same full state. Its wrapper `atomicGround_component_source_L1` uses exactly the same admissions A002+A004. See [the natural-language proof](CUSP_SOURCE_L1.md).

## Proved connection: the seven physical inactive cells

`InactiveCellL1Bounds` combines L¹ norms with the already separated kernels. After a loss δhop in geometric margins, each inactive cell is bounded by C(Γ²+1)λ¹⁰exp(−λ(Aref+31δhop)); the norm of their sum satisfies the same estimate after multiplying C by seven. The factor λ¹⁰ comes exactly from h²λ⁶λ⁶, with h=λ⁻¹. Radial source actions and actions in the margins recombine into Aref.

`AtomicInactiveCells` instantiates these bounds using the states from `AtomicComponentSourceL1`, margin β/2, and combined thresholds for both energies and ground-state simplicity. `SourcePhaseInvariance` transports each bound to the canonical state without changing the radial decomposition. The wrapper `atomicGround_inactive_cells` has no remaining potential-specific analytic hypothesis to supply; it uses A002+A004.

`RelativeNormalizationRatio` controls the missing factor by 4Dλ⁴ for the same Γ. `SaddleNormalizationIdentity` identifies the inverse positive saddle size exactly with the existing normalizer up to a fixed constant, and absorbs its square with any loss h⁻ᴺ using half an action margin. `AtomicInactiveRelative` now assembles this with the positive Gaussian envelope ε²a²c²Γ²λ⁶√λ exp(−λAref)S_G². Loss λ⁸ suffices after canceling common factors; margin 31δ is weakened to 30δ, and absorption retains 15δ. All seven bounds and the sum of their norms are supplied for the selected and canonical states.

`SaddleEnvelopeComparison` proves the exact ratio S_G²/S_Tex²=‖1+w‖/Re w, its limit 1, and eventual comparison by 2. `ActiveSaddleEnvelopeComparison` then `AtomicInactiveRelativeTex` transfer bounds to the envelope with the actual modulus of the TeX complex Hessian factor. This remains distinct from the [active-cell asymptotic](ACTIVE_CHANNEL_ASYMPTOTIC.md), now proved by a separate chain.

Finally, `CuspIncomingSourceFormula` supplies both exact incoming sources on the charts, then their integrand with three complex kernels and magnetic phase. `CuspSourcePairingCoordinates` now performs the exact integral change of variables, with Jacobians t²u² and exterior factor −h²; see [the natural-language proof](INCOMING_SOURCE_FORMULA.md).

## Proved connection: removing the correction from the active cell

`AtomicActiveScatteredBounds` combines L¹ norms of the same sources with the exact-action bridge kernel: logarithmic costs 3β₀ and 4β₀. `SharpSaddleSize` retains coefficient 2β in control of the inverse squared saddle size, absorbing every fixed polynomial power. `AtomicActiveScatteredRelative` and its wrapper bound the difference between the full and incoming cell, for the actual and canonical states, by C envelopeTex exp(−δβ log²λ), δβ=(3β₀−2β)/2. The corollary `atomicGround_active_incoming_reduction` fixes β₀=3β/4 and obtains δβ=β/8 without an extra analytic hypothesis. The four-term identity justifies decomposition of actual pairings; no analytic continuation of the correction is used. See [the detailed natural-language proof](ACTIVE_SCATTERED.md). [Asymptotic integration of the incoming term](INCOMING_PHYSICAL_ASYMPTOTIC.md) and the [double-well spectral block](GLOBAL_PARITY_DOUBLET.md) are also proved, with no tunneling-specific admission.

## Normalized incoming profile and error on the saddle contour

The assembly is detailed in [INCOMING_MULTIPLIER.md](INCOMING_MULTIPLIER.md). `ActiveSaddleSlopeEnergy` obtains both semiclassical energies at 1+O(h); `ComplexCuspFrozenSlope` freezes only the linear slope. `AtomicCuspKernelProfile` then gives the actual normalized profile, uniformly close to 1 on the complex window tStar h^(3/4). `CuspKernelProfileHolomorphic` proves joint holomorphy; `CuspSaddleMultiplier` deduces integrability and smallness of the integrated error after normalization, uniformly in s,r. `CuspSourcePairingFubini` permutes the actual density's four coordinates and proves integrability of every normal fiber. `IncomingCuspDensityNormalization` exactly identifies the normalized density with the product of two scalar models and the profile; `CuspTangentialMass` gives the positive tangential coefficient. Local deformation with bounded amplitude and scalar suppression of the connector are proved in `LogFlatContourMultiplier` and `LogFlatMultiplierConnector`. Real truncation, both deformations, and integrated connectors are assembled in the physical connection below. No admission is added.

## Assembly of the physical incoming integral

[INCOMING_PHYSICAL_ASYMPTOTIC.md](INCOMING_PHYSICAL_ASYMPTOTIC.md) describes the now compiled assembly. `AtomicIncomingNormalAsymptotic` connects the actual real density to the saddle with truncation, two shifts, and exact Jacobians. `IncomingCuspTangentialIntegration` justifies the remaining integration; `AtomicIncomingIntegralAsymptotic` gives the complex limit N_h² Z_h incomingCuspIntegral → tStar⁶(π/β)Bs², then relative ratio →1. Both energies remain moving and distinct; the limiting coefficient is nonzero. No tunneling result is added to the admissions. At this milestone, conversion to the active cell with its strengths, envelope, and phase, then assembly with scattered and inactive cells and the double-well spectral block, remained to be completed.

## Canonical channels and asymptotic of the actual hopping

The [full active assembly](ACTIVE_CHANNEL_ASYMPTOTIC.md) now closes the cell/envelope/phase steps and nine-cell assembly. `IncomingCellTexAsymptotic` gives the relative identity with o(1) error, independently of atomic choices. `ConcreteChannelWitnesses` reuses the same states, c, and Γ in active and inactive estimates. `CanonicalChannelAsymptotics` constructs `ChannelAsymptotics`, then the cosine formula for actual hopping via the universal classical resolvent representation. The amplitude is exactly 2K*envelopeTex. `ClassicalCanonicalChannelAsymptotics` supplies these results from `BasicConditions`, with a separation threshold chosen before L; its only admissions are A002–A004. The manuscript's explicit rate and literal Hessian phase are not claimed: o(1) and the continuous Gaussian phase of slope Φ* suffice for the final goal.

## Overlap, parity trials, and final spectral assembly

The [canonical overlap](OVERLAP_AND_PARITY_TRIALS.md) is now controlled: for L≥4r₀ and all large λ, |canonicalOverlap|≤(C/λ)exp(−dλ), with constants and threshold uniform in L. The proof splits the plane into two regions: in each, one translated state lies in its tail; Cauchy–Schwarz and the atomic Agmon tail give the bound. The zero limit required by `CanonicalParitySchurData.overlap_tendsto` is thus available.

Canonical even and odd trials are smooth, L², normalized, orthogonal, and independent. Translated-state residuals are identified exactly, first as differential expressions, then in the operator domain. Their normalized combinations belong to that domain and have the expected parities.

[Coercivity on the complement of the two states](TWO_WELL_COERCIVITY.md) is now proved by IMS localization and the atomic gap, then passage to actual graph closure. Its margin is hRad.gap * λ / 4, with a threshold fixed before L and every normalized ground state. Self-adjoint parity restrictions, actual eigenmodes, the double-well gap, and both min–max identifications are [proved](GLOBAL_PARITY_DOUBLET.md). Hopping and splitting continuity are also established.

For relative errors, [universal sources and opposite-support reconstruction](OPPOSITE_SUPPORT_ESTIMATES.md) retain core and bridge actions. Opposite mass controls the defect and physical residuals; the quadratic Schur bound and comparison with the same envelope give canonicalDefect=o(A) and Σ±=o(A) in [CanonicalParityRelativeErrors](../InfiniteZero/CanonicalParityRelativeErrors.lean). The absolute Agmon bound alone did not suffice for this step.

[ConstructedMainAssembly](../InfiniteZero/ConstructedMainAssembly.lean) and [ConstructedMainProof](../InfiniteZero/ConstructedMainProof.lean) then construct the analytic data and operator conclusion rather than assuming them. `CuspParameters.mainConclusion` chooses the threshold after p, then treats every L beyond it; `elementaryPotential_main` fixes `elementaryParameters.potential`. The compiled proof of [thm_main](../InfiniteZero/Remaining.lean) follows modulo A002–A004, without a new admission specific to the original result.