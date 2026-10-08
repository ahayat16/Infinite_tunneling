# Opposite support, relative Schur errors, and final assembly

Universal transport of L¹ norms compiles and is audited without additional admissions in [UniversalComponentSourceL1.lean](../InfiniteZero/UniversalComponentSourceL1.lean). It allows the same radial references and coefficients as [ConcreteChannelWitnesses.lean](../InfiniteZero/ConcreteChannelWitnesses.lean), while taking the actual canonical state as the full state. The reconstruction below also compiles without a new admitted statement in [OppositeSupportReconstruction.lean](../InfiniteZero/OppositeSupportReconstruction.lean). The fine chain is now assembled in [AtomicOppositeSupportFineBounds](../InfiniteZero/AtomicOppositeSupportFineBounds.lean), [CanonicalParityFineBound](../InfiniteZero/CanonicalParityFineBound.lean), and [CanonicalParityRelativeErrors](../InfiniteZero/CanonicalParityRelativeErrors.lean). It proves that the diagonal defect and both Schur corrections are `o(A)` for the same witnesses as the hopping asymptotic. Classical interfaces remain explicit arguments in these results. The final assembly [ConstructedMainProof](../InfiniteZero/ConstructedMainProof.lean) and `Remaining.thm_main` have compiled; `thm_main` no longer has a direct `sorry`. Its only admitted inputs are A002–A004. The final global check and inventory regeneration are managed separately.

## L¹ norms do not depend on the choice of witnesses

Fix the potential, its elementary conditions, radial spectral data, core and full-well realizations, a pair of cutoffs, and a margin `0<β₁<β`. The theorem `exists_universal_component_source_L1_of_radialData` gives `C,T>0` **before** the coupling. For any `λ≥T`, one may then supply arbitrarily:

- a normalized positive radial core ground state `φcore`;
- a real coefficient Γ giving its actual exterior tail `φcore=ΓK`;
- any normalized ground state ψ of the full potential.

The three sources `Fi=componentSource p λ⁻¹ ψ i` are integrable and satisfy

\[
 M_0:=\int|F_0|\le C_{\rm core}\lambda^2,
 \qquad M_++M_-\le C\Gamma\lambda^6
 e^{-\lambda G}e^{-\beta_1(\log\lambda)^2},
 \quad G=J_b(E_{\rm core},R).
\]

Here `Ecore=−λ⁻² atomicGroundEnergy p.b p.core λ` is the positive rescaled energy entering the kernel. The conclusion selects no new `φcore`, Γ, or ψ. It does not separately assume `Γ>0`: the exterior identity and transport from the positive witness suffice to identify this coefficient with the positive coefficient already constructed.

The proof combines two already verified uniqueness results. First, `RadialCoreSpectralData.positive_ground_coefficient_unique` identifies the two normalized positive references pointwise, then their exterior coefficients. Next, simplicity of the full ground state writes `ψ=z•ψ₀`, with `‖z‖=1`, at each fixed coupling. Each source is linear in the state, so its pointwise norm and integral of the norm are unchanged. The new lemma `AtomicGroundSimple.integral_norm_componentSource_eq` makes this transport explicit. No coupling-continuity of the phase choice is involved.

The threshold is the maximum of the thresholds for the existing L¹ estimate, radial simplicity, and full-well simplicity. For a witness `W : ConcreteChannelWitnesses p L`, enlarge it by `W.threshold` and instantiate `φcore=W.φ λ`, `Γ=W.Γ λ`. The canonical state is an actual ground state by `canonicalAtomicState_spec` and the existence supplied by `W.full_ground`. It therefore retains the same bounds with the same coefficient Γ.

The analytic interfaces remain explicit arguments: the proved interior elliptic estimate, radial data, and realizations. Universal transport does not admit them and does not use the resolvent identification A003.

## A single reconstruction, almost everywhere

The resolvent representation of the actual right state gives

\[
 \phi_R(x)=-h^2\int K_{b,h,E}(x,y)\,F_R(y)\,dy,
 \qquad h=\lambda^{-1},
\]

almost everywhere. The affine change `y=d−z` reduces the physical source to the sum of the three `componentSource` terms. Magnetic factors have norm one. Support separation avoids the kernel diagonal; continuity and compact support of the sources give their integrability. A kernel bound on each actual support also makes the convolution absolutely integrable before applying the triangle inequality.

The lemma `norm_rightState_le_componentL1_of_representation` holds pointwise wherever the representation holds. Its corollary `RightResolventRepresentation.ae_norm_rightState_le_componentL1` explicitly retains an almost-everywhere conclusion on the target set. It does not choose a representative to turn an a.e. identity into a pointwise identity without justification.

For `L≥cert.L₀`, write `D=2L−R`, `G=J_b(Ecore,R)`, and `J=J_b(Efull,D)`. The geometric result distinguishes the two energies: `Efull∈[1/2,1]` and `Ecore∈(0,2]` are independent. The proved kernel bounds give, almost everywhere on the opposite-well support,

\[
 \|\phi_R(x)\|\le B_\lambda,
 \qquad
 B_\lambda=C\left[
 \lambda^{-2}e^{-\lambda(G+J)}M_0
 +e^{-\lambda J}(M_++M_-)
 \right].
\]

The constant is chosen at fixed separation before λ, the energies, and the state. The core contribution already contains action `G+J` thanks to the separation margins. For cusp sources, the kernel carries J and a factor λ², canceled by the exterior h²; the L¹ bound supplies G. Active cross cells use the exact action bound, without an artificial `exp(η/h)` loss.

## From the a.e. estimate to actual defects and masses

For a continuous compactly supported potential V, `|V|≤1`, and continuous state u, an a.e. bound `‖u‖≤B` on `{V≠0}` suffices to give

\[
 \left|\int V|u|^2\right|\le B^2\int|V|,
 \qquad
 \int|Vu|^2\le B^2\int|V|.
\]

The second inequality uses `|V|²≤|V|`. All integrability statements come from compact support of the multiplier; no global integrability of the state's energy density is assumed. `potential_weighted_mass_le_of_ae_norm_bound` proves this step. After translation, the factor `∫|V|` is exactly that of the fixed potential, independently of L, the energies, and coupling. `exists_oppositeSupport_mass_bound_componentL1` applies this principle to `V(x+d)` and the right state with the same Bλ.

## Fine mass bound with the same exterior coefficient

`exists_atomic_oppositeSupport_mass_fine_bound_of_radialData` instantiates the actual representation, energy windows, and universal L¹ norms at a common threshold. A003 supplies the standard closed-operator resolvent formula; the universal smooth-solution representation follows from the proved domain and scaling bridges using A002. The bound `Γ⁻¹≤CΓ λ²` absorbs the core term while retaining the supplied exterior coefficient. Since `c≥1/2`, we obtain

\[
 B_\lambda\le Cc\Gamma\lambda^6e^{-\lambda(G+J)},\qquad
 \left|\int v^L|\phi_R|^2\right|,
 \quad\operatorname{mass}(v^L\phi_R)
 \le Cc^2\Gamma^2\lambda^{12}e^{-2\lambda(G+J)}.
\]

Constants and threshold precede the coupling, states, c, and Γ. The theorem applies to every actual full ground state and every positive radial reference giving the exact tail: no independent witness is chosen at this step.

## Exact connection to the physical residuals

[PhysicalResidualMass.lean](../InfiniteZero/PhysicalResidualMass.lean) compiles and is audited without additional admissions. For every representative uR of the actual right atomic state in the double-well domain, it proves

\[
 \|(H_{\rm double}-E_{\rm atom})u_R\|^2
 =\lambda^4\,\operatorname{mass}
   \bigl(v(x+d)\phi_R(x)\bigr).
\]

The analogous left identity and equality of the two masses follow from covariance and inversion. They hold for all representatives in the actual domain: the operator equation comes from bounded-potential transport, and almost-everywhere equality then identifies the L² classes. Residual smallness is not a hypothesis.

If `|translatedOverlap|≤1/2`, normalization of each parity trial costs at most one. The triangle inequality and symmetry therefore give, for every representative q of the actual normalized trial,

\[
 \|(H_{\rm double}-E_{\rm atom})q\|^2
 \le 4\lambda^4\,\operatorname{mass}
   \bigl(v(x+d)\phi_R(x)\bigr).
\]

The theorem `IsAtomicGroundState.normalizedParityTrial_residual_sq_le_mass` allows direct application of the reconstruction mass bound. [CanonicalParityCorrection](../InfiniteZero/CanonicalParityCorrection.lean) defines the actual correction `σ±=a±−E±`. The assembly [CanonicalParityCorrectionMass](../InfiniteZero/CanonicalParityCorrectionMass.lean) gives, with `g=hRad.gap>0`,

\[
 0\le\sigma_\pm\le\frac{32}{g}\lambda^3
                  \operatorname{mass}(v^L\phi_R).
\]

The diagonal defect costs λ², hence λ¹⁴ after the mass bound; the correction costs λ³, hence λ¹⁵. For `λ≥1`, both are therefore controlled by a common majorant of the form

\[
 Q_\lambda=Kc^2\Gamma^2\lambda^{15}e^{-2\lambda(G+J)}.
\]

It is the Schur correction, after division by the gap, that is compared with the envelope below. The chain does not use a separate claim that the squared residual is `o(A)`.

## The action margin giving the relative comparison

The TeX envelope retains the distinct energies and the same `c,Γ`:

\[
 A_{\rm Tex}=\varepsilon^2a^2c^2\Gamma^2\lambda^6\sqrt\lambda\,
 e^{-\lambda(2G+J)}S_{\rm Tex}(\lambda^{-1})^2.
\]

[OppositeSupportEnvelopeComparison](../InfiniteZero/OppositeSupportEnvelopeComparison.lean) uses exactly `2(G+J)=(2G+J)+J`. For `D=2L−R>0` and `Efull≥1/2`, `J≥sqrt(Efull)D≥D/2`. The remaining factor is therefore `λ⁹ exp(−Dλ/2)` after extracting `λ⁶ exp(−λ(2G+J))`. The already proved scalar saddle result eventually gives

\[
 S_G^{-2}\lambda^9e^{-D\lambda/2}\le e^{-D\lambda/4}.
\]

Using `sqrt λ≥1` and `S_G²≤2S_Tex²` gives the explicit control

\[
 Q_\lambda\le\frac{2K}{\varepsilon^2a^2}
 A_{\rm Tex}\,e^{-D\lambda/4}.
\]

The threshold precedes `λ,c,Γ`. The `IsLittleO` corollary allows arbitrary eventually positive functions `c(λ),Γ(λ)`, without further bounds or continuity. The wrapper under radial data itself deduces the threshold for `Efull≥1/2`; no new asymptotic hypothesis is introduced.

## Same witnesses and theorem conclusion

`canonicalParity_errors_isLittleO_of_radialData` takes the same `W : ConcreteChannelWitnesses p L` as the hopping asymptotic and proves `canonicalDefect=o(A_Tex)` and `σ±=o(A_Tex)` with `W.c,W.Γ`. The positive tangential factor, fixed in coupling, allows exactly the channel amplitude `2 K* A_Tex`. Since the overlap tends to zero, `nonempty_canonicalParitySchurData_of_radialData` constructs the required actual Schur package without assuming its relative errors.

[ConstructedMainAssembly](../InfiniteZero/ConstructedMainAssembly.lean) combines this package, the oscillatory continuous hopping, splitting continuity, and actual global modes. [ConstructedMainProof](../InfiniteZero/ConstructedMainProof.lean) constructs all its inputs under only the explicit analytic interfaces. In [Remaining](../InfiniteZero/Remaining.lean), `elementaryPotential_main` literally fixes `elementaryParameters`, and `thm_main` deduces the existential statement. The potential is therefore chosen before L₀, then each `L≥L₀`. The only remaining admissions are A002 (realization), A003 (standard free resolvent), and A004 (unit-field radial spectral theorem). The interior elliptic estimate is proved without admissions. No tunneling-specific estimate is added to the final hypotheses.
