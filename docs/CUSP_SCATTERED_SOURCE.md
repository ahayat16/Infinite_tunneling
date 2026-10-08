# The scattered source’s two log-flat factors

The Lean assembly and public wrapper are compiled. The wrapper depends on A002+A004, without A003 or `thm_main`. The [final proof](../InfiniteZero/Remaining.lean) is now compiled modulo the two classical admissions A002 and A004.

This block connects the [pointwise atomic-correction jets](ATOMIC_RESPONSE_JETS.md) to sublemma `T3-4-pointwise-response` of the [manuscript, lines 2927–2943](../article/Infinite_Zero_Tunneling_Lean_oriented_V2.tex#L2927). It separately retains the correction’s global log-flat cost and the potential’s local log-flat profile. No additional tunneling result is admitted: the classical interfaces for the physical connection are explicit arguments already used for the atomic correction.

## Exact source and common states

Fix `p.BasicConditions`, a weight `χ : CuspWeightCutoffs p`, maximum order `n`, and two independent numbers

\[
 0<\beta_g<\beta,\qquad 0<\beta_{\rm local}<\beta.
\]

The physical connection also takes radial-core spectral data, core and full operator realizations, and `hInterior : HasInteriorEllipticEstimate`. The radial data are assembled from A002+A004, the realizations come from A002, and the interior estimate is proved without admissions; A003 is not used here. The public wrapper [`atomicGround_scattered_source_jets`](../InfiniteZero/ClassicalAtomicScatteredSourceJets.lean#L23) supplies these interfaces and chooses the cutoffs; it requires only `BasicConditions`, both margins, and the maximum order.

Write `h=λ⁻¹`, `W=p.atomicPerturbation`, and

\[
 W=v-v^\circ=\varepsilon(q_++q_-),\qquad
 \eta=\psi-c\phi,
\]

where `φ` is an actual normalized positive radial core ground state, `ψ` an actual normalized full-potential ground state, `1/2≤c≤1`, and `⟨φ,η⟩=0`. The coefficient `Γ>0` belongs to the same state:

\[
 \phi(x)=\Gamma K_h^{\mathcal E_h^\circ}(|x|),\qquad |x|>r_0,
 \qquad \mathcal E_h^\circ=-h^2E_{\rm core}(\lambda).
\]

The scattered source is the existing project function

\[
 F^{\rm sc}=\operatorname{atomicSource}(h,W,\eta)
            =h^{-2}W\eta.
\]

On the cusp of sign `σ`, it locally agrees with `componentSource p h η 1` or `componentSource p h η 2`, namely `h⁻² ε qσ η`. Thus both `ε` and the physical factor `h⁻²` are present in the definition. The factor `c` in the bound below comes from the estimate on `η`: the definition of `Fsc` is not multiplied by another `c`.

Likewise, `Fin=h⁻² W(cφ)`. Linearity of `atomicSource` gives the exact identity `h⁻²Wψ=Fin+Fsc`. This decomposes the cusp source; the core source remains a separate component. These conventions match the [TeX, lines 2517–2564](../article/Infinite_Zero_Tunneling_Lean_oriented_V2.tex#L2517).

## Physical statement obtained by assembly

The theorem `CuspParameters.exists_atomicGround_scattered_source_jets_of_radialData` in [AtomicScatteredSourceJets](../InfiniteZero/AtomicScatteredSourceJets.lean) chooses `κ₀,Cη,Csc,N>0` before `λ`. For each `λ≥N`, it supplies the states and coefficients above; the same witnesses then satisfy the bounds for every `κ∈[0,κ₀]`, every `j≤n`, and both branches.

Set

\[
 A_\lambda=c\Gamma
   e^{-\lambda J_{\mathcal E_h^\circ}(R)}
   e^{-\beta_g(\log\lambda)^2}.
\]

This `Aλ` is the common source-bound factor, not the active-cell envelope. The theorem first retains

\[
 e^{\kappa\lambda T(x)}h^j\|D^j\eta(x)\|
   \le C_\eta\lambda^4A_\lambda,
 \qquad x\in\overline{U'_{\rm pkt}}.
\]

On each closed cusp support, with `t=normalCoordinate x` on the upper branch and `t=normalCoordinate (reflection x)` on the lower branch, it gives

\[
 \boxed{
 h^j\|D^jF^{\rm sc}(x)\|
 \le C_{\rm sc}\,c\Gamma\lambda^6
   e^{-\lambda J_{\mathcal E_h^\circ}(R)}
   e^{-\beta_g(\log\lambda)^2}
   \operatorname{logFlat}(\beta_{\rm local},t_*,t)
   e^{-\kappa\lambda t}.}
\]

For `t>0`, the local profile is `exp(-βlocal log²(t*/t))`; its extended value for `t≤0` is zero. Derivatives are Fréchet jets in physical coordinates, subsequently multiplied by `hʲ`. Their norm controls every evaluation on directions of norm at most one. These are neither derivatives of the function composed with the cusp chart nor derivatives of the weight.

The same statement retains smoothness of `η` and the right-hand side `f`, L² membership of `η`, orthogonality, and the exact pointwise equation

\[
 h^2(H_{\lambda,v}-E_{\rm full})\eta
   =-cW\phi+c h^2(E_{\rm full}-E_{\rm core})\phi=f.
\]

Maximum order `n` is chosen before the constants and states. One witness family works for all orders `j≤n`, all points, and both branches. The statement does not supply a simultaneous choice for all natural orders; an application requiring finitely many derivatives first selects their maximum order.

## Natural-language proof and Lean correspondence

1. **Leibniz with the weight after differentiation.**
   [WeightedSemiclassicalProduct](../InfiniteZero/WeightedSemiclassicalProduct.lean) proves `weighted_semiclassical_norm_iteratedFDeriv_smul_le_of_bounds`. If `‖Dⁱq(x)‖≤AᵢL` and `w hᵏ‖Dᵏu(x)‖≤M`, semiclassical Leibniz gives
   \[
    wh^j\|D^j(qu)(x)\|
       \le\Bigl(\sum_{i=0}^j\binom ji A_i\Bigr)LM,
       \qquad 0\le h\le1.
   \]
   Every term retains exactly `hⁱ hʲ⁻ⁱ=hʲ`. The multiplier’s factor `hⁱ` is then bounded by one. A finite sum gives a common positive constant for `j≤n` in `exists_weighted_semiclassical_smul_bound_upTo`. The weight `w≥0` is simply a value at the point considered: this algebraic lemma requires no weight regularity.

2. **Actual sources and equality of germs.**
   [AtomicCuspSource](../InfiniteZero/AtomicCuspSource.lean) expands the two exact components, with `ε` and `h⁻²`. The cusps have disjoint closed supports. Near a point of the upper support, the lower component therefore vanishes identically, and conversely. `atomicPerturbation_source_eventuallyEq_plus/minus` expresses this equality of germs; `iteratedFDeriv_atomicPerturbation_source_eq_plus/minus` transfers it to every jet. Equality of values on the support alone would not suffice. The germ comparison itself does not assume smoothness of `η`; source smoothness and jet-norm lemmas are supplied separately.

3. **Retaining the second log-flat factor.**
   [CuspScatteredSourceJets](../InfiniteZero/CuspScatteredSourceJets.lean) uses the proved jet bounds for `q₊,q₋` in [ConstructionCuspJetBounds](../InfiniteZero/ConstructionCuspJetBounds.lean). Every local inverse-power and logarithmic loss has already been absorbed by passing from `β` to `βlocal<β`. On the closed supports, `T=t` by `χ.weight_eq_normal_on_plus/minus`, and those supports lie in `U'pkt`. The generic Leibniz lemma therefore applies with `L=logFlat βlocal tStar t`; then remove `exp(κλt)` and multiply by `h⁻² ε=λ² ε`. The intermediate result is `C λ² M L exp(-κλt)`. The constant is fixed before `λ,κ,η,M` and common to both branches. Tips are included: the local profile vanishes there and the flat-extension jet control forces the corresponding vanishing.

4. **Substituting the actual correction.**
   [AtomicScatteredSourceJets](../InfiniteZero/AtomicScatteredSourceJets.lean) instantiates the preceding result with the same witnesses as [AtomicFineResponseJets](../InfiniteZero/AtomicFineResponseJets.lean) and `M=Cη λ⁴ Aλ`. This gives `λ²λ⁴=λ⁶`, losing neither the global factor `exp(-βg log²λ)` nor the local profile. No scattered-source bound is assumed in this physical connection. The intermediate conditional lemma is supplied with the already-proved jets of the actual state.

## Use and limitations

The coefficients `βg` and `βlocal` are independent in the result. The global cost comes from the weighted solution, the local cost from the multiplier. The former is never used to absorb a local singularity in `t`.

To apply the log-flat integrals, fix `κ>0` before `λ`, for example `κ=κ₀/2`. The API also permits `κ=0`, but that choice alone does not supply the positive source slope used in these integrations and the manuscript’s route estimates. Source norms use the actual Jacobian `t² dt ds`. Integrating the scattered bound therefore supplies cost `βg+βlocal`, up to a small loss. The connection to actual [L¹ norms](CUSP_SOURCE_L1.md) and [active scattered cells](ACTIVE_SCATTERED.md) is now proved.

Positivity of both coefficients alone does not suffice to exclude responses from the active cell. If the incoming bound retains a local coefficient `βin`, the costs are

\[
 \beta_{\rm in}+\beta_g+\beta_{\rm local}
 \quad\text{(mixed)},\qquad
 2(\beta_g+\beta_{\rm local})
 \quad\text{(double-scattered)}.
\]

They must strictly exceed `2β`, the active-envelope cost, with enough margin for small integration losses. Choosing `βg=βlocal=β₀`, `2β/3<β₀<β`, and an incoming bound at least as strong as coefficient `β₀`, recovers the margins `3β₀−2β` and `4β₀−2β` of the [TeX, Section 6.8](../article/Infinite_Zero_Tunneling_Lean_oriented_V2.tex#L5386). Any fixed power `λᴹ`, even depending on the preselected order, can be absorbed by part of this quadratic margin in `log λ`. The bound `c≥1/2` also controls inverse normalization factors.

The source’s radial action is exactly that of the core, `Gp,h=J(ℰ°h,R)`. The cell bridge kernel uses the full potential’s positive scaled energy `ℰh=-h²Efull`. Their common action is `A*,h=2Gp,h+J(ℰh,2L−R)`; the two energies are not silently identified. Their comparisons and uniformity must be used explicitly in any step that replaces or varies them.

This block does not prove the active cell’s leading asymptotic. In particular, it supplies neither the relative incoming prefactor \(h^{-7/2}\), its local holomorphic continuation, nor complete integration with moving energy. Those conclusions require the exact radial identity and kernel asymptotics, as in the [incoming active-layer lemma](../article/Infinite_Zero_Tunneling_Lean_oriented_V2.tex#L4610). The scattered source remains on real supports and is not analytically continued. The [cells](ACTIVE_CHANNEL_ASYMPTOTIC.md), [physical double-well reduction](GLOBAL_PARITY_DOUBLET.md), and [final assembly of thm_main](../InfiniteZero/ConstructedMainProof.lean) are now proved in separate steps.
