# Simultaneous profiles of actual cusp sources

The incoming and scattered sources have local bounds on both closed supports, at every fixed order, for **the same states, normalization c, and coefficient Γ**. The incoming lemma [CuspIncomingSourceJets](../InfiniteZero/CuspIncomingSourceJets.lean) is compiled and its targeted audit finds only standard Lean axioms. The assembly [AtomicSourceProfiles](../InfiniteZero/AtomicSourceProfiles.lean) and its public wrapper [ClassicalAtomicSourceProfiles](../InfiniteZero/ClassicalAtomicSourceProfiles.lean) compile without warnings of their own. The wrappers depend on A002+A004, without A003 or the final theorem `thm_main`.

The result is a version of the differentiated bounds of [Theorem 3.4](../article/Infinite_Zero_Tunneling_Lean_oriented_V2.tex#L2566) with explicit polynomial losses. It retains the exact action and local log-flat profiles. It does not replace the manuscript’s leading incoming prefactor `h⁻⁷ᐟ²`.

## Sources, energy, and order of choices

Write

\[
 h=\lambda^{-1},\qquad W=p.\mathrm{potential}-p.\mathrm{core}
   =\varepsilon(q_++q_-),\qquad
 \mathcal E_h^\circ=-h^2E_{\rm core}(\lambda),
 \qquad G_h=J_b(\mathcal E_h^\circ,R).
\]

For an actual normalized positive radial core state `φ`, a full ground state `ψ`, and `c∈[1/2,1]`, set `η=ψ−cφ`. The coefficient `Γ>0` belongs to the exact tail of this same state:

\[
 \phi(x)=\Gamma K(b,h,\mathcal E_h^\circ,\|x\|)
 \quad\text{for }\|x\|>r_0.
\]

The two functions used are the existing physical definitions:

\[
 F^{\rm in}=\operatorname{atomicSource}(h,W,c\phi)=h^{-2}Wc\phi,
 \qquad
 F^{\rm sc}=\operatorname{atomicSource}(h,W,\eta)=h^{-2}W\eta.
\]

Thus `ε` is already included in W, and `h⁻²` in `atomicSource`. Linearity proved in [AtomicCuspSource](../InfiniteZero/AtomicCuspSource.lean) gives exactly `atomicSource h W ψ = Fᶦⁿ+Fˢᶜ`. This is the cusp part of the atomic source; the core component is not added to these profiles.

Fix the potential, weight cutoffs, maximum order `n`, and three **independent** margins

\[
 0<\beta_{\rm in}<\beta,\qquad
 0<\beta_{\rm global}<\beta,\qquad
 0<\beta_{\rm local}<\beta.
\]

The theorem `exists_atomicGround_source_profiles_of_radialData` then chooses `κ₀,Cin,Csc,threshold>0`. For each `λ≥threshold`, it chooses `φ,ψ,c,Γ` once, before `κ∈[0,κ₀]`, order `j≤n`, and the point on either support. The correction is smooth, belongs to L², and satisfies `waveInner φ η=0`. The threshold ensures that the actual core energy lies in `[1/2,1]` and h is small enough for the incoming bound.

The assembly retains as hypotheses the core radial data, core/full operator realizations, and universal interior elliptic estimate. It assumes no source or response estimate. The wrapper [`atomicGround_source_profiles`](../InfiniteZero/ClassicalAtomicSourceProfiles.lean) supplies these inputs from `BasicConditions`, the three margins, and n, through A002 and A004. A003 is not used in this profile construction.

## Incoming bound with explicit polynomial loss

Write `t₊(x)=normalCoordinate x` and `t₋(x)=normalCoordinate (reflection x)`. For `t>0`, write

\[
 L_\alpha(t)=\exp[-\alpha\log^2(t_*/t)],
 \qquad L_\alpha(t)=0\quad(t\le0).
\]

On each cusp’s closed support, for every `j≤n`, the result is

\[
 h^j\|D^jF^{\rm in}(x)\|
 \le C_{\rm in}c\Gamma h^{-(n+4)}L_{\beta_{\rm in}}(t_\pm(x))
       \exp\!\left[-\frac{G_h+t_\pm(x)/8}{h}\right].
\]

`Dʲ` is the real Fréchet jet, measured in operator norm; the bound therefore also controls its evaluation on directions of norm at most one. The constant and threshold are common to every order `j≤n`. The analytic lemma `exists_cusp_incoming_source_jet_bound` is more general: the energy may be any `E∈[1/2,1]`, `c,Γ≥0`, and the state need only be smooth with exterior tail ΓK. These parameters are all quantified after the constants.

The proof has four concrete steps.

1. On the fixed annulus containing the supports, the [jets of the actual radial tail](../InfiniteZero/ExteriorRadialJetBounds.lean) simultaneously satisfy, for `k≤n`, `‖Dᵏ(cφ)(x)‖≤CK cΓ h⁻⁽ⁿ⁺²⁾ exp(−J(E,‖x‖)/h)`. The exterior identity is used locally; no new state or coefficient is chosen.
2. The [cusp jets](../InfiniteZero/ConstructionCuspJetBounds.lean) are bounded by `Ai Lβin(t±)`. The strict margin `βin<β` absorbs the inverse powers and logarithmic polynomials produced by derivatives, including at the tip.
3. [WeightedSemiclassicalProduct](../InfiniteZero/WeightedSemiclassicalProduct.lean) applies Leibniz with weight one, then a common constant for all required orders. The physical factor `εh⁻²` produces the stated power `h⁻⁽ⁿ⁺⁴⁾`. Choosing `h≤1` allows this common bound, without claiming to optimize the power for each order.
4. The [geometric action gain](../InfiniteZero/CuspWeightedActionGain.lean) is exactly `J(E,‖x‖)≥J(E,R)+t±(x)/8` on the closed support. No part of the base action `J(E,R)` is lost.

Separation of the **closed supports** ensures that the other cusp vanishes identically near each point considered. `AtomicCuspSource` therefore identifies the germs, and then every jet, of the W source with those of `componentSource` of index 1 or 2. This includes tips and boundaries; it does not rely on mere pointwise equality before differentiation.

## Scattered profile retained in the same assembly

The [scattered bound](CUSP_SCATTERED_SOURCE.md) simultaneously gives

\[
 h^j\|D^jF^{\rm sc}(x)\|
 \le C_{\rm sc}c\Gamma h^{-6}e^{-G_h/h}
    e^{-\beta_{\rm global}\log^2(1/h)}
    L_{\beta_{\rm local}}(t_\pm(x))
    e^{-\kappa t_\pm(x)/h},\qquad j\le n.
\]

The global cost comes from the weighted solution and elliptic propagation of η. The local profile comes from the cusp multiplier after Leibniz. The weight is applied after differentiation; the exact Lipschitz weight is never differentiated. The global cost is not reused to absorb singularities of the local profile.

Both bounds use `G_h=J(𝓔°h,R)`, with the **core** energy. The kernel between two sources in the cells uses the full-potential energy. This result does not implicitly replace either energy with the other.

## Margins and completed connections

All three margins may be chosen before coupling in `(2β/3,β)`, for example all equal to `5β/6`. Log-flat integrations with small losses give the costs

\[
 \beta_{\rm in}+\beta_{\rm global}+\beta_{\rm local}>2\beta
 \quad\text{for a mixed cell},
 \qquad
 2(\beta_{\rm global}+\beta_{\rm local})>2\beta
 \quad\text{for a double-scattered cell}.
\]

These strict margins absorb fixed polynomial losses. To use the scattered-source slope, also fix `κ>0` before λ, for example `κ₀/2`; the API permits κ=0 but assigns no positive slope to it.

Passage to [L¹ norms](CUSP_SOURCE_L1.md) in the charts, with Jacobian `t² dt ds` and transverse factor `2s₀`, is now proved. Application to the [seven inactive cells](INACTIVE_CELLS.md) is assembled, including their comparison with the positive saddle envelope. The cost inequalities above concern the active cell’s scattered terms; their [relative negligibility](ACTIVE_SCATTERED.md) is now proved, with margin β/8 after fixing β₀=3β/4.

The proved incoming bound is the strict-margin, polynomial-loss version of the jets in `sublemma:T3-4-incoming`. Even at order zero, it uses `βin<β` and `h⁻⁴` here. It establishes neither the TeX’s optimal `h⁻⁷ᐟ²` bound with local coefficient β, nor the active-layer relative expansion, amplitude, or holomorphic continuation. The [exact incoming formula in the charts](INCOMING_SOURCE_FORMULA.md) now connects physical sources to the complex kernels already constructed. The exact integral change of variables for the incoming part and removal of scattered terms are proved. The [leading incoming asymptotic](INCOMING_PHYSICAL_ASYMPTOTIC.md) and [double-well spectral connection](GLOBAL_PARITY_DOUBLET.md) are also established separately. They enter the [proof of thm_main](../InfiniteZero/Remaining.lean), with the three classical admissions A002–A004.
