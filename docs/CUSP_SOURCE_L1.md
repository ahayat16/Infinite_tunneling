# Actual L¹ norms of atomic sources

Local incoming- and scattered-source profiles yield L¹ bounds through the real cusp change of variables. The Jacobian is exactly `t²`, and the transverse factor is **`2s₀`**, the length of `(-s₀,s₀)`. No implicit normalization replaces this factor with 2.

The generic lemmas in [CuspProfileIntegral](../InfiniteZero/CuspProfileIntegral.lean), their [reflection transfer](../InfiniteZero/CuspProfileIntegralReflection.lean), and the [support and norm connections](../InfiniteZero/AtomicCuspSourceSupport.lean) are compiled and audited without admissions. The physical assemblies `AtomicSourceL1` and `AtomicComponentSourceL1`, and their classical wrappers, are also compiled. Both wrappers depend on A002+A004, without A003 or `thm_main`. The [final assembly](../InfiniteZero/ConstructedMainProof.lean) and [thm_main](../InfiniteZero/Remaining.lean) are now compiled modulo the three classical admissions A002–A004.

## Support, integrability, and actual L¹ space

Consider a continuous wavefunction F such that `Function.support F ⊆ Function.support p.cuspPlus`. The cusp’s closed support is compact, so F also has compact support. Continuity then supplies `Integrable F` before any estimate of its integral. We do not rely on the conventional value assigned to a nonintegrable integral.

For physical sources, `componentSource_plus_support_subset` and `componentSource_minus_support_subset` give this support inclusion for every wavefunction. Continuity follows from the state and potential. On each cusp’s closed support, `atomicPerturbation_source_eq_plus/minus` identifies the W source with the corresponding component, including at the tip.

The estimated quantities are integrals of norms, accompanied by integrability proofs. They are exactly the norms of Mathlib’s L¹ quotient:

\[
 \|h_F.\mathrm{toL1}(F)\|
   =\int_{\mathbb R^2}\|F(x)\|\,dx.
\]

This is `norm_toL1_eq_integral_norm hF`, generic in the measure and target normed space. No new “source norm” convention is introduced.

## Exact reduction to the second-order moment

For `t>0`, write

\[
 L_\beta(t)=\exp[-\beta\log^2(t_*/t)],
 \qquad L_\beta(t)=0\quad(t\le0).
\]

Assume `B≥0` and, on the positive closed support,

\[
 \|F(x)\|\le B L_\beta(t_+(x))e^{-a t_+(x)/h}.
\]

The cusp’s nonzero support lies in the image of `(0,t₀)×(-s₀,s₀)` under the actual `cuspChart`. The theorem [`integral_image_cuspChart`](../InfiniteZero/CuspChartJacobian.lean) and identity `normalCoordinate(cuspChart(t,s))=t` give

\[
\begin{aligned}
 \int_{\mathbb R^2}\|F(x)\|\,dx
 &=\int_{(0,t_0)\times(-s_0,s_0)}
       t^2\|F(\Psi_+(t,s))\|\,dt\,ds\\
 &\le 2s_0 B\int_0^{t_0}t^2
       \exp[-\beta\log^2(t_*/t)-at/h]\,dt.
\end{aligned}
\]

The bound also applies at image points where F vanishes. The rectangle integrands are integrable by continuity of the log-flat extension and compactness of the closed rectangle. Fubini then separates the constant tangential factor.

`integral_norm_le_cuspPlus_profile` formalizes this inequality using the existing moment `logFlatLaplaceIntegral β tStar t₀ a h 2`. This is the **power-two moment**, with no deletion or duplication of the Jacobian.

Plane reflection is a real linear isometry preserving the project’s fixed volume; see [PlaneReflectionMeasure](../InfiniteZero/PlaneReflectionMeasure.lean). Applying the result to `F ∘ reflection` gives the same integral, integrability, and constant for the negative cusp, with `t₋(x)=normalCoordinate(reflection x)`. This transport introduces no additional factor.

## Uniform threshold and spending the local margin

For `0<β'<β` and `aMin>0`, the theorems `exists_cuspPlus_profile_integral_threshold` and `exists_cuspMinus_profile_integral_threshold` choose `N>0` before

\[
 \lambda\ge N,\qquad a\ge a_{\min},\qquad B\ge0,
 \qquad F\text{ continuous and supported on the cusp}.
\]

If the local bound has slope `exp(−aλt)`, they give

\[
 \int\|F\|\le2s_0 B\exp[-\beta'\log^2\lambda].
\]

The proof uses `h=λ⁻¹` and [`eventually_logFlatLaplaceIntegral_le_exp`](../InfiniteZero/LogFlatIntegral.lean). Part of `β−β'` supplies the uniform moment bound; the rest absorbs its fixed prefactor `t₀³`. The threshold depends on the fixed parameters, margin, and minimum slope, but not on a, B, or F. In particular, the envelope B may contain Γ, λ, and the action without changing this threshold.

## Incoming and scattered sources of the same states

[AtomicSourceL1](../InfiniteZero/AtomicSourceL1.lean) applies these lemmas to the [simultaneous profiles](CUSP_SOURCE_PROFILES.md), at order zero. Set

\[
 h=\lambda^{-1},\quad
 \mathcal E_h^\circ=-h^2E_{\rm core}(\lambda),\quad
 J_h=J_b(\mathcal E_h^\circ,R),\quad
 \eta=\psi-c\phi.
\]

The states `φ` and `ψ` are actual normalized ground states of the core and full potential, `φ` is positive radial, `c∈[1/2,1]`, and `Γ>0` is the exact-tail coefficient of this same φ. For each cusp component `i=1,2`, we obtain

\[
\begin{aligned}
 \|\operatorname{componentSource}_i(h,c\phi)\|_1
 &\le C_{\rm in}\,c\Gamma\lambda^4e^{-\lambda J_h}
                   e^{-\beta_{\rm in}\log^2\lambda},\\
 \|\operatorname{componentSource}_i(h,\eta)\|_1
 &\le C_{\rm sc}\,c\Gamma\lambda^6e^{-\lambda J_h}
           e^{-(\beta_{\rm global}+\beta_{\rm local})\log^2\lambda}.
\end{aligned}
\]

The three target coefficients are independent in `(0,β)`. To obtain local targets `βin` and `βlocal`, the profiles are requested at intermediate coefficients `(βin+β)/2` and `(βlocal+β)/2`, and these margins are spent in the two integrals. The response’s global coefficient `βglobal` is retained in full and adds to the integrated local cost.

The incoming slope is `1/8`. The scattered slope is fixed at `κ₀/2>0` **before λ**, after choosing the weighted regime. The four incoming/scattered and positive/negative thresholds are combined into one threshold before λ. The two states and Γ are not reselected during the four applications. The factor `ε` is already in `componentPotential`, and `h⁻²` is already in `atomicSource`; neither is multiplied in twice.

The theorem `exists_atomicGround_source_L1_of_radialData` takes radial data, core/full realizations, and the interior elliptic estimate as explicit inputs. Its wrapper [`atomicGround_source_L1`](../InfiniteZero/ClassicalAtomicSourceL1.lean) supplies them through A002 and A004. Passage to the integrals itself adds no admission and does not use A003.

## Full components and core

[AtomicComponentSourceL1](../InfiniteZero/AtomicComponentSourceL1.lean) assembles the full source of each cusp through the linear identity

\[
 F_i=\operatorname{componentSource}_i(h,\psi)
     =F_i^{\rm in}+F_i^{\rm sc},\qquad i=1,2.
\]

The triangle inequality, `c≤1`, `λ≥1`, and the choice `βin=βglobal=βlocal=β₁`, with `0<β₁<β`, give

\[
 \|F_1\|_1+\|F_2\|_1
 \le C\Gamma\lambda^6e^{-\lambda J_h}
                    e^{-\beta_1\log^2\lambda}.
\]

The constant may be taken as `2(Cin+Csc)`: bound `λ⁴` by `λ⁶` and the scattered cost `exp(−2β₁log²λ)` by `exp(−β₁log²λ)`.

The sum is over the **two full cusp components**, each including its incoming and scattered parts. It does not include the core component, which separately satisfies

\[
 \|F_0\|_1\le C_{\rm core}\lambda^2.
\]

The [core bound](../InfiniteZero/CoreSourceBound.lean) applies Cauchy–Schwarz to `h⁻² core·ψ`, using unit mass of the actual full state and the L² norm of the compact radial potential. This component requires neither Γ nor an action cost.

`exists_atomicGround_component_source_L1_of_radialData` supplies all three integrability proofs and both estimates, with the same φ, ψ, c, Γ and constants before λ. Its wrapper [`atomicGround_component_source_L1`](../InfiniteZero/ClassicalAtomicComponentSourceL1.lean) requires only `BasicConditions` and `0<β₁<β`, using the same classical interfaces A002 and A004.

## Scope in L5.6 and completed connections

These bounds are the componentwise inputs to [`lem:component-source-L1` and L5.6](../article/Infinite_Zero_Tunneling_Lean_oriented_V2.tex#L4293). The target `β₁` can be chosen in `(0,β)`, and the common cusp-sum prefactor is explicit: `λ⁶`. For the TeX formulation with `β₀−η`, choose this coefficient when positive; when the target is nonpositive, a bound with any allowed positive coefficient is stronger.

These norms are now combined with kernel bounds and action margins for the [seven inactive cells](INACTIVE_CELLS.md), then with both log-flat margins for [negligibility of active scattered terms](ACTIVE_SCATTERED.md). The leading amplitude is obtained separately through the [incoming prefactor and oscillatory assembly](ACTIVE_CHANNEL_ASYMPTOTIC.md); absolute L¹ bounds alone do not supply it.
