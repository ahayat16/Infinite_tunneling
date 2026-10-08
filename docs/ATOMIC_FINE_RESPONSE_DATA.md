# Sharp data for the actual atomic response equation

The full right-hand side of the response equation is controlled at every fixed order, for the same states, relative phase, and tail coefficient. Both terms retain **a single Γ factor**. The results are assembled in [AtomicFineResponseData](../InfiniteZero/AtomicFineResponseData.lean) and [AtomicFineResponseDecomposition](../InfiniteZero/AtomicFineResponseDecomposition.lean). This block’s global check passed: compilation, guards against unauthorized admissions, and dependency export. Its only classical inputs are A002 and A004. The [final assembly](../InfiniteZero/ConstructedMainProof.lean) and [thm_main](../InfiniteZero/Remaining.lean) are now compiled modulo the two classical admissions A002 and A004.

The inputs are `BasicConditions`, spectral data for the radial core alone, and operator realizations of the core and full potential. The radial data are assembled from A004 and A002; the operator realizations are supplied by A002. No source, response, or tunneling estimate is assumed, and A003 is not used. Elliptic propagation to pointwise correction derivatives is proved in a [separate block](ATOMIC_RESPONSE_JETS.md) using the proved interior estimate.

## Energies, states, and exact equation

Fix the potential, cutoffs `χ : CuspWeightCutoffs p`, weight `T=χ.weight`, an integer `n`, and `0<β₁<β`. Write

\[
h=\lambda^{-1},\quad W=v-v_0,\quad
\mathcal E_h=-h^2 E_{\rm core}(\lambda)\in[1/2,1],\quad
\delta_h=h^2(E_{\rm full}(\lambda)-E_{\rm core}(\lambda)).
\]

The notation `𝓔_h` denotes the Landau kernel’s positive energy. It differs from the core’s negative semiclassical eigenvalue. Throughout the action below, `J=bridgeAction b 𝓔_h R` uses the **core** energy, without replacing it by the full-potential energy.

The Schur certificate supplies a normalized positive radial core state `φ`, an actual full ground state `ψ`, and

\[
c=(1+\|\zeta\|_2^2)^{-1/2}\in[1/2,1],\qquad
\eta=\psi-c\phi,\qquad \langle\phi,\eta\rangle=0.
\]

The core state has its exact tail `φ(x)=Γ K(b,h,𝓔_h,‖x‖)` for `‖x‖>r₀`, with `Γ>0`. The same coefficient is retained throughout all estimates.

[AtomicScaledResponseEquation](../InfiniteZero/AtomicScaledResponseEquation.lean) proves, at every point of the plane,

\[
h^2\bigl(H_{\lambda,v}\eta-E_{\rm full}\eta\bigr)
 =-cW\phi+c\delta_h\phi=:f_h.
\]

Signs and factors follow directly from both actual eigenvalue equations: `Hλ,v φ=Ecore φ+λ²Wφ`, then `h²λ²=1`. The Lean definitions are `atomicScaledEnergyShift` and `atomicScaledResponseSource` in [AtomicResponseDataJets](../InfiniteZero/AtomicResponseDataJets.lean). The representative wrapper retains exactly the normalized vector of the same certificate and its correction; it does not choose a new phase.

## Why the energy term does not produce Γ²

Set the common envelope

\[
 B_h=\Gamma h^{-2}e^{-J(b,\mathcal E_h,R)/h}
                     e^{-\beta_1\log^2(1/h)}.
\]

The [forcing derivatives](CUSP_FORCING_DERIVATIVES.md) supply, for `j≤n`, a global bound `e^(κT/h) hʲ ‖Dʲ(Wφ)‖≤Cforce B_h`, together with `‖e^(κT/h)Wφ‖₂≤Cnorm B_h`. Constants are common to all required orders. The weight always multiplies **after** differentiation.

The scalar equation of the same certificate, formalized in [AtomicEnergyShiftForcing](../InfiniteZero/AtomicEnergyShiftForcing.lean), gives

\[
 |\delta_h|\le3\|e^{\kappa T/h}W\phi\|_2
              \le3C_{\rm norm}B_h.
\]

Indeed, `c≥1/2` implies `‖ζ‖²≤3`, hence `1+‖ζ‖≤3`; the scalar equation and residual control then suffice. The forcing appears only once in this estimate.

The second factor to control is the radial jet multiplying `δ_h`. The [normalized weighted radial jets](RADIAL_WEIGHTED_JETS.md) prove, on each fixed annulus `R/2≤‖x‖≤rMax`,

\[
 e^{\kappa T(x)/h}h^j\|D^j\phi(x)\|
 \le C_\phi e^{-d/h}\le C_\phi,\qquad j\le n.
\]

This conclusion no longer contains Γ. The proof uses unit mass and radial monotonicity to bound `φ(2r₀)`, then a kernel lower bound to obtain `Γ≤C h² exp((J(𝓔_h,2r₀)+εact)/h)`. The action margin between `2r₀` and `R/2`, strictly positive by `8r₀<R`, absorbs this normalization, the small weight, and polynomial derivative losses. Here it replaces the radial elliptic argument proposed in the TeX; no elliptic estimate is assumed.

Jet linearity and the triangle inequality therefore give

\[
\begin{aligned}
e^{\kappa T/h}h^j\|D^j f_h\|
&\le c\,e^{\kappa T/h}h^j\|D^j(W\phi)\|
 +c|\delta_h|e^{\kappa T/h}h^j\|D^j\phi\|\\
&\le (C_{\rm force}+3C_{\rm norm}C_\phi)cB_h.
\end{aligned}
\]

`exists_atomicGround_fine_response_data_of_radialData` combines this pointwise annular bound with the already-proved correction bound:

\[
\|e^{\kappa T/h}\eta\|_2
 \le C_{\rm response}\,c\Gamma h^{-3}
       e^{-J(b,\mathcal E_h,R)/h}e^{-\beta_1\log^2(1/h)}.
\]

The prefactors are therefore `cΓλ²` for the data and `cΓλ³` for the correction in L² norm. Constants and threshold precede `λ`; the reference, certificate, `c`, and Γ are chosen before `κ∈[0,κ₀]`. They do not depend on the point or order `j≤n`. The threshold and constants may depend on `n`, `β₁`, the fixed weight, and the potential.

## Fixed neighborhoods and actual local L² norms

[CuspPacketNeighborhood](../InfiniteZero/CuspPacketNeighborhood.lean) defines

\[
\begin{gathered}
R_{\rm pkt}=\max(R,R_{\rm support})+2,\\
U=\{R/2<\|x\|<R_{\rm pkt}\},\qquad
U'=\{3R/4<\|x\|<R_{\rm pkt}-1\}.
\end{gathered}
\]

The closed supports of both cusps and W lie in `U'`, and `closure U'` is compact and contained in U. For `0<h≤min(R/16,1/4)`, every closed ball of radius `2h` centered in `closure U'` remains in U. These inclusions cover the tips.

For directions `v₁,…,vⱼ` of norm at most one, define

\[
F_{j,v}(x)=1_U(x)e^{\kappa T(x)/h}h^j
                     D^j f_h(x)[v_1,\ldots,v_j].
\]

The actual function is the indicator of U applied to `weightedSemiclassicalJet`. Neither the weight nor the indicator is differentiated. The jet of `f_h` is continuous, and U is measurable and contained in the ball of radius `Rpkt`. The pointwise bound supplies `MemLp F_{j,v} 2` and, using the disk’s area,

\[
 \operatorname{mass}(F_{j,v})\le(C_{\rm data,L^2}cB_h)^2.
\]

The square applies to the entire envelope: the L² norm therefore retains coefficient β₁ and a single Γ. For every finite family `i↦(jᵢ,vᵢ)` with `jᵢ≤n`, the theorem supplies actual `toLp` vectors and

\[
 \sum_i\|F_{j_i,v_i}\|_2\le|I|C_{\rm data,L^2}cB_h.
\]

The constant also precedes the family; its cardinality remains explicit. This formulation covers the fixed coordinate-derivative families needed for a multi-index sum. It introduces no new convention for weak derivatives or Sobolev norms.

## Assembly and exact scope

`exists_atomicGround_fine_response_decomposition_of_radialData` collects the same `φ,ψ,c,Γ`, exact tail, orthogonality, regularity of `η` and `f_h`, scaled PDE, global weighted mass of `η`, and local masses and sums of jets of `f_h` on U. The compiled public connection is `CuspParameters.atomicGround_fine_response_data` in [ClassicalAtomicFineResponseData](../InfiniteZero/ClassicalAtomicFineResponseData.lean): it supplies A002+A004 from `BasicConditions`, `0<β₁<β`, and `n`, with cutoffs chosen before the constants and coupling. The exported graph confirms exactly A002+A004 as transitive admissions, without A003 or dependency on the final theorem `thm_main`.

This block completes the data of `sublemma:T3-4-forcing-derivatives`, with an explicit polynomial power and the same action/log-flat bound. `sublemma:T3-4-uncompressed` is supplied by the exact PDE on the whole plane. The full source is not assumed compactly supported: the term `δ_h φ` explains restriction to U in the local differentiated estimates.

[Elliptic propagation to jets of η](ATOMIC_RESPONSE_JETS.md) is proved in a separate block using the interior estimate. Both profile factors of the [scattered source](CUSP_SCATTERED_SOURCE.md) are then retained by Leibniz. At this milestone, cell estimates and physical double-well reduction remained. The only prefactors claimed here are the explicit powers in the Lean statements.
