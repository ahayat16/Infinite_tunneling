# Pointwise jets of the actual atomic correction

This block passes from the [full PDE data](ATOMIC_FINE_RESPONSE_DATA.md) to pointwise derivatives of its solution using the [proved interior estimate](CLASSICAL_ELLIPTIC_INTERIOR.md). Point evaluation by the H² norm follows from a fixed cutoff, the fundamental theorem of calculus, and Cauchy–Schwarz. Cutoff energy estimates and induction prove the uniform interior Sobolev estimate; higher-order point bounds and coordinate/directional norm conversions are also proved. Magnetic coefficients, changes of scale and measure, weights, and application to the actual states of the constructed potential are handled separately in Lean. This step adds no admission.

## Equation after rescaling

Set `h=λ⁻¹`, `x=x₀+hy`, `û(y)=u(x₀+hy)`, and `e=h²E`. [MagneticEllipticExpansion](../InfiniteZero/MagneticEllipticExpansion.lean) expands the two actual covariant derivatives; [MagneticAffineRescaling](../InfiniteZero/MagneticAffineRescaling.lean) then proves exactly

\[
 h^2(H_{\lambda,v}-E)u=f
 \quad\Longrightarrow\quad
 -\Delta_y\widehat u+\sum_i a_i(y)\partial_i\widehat u+q(y)\widehat u
   =f(x_0+hy),
\]

with `aᵢ(y)=ib(x₀+hy)ᵢ⊥` and `q(y)=(b/2)²‖x₀+hy‖²+v(x₀+hy)−e`. The signs and factors are those of the project’s Hamiltonian.

No additional gauge is necessary: the centers `x₀` remain in a bounded set. For `0≤h≤1`, `‖x₀‖≤R`, and `‖y‖≤2`, the physical point remains in the ball of radius `R+2`. [RescaledMagneticCoefficientBounds](../InfiniteZero/RescaledMagneticCoefficientBounds.lean) bounds all required jets of `aᵢ,q` simultaneously by a constant chosen before `h,x₀,e`, under a fixed bound on `|e|`. Compactness and smoothness of the actual potential supply these bounds; they are not outstanding cusp-specific assumptions.

## Derivatives, measure, and weights

[AffineScaleJets](../InfiniteZero/AffineScaleJets.lean) gives `Dʲû(y)=hʲ Dʲu(x₀+hy)` as an equality of multilinear forms. [AffineScaleL2](../InfiniteZero/AffineScaleL2.lean) proves the exact planar change of measure:

\[
 \int_{B(0,2)}|g(x_0+hy)|^2\,dy
   =h^{-2}\int_{B(x_0,2h)}|g(x)|^2\,dx.
\]

[MagneticInteriorEstimate](../InfiniteZero/MagneticInteriorEstimate.lean) takes the derived `HasInteriorEllipticEstimate` contract as an explicit argument: if the local mass of `u` is at most `U²`, and those of all jets `hʲDʲf`, `j≤n`, are at most `F²`, then `hʲ‖Dʲu(x₀)‖≤Cλ(U+F)`. The factor `λ` comes solely from the change of measure in the L² norm in dimension two.

For `w=exp(κλT)`, Lipschitz comparison on `B(x₀,2h)` gives `w(x₀)≤Cw w(x)`, with `Cw` independent of `λ,x₀` and of `κ` in a fixed interval. [WeightedLocalMassComparison](../InfiniteZero/WeightedLocalMassComparison.lean) removes this weight from the local masses. The balls lie in the outer cusp neighborhood, including when centered at a tip. [WeightedMagneticInteriorEstimate](../InfiniteZero/WeightedMagneticInteriorEstimate.lean) deduces

\[
 w(x_0)h^j\|D^ju(x_0)\|\le C\lambda(U_w+F_w),\qquad j\le n.
\]

Here `U_w` bounds the global weighted norm of `u`, and `F_w` the local weighted norms of the right-hand-side jets. The weight and neighborhood indicator multiply after differentiation; no derivatives of these factors are used.

## Application to the same Schur correction

[AtomicFineResponseJets](../InfiniteZero/AtomicFineResponseJets.lean) retains the actual states `φcore,ψfull`, the same `c∈[1/2,1]`, the same exterior-tail coefficient `Γ>0`, and `η=ψfull−cφcore`. The PDE is the one already proved at every point:

\[
 h^2(H_{\lambda,v}-E_{\rm full})\eta
   =-cW\phi_{\rm core}+c h^2(E_{\rm full}-E_{\rm core})\phi_{\rm core}.
\]

The full potential’s semiclassical energy is bounded in magnitude by one beyond the chosen threshold. The sharp data give `U_w≤Cresponse cΓλ³Aλ` and `F_w≤Cdata cΓλ²Aλ`, where

\[
 A_\lambda=e^{-\lambda J(b,\mathcal E_{\rm core,h},R)}
             e^{-\beta_1\log^2\lambda},\qquad 0<\beta_1<\beta.
\]

For `λ≥1`, the interior estimate therefore gives, on the closure of the inner neighborhood,

\[
 \boxed{\ e^{\kappa\lambda T(x)}\lambda^{-j}\|D^j\eta(x)\|
    \le Cc\Gamma\lambda^4 A_\lambda,\qquad j\le n.\ }
\]

The tail action remains that of the actual core, whereas the PDE uses the full-potential energy. These two energies are not identified. No action or log-flat margin is spent in this step. For every fixed maximum order, the constants and threshold precede `λ`; the states and `c,Γ` precede `κ`, the jet order, and the point.

The public wrapper is `CuspParameters.atomicGround_fine_response_jets`, in [ClassicalAtomicFineResponseJets](../InfiniteZero/ClassicalAtomicFineResponseJets.lean). It supplies the classical inputs through A002 and A004, without A003.

The wrapper depends on A002 and A004, without using `thm_main`; the generic elliptic estimates have no admitted dependency.

This result concerns jets of the **correction**. The connection to the [scattered source](CUSP_SCATTERED_SOURCE.md) is now proved: multiplication by `λ²W` and Leibniz simultaneously retain the local log-flat factor of `W` and the global factor obtained here. At this milestone, analysis of the full active cell, inactive contributions, and double well remained to be completed.
