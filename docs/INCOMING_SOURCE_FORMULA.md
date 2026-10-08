# Exact incoming-source formula in the charts

The next step is documented in [INCOMING_MULTIPLIER.md](INCOMING_MULTIPLIER.md): Fubini for the physical density, exact normalization with both Jacobians, uniform complex profile at the actual energies, and integrated error on the saddle contour. The [physical connection](INCOMING_PHYSICAL_ASYMPTOTIC.md) now gives the normalized limit of the four-coordinate integral. The [final conversion to a relative cell and canonical channels](ACTIVE_CHANNEL_ASYMPTOTIC.md) is also proved, with explicit amplitude and continuous phase.

[CuspIncomingSourceFormula](../InfiniteZero/CuspIncomingSourceFormula.lean) connects the actual sources in `HoppingChannels` to the three complex kernels already constructed. Its six lemmas compile without admissions; this step does not itself claim an asymptotic evaluation of the active cell. [CuspSourcePairingCoordinates](../InfiniteZero/CuspSourcePairingCoordinates.lean) now adds the exact change of variables for the incoming integral.

Fix a potential satisfying `BasicConditions` and a reference state with exact tail

\[
 \phi(x)=\Gamma K_{b,h}^{E_\circ}(\lVert x\rVert),\qquad \lVert x\rVert>r_0.
\]

This identity is an assumption of the algebraic lemma. For actual normalized radial states, it is already supplied by [RadialCoreExteriorState](../InfiniteZero/RadialCoreExteriorState.lean) and retained in the physical source estimates.

Write \(z=\Psi_+(t,s)\), \(w=\mathcal R\Psi_+(u,r)\), with \(t,u>0\). The bound `normalCoordinate_le_norm` implies \(\lVert\Psi_+(t,s)\rVert\ge R/2+t>r_0\), since \(8r_0<R\). It holds for every real tangential parameter: the tail applies before any restriction to the cutoff support. Reflection preserves the norm.

Set

\[
 q(t,s)=e^{-\beta\log^2(t_*/t)}\chi_a(t)\chi_b(s),
 \qquad H=h^{-2}\varepsilon a c\Gamma.
\]

The two exact physical identities are

\[
 F_+^{\rm in}(z)=-Hq(t,s)K_{b,h}^{E_\circ}(\lVert z\rVert),\qquad
 F_-^{\rm in}(w)=-Hq(u,r)K_{b,h}^{E_\circ}(\lVert w\rVert).
\]

The real cutoffs remain present, including where they vanish. The factor \(h^{-2}\) comes from `atomicSource`, and \(\varepsilon\) from `componentPotential`; neither is inserted a second time. No phase choice for the full ground state is involved.

`ComplexCuspPhysicalBridge` identifies these real kernels exactly with the restrictions of the complex kernels in the charts. Thus `incoming_channelIntegrand_cuspChart_eq` gives

\[
 \overline{F_+^{\rm in}(z)}K_{\rm source}(z,w)F_-^{\rm in}(w)
 =H^2q(t,s)q(u,r)\,
 K_+^{E_\circ}K_-^{E_\circ}K_{\rm bridge}^{E}
 e^{i\Phi(z,w)/h}.
\]

The incoming factors are real, justifying the treatment of conjugation. The bridge kernel retains the full energy E, distinct from the core energy \(E_\circ\). The identity concerns the pointwise integrand: the Jacobians \(t^2u^2\) and outer factor \(-h^2\) are now inserted exactly by `incoming_sourceCell_eq_cuspCharts`. The formula is an iterated integral over two `cuspChartDomain` rectangles, with the three kernels, cutoffs, and phase above. Physical integrability is proved; the change of variables never divides by a cutoff. It does not yet permute the four real variables.

This step supplies the exact formula to which the relative kernel profiles apply. It does not deform the full cell’s contour, integrate the relative remainder, or control terms containing the scattered response. That last control is proved separately in [ACTIVE_SCATTERED.md](ACTIVE_SCATTERED.md). This construction never analytically continues the scattered response.
