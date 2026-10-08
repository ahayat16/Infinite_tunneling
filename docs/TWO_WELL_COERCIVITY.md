# Double-well coercivity outside the two atomic states

**Status:** the cutoffs, test-function assembly, and passage to the actual operator domain compile without warnings. The global check validated this block; current inventories are in [STATUS.md](STATUS.md). The wrapper `doubleWell_complement_coercivity` depends exactly on A002 and A004. Spectral consequences are assembled separately in [GLOBAL_PARITY_DOUBLET.md](GLOBAL_PARITY_DOUBLET.md).

Fix `hp : p.BasicConditions`, a `cert : p.SeparationCertificate`, [radial spectral data](../InfiniteZero/RadialCoreSpectralData.lean) `hRad`, and magnetic realizations of the core and full potential for each coupling. Passage to the domain also requires the double-well realization for every coupling and separation. Write `V = p.potential`, `d = displacement L`,

\[
 V_L(x)=V(x+d)+V(d-x),\qquad
 E_\lambda=\operatorname{atomicGroundEnergy}(p.b,V,\lambda),\qquad
 \gamma=\tfrac12\,\mathrm{hRad.gap}>0.
\]

The magnetic form contains the potential `λ² V_L`. For a normalized full atomic ground state `φ`, write `φ_L = leftState … φ` and `φ_R = rightState … φ`. These are the actual magnetic translations and their image under inversion. No phase choice for `φ` is required.

The test-function result supplies a threshold `T > 0`, chosen **before** `λ ≥ T`, **every** `L ≥ cert.L₀`, every full ground state `φ`, and then every `ψ : IsTestFunction`, such that

\[
 \mathfrak q_{\lambda,L}(\psi)-E_\lambda\|\psi\|_2^2
 \ge \frac{\mathrm{hRad.gap}}4\lambda\|\psi\|_2^2
 -\mathrm{hRad.gap}\,\lambda
   \bigl(|\langle\phi_L,\psi\rangle|^2
          +|\langle\phi_R,\psi\rangle|^2\bigr).
\tag{1}
\]

Existence of a full atomic ground state beyond the same threshold is also included. The sum of the two overlaps is used as stated: the translated states are not assumed orthogonal.

## From the atomic certificate to two wells

[GroundStateRankOne.lean](../InfiniteZero/GroundStateRankOne.lean) turns the ground-state certificate’s gap into an inequality with a rank-one defect. [AtomicGroundRankOne.lean](../InfiniteZero/AtomicGroundRankOne.lean) applies it to actual tests and, through simplicity and invariance of the overlap norm under a unit phase, to **every** normalized full ground state:

\[
 g\bigl(\|u\|_2^2-|\langle\phi,u\rangle|^2\bigr)
 \le \mathfrak q_{\lambda,V}(u)-E_\lambda\|u\|_2^2,
 \qquad g=\gamma\lambda.
\]

The certificate and gap are already constructed from the radial core; the nonradial inequality is not a new assumption. [TranslatedAtomicGap.lean](../InfiniteZero/TranslatedAtomicGap.lean) transports this bound exactly by magnetic covariance and then inversion. The threshold and coefficient `g` remain independent of `L`.

## A fixed partition around the full supports

[DoubleWellLocalizationCutoffs.lean](../InfiniteZero/DoubleWellLocalizationCutoffs.lean) sets `S = max(cert.supportRadius, 4r₀)` and chooses `a = (2S + cert.L₀)/3`, `b = (S + 2cert.L₀)/3`. The assumptions give `0 < S < a < b < cert.L₀`. A smooth radial bump `B`, equal to one on the ball of radius `a` and zero outside radius `b`, defines the partners `χ = sin(π B/2)` and `η = cos(π B/2)`.

After translation to the two centers, `χ_L, χ_R, η_L, η_R` are smooth, lie between zero and one, and satisfy

\[
 \chi_L^2+\eta_L^2=1,\quad \chi_R^2+\eta_R^2=1,\quad
 \eta_L\chi_R=\chi_R,\quad \chi_{\rm ext}=\eta_R\eta_L,\quad
 \chi_L^2+\chi_R^2+\chi_{\rm ext}^2=1.
\]

The closed supports of the two interior cutoffs are disjoint. Their plateaus contain the corresponding potential supports and the balls of radius `4r₀`. The opposite potential vanishes after multiplication by each interior cutoff; both potentials vanish after multiplication by `χ_ext`. Finally, `exists_doubleWellIMSError_bound` supplies `D > 0` before `L, λ`, bounding the IMS errors of both pairs.

## Localizing forms and overlaps

[MagneticIMSThree.lean](../InfiniteZero/MagneticIMSThree.lean) applies two successive binary IMS identities. Compatibility `η_L χ_R = χ_R` gives exactly the three states `χ_L ψ`, `χ_R ψ`, `χ_ext ψ`, without an additional cross term. The total cost is at most `2D ‖ψ‖₂²`.

Set `tail(φ) = ∫_{‖x‖≥4r₀} |φ(x)|² dx`. [LocalizedOverlap.lean](../InfiniteZero/LocalizedOverlap.lean) expresses the overlap error with `χ_L ψ` using `(1−χ_L)φ_L`. Cauchy–Schwarz and `|a+b|² ≤ 2|a|²+2|b|²`, followed by mass invariance under magnetic translation, give

\[
 |\langle\phi_L,\chi_L\psi\rangle|^2
 \le 2|\langle\phi_L,\psi\rangle|^2
       +2\,\mathrm{tail}(\phi)\,\|\psi\|_2^2.
\]

[DoubleWellLocalizedEstimates.lean](../InfiniteZero/DoubleWellLocalizedEstimates.lean) supplies both versions, the exact localized-form identities, and nonnegativity of the exterior form. If `g ≤ −E_λ`, the latter contributes at least `g ‖χ_ext ψ‖₂²` to the shifted form. The sum of the three masses is `‖ψ‖₂²`. This gives

\[
 \mathfrak q_{\lambda,L}(\psi)-E_\lambda\|\psi\|_2^2
 \ge (g-4g\,\mathrm{tail}(\phi)-2D)\|\psi\|_2^2
       -2g\bigl(|\langle\phi_L,\psi\rangle|^2
                +|\langle\phi_R,\psi\rangle|^2\bigr).
\tag{2}
\]

## Uniform absorption and scope

[AtomicGroundAgmon.lean](../InfiniteZero/AtomicGroundAgmon.lean) uniformly controls all full ground states by `tail(φ) ≤ C λ⁻² exp(−2dλ) ≤ C λ⁻²`. The energy bound `E_λ ≤ −λ² + Bλ` ensures `g ≤ −E_λ` at large coupling. [DoubleWellCoercivityScalar.lean](../InfiniteZero/DoubleWellCoercivityScalar.lean) chooses a threshold independent of `L` absorbing `4γλ C/λ² + 2D` into `γλ/2`. Thus (2) gives (1), with exactly the stated coefficients.

## Passage to the actual closed domain

[MagneticGraphTwoModeLowerBound.lean](../InfiniteZero/MagneticGraphTwoModeLowerBound.lean) proves that the quadratic inequality, with both overlaps, is closed in the graph variables `(u, Hu)`. Integration by parts on tests identifies the form with `Re⟨u, Hu⟩`; closure of the test graph then transfers (1) to the concrete magnetic graph. Approximation by tests already orthogonal to both references is unnecessary.

[DoubleWellOperatorCoercivity.lean](../InfiniteZero/DoubleWellOperatorCoercivity.lean) supplies `exists_doubleWell_operator_rankTwo_gap_of_radialData`, then `exists_doubleWell_operator_complement_gap_of_radialData`. For all representatives `vL`, `vR` of the same `φ_L`, `φ_R` and every `u` in the actual domain, both orthogonality conditions imply exactly

\[
 \operatorname{Re}\langle u,H_{\lambda,L}u\rangle
 \ge \left(E_\lambda+\frac{\mathrm{hRad.gap}}4\lambda\right)\|u\|_2^2.
\]

Constants are chosen before `λ`, `L`, the state, and its representatives. The wrapper in [ClassicalDoubleWellCoercivity.lean](../InfiniteZero/ClassicalDoubleWellCoercivity.lean) replaces the explicit classical data with `hp` and `cert`, and exports `∃ γ>0, ∃ T>0, ∀ λ≥T, ∀ L≥cert.L₀` with coercivity `γλ`. In semiclassical units, multiplication by `h²`, with `h=λ⁻¹`, gives the coefficient `γh` of Theorem T4.2. The statement is established on the operator domain; no separate extension to the entire closed form domain is claimed.

The conditional modules require no further admission. Instantiating them from geometric conditions alone uses the classical inputs A002 (operator realizations) and A004 (radial-core spectrum), without A003. [L2Inversion.lean](../InfiniteZero/L2Inversion.lean) constructs the complex linear isometric involution on L². The [parity block](PARITY_SPECTRAL_CONSTRUCTION.md) now proves invariance of the actual graph, self-adjoint restrictions to the closed sectors, and transfer of this coercivity to the complements of even and odd trials. In a sector, orthogonality to the normalized trial implies orthogonality to both atoms: the lower bound therefore remains `Eatom + hRad.gap·λ/4`, with the same quantifier order.

The abstract constructor `ParitySchurGroundConstruction` produces a simple isolated eigenmode once a trial with Rayleigh value below the complement bound is supplied. `ParityEnergyIdentification` identifies its energy with `parityEnergy`, the original normalized-test infimum. The physical assembly `DoubleWellParityGround` is now compiled: its modes have energy ≤Eatom+hRad.gap·λ/8 and gap ≥hRad.gap·λ/8, with a threshold before λ and L. `EigenvectorComplementBound` retains the absolute lower bound Eatom+hRad.gap·λ/4 on the complement of each actual mode within its sector. The wrapper `doubleWell_parityGrounds hp cert` instantiates only A002+A004. Using the low trials and exact parity-projection decomposition, `ConstructedGlobalMinmax` now identifies the first two min-max values with `min(E+,E−)` and `max(E+,E−)`. The global eigenspaces and their normalized physical representatives are described exactly, with a positive gap. The wrappers `doubleWell_global_minmax hp cert` and `doubleWell_spectral_realization hp cert` use A002+A004; the latter supplies the full spectral contract and gap above the ground state, with a threshold before L. `doubleWell_twoModeRealization hp cert` also directly retains the mode descriptions required by the analytic contract.

The physical diagonal is exactly `Eatom+(δ±Reρ)/(1±s)` (`ParityTrialRayleigh`). `ConstructedParitySchurEnergyBound` further gives `0≤a±−E±≤‖(H−Eatom)q±‖²/(hRad.gap·λ/8)`, with a threshold before λ and L. The `o(A)` errors needed to transfer hopping to splitting do not follow from coercivity or this quadratic bound alone.
