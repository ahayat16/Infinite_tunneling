#!/usr/bin/env python3
"""Index the actual sublemma labels in the supplied TeX, without claiming
that every statement has already been translated to a Lean declaration."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
TEX = "article/Infinite_Zero_Tunneling_Lean_oriented_V2.tex"

# Deliberately conservative: a related calculation does not certify every
# conclusion (uniformity, derivatives, rates, etc.) of its source sublemma.
COVERAGE = {
    'sublemma:L2-1-core-taylor': (
        'Core hypotheses, radial second derivative and a global quadratic upper bound proved; fourth-order Taylor remainder not exported',
        'CoreRadialHypotheses and RadialSingleWell verify the hypotheses for core/b². CoreQuadraticBound proves 0≤core(x)+1≤2|x|²/r₀². RadialCoreVariationalBound derives Ecore(λ)≤−λ²+Cλ for every λ>0 independently of spectral admissions'),
    'sublemma:L2-1-rescale': (
        'Exact test-form dilation and unit-field conversion proved; local oscillator remainder not exported',
        'MagneticDilation proves mass preservation and exact quadratic-form scaling. MagneticFieldScaling identifies (b,λ,core) with (1,bλ,core/b²). SemiclassicalOperator and SemiclassicalDifferentialExpression prove Lh=h²H(1/h), unchanged operator domain and scaling of both min-max levels. RadialCoreVariationalBound applies dilation to a normalized compactly supported trial state'),
    'sublemma:L2-1-oscillator': (
        'Ordering of the full mode family, unique ground mode and first gap proved; oscillator spectral decomposition remains classical',
        'RadialOscillatorLevels proves the first two ordered mode infima are sqrt(1+2d) and 2sqrt(1+2d)−1. ClassicalRadialLowLevels admits the positive radial ground state and two semiclassical O(h^(3/2)) level expansions, using the classical oscillator mode spectrum. RadialHarmonicLimits proves the first-order limits and their coupling conversion; see RADIAL_HARMONIC_CONTRACT.md'),
    'sublemma:L2-1-gap-transfer': (
        'Min-max complement inequality, gap limit and common positive threshold proved from the first two level expansions',
        'OperatorSecondMinmax derives complement coercivity using the two-dimensional span of the ground vector and an orthogonal vector. RadialHarmonicAssembly constructs the certificate from A004 low-level data and A002 realization. MagneticGapThreshold yields gap≥(bδ/2)λ; RadialGroundCertificate and RadialCoreSpectralAssembly recover the unchanged test-function interface'),
    'sublemma:P2-2-critical': (
        'Derivatives and uniqueness of the critical point proved',
        'BridgeActionMinimum: unique global minimum on τ>0'),
    'sublemma:P2-2-action-value': (
        'Proper-time minimum value proved',
        'BridgeActionMinimum.bridgeAction_eq_sInf_properTimePhase'),
    'sublemma:P2-2-action-derivatives': (
        'Radial and energy derivatives, eikonal identity, and integral proved',
        'BridgeAction, BridgeActionEnergy: ∂E J = τ*'),
    'sublemma:P2-2-growth': (
        'Quadratic bound proved; large-radius expansion remains',
        'bridgeAction_sub_ge_quadratic; does not certify the full expansion'),
    'sublemma:P2-3-critical-compact': (
        'Uniform bounds on τ* and positive Hessian proved; higher derivatives remain',
        'LandauLaplace.bridgeTime_mem_uniform_Icc/exists_uniform_properTimePhase_hessian_lower'),
    'sublemma:P2-3-offgraph-gap': (
        'Uniform positive gap proved for all τ>0 outside a neighborhood of the graph',
        'LandauLaplace.exists_uniform_properTimePhase_gap'),
    'sublemma:P2-3-tails': (
        'Uniform exponential tails and absorption of every power proved; derivatives remain',
        'LandauLaplaceTails; complement of a measurable neighborhood of the minimum'),
    'sublemma:P2-3-phase-factor': (
        'Quadratic mean-value formula, moving-parameter limit, and uniform Gaussian domination proved; exact smooth factorization B remains',
        'LandauLaplaceUniformLeading.exists_properTimePhase_quadratic_point/tendsto_scaled_properTimePhase_parameters; positive real parameters'),
    'sublemma:P2-3-coefficients': (
        'Positive leading coefficient and power h^(-3/2) proved, with relative o(1) error uniform on every positive real compact set',
        'LandauLaplaceLeading, LandauLaplaceUniformLeading.tendstoUniformlyOn_landauKernel_relative; fixed b, moving E and r; full series, O(h) rate, derivatives, and complex parameters remain'),
    'sublemma:P2-4-radial-ode': (
        'Exact radial equation proved for the integral kernel and actual positive radial core eigenstate',
        "LandauRadialEquation.landauKernel_radial_ode: two differentiations under the integral and vanishing time-boundary terms proved; MagneticRadialReduction.magneticHamiltonian_radial and RadialCoreExteriorState.IsAtomicGroundState.radialCore_ode reduce the concrete Hamiltonian outside the core, with h=λ⁻¹ and E=−λ⁻² atomicGroundEnergy; only the positive radial choice is classical through A004's explicit field, not this reduction; see [RADIAL_EXTERIOR_KERNEL.md](RADIAL_EXTERIOR_KERNEL.md)"),
    'sublemma:P2-4-decaying-branch': (
        'Uniqueness of the real L²(r dr) branch and exact identity φcore=ΓK with Γ>0 proved under radial data; wrapper via A002+A004 compiled and audited',
        'LandauExteriorUniqueness: Caccioppoli gives finite derivative energy on r>a+2, then the Wronskian gives proportionality on all r>a; RadialPlaneL2 proves passage from planar MemLp to L²(r dr); CuspParameters.exists_radialCore_kernel_of_radialData then radialCore_kernel via A002+A004: T chosen before λ, then φλ,Γλ>0 for every λ≥T and r>r₀; RadialCoreKernelComparison also proves φcore(r)≤ΓK(r) for all r>0 by coefficient ordering; polynomial Γ control handled separately in LB.2, without a differentiated expansion or a positive phase for canonicalAtomicState'),
    'sublemma:P2-4-kernel-decay': (
        'Exterior L² integrability of the actual kernel with radial density r proved on every r>a>0',
        'LandauRadialL2.integrableOn_radial_landauKernel_sq: K≤1/(πEr²), hence r|K|² dominated by (πE)⁻²r⁻³; sufficient variant without a radial Gaussian majorant or differentiated asymptotic expansion'),
    'sublemma:LB-2-radial-green': (
        'Radial differential reduction, polar measure, and off-diagonal kernel equation proved; distributional identity remains',
        'MagneticRadialReduction, RadialPlaneL2, and LandauKernelEquationOffDiagonal: source-variable equation with field −b, local C² covariance without smoothness at the singularity; no radial-resolvent construction or delta/(2πs) identity claimed'),
    'sublemma:LB-2-factorization': (
        'Uniqueness of the exterior L² branch and Wronskian comparison proved; radial Green factorization remains',
        'LandauExteriorUniqueness and RadialWronskianComparison; neither a global regular Volterra solution nor R-independence of the angular-average ratio is established'),
    'sublemma:LB-2-angular-average': (
        'Angular average of the actual kernel, exact polar convolution formula, and value at s=0 proved',
        'RadialLandauAverage and RadialCoreNormalization: exact factor 1/(2π), density s ds, radialFreeLandauAverage_zero and regularLandauProfile_zero; identification with a factored radial Green function and punctured limit s↓0 not exported'),
    'sublemma:LB-2-positive': (
        'Generic first-zero argument proved for a regular solution with nonnegative coefficient; connection to the angular average remains',
        'RadialRegularPositive.radial_regular_pos/monotoneOn/center_le: continuity of f and f′ up to 0 and flux equation on the open interval; no positivity of regularLandauProfile follows from this module alone'),
    'sublemma:LB-2-gamma-formula': (
        'Exact integral formula for Γ of the same radial state proved under the classical kernel contract; integrand positivity not claimed',
        'RadialCoreSourceRepresentation passes from a.e. equality to each exterior point; RadialCoreNormalization.radialCore_normalization gives Γ=2π∫s u_R(s)(−core(s))φ(s)ds, u_R=Re(angular average)/K(R), u_R(0)=1; explicit hKernel, supplied by the proved resolvent formula, fixed R, R-independence of u_R remains'),
    'sublemma:LB-2-lower-bound': (
        'Sufficient polynomial variant proved: φcore≥c on [0,h], Γ≥c′h², Γ⁻¹≤Ch⁻²; TeX powers h⁻¹/² and h³/² not claimed',
        'RadialCoreProfileEstimates: flux monotonicity, L² normalization, exterior mass, and quadratic lower bound; RadialWronskianComparison/RadialCoreKernelComparison give φcore≤ΓK on r>0; LandauCoefficientBounds uses K(h)≤1/(πEh²), E≥1/2; RadialCoreNormalizationLower assembles bounds for the same state and actual tail, constants before λ and uniform over positive radial states; explicit radial data and core realization, wrapper via A002+A004 without A003; neither harmonic-profile convergence nor angular-average positivity needed'),
    'sublemma:L7-1-ratio': (
        'Physical relative comparison of all seven cells and sum of norms proved for the explicit saddle envelope',
        'RelativeNormalizationRatio: same φcore and Γ, ratio≤4Dλ⁴ for c≥1/2; h⁻⁴ variant suffices. ActiveSaddleEnvelope and AtomicInactiveRelative absorb λ⁸ and S_G⁻² into 30δ, leaving exp(−15δλ); same states, core/core/full action, seven actual/canonical bounds and sum of norms. SaddleEnvelopeComparison proves S_G²/S_Tex²=‖1+w‖/Re w→1, then AtomicInactiveRelativeTex transfers to the TeX Hessian envelope within a factor 2; wrappers A002+A004, no new admission or upper-bound hypothesis on Γ; the active asymptotic is separate and was open at this milestone'),
    'sublemma:L2-8-integrability': (
        'Proved for natural powers m≥0; log factors and other exponents remain',
        'LogFlatIntegral.integrableOn_logFlat_laplace'),
    'sublemma:L2-5-agmon-identity': (
        'Exact local identity and weighted inequality proved; cutoffs removed for bounded smooth weights by L² dominated convergence',
        'MagneticLocalEnergy, MagneticAgmonWeighted, MagneticAgmonBounded; no globally integrable energy assumed; full form-domain identity and the TeX Lipschitz weights not claimed; see [AGMON_DECAY.md](AGMON_DECAY.md)'),
    'sublemma:L2-5-weight': (
        'Concrete bounded C∞ weight constructed, zero up to 3r₀ and a positive constant from 4r₀ onward',
        'AtomicAgmonWeight: Fλ=dλ(1−bump), d>0 fixed before λ, gradient²≤λ²/16; variant for this fixed exterior, not every arbitrary compact set separated from the core'),
    'sublemma:L2-5-global-tail': (
        'Global absolute L² tail proved for normalized core and full-potential eigenstates under E≤−3λ²/4',
        'AtomicAgmonGlobal: λ>0, (C/λ²)exp(−2dλ) on ‖x‖≥4r₀, fixed constants; AtomicGroundAgmon applies the tail to ground states, canonical wrapper modulo A002+A004; TeX weighted kinetic bound and fine action rates not claimed'),
    'sublemma:L3-1-ims': (
        'Concrete IMS identity proved pointwise then integrated on tests; three-term version and uniform double-well error proved',
        'MagneticIMSIntegrated.magneticForm_sub_mass_ims, MagneticIMSThree, and DoubleWellLocalizationCutoffs: two compatible sine/cosine partitions, three exact masses, cost at most 2D independent of λ and L. Coercive consequences pass to the operator domain by graph closure, without claiming IMS on the entire closed form domain'),
    'sublemma:L3-1-local-orthogonality': (
        'Fixed partition constructed; orthogonality defect bounded by exterior mass, itself bounded by core excess energy',
        'AtomicLocalizationCutoffs, AtomicLocalizationOverlap, AtomicLocalizationEnergy; sufficient O(h) exterior-mass variant for initial coercivity; TeX exponential bound not claimed'),
    'sublemma:L3-1-exterior': (
        'Exterior margin, absorption, and operator-domain transfer proved for the actual potential under only the displayed radial data',
        'AtomicSpectralCoercivity.exists_atomic_spectral_operator_complement_threshold; margin 1/4, threshold before λ, and operator-domain passage by closure proved; version without noncompact form integrability; classical radial input supplied by A004'),
    'sublemma:P3-2-domain-coordinates': (
        'Orthogonal coordinates, operator-domain preservation, and actual self-adjoint compression proved',
        'OrthogonalCompression.isSelfAdjoint_orthogonalCompression, OrthogonalSchurGeometry; AtomicPerturbationDomain identifies core/full-potential domains; the closed form domain is not formalized here'),
    'sublemma:P3-2-rank-one': (
        'Simple ground state constructed for the actual potential under explicit radial data; direct Schur route',
        'AtomicGroundConstruction.eventual_atomicGround_properties_of_radialData, GroundStateCertificate; application under BasicConditions via A002+A004 in Remaining.eventual_atomicGround_properties; spectral-projection rank and TeX lower window E₀−g/4 not claimed'),
    'sublemma:P3-2-overlap-inverse': (
        'Actual compression and resolvents constructed; L² comparison with positive real overlap and weighted inverse for E≤Ecore',
        'CoerciveResolvent: unweighted inverse continuous in energy; AtomicGroundComparison: fixed relative phase and Efull≤Ecore; AtomicCuspWeightedInverse: norm ≤12/(γλ), under radial data and realizations; sufficient variant at Efull, not the full symmetric window or a pointwise profile'),
    'sublemma:P3-2-feshbach-algebra': (
        'Exact compressed and scalar equations and eigenvector reconstruction proved in the actual domain',
        'SchurGroundExistence.exists_schur_root_data, SchurEigenvector.schur_eigenvector_graph; applied to the actual potential by AtomicGroundConstruction under explicit radial data and realizations'),
    'sublemma:P3-2-normalization': (
        'Exact normalization of the same certificate, quadratic coefficient bound, and uniform interval c∈[1/2,1] for the actual weighted response proved',
        'SchurGroundQuantitative, SchurNormalizationThreshold, AtomicGroundWeightedDecay: 1−c≤‖ζ‖², loss ≤K²exp(−2dλ) if ‖ζ‖≤Kexp(−dλ), threshold before λ and ζ; positive radial state and full certificate chosen before κ; state continuity and canonicalAtomicState phase not imposed'),
    'sublemma:L3-3-gap': (
        'Coercive gap above the constructed ground state proved by a direct route under radial data',
        'SchurGroundState.schur_groundVector_gap, AtomicGroundConstruction.exists_atomicGroundCertificate_of_radialData: gap γλ/2 for the unscaled operator; GroundStateCertificate.hasGapAboveGround; no spectral-projection calculation'),
    'sublemma:L3-3-energy-coefficient': (
        'Actual core/full energies and normalized L² ground states exponentially close; positive kernel energy tends to 1 and eventually lies in [1/2,1]',
        'AtomicGroundComparison: 0≤Ecore−Efull≤Cexp(−dλ), ‖v−u‖₂≤Cexp(−dλ), fixed relative phase; AtomicGroundWeightedDecay retains c∈[1/2,1] for the same certificate and positive radial reference; classical data A002+A004, without fine pointwise amplitudes or continuity of canonical phases'),
    'sublemma:T3-4-logloss': (
        'Strict margin proved for natural inverse powers, logarithmic polynomials, and every derivative of real profiles and actual cusps',
        'LogFlatDerivativeLoss: coefficient factorization then compact bound for the zero-extended profile; CuspKernelJetBounds and ConstructionCuspJetBounds: all Fréchet cusp jets, including tips, arbitrary β₂∈(0,β); covers actual derivative losses without stating all real TeX exponents; see CUSP_FORCING_DERIVATIVES.md'),
    'sublemma:T3-4-leibniz': (
        'Fréchet jet bounds and exact redistribution of all semiclassical powers proved',
        'SemiclassicalLeibniz: hⁿ times the binomial sum equals the sum of products hⁱ and hⁿ⁻ⁱ for every h; inequalities for real/complex products and evaluation on directions of norm≤1; sufficient norm variant, not a new definition of TeX multi-indices'),
    'sublemma:T3-4-weighted-forcing': (
        'Forcing and all its semiclassical jets through every fixed order proved, with exact action and log-flat cost arbitrarily close to β',
        'CuspFineForcingJets and AtomicCuspFineForcingDerivatives: pointwise bound then mass of actual Wφ; RadialCoreFineForcingDerivatives gives common C,N,Γ for all j≤n and any finite family of unit directions, sum of actual L² norms ≤card*CΓλ²exp(−λJ(Ecore,h,R)−β₁log²λ), κ≤1/16, 0<β₁<β; actual state and effective energy, no tail assumed in the physical application; wrapper ClassicalCuspForcingDerivatives via A002+A004 only; power M=2 suffices, local incoming profile and optimal prefactor not claimed; see CUSP_FORCING_DERIVATIVES.md'),
    'sublemma:T3-4-weighted-projection': (
        'Weighted projection control without commutation proved and included in the actual conjugated resolvent',
        'WeightedProjectedResolvent.norm_weighted_complementProjection_le and AtomicExponentialWeightOps; AtomicCuspWeightedInverse constructs the same positive radial AtomicSchurReference and resolvent R, with bound 12/(γλ) for E≤Ecore'),
    'sublemma:T3-4-weighted-response': (
        'Fine bound for the actual weighted response proved, retaining exact action and factors c,Γ',
        "AtomicGroundFineResponse and AtomicGroundFineDecomposition: ‖exp(κλT)η‖≤CcΓλ³exp(−λJ(Ecore,h,R)−β₁log²λ), every 0<β₁<β; RadialCoreEnergyBounds places the same core's actual energy in [1/2,1], its actual tail supplies Γ; states and c∈[1/2,1] chosen before κ, constants before λ, no fine source admitted; A002+A004 suffice; pointwise control and derivatives were subsequent steps"),
    'sublemma:T3-4-energy-forcing': (
        'Single-forcing-factor bound proved for the same certificate, then rescaled and weighted',
        'AtomicEnergyShiftForcing: |Efull−Ecore|≤(1+‖ζ‖)‖λ²Wu‖ by the scalar equation; c≥1/2 forces ‖ζ‖²≤3 and gives |λ⁻²(Efull−Ecore)|≤3‖exp(κλT)Wu‖, κ≥0; no new asymptotic, second Γ factor, or weight–domain commutation'),
    'sublemma:T3-4-uncompressed': (
        'Exact normalized-correction equation proved in the actual graph then pointwise for the same smooth response',
        'SchurResponseEquation: (A−E)η=−c r+c(E−Ecore)φcore, r=λ²(potential−core)φcore; AtomicResponseWavefunction chooses φfull representing exactly q.normalizedVector; AtomicGroundWeightedDecomposition assembles η=φfull−cφcore, exact orthogonality, weighted mass, and PDE at every point for these same states; explicit A002 realizations, both signs retained, no local elliptic estimate or fine pointwise bound concluded'),
    'sublemma:T3-4-forcing-derivatives': (
        'Both terms of the actual right-hand side controlled at every fixed order, pointwise then in local L²',
        'AtomicFineResponseData and AtomicFineResponseDecomposition: f_h=−cWφcore+c h²(Efull−Ecore)φcore, same state and Γ; radial normalization and action gap give weighted φcore jets without extra Γ; jets h^jD^jf_h, j≤n, bounded by CcΓλ²exp(−λJ−β₁log²λ) on U, including masses and finite sums of actual local L² norms; exact PDE and fine η mass for the same wavefunctions; wrapper atomicGround_fine_response_data via A002+A004 only'),
    'sublemma:T3-4-response-interior': (
        'Pointwise jets of the actual correction proved at every fixed maximum order via A002+A004',
        'AtomicFineResponseJets: same φcore,ψfull,c,Γ and PDE; bounded actual full-potential energy, admissible balls under a uniform threshold; exp(κλT)λ^-j‖D^jη‖≤CcΓλ⁴exp(−λJ(Ecore,R)−β₁log²λ) on closure U′, j≤n, every 0<β₁<β; wrapper atomicGround_fine_response_jets requires only BasicConditions, β₁, n; constants before λ, states before κ,j,x; no scattered-source profile admitted'),
    'sublemma:T3-4-pointwise-response': (
        'Full scattered source and all jets through the fixed order proved, with two independent log-flat factors',
        'AtomicCuspSource proves physical-source germs and jets on each closed support; WeightedSemiclassicalProduct and CuspScatteredSourceJets multiply the same η by λ²W, with T=t; AtomicScatteredSourceJets retains actual φcore,ψfull,c,Γ and J(Ecore,R), giving λ^-j‖D^jFsc‖≤CcΓλ⁶exp(−λJ−βglobal log²λ)logFlat βlocal tStar t exp(−κλt), j≤n, including tips; βglobal and βlocal independent in (0,β), constants before λ, states before κ,j,x; wrapper atomicGround_scattered_source_jets via A002+A004, no new admission; see CUSP_SCATTERED_SOURCE.md'),
    'sublemma:T3-4-incoming': (
        'Local upper bound for all semiclassical jets proved with sufficient polynomial loss; relative leading prefactor is separate',
        'CuspIncomingSourceJets: actual source h⁻²W(cφcore), jets through n bounded by CcΓh^(-(n+4))logFlat βin tStar t exp(−(J(Ecore,R)+t/8)/h) on both closed supports; exact tail ΓK, exterior jets, radial gain t/8, constants before E,h,c,Γ,φ; AtomicSourceProfiles assembles incoming and scattered profiles for the same actual states, Γ, threshold, independent βin/βglobal/βlocal margins; wrapper atomicGround_source_profiles via A002+A004; neither optimal h⁻⁷/² power nor relative leading formula claimed; see CUSP_SOURCE_PROFILES.md'),
    'sublemma:LA-3-rescaling': (
        'Magnetic rescaling, jets, measure, weight, and uniform coefficients proved',
        'AffineScaleJets and AffineScaleL2 prove x=x₀+hy, jet factor h^j and mass factor h⁻²; MagneticEllipticExpansion and MagneticAffineRescaling give exactly −Δ+a·∇+q; RescaledMagneticCoefficientBounds bounds all required jets uniformly before h,x₀,E; no extra gauge needed because centers are bounded; ball containment in U and Lipschitz weight oscillation already proved'),
    'sublemma:LA-3-interior': (
        'Uniform elliptic regularity proved; only H² point evaluation remains classical',
        'EllipticCaccioppoli, LaplacianHessianEnergy and LocalPoissonH2 prove the local H² base. CoordinateSobolevProduct and EllipticSobolevBootstrap prove the higher-order estimate with constants uniform under the prescribed coefficient bounds. CoordinateRectangleFTC and CoordinatePointEvaluation prove point evaluation by two applications of the fundamental theorem and Cauchy–Schwarz; CoordinateSobolevEmbedding derives all derivative evaluations without admissions. EllipticSobolevAssembly proves the unchanged HasInteriorEllipticEstimate'),
    'sublemma:LA-3-weighted-bound': (
        'Application to the actual operator and weight transport proved from the admission-free interior estimate',
        "MagneticInteriorEstimate then WeightedMagneticInteriorEstimate: exp(κλT(x₀))λ^-j‖D^ju(x₀)‖≤Cλ(U+F), U the solution's global weighted norm, F a common bound on weighted right-hand-side jets in local L²; constant before λ,E,x₀,u,f,κ; weight and indicator never differentiated, exact loss h⁻¹ in dimension two"),
    'sublemma:LA-1-weight': (
        'Exact nonnegative, compactly supported, globally Lipschitz weight constructed, equal to the normal coordinate on both closed supports',
        'CuspWeight; CuspWeightApproximation additionally supplies C∞ weights at uniform distance ≤ε, with value and gradient bounds independent of ε∈(0,1]; Sobolev W¹,∞ membership and weak-gradient formula not encoded'),
    'sublemma:LA-1-neighborhoods': (
        'Support separation and vanishing near the core proved; nested TeX open sets not constructed',
        'CuspWeight.CuspWeightCutoffs: each closed cutoff support avoids the closed 4r₀ ball and opposite cusp support; compactly supported weight zero on ‖x‖≤4r₀; neither disjointness of both cutoff supports nor equality to one on open neighborhoods claimed'),
    'sublemma:LA-1-exponential': (
        'Exponentially small defect and weighted radial-vector bound proved uniformly for κ∈[0,κ₀]',
        'AtomicWeightedTail.exists_atomicWeightedTail_of_radialData: ‖(exp(κλT)−1)φcore‖≤Cexp(−cλ), ‖exp(κλT)φcore‖≤1+Cexp(−cλ), for every bounded continuous nonnegative weight zero up to 4r₀; constants before λ; applied to the exact weight by AtomicCuspWeightedInverse'),
    'sublemma:LA-2-compressed-domain': (
        'Actual self-adjoint compression and inverse constructed on the operator domain for E≤Ecore',
        'OrthogonalCompression, CoerciveResolvent, AtomicCuspWeightedInverse: domain D(A)∩φcore⊥ and margin γλ/2 in the unscaled convention; inverse existence obtained before its weighted estimate; symmetric window above Ecore not claimed'),
    'sublemma:LA-2-rank-one': (
        'Exact lifted equation and rank-one defect coefficient proved in the actual domain',
        'WeightedCompression.compression_lift_shifted_eq_of_residual; AtomicPerturbationDomain identifies the residual with λ²(potential−core)φcore; valid for every real shift E'),
    'sublemma:LA-2-weighted-products': (
        'Differential products and magnetic identities proved for test functions and smooth weights',
        'MagneticIMS.covariantDerivative_real_mul, MagneticWeightedTest; AtomicExponentialWeightOps constructs actual inverse L² multipliers ±κ; form-domain preservation by the Lipschitz weight not formalized, replaced by graph closure then strong limit'),
    'sublemma:LA-2-conjugation': (
        'Exact form identity for smooth weights on tests; useful inequality extended to the graph then exact weight',
        'MagneticWeightedTest.magneticForm_exp_test, MagneticWeightedGraph, AtomicSmoothWeightedGraph, AtomicCuspWeightedGraph; BoundedMultiplierLimits justifies strong convergence at fixed λ; neither a general closed-form-domain identity nor operator-domain preservation by the Lipschitz weight claimed'),
    'sublemma:LA-2-almost-orthogonality': (
        'Exact orthogonality-defect identity and control by the multiplier defect proved',
        'WeightedCompression.weighted_orthogonality_defect_le_weighted_norm, AtomicExponentialWeightOps.norm_le_atomicExponentialWeightMul, AtomicWeightedTail; the weight need not preserve φcore⊥ and this invariance is not assumed'),
    'sublemma:LA-2-inner-overlap': (
        'Localized identity and bound by global overlap plus exterior mass proved; TeX localized exponential estimate not claimed',
        'AtomicLocalizationOverlap.norm_waveInner_atomicInnerCutoff_sq_le_overlap_exterior_mass; AtomicWeightedTestCoercivity uses the O(1/λ) exterior bound sufficient to retain coercivity with a rank-one defect'),
    'sublemma:LA-2-inner-gap': (
        'Radial gap on localized tests and treatment of orthogonality defect proved under radial data',
        'AtomicWeightedTestCoercivity.atomic_test_rankOne_lower_sub_penalty; smooth weights zero near the core by AtomicSmoothWeight; variant at Ecore, without claiming coefficient 3γh/4 or the TeX symmetric window'),
    'sublemma:LA-2-outer-gap': (
        'Exterior margin and gradient-penalty absorption proved for the concrete potential',
        'AtomicLocalizationForms.atomicOuterCutoff_form_lower: margin λ²/4 under Ecore/λ²≤−3/4; AtomicWeightedTestCoercivity absorbs a penalty ≤λ²χ₁²/8; AtomicSmoothWeight and CuspWeightApproximation supply this bound uniformly in ε and κ≤κ₀'),
    'sublemma:LA-2-ims-error': (
        'Integrated IMS identity and fixed error constant proved on tests; coercive consequences transferred to the actual graph',
        'MagneticIMSIntegrated, AtomicLocalizationCutoffs.exists_atomicIMSError_bound, AtomicWeightedTestCoercivity; O(1) error before rescaling, hence O(h²) after; IMS identity on the entire form domain not claimed'),
    'sublemma:LA-2-coercivity': (
        'Weighted coercivity with rank-one defect proved on the actual graph for the exact Lipschitz weight',
        'AtomicCuspWeightedGraph.exists_atomic_cusp_weighted_graph_lower_of_radialData: margin γλ/2, defect 2γλ|⟨φcore,Wu⟩|²; constants before λ, φcore before κ; WeightedCompressedEstimate absorbs defect and residual for E≤Ecore without assuming domain stability under W'),
    'sublemma:LA-2-defect-small': (
        'Actual radial-state residual exponentially small and lifted coefficient controlled',
        'AtomicResidualDecay: ‖λ²(potential−core)φcore‖≤Kλexp(−dλ); WeightedCompression controls the coefficient by this norm and ‖u‖≤‖Wu‖; AtomicWeightedTail bounds ‖Wφcore‖ uniformly in κ'),
    'sublemma:LA-2-absorption': (
        'Uniform absorption of overlap defect and residual proved, then estimate of the actual compressed inverse',
        'WeightedResidualAbsorption chooses the threshold before λ; WeightedCompressedEstimate.weighted_compression_resolvent_bound and AtomicCuspWeightedInverse give ‖WRf‖≤4/(γλ)‖Wf‖ for E≤Ecore; no weighted inverse assumed as input'),
    'sublemma:LA-2-rank-one-norm': (
        'Required weighted-projection bound proved without weight commutation',
        'WeightedProjectedResolvent.norm_weighted_complementProjection_le: ‖WQW⁻¹v‖≤(1+‖Wφcore‖)‖v‖; concrete inverse and contraction W⁻¹ in AtomicExponentialWeightOps; general rank-one norm equality not exported here'),
    'sublemma:LA-2-projection-norm': (
        'Projected conjugated inverse constructed on all L², norm ≤12/(γλ) for E≤Ecore',
        'AtomicCuspWeightedInverse.exists_atomic_cusp_weighted_inverse_of_radialData, WeightedProjectedResolvent; equivalent to O(h⁻¹) for the rescaled operator, h=1/λ; sufficient at Efull≤Ecore, but certifies neither the full symmetric window nor uniformity on a neighborhood of geometric parameters'),
    'sublemma:L2-8-upper': (
        'Bound with arbitrary loss proved, uniform in a≥a_min>0, for natural m',
        'LogFlatIntegral.eventually_logFlatLaplaceIntegral_le_exp and cutoff version; m=2 included'),
    'sublemma:L2-8-lower': (
        'Lower bound and uniform logarithmic rate proved for natural powers',
        'LogFlatIntegralLower; integration on (h,2h) without saddle localization; version with cutoff equal to 1 near 0'),
    'sublemma:P2-6-action-slopes': (
        'Normal action derivatives and positivity proved',
        'GeometryActionSlopes'),
    'sublemma:P2-6-displacement': (
        'Growth, divergence, and uniform separation choice proved',
        'ActionReserves, UniformActionReserves, SeparationCertificate'),
    'sublemma:P2-6-phase-calculation': (
        'Phase calculations covered',
        'Geometry.phase_at_tips, phaseStar_pos, hasDerivAt_phase_normal_plus/minus'),
    'sublemma:P2-6-same-cusp': (
        'Bound 3bR²/4 proved at the tips for the explicit action, uniform in E>0',
        'GeometryAction.same_cusp_action_gap_ge / same_cusp_minus_action_gap_ge; kernel identification remains'),
    'sublemma:L2-9-chart-calculus': (
        'Chart, inverse, injectivity, Jacobian t², and integral change of variables proved',
        'CuspChartJacobian; weighted cusp integral reduced exactly to the normal integral'),
    'sublemma:L2-9-coordinate-inequalities': (
        'Bounds on closed supports proved, constants 1/4',
        'ConstructionCuspBounds; both signs and radial growth of the action'),
    'sublemma:L2-9-potential': (
        'Admissibility, disjoint supports, minimum, and reflection proved',
        'ConstructionExistence, ConstructionSmooth, ConstructionSupportSeparation, ConstructionMinimum; Hessian in directional form'),
    'sublemma:L2-9-flat-extension': (
        'C∞ extension and vanishing of all jets proved; quantitative jet bound not exported',
        'LogFlatSmooth, CuspKernelSmooth, ConstructionCuspJets; proof by a derivative-stable family'),
    'sublemma:C7-4-phase-points': (
        'Replaced for thm:main by a weaker sufficient lemma',
        'CosineAsymptotic.exists_phase; neither uniqueness nor monotonicity claimed'),
    'sublemma:C7-4-signs': (
        'Unbounded signs and zeros proved and instantiated for actual hopping',
        'CosineAsymptotic.unboundedSigns/unboundedZeros; ConstructedMainProof constructs physical data and continuity, then Remaining.elementaryPotential_main instantiates them for elementaryParameters via A002 and A004'),
    'sublemma:C8-7-crossings': (
        'Unbounded crossings constructed for the explicit potential',
        'SpectralAsymptotics.result_above; CanonicalParityRelativeErrors supplies actual o(A) errors for the same witnesses as hopping; ConstructedMainAssembly then ConstructedMainProof give the physical conclusion, instantiated in Remaining via A002 and A004'),
    'sublemma:C8-7-multiplicity': (
        'Physical decompositions, exact multiplicity, and infinitely many crossings assembled',
        'ParityGroundEigenspaces and PhysicalParityModes give actual normalized modes and their spans; ParityDoubletRealization then ConstructedDoubleWellSpectral construct TwoModeRealization. GroundSpaceAlgebra gives dimension exactly two at sufficiently large crossings. ConstructedMainProof and Remaining.elementaryPotential_main assemble divergent sequences and spectral conclusions for fixed parameters via A002 and A004'),
    'sublemma:C8-7-spacing': (
        'Outside thm:main — not formalized',
        'Optional spacing from the introduction'),
    'sublemma:T1-1-fixed-potential': (
        'Explicitly fixed potential and final theorem proved modulo two classical admissions',
        'Remaining.elementaryPotential_main fixes elementaryParameters before L₀, then treats every L≥L₀; Remaining.thm_main deduces ConstructedPotentialMainTheorem without direct sorry. ConstructedMainProof constructs original data; only admissions A002 and A004, no tunneling hypothesis'),
    'sublemma:T1-1-two-zero-statements': (
        'Both zero conclusions assembled for the explicit potential',
        'LocalAnalyticData.conclusion, ConstructedMainAssembly, and ConstructedMainProof; continuous canonical hopping and splitting, amplitudes and Schur errors for the same witnesses; Remaining.elementaryPotential_main and thm_main via A002 and A004'),
    'sublemma:T1-1-full-ground-space': (
        'Operator conclusion and actual eigenspaces assembled for the explicit potential',
        'ConstructedMainProof.operatorMainConclusion_of_radialData constructs the conclusion from explicit spectral and resolvent interfaces and the interior estimate; Remaining.elementaryPotential_main then thm_main instantiate A002 and A004. Physical modes and multiplicities come from the actual domain and global min–max levels'),
    'sublemma:L4-1-global-tail': (
        'Sufficient variant proved for fixed double-well cutoffs using the radial tail beyond 4r₀',
        'AtomicGroundAgmon supplies Cλ⁻²exp(−2dλ) for exterior mass of every full ground state. DoubleWellLocalizationCutoffs constructs plateaus containing full supports and 4r₀ balls, with radii fixed before L. This tail controls overlap errors in DoubleWellLocalizedEstimates; the generic theorem for every near-support cutoff and distance weight is not claimed'),
    'sublemma:T4-2-localized': (
        'Physical variant proved: exact gap of each full atom, localized-form identities, controlled overlap defects',
        'GroundStateRankOne, MagneticTestRankOne, and AtomicGroundRankOne give g=hRad.gap·λ/2 for every actual full ground state; TranslatedAtomicGap retains g and the threshold under covariance and inversion. DoubleWellLocalizedEstimates gives potential identities and norm(local overlap)²≤2norm(global overlap)²+2tail·mass; the orthogonal case follows with the actual Agmon tail. All test integrability is deduced; no extra nonradial spectral data assumed'),
    'sublemma:T4-2-outside': (
        'Sufficient exterior margin proved by kinetic nonnegativity and atomic energy; free coefficient bh not claimed',
        'DoubleWellLocalizationCutoffs makes both potentials vanish after multiplication by χext; MagneticLocalizedForm and DoubleWellLocalizedEstimates.doubleWellExteriorCutoff_form_nonneg give exterior form ≥0. In DoubleWellTestCoercivity, Eatom≤−λ²+Bλ ensures g≤−Eatom and supplies g·exterior mass, sufficient for absorption. Neither free-bottom calculation bh nor a separate literal 1/2 bound exported here'),
    'sublemma:T4-2-absorption': (
        'Coercivity of the actual two-atom complement proved on tests then the operator domain, uniformly in separation',
        "MagneticIMSThree, DoubleWellCoercivityScalar, and DoubleWellTestCoercivity: coefficient g−4g·tail−2D, then hRad.gap·λ/4 with defect hRad.gap·λ times the sum of both squared overlaps. MagneticGraphTwoModeLowerBound and DoubleWellOperatorCoercivity transfer to the actual closed graph with arbitrary representatives; threshold T before all λ≥T, L≥cert.L₀, and full ground states. ClassicalDoubleWellCoercivity.doubleWell_complement_coercivity uses exactly A002+A004. After multiplication by h², this is the TeX c_dw h variant; a separate closed-form-domain extension is not claimed. ParityTrialCoercivity now retains the absolute lower bound in each sector trial's complement; self-adjoint restrictions are proved separately. See [TWO_WELL_COERCIVITY.md](TWO_WELL_COERCIVITY.md)"),
    'sublemma:L4-1-transport': (
        'Exact exterior-mass transport and connection to actual double-well IMS cutoffs proved',
        'MagneticCovariance, ParityTrialStates, and LocalizedOverlap: magnetic translation and inversion preserve mass and MemLp and transport exterior integrals beyond 4r₀. DoubleWellLocalizationCutoffs supplies the corresponding plateaus; DoubleWellLocalizedEstimates bounds each squared localized overlap by twice the squared global overlap plus twice the atomic tail times mass. Fixed variant used in the physical proof, not every manuscript cutoff χ'),
    'sublemma:T4-3-reality': (
        'Reality of overlap proved by inversion; reality of canonical hopping already proved through sources',
        'ParityTrialStates.waveInner_left_right_im_eq_zero, without spectral hypotheses; AtomicSourceFacts.hopping_real and CanonicalHoppingFromChannels give real hopping in the physical regime under an explicit free-resolvent contract. Self-adjoint restrictions are constructed separately by L2ParitySectors, DoubleWellParityGraph, and ReducingSubspaceRestriction; they are not added spectral hypotheses'),
    'sublemma:T4-3-overlap-bound': (
        'Sufficient variant proved: canonical overlap ≤Cλ⁻¹exp(−dλ), uniform for L≥4r₀',
        'MagneticOverlapTail: |⟨φL,φR⟩|²≤4∫_{‖x‖≥a}|φ|² for L≥a>0, by measurable partition and Cauchy–Schwarz; CanonicalOverlapDecay applies Agmon with a=4r₀, constants before λ and L, zero limit and uniform smallness. ClassicalCanonicalOverlapDecay instantiates only A002+A004; R<2L suffices since 8r₀<R. The literal two-smooth-cutoff formula and fine action rates are not claimed'),
    'sublemma:L4-4-residual': (
        'Exact pointwise and operator residuals, then coarse exponential norm bound proved; relative comparison handled separately',
        'DoubleWellResidual: (Hdouble−Eatom)φL=λ²vRφL and reflected identity, without gauge error; DoubleWellTrialDomain transports L² classes by bounded perturbation and gives the same residual as a multiplier. Eatom is the full-well energy; in units h²H the λ² factor disappears. DoubleWellTrialResidualBound controls these multipliers by the tail beyond 4r₀, then their norm by sqrt(C)λexp(−dλ); ParityTrialEnergyBound gives the small spectral cost γλ/8. The literal cutoff formula remains distinct; PhysicalResidualMass and CanonicalParityCorrectionMass connect exact residuals to opposite mass, then CanonicalParityRelativeErrors controls the correction after division by the gap, without asserting residual²=o(A)'),
    'sublemma:T4-7-trial-normalization': (
        'Exact masses, normalization, parity, orthogonality, and actual-domain membership proved for trial states',
        'ParityTrialStates: masses 2(1±s), C∞ and L² states, unit mass under |s|<1, orthogonal even/odd trials; IsAtomicGroundState.exists_normalizedParityTrialState_unit_operator_vector in ParityTrialDomain gives their unit-norm L² class and parity in the double-well domain under explicit realizations. These are trials; no eigenvalue equation or min–max identification concluded'),
    'sublemma:T4-7-block-domain': (
        'Actual self-adjoint restrictions and exact physical Rayleigh quotient proved; literal spectral window not claimed',
        'L2ParitySectors, DoubleWellParityGraph, and DoubleWellParityOperator give closed sectors and actual domain D(H)∩sector with the same action. ParityTrialCoercivity and ParitySchurGroundConstruction construct the sector certificate. ParityTrialRayleigh identifies exactly a±=Eatom+(δ±Reρ)/(1±s), with physical integrals and canonical version. ParitySchurEnergyShift then ConstructedParitySchurEnergyBound give 0≤a±−E±≤residual²/(γλ/8). The entire TeX window remains distinct; relative errors required by CanonicalParitySchurData are now constructed in CanonicalParityRelativeErrors for the same witnesses, then used in ConstructedMainProof; see GLOBAL_PARITY_DOUBLET.md and OPPOSITE_SUPPORT_ESTIMATES.md'),
    'sublemma:T4-7-kernel-map': (
        'Schur elimination, sector simplicity, and exact global eigenspaces proved',
        'SchurBlock reconstructs the exact kernel; ParityGroundCertificate gives the sector span. ParityGroundEigenspaces projects actual eigenvalue equations and gives a singleton span if energies differ, the span of both modes at a crossing. PhysicalParityModes normalizes certificates without changing their gap and supplies pointwise eigenfunction decompositions. Neither a classification of the whole spectrum in a window nor a rank-two spectral projection is claimed'),
    'sublemma:T4-7-existence': (
        'Actual simple sector ground states of the constructed potential proved, at parityEnergy energies',
        'ParitySchurGroundConstruction applies actual resolvents and the Schur root to the self-adjoint restriction; EigenvectorComplementBound preserves the absolute lower bound. DoubleWellParityGround.exists_doubleWell_parityGroundCertificates_of_radialData gives T before λ,L, then a certificate for each parity at E=parityEnergy: E≤Eatom+γλ/8, gap≥γλ/8, E+gap=Eatom+γλ/4. ParityEnergyIdentification proves equality with the test infimum, including nonemptiness; ParityGroundCertificate supplies simplicity and a smooth normalized state. Only explicit classical data A002+A004, instantiated by ClassicalDoubleWellParityGround.doubleWell_parityGrounds hp cert; neither physical expansion nor equivalence to the whole spectrum in the window claimed'),
    'sublemma:T4-7-lowest-two': (
        'First two global min–max levels, physical descriptions, and global gap proved; window projection not claimed',
        "ParityOperatorDecomposition lifts projections to the actual domain. SecondEnergyParityUpper uses nearly minimizing even/odd tests; SecondEnergyComplementLower uses dimension two and the lower bound on the low mode's complement. ConstructedGlobalMinmax and doubleWell_global_minmax hp cert give groundEnergy=min(E+,E−), secondEnergy=max(E+,E−), threshold before λ and L. ParityDoubletRealization and ConstructedDoubleWellSpectral assemble TwoModeRealization; ClassicalDoubleWellSpectral.doubleWell_twoModeRealization hp cert directly supplies LocalChannelAnalyticData modes; its corollary doubleWell_spectral_realization supplies SpectralRealization and HasGapAboveGround via A002+A004 only. The whole spectrum, literal window, and projection are not formalized here"),
    'sublemma:P5-1-source-resolvent': (
        'Right-state equation and representation deduced from atomic existence and the proved free-resolvent formula',
        'MagneticCovariance, LandauResolventBridge, AtomicSourceRegime; existence and energy regime now supplied from BasicConditions via A002+A004, threshold before L; source amplitudes are a separate step'),
    'sublemma:P5-1-gauge-sources': (
        'Gauges and normalizations proved',
        'HoppingSourceIdentity.leftPhysicalSource_gauge/rightPhysicalSource_gauge'),
    'sublemma:P5-1-wedge-phase': (
        'Exact phase and affine substitutions proved',
        'HoppingSourceIdentity.sourcePhase_affine/physical_source_integrand_affine'),
    'sublemma:P5-1-fubini': (
        'Absolute convergence proved for sources of the concrete potential',
        'HoppingIntegrability.cellsIntegrable_of_continuous; R<2L, h,E>0'),
    'sublemma:L5-3-swap': (
        'Conjugation under source exchange proved',
        'HoppingChannels.sourcePairing_swap/sourceKernel_swap'),
    'sublemma:T5-5-core-core': (
        'Distance and action margin proved on the entire support',
        'InactiveSupportGaps.core_core_action_gap: 32δ, distinct E and E₀'),
    'sublemma:T5-5-core-cusp': (
        'Four mixed cells covered on entire supports',
        'InactiveSupportGaps.core_cusp_action_gap/cusp_core_action_gap: 32δ'),
    'sublemma:T5-5-same-cusp': (
        'Both same-cusp cells covered on entire supports',
        'InactiveSupportGaps.same_cusp_total_action_gap: 48δ'),
    'sublemma:L5-7-annulus': (
        'Positive compact annulus common to all nine cells proved',
        'SeparationCertificate.component_support_annulus'),
    'sublemma:L5-6-core-source': (
        'L¹ bound on the actual core source proved',
        'CoreSourceBound: C=sqrt(∫core²), uniform over normalized L² states'),
    'sublemma:L5-6-cusp-source': (
        'L¹ norms of both full cusp sources proved for the same actual atomic state',
        'CuspProfileIntegral and its reflection: support, integrability, Jacobian t², factor 2s₀, uniform threshold giving any coefficient strictly below the local profile; AtomicSourceL1 separately retains CI cΓλ⁴exp(−λJ−βin log²λ) and CS cΓλ⁶exp(−λJ−(βglobal+βlocal)log²λ); AtomicComponentSourceL1 deduces full-component sum ≤CΓλ⁶exp(−λJ−β₁log²λ), every 0<β₁<β, plus core bound Ccoreλ² and integrability of all three components; same φcore,ψfull,c,Γ and threshold before λ; wrappers via A002+A004, no new admission; norm_toL1_eq_integral_norm identifies actual norms; see CUSP_SOURCE_L1.md'),
    'sublemma:L5-7-kernel-infimum': (
        'Sufficient version with arbitrary exponential loss proved on supports; exact prefactor remains',
        'InactiveKernelBounds.exists_inactiveKernelUpperBounds; Cexp(-(J−η)/h), not yet Ch^(-3/2)exp(-J/h)'),
    'sublemma:T8-5-algebra': (
        'Scalar identity and exact physical Rayleigh quotients proved',
        'ParityTransfer.rayleigh_difference; ParityTrialRayleigh identifies a±=Eatom+(δ±Reρ)/(1±s), with actual translatedDefect/translatedOverlap/hopping, and canonical definitions in canonicalParityTrial_schurDiagonal'),
    'sublemma:P5-8-product': (
        'Actual pairing bounded by both L¹ norms',
        'InactiveKernelBounds.norm_sourcePairing_le/sourceKernel_le; bound only on actual supports'),
    'sublemma:P5-8-three-types': (
        'Seven absolute bounds proved for the same actual states and canonical cells',
        'InactiveCellL1Bounds: separated kernels and L¹ norms give K(Ccore+S+1)²(Γ²+1)λ¹⁰exp(−λ(Aref+31δhop)), then the norm of the sum with factor 7; AtomicInactiveCells instantiates sources and both actual energies in [1/2,1], same φcore,ψfull,c,Γ, core/core/full action; SourcePhaseInvariance transports to canonical cells; wrapper atomicGround_inactive_cells via A002+A004, no new admission; InactiveCellNormSum also exports the sum of seven norms; relative comparison proved in block L7.1; see INACTIVE_CELLS.md'),
    'sublemma:T8-5-rayleigh-error': (
        'Sufficient variant: diagonal defect and actual Schur corrections o(envelope) proved for the same witnesses',
        'AtomicOppositeSupportFineBounds gives masses ≤C c²Γ²λ¹²exp(−2λ(G+J)); CanonicalParityCorrectionMass then FineBound cost λ² for the defect and λ³ for the correction, bounded by λ¹⁵. OppositeSupportEnvelopeComparison retains margin J≥(2L−R)/2 and gives ≤C envelopeTex exp(−(2L−R)λ/4). CanonicalParityRelativeErrors uses exactly W.c,W.Γ from ConcreteChannelWitnesses. The final version used is o(A), without a separate residual²=o(A) assertion or claim of the full TeX remainder rate; see OPPOSITE_SUPPORT_ESTIMATES.md'),
    'sublemma:L8-6-form-bottoms': (
        'Continuity of actual parity energies and signedSplitting proved for every positive coupling',
        'ParityEnergyContinuity gives variational continuity by dilation and uniform potential comparison. MagneticParityNormalization and ConstructedParityEnergyContinuity prove required nonemptiness for the constructed potential; ClassicalDoubleWellParityGround.doubleWell_parityEnergy_continuous/doubleWell_signedSplitting_continuous instantiate A002+A004 under hp,cert,L≥cert.L₀. No continuous eigenfunction choice required; hopping treated separately at label L8-6-hopping; see DILATION_AND_CONTINUITY.md'),
    'sublemma:L8-6-hopping': (
        'Canonical hopping continuity proved on a half-line for the constructed potential under explicit radial data and realizations',
        'HoppingContinuity, CuspParameters.exists_canonicalHopping_continuous_of_radialData: hp,hRad,hAcore,hApot → ∃T>0,∀L,ContinuousOn (canonicalHopping p.b p.potential L) (Ici T). Bilinear bound norm_hopping_sub_le_of_mass_one, continuity with fixed dilated reference continuous_hopping_magneticDilation_inv, actual-state comparison modulo phase by AtomicGroundDilationComparison, and HoppingPhase invariance. Standard-axioms-only audit of the conditional result; wrapper canonicalHopping_continuous hp compiled in ClassicalHoppingContinuity via A002+A004. Sufficient large-coupling variant without a continuous canonical choice or abstract continuous spectral-projection theorem; see DILATION_AND_CONTINUITY.md'),
    'sublemma:T8-5-transfer': (
        'Transfer and existence of actual Schur data proved, with relative o(1) error',
        'CanonicalParityRelativeErrors.nonempty_canonicalParitySchurData_of_radialData constructs data for the exact amplitude 2K*envelopeTex of the same W; CanonicalParitySchurData.transfer then ConstructedMainProof assemble physical splitting. The o(1) variant suffices for thm_main; no extra final O(1/log λ) rate claimed'),
    'sublemma:D6-4-log-disc': (
        'Lipschitz logarithm estimate proved on half-planes Re≥a>0',
        'ComplexLambertRoot.norm_complex_log_sub_le_of_re_ge; sufficient version for contraction'),
    'sublemma:D6-4-contraction': (
        'Quantitative contraction construction proved with a larger disc',
        'ComplexLambertRoot; iteration w↦L−log(w), then error ≤R/(Re L−R)'),
    'sublemma:D6-4-lambert': (
        'Existence, uniqueness in Re≥2, uniform asymptotic, holomorphy, and derivative on the explicit domain proved',
        'ComplexLambertRoot/Asymptotics/Regularity; root constructed directly, without a Lambert-W axiom'),
    'sublemma:D6-4-log-change': (
        'Exact Lebesgue change of variables and integrability proved for natural m',
        'ComplexLogFlatChange; factor tStar^(m+1), physical m=2 included'),
    'sublemma:D6-4-saddle-location': (
        'Saddle point for coefficient c*tStar/h constructed; identity and O(h log(1/h)) bound proved',
        'ComplexLogFlatSaddle; fixed parameters, c≠0, no assumed saddle existence'),
    'sublemma:D6-4-critical-calculation': (
        'Derivatives and exact critical identities proved for the constructed point',
        'ComplexLogFlatSaddle.eventually_logFlatSaddleRoot_value_hessian; f′=0, critical value, and f″=2β(1+w)'),
    'sublemma:D6-4-branches': (
        'Unambiguous argument and bound Re(c exp(−iη))≥Re c proved on the connector',
        'ComplexSaddleBranches; Re c>0 and sufficiently small h'),
    'sublemma:D6-4-deformation': (
        'Exact logarithmic-ray deformation and connection to the actual potential cutoff proved',
        'ComplexLogFlatContour, ComplexLogFlatCutoffAsymptotic; fixed parameters, natural m'),
    'sublemma:D6-4-fixed-connectors': (
        'Connector, left tail, and fixed cutoff region proved exponentially small, then absorbed',
        'ComplexLogFlatErrors/Cutoff/Normalization; explicit positive rates'),
    'sublemma:D6-4-phase-difference': (
        'Exact phase difference proved for every complex displacement',
        'ComplexLogFlatPhase.logFlatComplexPhase_difference'),
    'sublemma:D6-4-real-phase-bounds': (
        'Real part, integrability, and global quadratic/linear bound proved',
        'ComplexLogFlatPhase, ExponentialRemainderBounds; uniform majorant after dilation'),
    'sublemma:D6-4-gaussian-evaluation': (
        'Complex Gaussian limit, connection to the original integral, and absolute horizontal-line bound proved; O(1/|w|) rate not claimed',
        'ComplexSaddleLeading, ComplexLogFlatCutoffAsymptotic; fixed parameters, natural m, relative o(1) error; ComplexSaddleAbsolute.sqrt_re_mul_integral_norm_horizontalSaddle_le, constant depending only on β for Re w≥1'),
    'sublemma:D6-4-leading-size': (
        'Saddle normalization, exp(−d/h) absorption, and nonvanishing of the integral term proved; precise log|S| expansion and derivatives remain',
        'ComplexLogFlatNormalization, ComplexLogFlatCutoffAsymptotic; ComplexLogFlatPhaseGrowth also proves positivity of the model leading size, with sqrt(Re w) in the denominator'),
    'sublemma:C6-1-spatial': (
        'Bilinear radius and joint holomorphy of actual-kernel spatial compositions proved',
        'ComplexCuspGeometry, ComplexCuspKernelHolomorphic; domain Re(z·z)>0 and common bidisc; uniform bounds on all derivatives not exported'),
    'sublemma:C6-1-holomorphy': (
        'Holomorphy of the actual complex integral on Re(r²)>0 proved, with local integrable domination deduced',
        'ComplexLandauHolomorphic.analyticOnNhd_complexLandauKernel; positive real b,h,E; Cauchy then differentiation under the integral, without an extra domination hypothesis'),
    'sublemma:C6-1-expansion': (
        'Order-zero variant proved: relative complex kernel 1+o(1) uniformly on window δ=O(h^(3/4))',
        'ComplexLandauLocalProfile, ComplexLandauTails, ComplexLandauAsymptotic; moving real energy, Gaussian and tails proved; all derivatives and fixed complex neighborhoods not claimed'),
    'sublemma:T6-1-assembly': (
        'Exact assembly and uniform relative asymptotic proved on the shrinking active window',
        'ComplexLandauDecomposition, ComplexLandauAsymptotic.tendstoUniformlyOn_complexLandauKernel_relative_rectangle; phase J(E,r)+J′(E,r)δ and power h^(-3/2), without an all-orders expansion'),
    'sublemma:P6-7-common-domain': (
        'Common bidisc and joint holomorphy of three radii, kernels, and normalized physical profile proved',
        'ComplexCuspKernelHolomorphic, CuspActiveWindow, CuspKernelProfileHolomorphic; geometric radius chosen before h and both positive energies. The normalized profile retains distinct core/full energies and the full phase. Full physical deformation is a separate step; no continuation of the scattered response'),
    'sublemma:P6-7-real-germ': (
        'Exact sources, density, and normalization proved; Fubini and integrability of every normal fiber established',
        'CuspIncomingSourceFormula, CuspSourcePairingCoordinates, CuspSourcePairingFubini, IncomingCuspDensityNormalization: Jacobians t²u², three core/core/full kernels, exact phase; multiplicative identity with two scalar m=2 models and actual normalized profile. Factor −h² and source strengths stay outside; tStar⁶ appears only in logarithmic substitutions'),
    'sublemma:P6-7-radius-derivatives': (
        'Complex normal derivatives equal to 1/2 and three uniform quadratic remainders proved',
        'ComplexCuspGeometry, ComplexCuspRemainder, ComplexCuspKernelProfile; remainders/h→0 and profiles normalized with t/2 and (t+u)/2 at actual radii; atomic amplitudes are a separate step'),
    'sublemma:P6-7-magnetic-polynomial': (
        'Exact polynomial phase expansion, uniform quadratic remainder, and exponential correction tending to one proved',
        'ComplexCuspPhase; phaseStar + phaseSlope*(t+u), bounded tangential variables, normals O(h^(3/4)), no assumed remainder'),
    'sublemma:P6-7-joint-phase': (
        'Joint profile and freezing of the limiting slope proved at actual energies; moving action retained',
        'ComplexCuspKernelProductProfile, ActiveSaddleSlopeEnergy, ComplexCuspFrozenSlope, AtomicCuspKernelProfile: Ec,Ef=1+O(h), Lipschitz energy dependence of J′, uniform freezing factor 1+o(1); normalized three-kernel product and phase 1+o(1) on the complex h^(3/4) window'),
    'sublemma:P6-7-exponential-budget': (
        'Uniform relative o(1) error and normalized integrated error on the saddle contour proved; explicit TeX rate not claimed',
        'AtomicCuspKernelProfile then CuspSaddleMultiplier: actual multiplier bounded by 2, continuity and integrability deduced, N_h²∫F_h(P_h−1)→0 uniformly in s,r; absolute product bound without dividing by an oscillatory integral. Physical real connection, truncation, and double deformation now proved in AtomicIncomingNormalAsymptotic'),
    'sublemma:P6-7-one-contour': (
        'Two physical fiber identities proved with integrability deduced and the actual multiplier',
        'AtomicCuspRayShift applies LogFlatContourMultiplier to actual energies and the frozen profile: threshold independent of tangential variables, the other normal in the window, and every shift height. Explicit connector; LogFlatMultiplierConnector retains exp(−tStar Re(c) h^(−1/4)). No physical profile or integrability admitted'),
    'sublemma:P6-7-product-contour': (
        'Two physical deformations, hybrid integrability, and uniform normalized o(1) error proved',
        'AtomicCuspDoubleRayShift uses Fubini and both fiber identities: bound Cexp(−d h^(−1/4)), then N_h²(I00−Ivv)→0 uniformly in s,r. AtomicCuspContourTranslation exactly identifies the shifted contour with the centered domain. CuspSaddleMultiplier controls the actual profile on this domain'),
    'sublemma:P6-7-real-truncation': (
        'Physical h^(3/4) variant proved: removal of the box complement after full normalization',
        'IncomingCuspDensityBound then IncomingCuspRealTruncation: actual density ≤Ch⁻⁶exp(−A/h)t²u²exp(−(t+u)/(8h)), and error outside the box ≤Ch⁻⁶exp(−A/h)t₀⁶exp(−tStar h^(−1/4)/8). IncomingCuspNormalizationBounds and AtomicIncomingRealTruncation absorb this error after N² Z_h at both actual energies; no physical bound remains'),
    'sublemma:P6-7-scalar-product': (
        'Truncated normalized product and actual multiplier evaluated: limit π/β, uniform in s,r',
        'CuspSaddleLeading: left tail removed, scalar product factored without conjugation, actual-multiplier error integrated. LogFlatMultiplierChange and IncomingCuspLogarithmicChange separately prove both physical substitutions, their factor tStar⁶, and prior removal of χa=1 on the window'),
    'sublemma:P6-7-evaluation': (
        'Physical incoming integral and actual cell evaluated, exact amplitude and phase with relative o(1) error',
        'AtomicIncomingNormalAsymptotic assembles truncation, exact changes, and two contours for the actual density on the full real domain. IncomingCuspTangentialIntegration deduces integrability/Fubini and error ≤δ(2s₀)²; AtomicIncomingIntegralAsymptotic proves N_h² Z_h incomingCuspIntegral→tStar⁶(π/β)Bs², nonzero coefficient, actual core/full energies. IncomingCellAsymptotic then IncomingCellTexAsymptotic restore negative sign, λ⁶√λ, coefficient K*, and phase; witness-independent remainder. The o(1) variant, not the TeX rate. See ACTIVE_CHANNEL_ASYMPTOTIC.md'),
    'sublemma:P6-8-mixed': (
        'Sufficient variant proved for both actual mixed terms: cost 3β₀, power λ¹⁰, exact action',
        'ActiveCrossPairingBound + AtomicSourceL1 + AtomicActiveScatteredBounds: cancellation h²·h⁻², same φψcΓ and core/core/full energies. Local losses are already spent before choosing effective margins β₀<β; neither a literal factorization with extra bridge slope nor continuation of the correction is needed'),
    'sublemma:P6-8-double': (
        'Actual scattered–scattered term bounded with cost 4β₀ and power λ¹²',
        'AtomicActiveScatteredBounds: two local and two global costs, same active action and c²Γ²; absolute bounds proved by the product of actual L¹ norms, without cancellation'),
    'sublemma:P6-8-envelope': (
        'Full/incoming reduction proved relative to envelopeTex, margin (3β₀−2β)/2>0',
        'SharpSaddleSize absorbs every power with coefficient 2β+η; ActiveScatteredEnvelope and SourcePairingAdditivity control all three terms and their sum. AtomicActiveScatteredRelative exports actual/canonical differences; atomicGround_active_incoming_reduction fixes β₀=3β/4, margin β/8, under BasicConditions and R<2L via A002+A004. Separate stronger double-scattered rate not exported; incoming asymptotic now proved and assembled with the same witnesses in CanonicalChannelAsymptotics. See ACTIVE_CHANNEL_ASYMPTOTIC.md'),
    'sublemma:D6-6-tail': (
        'Variant with window tStar h^(3/4) proved: real tail uniformly negligible for A≥A₀ under fixed complex normalization',
        'LogFlatActiveRealTail, LogFlatPolynomialErrors; natural m, fixed c, h^(-N) factors absorbed; optimal M₀h log(1/h) window and uniformity in c not claimed'),
    'sublemma:D6-6-contour-location': (
        'h^(3/4) variant: saddle in the window and truncated contour contained in the normal disc proved',
        'LogFlatActiveWindow.tendsto_logFlatSaddle_location_div_window, LogFlatActiveTruncation.norm_logarithmicPoint_le_activeWindow; fixed parameters'),
    'sublemma:D6-6-connector': (
        'h^(3/4) variant: connector and left tail O(exp(−d h^(-1/4))), negligible after normalization',
        'LogFlatActiveTruncation, LogFlatPolynomialErrors; threshold uniform in the moving endpoint, h^(-N) factors absorbed; fixed c'),
    'sublemma:D6-6-common-choice': (
        'h^(3/4) variant: same window for real tail, saddle, bounded contour, and absolute control of the restricted product',
        'LogFlatActiveRealTail, LogFlatActiveTruncation, ComplexSaddleProduct; original M₀h log(1/h) window not claimed'),
    'sublemma:L6-6-common-choice': (
        "h^(3/4) variant: truncation and inclusion in the actual cutoff's constant region proved without changing the potential",
        'CuspActiveWindow.CuspParameters.eventually_activeWindow_local; fixed parameters; compact uniformity in c remains'),
    'sublemma:T7-2-phase': (
        'Continuous real phase and cosine asymptotic for actual hopping proved, explicit positive envelope',
        'ActiveIncomingPhase and CanonicalChannelAsymptotics: Θ=λΦ*+2phaseGauss, Θ/λ→Φ*. Gaussian/TeX envelope ratio absorbed into o(1). Same amplitude 2K*envelopeTex and witnesses; classical wrappers A002 and A004. Literal TeX phase not claimed'),
    'sublemma:L7-3-monotonicity': (
        'Weaker property proved for the model phase correction: eventual continuity and phase/λ→0',
        'ComplexLogFlatPhaseGrowth.tendsto_logFlatSaddlePhase_inv_div; fixed parameters; physical-phase connection proved in ActiveIncomingPhase and CanonicalChannelAsymptotics; O(log λ) bound, derivative, and monotonicity remain'),
}


def main():
    text = (ROOT / TEX).read_text()
    # Ignore commented-out text while preserving the original line numbers.
    text = re.sub(r"(?<!\\)%[^\n]*", "", text)
    labels = list(re.finditer(r"\\label\{(sublemma:[^}]+)\}", text))
    found = {m[1] for m in labels}
    if len(found) != len(labels) or not set(COVERAGE) <= found:
        raise SystemExit("Duplicate labels or stale coverage mapping")
    lines = [
        "# Blueprint correspondence", "",
        f"The supplied TeX file contains **{len(labels)} distinct sublemma labels**. "
        "This index follows that file, even though the preparatory note describes a version with 176 sublemmas.", "",
        "This table does not equate Lean declarations with manuscript sublemmas: "
        "some Lean proofs are auxiliaries, and some sublemmas have several conclusions, "
        "only part of which has been formalized. "
        "The original estimates needed for thm_main are now constructed; A002 and A004 collect "
        "the documented classical interfaces. Entries not individually formalized do not represent "
        "hundreds of fictitious independent `sorry` placeholders.", "",
        "Generate with `python3 scripts/blueprint_index.py`. "
        "Exact logical status of the code: [STATUS.md](STATUS.md).", "",
        "| Source reference | Current coverage | Correspondence / remaining work |",
        "|---|---|---|",
    ]
    for match in labels:
        label = match[1]
        line = text.count("\n", 0, match.start()) + 1
        status, note = COVERAGE.get(label, (
            "Not yet individually formalized",
            "Substatement not formalized separately; check the sufficient variant used for thm_main and the classical interfaces"))
        lines.append(f"| [`{label}`](../{TEX}#L{line}) | {status} | {note} |")
    (ROOT / "docs" / "BLUEPRINT_INDEX.md").write_text("\n".join(lines) + "\n")
    print(f"Indexed {len(labels)} blueprint sublemmas")


if __name__ == "__main__":
    main()
