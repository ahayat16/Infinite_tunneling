# Dependency graph

The [full DOT graph](dependencies.dot) is extracted from actual references in Lean types and proofs. The [inventory](STATUS.md) and [JSON data](declarations.json) record statuses, files, and axioms.

This summary distinguishes proved code from the work needed to complete the concrete-potential proof. Dotted arrows indicate further steps, not already verified deductions. A proved conditional result does not certify existence of its inputs.

```mermaid
flowchart TD
  P["Explicit formula: core + two cusps"]:::definition
  V["C∞, compact support, nonradiality, unique minimum"]:::proved
  EX["Explicit admissible elementary parameters"]:::proved
  J["Action: unique minimum, derivatives, convexity"]:::proved
  K["Positive Landau integral; uniform exponential rate"]:::proved
  RKE["Integral kernel: two radial derivatives, time FTC, exact ODE"]:::proved
  RKL["Integral kernel: exterior radial L² by r⁻³ domination"]:::proved
  RCE["Radial ODE + L² → finite derivative energy by Caccioppoli"]:::proved
  RWU["Wronskian → unique real L² branch, proportional to K"]:::proved
  RMR["Actual radial Hamiltonian calculation at x≠0"]:::proved
  RPL["Planar L² → radial integrability of r f² by polar coordinates"]:::proved
  RCS["Actual positive radial ground state: φcore=ΓK, Γ>0, modulo A004"]:::classical
  RPF["Full ODE + mass → decreasing profile and f≥c on [0,h]"]:::proved
  RWC["Ordered Wronskian → f≤ΓK on all r>0, same coefficient"]:::proved
  RGN["Radial data + realization → Γ≥c h² and Γ⁻¹≤C h⁻²"]:::proved
  RGH["b>0, r₀>0 → actual core normalization, modulo A002+A004"]:::classical
  RCV["Continuous convolution outside support; a.e. → pointwise equality"]:::proved
  RCI["A003 contract + actual source → exact polar formula for the same Γ"]:::proved
  LP0["Uniform Laplace tails and prefactor on positive real compact sets"]:::proved
  CK["Complex-radius kernel: convergence, real agreement, exact majorant"]:::proved
  CLP["Complex kernel: uniform relative asymptotic on h^(3/4)"]:::proved
  LP["Holomorphy of actual kernel and three compositions on a common bidisc"]:::proved
  CKP["Relative profiles at three chart radii; negligible phase remainder/h"]:::proved
  SEP["Uniform choice of L₀; seven margins on entire supports"]:::proved
  KB["Uniform exponential kernel bounds on cells"]:::proved
  INT["Absolute convergence of all nine concrete cells"]:::proved
  A3["A003: referenced classical free resolvent"]:::admitted
  COV["Magnetic covariance and right-state equation"]:::proved
  RES["Classical resolvent + atomic state → right representation"]:::proved
  ID["Resolvent equation → exact hopping identity"]:::proved
  AT["Literal B.1 / harmonic convergence: outside retained variant, unproved"]:::open
  SRC["Exact incoming cell: sign, amplitude, phase, and o(1) remainder"]:::proved
  LF["Real log-flat integral: two bounds and uniform logarithmic rate"]:::proved
  CJ["Cusp chart: Jacobian t² and exact integral reduction"]:::proved
  CG["Complex radii: bidisc, analyticity, slopes 1/2, uniform quadratic remainders"]:::proved
  W["Complex root: existence, uniform asymptotic, holomorphy"]:::proved
  PH["Exact critical value, Hessian, and phase difference"]:::proved
  CL["Horizontal integral: nonzero complex Gaussian leading term"]:::proved
  CT["Logarithmic substitution and exact contour shift"]:::proved
  CE["Connector and left tail: exponential errors absorbed"]:::proved
  LN["Normal integral with p.χa: nonzero complex asymptotic, fixed parameters"]:::proved
  PG["Leading-term phase: continuity and sublinear growth"]:::proved
  CA["Normalized absolute bound on the product of restricted contours"]:::proved
  TW["h^(3/4) window: negligible tails and contours, h^(-N) factors absorbed"]:::proved
  CW["Window in the bidisc and χa=1 region of the actual potential"]:::proved
  F0["Core source: L¹ bound C h⁻²"]:::proved
  I00["Actual core–core cell: absolute exponential bound"]:::proved
  INV["Radial data → exact-weight inverse, norm ≤12/(γλ), E≤Ecore"]:::proved
  CWT["Exact Lipschitz cusp weight, smooth approximations with uniform gradient"]:::proved
  CWG["Weighted test identity → closed graph → strong limit at exact weight"]:::proved
  CWP["Exponential weighted defect and residual, exact compressed lifting, controlled projection"]:::proved
  RCHOICE["Test gap → core simplicity → same positive radial choice with gap"]:::proved
  WRESP["Same reference and Schur: response equation, 12cλ/γ bound by actual weighted forcing"]:::proved
  WRES["Actual weighted residual ≤Kλexp(−dλ), κ₀ fixed before λ"]:::proved
  WDEC["Same state before κ: weighted correction ≤Cexp(−dλ), c∈[1/2,1]"]:::proved
  WPDE["Same certified vector → actual smooth representatives and pointwise response PDE"]:::proved
  WPHY["Same positive φcore and ψfull: smooth decomposition, orthogonality, weighted mass, PDE"]:::proved
  KEX["Real kernel: K≤C h⁻²exp(−J/h), uniform exact action"]:::proved
  CGAIN["Real supports: radial gain t/8, weight leaving t/16"]:::proved
  RECORE["Radial data + core realization → kernel energy in [1/2,1]"]:::proved
  WFORCE["Exact tail → actual undifferentiated forcing ≤CΓh⁻²exp(−J/h−β₁log²(1/h))"]:::proved
  DFLAT["Strict margin: all actual cusp jets retain β₂<β"]:::proved
  DKERNEL["Cauchy on a radius-h disc: all radial jets with exact action"]:::proved
  DSPAT["Radial composition → spatial jets; germs → same tail ΓK"]:::proved
  DFORCE["Leibniz + weighted gain → hⁿDⁿ(Wφ), fine pointwise bound"]:::proved
  DFL2["Fixed support → actual jets MemLp and fine mass, weight after differentiation"]:::proved
  DRAD["Radial data + realization: same φcore, energy, Γ for j≤n; L² sums"]:::proved
  DCLASS["BasicConditions → actual states and forcing jets, via A002+A004"]:::classical
  WLOCAL["Weight on dist≤ρh: ratio bounded independently of h"]:::proved
  WFINE["Same correction: ≤CcΓh⁻³exp(−J/h−β₁log²(1/h)), c∈[1/2,1]"]:::proved
  WFPHY["Actual wavefunctions: fine mass, same Γ, orthogonality, PDE"]:::proved
  EFORCE["Same certificate: semiclassical shift ≤3‖exp(κλT)Wφcore‖"]:::proved
  RUP["Unit mass + decreasing profile → φ(r)≤1/(√π r), then exponential upper bound on same Γ"]:::proved
  RWD["Action gap on annulus → all weighted radial jets ≤Ce⁻ᵈλ, without Γ"]:::proved
  CU["Supports in U′⊂⊂U; closedBall(x₀,2h)⊆U uniformly"]:::proved
  FD["Actual f_h=−cWφ+cδφ: all weighted jets ≤CcΓλ²exp(−λJ−β₁log²λ)"]:::proved
  FDP["Same wavefunctions: semiclassical PDE, fine η mass, local f_h norms"]:::proved
  FDC["BasicConditions → full PDE data, via A002+A004"]:::classical
  AFF["Change x=x₀+hy: jets h^j, measure h², exact magnetic equation"]:::proved
  ECO["Actual smooth potential on compact set → uniform rescaled coefficient jets"]:::proved
  A5["A005: referenced classical fixed-ball elliptic estimate"]:::admitted
  ELOC["Fixed contract + rescaling + weight → weighted jets ≤Cλ(U+F)"]:::proved
  ELL["Full data + interior → same η jets ≤CcΓλ⁴exp(−λJ−β₁log²λ)"]:::proved
  EPUB["BasicConditions → actual corrected-state jets, via A002+A004+A005"]:::classical
  SLE["Weighted Leibniz: common constant through n, weight after differentiation"]:::proved
  SGERM["Existing sources: germs and jets on each closed support, exact λ²ε"]:::proved
  SCP["Weighted η jets × cusp → source with local log-flat profile"]:::proved
  SCF["Same φcore,ψfull,c,Γ: scattered source λ⁶, separate local and global costs"]:::proved
  SCLASS["BasicConditions → actual scattered source, via A002+A004+A005"]:::classical
  INC["Tail ΓK + jets: incoming source ≤CcΓλ^(n+4) logFlat βin t exp(−λ(J+t/8))"]:::proved
  SPRO["Same actual states and Γ: simultaneous incoming/scattered profiles on both cusps"]:::proved
  SPCLASS["BasicConditions → simultaneous physical profiles, via A002+A004+A005"]:::classical
  RMEAS["Real reflection: isometry, measure preservation, support exchange"]:::proved
  L1CH["Cusp profile → actual L¹ norm: t² moment, factor 2s₀, uniform threshold"]:::proved
  L1SEP["Same φ,ψ,c,Γ: incoming/scattered norms, costs βin and βglobal+βlocal"]:::proved
  L1FULL["Same ψ: three integrable sources, core Cλ² and cusp sum CΓλ⁶exp(−λJ−β₁log²λ)"]:::proved
  L1PUB["BasicConditions → physical L¹ norms, via A002+A004+A005"]:::classical
  SPHASE["Unit phase: canonical sources, pairings, and cells unchanged"]:::proved
  IABS["Seven cells: absolute bound K(Γ²+1)λ¹⁰exp(−λ(Aref+31δhop))"]:::proved
  IPHYS["Same physical states and Γ, correct energies; seven canonical bounds too"]:::proved
  IPUB["BasicConditions → seven physical bounds, via A002+A004+A005"]:::classical
  NRATIO["Same Γ: (Γ²+1)/(c²Γ²)≤4Dλ⁴ for c≥1/2"]:::proved
  SNORM["Scalar saddle size: inverse square and polynomial losses absorbed by exp(−a/h)"]:::proved
  STEX["Re w / 1+w prefactors: ratio of squares →1, uniform comparison by 2"]:::proved
  ENVS["Explicit positive envelopes: limiting slope, moving action, λ⁶√λ"]:::proved
  IRELH["BasicConditions → seven physical relative bounds and sum of norms, via A002+A004+A005"]:::classical
  RGU["Simplicity + positivity: unique radial state and exterior coefficient"]:::proved
  IUNIV["Relative canonical bounds for any positive radial state, its Γ, and any c≥1/2"]:::proved
  INEX["Exact incoming sources in charts: three core/core/full kernels and phase"]:::proved
  INCO["Incoming cell: exact integral change, Jacobians t²u² and −h²"]:::proved
  XPAIR["Active bridge: exact action and pairing bounded by product of L¹ norms"]:::proved
  XLOG["Three scattered pairings: logarithmic costs 3β₀ and 4β₀"]:::proved
  SHARP["Inverse squared saddle size: coefficient 2β and any polynomial loss"]:::proved
  XADD["Actual cells: mixed integrability and exact four-term decomposition"]:::proved
  XREL["Full active cell minus incoming ≤C envelopeTex exp(−δβ log²λ)"]:::proved
  XPUB["BasicConditions + R<2L: physical/canonical reduction, δβ=β/8, via A002+A004+A005"]:::classical
  EFRZ["Actual energies 1+O(h); frozen slope, moving action retained"]:::proved
  IPROF["Actual three-kernel product and phase: uniform profile 1+o(1)"]:::proved
  FHOL["Normalized profile jointly holomorphic on common bidisc"]:::proved
  FCONT["Physical density: Fubini and integrability of every normal fiber"]:::proved
  NDEN["Normalized density = two log-flat models × actual profile, exact identity"]:::proved
  SPERR["Actual saddle multiplier: integrability and normalized o(1) error"]:::proved
  CPMULT["Cauchy on half-strip: exact deformation with bounded local amplitude"]:::proved
  CLEF["Multiplied connector: exp(−c h^(−1/4)) gain, negligible after normalization"]:::proved
  TC["Positive tangential mass; relative moving coefficient →1"]:::proved
  RBOX["Actual density on full rectangle: exact action, h⁻⁶, gain (t+u)/8"]:::proved
  PTRUNC["Negligible physical real truncation after N² and actual normalizer"]:::proved
  LCHANGE["Cutoff =1 then two exact substitutions; factor tStar⁶"]:::proved
  DRAY["Two physical Cauchy shifts: integrable hybrids and normalized o(1) error"]:::proved
  PCENTER["Measure-preserving translation to centered saddle domain"]:::proved
  SLEAD["Actual product on truncated saddle: normalized limit π/β, uniform in s,r"]:::proved
  NLEAD["Full physical normal integral: uniform asymptotic at actual energies"]:::proved
  TINT["Physical Fubini and tangential error ≤δ(2s₀)²"]:::proved
  ILEAD["Full physical integral: N² Z_h I→tStar⁶(π/β)Bs², relative ratio→1"]:::proved
  IMS0["Pointwise magnetic IMS and integrated IMS on tests"]:::proved
  CUT["Fixed real partition, separation, globally bounded IMS error"]:::proved
  OV["Orthogonality defect ≤exterior mass; mass controlled by energy"]:::proved
  RAD["A004: referenced classical harmonic approximation and positive radial choice"]:::admitted
  COER["Radial data → full-potential coercivity on tests"]:::proved
  IBP["Integration by parts: Hamiltonian = form on tests"]:::proved
  GRAPH["Linear test graph, closure, and L² representatives"]:::proved
  OCOER["Radial data → full-potential coercivity on operator domain"]:::proved
  PDOM["Bounded perturbation: equal core/potential domains, exact residual"]:::proved
  CINV["Coercive self-adjoint operator → positive bounded inverse"]:::proved
  ATRANS["Nonzero ground vector / dimension one → normalized smooth state / phase uniqueness"]:::proved
  EXT["Radial state + energy → exterior mass by graph closure"]:::proved
  COMP["Self-adjoint orthogonal compression on its actual domain"]:::proved
  SCHG["Complement coercivity + trial vector → simple ground state with gap"]:::proved
  ATOM["Radial data + realizations → simple full-potential ground state and gap"]:::proved
  RHYP["Radial core: compact C∞ profile, strict minimum, second derivative 2/r₀²"]:::proved
  EN["Radial data → energy −λ²+O(λ), kernel energy →1 and eventually [1/2,1]"]:::proved
  ASRC["BasicConditions + classical inputs → actual canonical state and source regime, threshold before L"]:::classical
  LOC["Compact-cutoff energy identity for actual eigenfunction"]:::proved
  WLOC["Local weighted inequality, integrability deduced"]:::proved
  AREG["Actual potential's exterior region: margin λ²/4; weight absorbed under gradient bound"]:::proved
  AWEIGHT["Bounded C∞ weight: 0 up to 3r₀, dλ from 4r₀, gradient²≤λ²/16"]:::proved
  ADCT["Cutoff removal by L² dominated convergence, without globally integrable energy"]:::proved
  ATAIL["Core and full potential: L² tail ≤(C/λ²)exp(−2dλ), E≤−3λ²/4"]:::proved
  AGROUND["Actual canonical ground state: exponential tail at large coupling, modulo A002+A004"]:::classical
  DOVR["Inversion: real overlap and masses of even/odd combinations"]:::proved
  DOVT["Partition of two exteriors: squared overlap ≤4 exterior mass"]:::proved
  DOVC["Radial data → canonical overlap ≤Cλ⁻¹exp(−dλ), uniform in L≥4r₀"]:::proved
  DOVH["BasicConditions → overlap decay and limit, via A002+A004"]:::classical
  DWRES["Actual translated atomic states: exact differential residuals λ² opposite potential × state"]:::proved
  DWDOM["Realizations + bounded perturbation → L² classes in double-well domain, exact residuals"]:::proved
  PWTR["Even/odd trials: C∞, L², unit masses, orthogonality under |s|<1"]:::proved
  PDTR["Normalized trials in double-well domain: unit norm and L² parity"]:::proved
  GSR1["Ground certificate → exact rank-one bound on actual domain"]:::proved
  ATR1["Actual full ground state: gap γλ for all tests, phase-invariant"]:::proved
  TRGAP["Magnetic covariance and inversion: same gap at both wells, threshold before L"]:::proved
  DWLOC["C∞ cutoffs: three squares, disjoint supports, 4r₀ plateaus, uniform IMS error"]:::proved
  LOV["Localized overlaps ≤2 global overlaps +2 tail × mass"]:::proved
  LFORM["Localized forms: one potential per well, nonnegative exterior"]:::proved
  IMS3["Two successive IMS steps: three exact masses and cost ≤2D"]:::proved
  DWABS["Tail C/λ² and fixed errors absorbed before λ and L"]:::proved
  DWTEST["Actual tests: rank-two defect and coefficient hRad.gap λ/4"]:::proved
  DWGRAPH["Two-overlap inequality closed on the actual graph"]:::proved
  DWCOER["Double-well domain: coercivity γλ on two-atom complement, uniform in L≥L₀"]:::proved
  DWCLASS["BasicConditions + separation → complement coercivity, via A002+A004"]:::classical
  L2INV["L² inversion: isometric involution and parity equations"]:::proved
  PARSEC["Closed sectors, invariant graph, actual self-adjoint parity restrictions"]:::proved
  PTRCOER["Each sector trial's complement: lower bound Eatom+γλ/4, threshold before L"]:::proved
  PTEST["Projection and closure of parity-test graph; nonemptiness and normalization"]:::proved
  PEID["Sector certificate → energy equals actual infimum parityEnergy"]:::proved
  PCERT["Sector certificate → eigenspace dimension one, gap, smooth normalized representative"]:::proved
  PSCH["Low trial + coercive complement → actual sector certificate by Schur"]:::proved
  PTRLOW["Actual trials: Rayleigh ≤Eatom+γλ/8, uniform in L≥L₀"]:::proved
  PHYQ["Actual trials: exact diagonal Eatom+(δ±Reρ)/(1±s), including canonical case"]:::proved
  PPHYS["Concrete potential: sector certificates at parityEnergy, gap ≥γλ/8; threshold before λ and L"]:::proved
  PFLOOR["Actual sector mode's complement: same absolute lower bound Eatom+γλ/4"]:::proved
  PDECOMP["Projections on actual domain: additive norm and energy, min/max lower bounds"]:::proved
  GLOBAL2["First two global min–max levels = min/max of sector bottoms"]:::proved
  GCLASS["BasicConditions + separation → global min–max levels, via A002+A004"]:::classical
  GSPACE["Exact one-/two-mode global eigenspaces, normalized physical representatives, gap"]:::proved
  SREAL["Constructed potential: TwoModeRealization and global gap, threshold before L"]:::proved
  SREALPUB["BasicConditions + separation → TwoModeRealization, SpectralRealization, gap, via A002+A004"]:::classical
  PSHIFT["Actual sector correction: 0≤a−E≤residual²/(γλ/8)"]:::proved
  QSCH["Schur correction, energy, normalization controlled by actual residual"]:::proved
  PRES["Concrete residual norm² ≤(2λ²εa)² × mass beyond 4r₀"]:::proved
  RDEC["Radial data → actual residual ≤Kλexp(−dλ)"]:::proved
  ACMP["Same certified root → exponential energy and actual L² vector comparison, fixed relative phase"]:::proved
  ACMPH["BasicConditions → atomic comparison, modulo A002+A004"]:::classical
  SADDLE["Complex saddle: active cell and positive envelope"]:::proved
  CAN["Same witnesses: actual construction of ChannelAsymptotics"]:::proved
  HOP["Channels + explicit classical resolvent: cosine of actual hopping"]:::proved
  HOPH["BasicConditions → ∃L₀∀L≥L₀: oscillatory hopping, modulo A002–A005"]:::classical
  INACT["Seven cells and sum of norms ≤C envelopeTex exp(−15δhop λ)"]:::proved
  CH["Nine cells → real cosine formula for hopping"]:::proved
  SCH["Exact algebraic Schur elimination"]:::proved
  UL1["Universal L¹ norms: same φcore, Γ, and any full ground state"]:::proved
  OSREC["A.e. opposite-support reconstruction: distinct actions G+J"]:::proved
  OSMASS["Fine opposite mass ≤C c²Γ²λ¹²exp(−2λ(G+J))"]:::proved
  OSENV["Margin J: λ¹⁵ majorant ≤C envelopeTex exp(−(2L−R)λ/4)"]:::proved
  ERR["Same W: diagonal defect and actual Schur corrections o(envelope)"]:::proved
  TR["Equations and component errors → splitting cosine"]:::proved
  PCLASS["BasicConditions + separation: sector certificates, via A002+A004"]:::classical
  PCONT["Parity energies and signedSplitting continuous on λ>0"]:::proved
  DILCMP["L² dilation + potential comparison + gap: states close modulo phase"]:::proved
  CONT["Radial data + realizations: canonical hopping continuous on λ≥T, threshold before L"]:::proved
  CONTC["BasicConditions → canonical hopping continuous on λ≥T, via A002+A004"]:::classical
  DATA["FixedAnalyticData: historical contract; concrete assembly via LocalAnalyticData"]:::definition
  OSC["Oscillation / IVT: two zero sequences and alternation"]:::proved
  ASM["of_analytic_data auxiliaries: conditional assembly"]:::proved
  A2["A002: referenced classical self-adjoint realization"]:::admitted
  OP["Transfer of eigenspaces and parity to L²"]:::proved
  MAINASM["ConstructedMainAssembly: actual modes, hopping, Schur, continuity"]:::proved
  MAINPROOF["ConstructedMainProof: all original data constructed"]:::proved
  ELEMMAIN["elementaryPotential_main: fixed elementaryParameters, via A002–A005"]:::classical
  TM["thm_main proved without direct sorry; only admissions A002–A005"]:::classical
  EN --> EFRZ
  CKP --> IPROF
  EFRZ --> IPROF
  IPROF --> FHOL
  LP --> FHOL
  INCO --> FCONT
  FCONT --> NDEN
  IPROF --> NDEN
  IPROF --> SPERR
  FHOL --> SPERR
  CA --> SPERR
  CT --> CPMULT
  CE --> CLEF
  P --> TC
  LP0 --> TC
  NDEN --> SRC
  SPERR --> SADDLE
  CPMULT --> SADDLE
  CLEF --> SADDLE
  FCONT --> SADDLE
  TC --> SADDLE
  KEX --> RBOX
  CGAIN --> RBOX
  FCONT --> RBOX
  RBOX --> PTRUNC
  TW --> PTRUNC
  EFRZ --> PTRUNC
  NDEN --> LCHANGE
  CW --> LCHANGE
  FHOL --> DRAY
  CPMULT --> DRAY
  CLEF --> DRAY
  DRAY --> PCENTER
  SPERR --> SLEAD
  TW --> SLEAD
  CL --> SLEAD
  PTRUNC --> NLEAD
  LCHANGE --> NLEAD
  DRAY --> NLEAD
  PCENTER --> NLEAD
  SLEAD --> NLEAD
  FCONT --> TINT
  TC --> TINT
  NLEAD --> ILEAD
  TINT --> ILEAD
  ILEAD --> SRC
  P --> V --> EX
  P --> RHYP
  RHYP --> RAD
  J --> K
  K --> RKE
  LP --> RKE
  K --> RKL
  RKE --> RWU
  RKL --> RWU
  RCE --> RWU
  RWU --> RCS
  RMR --> RCS
  RPL --> RCS
  RAD --> RCS
  RCS -.-> AT
  RMR --> RPF
  RPL --> RPF
  EXT --> RPF
  P --> RPF
  RPF --> RWC
  RCS --> RWC
  RKE --> RWC
  RWC --> RGN
  K --> RGN
  RAD --> RGN
  RGN --> RGH
  RAD --> RGH
  A2 --> RGH
  K --> RCV
  RCV --> RCI
  A3 --> RCI
  RCS --> RCI
  RGN --> SRC
  K --> LP0
  K --> CK
  CK --> LP
  CK --> CLP
  J --> CLP
  LP0 --> CLP
  TW --> CLP
  CLP --> CKP
  CG --> CKP
  TW --> CKP
  CG --> LP
  CKP --> SADDLE
  P --> SEP
  J --> SEP
  SEP --> KB
  K --> KB
  P --> INT
  K --> INT
  COV --> RES
  A3 --> RES
  ATOM --> RES
  RES --> ID
  INT --> ID
  P -.-> AT
  P --> CWT
  CWT --> CWG
  COER --> CWG
  GRAPH --> CWG
  CWG --> INV
  CWP --> INV
  CINV --> INV
  RAD --> RCHOICE
  GRAPH --> RCHOICE
  A2 --> RCHOICE
  RCHOICE --> INV
  INV --> WRESP
  QSCH --> WRESP
  PDOM --> WRESP
  RDEC --> WRES
  CWT --> WRES
  WRESP --> WDEC
  WRES --> WDEC
  QSCH --> WDEC
  WRESP --> WPDE
  A2 --> WPDE
  WDEC --> WPHY
  WPDE --> WPHY
  WPHY --> SRC
  K --> KEX
  P --> CGAIN
  CWT --> CGAIN
  J --> CGAIN
  RAD --> RECORE
  A2 --> RECORE
  RCS --> WFORCE
  RECORE --> WFORCE
  KEX --> WFORCE
  CGAIN --> WFORCE
  LF --> WFORCE
  P --> DFLAT
  LP --> DKERNEL
  CK --> DKERNEL
  KEX --> DKERNEL
  J --> DKERNEL
  DKERNEL --> DSPAT
  RCS --> DSPAT
  DFLAT --> DFORCE
  DSPAT --> DFORCE
  CGAIN --> DFORCE
  LF --> DFORCE
  DFORCE --> DFL2
  DFL2 --> DRAD
  RECORE --> DRAD
  RCS --> DRAD
  DRAD --> DCLASS
  A2 --> DCLASS
  RAD --> DCLASS
  DRAD --> SRC
  CWT --> WLOCAL
  WLOCAL --> SRC
  WFORCE --> WFINE
  WRESP --> WFINE
  WDEC --> WFINE
  WFINE --> WFPHY
  WPDE --> WFPHY
  QSCH --> EFORCE
  WDEC --> EFORCE
  WFPHY --> SRC
  EFORCE --> SRC
  RPF --> RUP
  RCS --> RUP
  K --> RUP
  RUP --> RWD
  DSPAT --> RWD
  RECORE --> RWD
  CWT --> RWD
  P --> CU
  DRAD --> FD
  RWD --> FD
  EFORCE --> FD
  WFINE --> FD
  FD --> FDP
  WPDE --> FDP
  CU --> FDP
  FDP --> FDC
  A2 --> FDC
  RAD --> FDC
  P --> ECO
  AFF --> ECO
  AFF --> ELOC
  ECO --> ELOC
  A5 --> ELOC
  FDP --> ELL
  WLOCAL --> ELOC
  CU --> ELOC
  ELOC --> ELL
  EN --> ELL
  ELL --> EPUB
  A2 --> EPUB
  RAD --> EPUB
  A5 --> EPUB
  P --> SGERM
  V --> SGERM
  DFLAT --> SCP
  SLE --> SCP
  SGERM --> SCP
  ELL --> SCF
  SCP --> SCF
  SCF --> SCLASS
  A2 --> SCLASS
  RAD --> SCLASS
  A5 --> SCLASS
  SCF --> SRC
  DSPAT --> INC
  DFLAT --> INC
  CGAIN --> INC
  SGERM --> INC
  SLE --> INC
  INC --> SPRO
  SCF --> SPRO
  RECORE --> SPRO
  SPRO --> SPCLASS
  A2 --> SPCLASS
  RAD --> SPCLASS
  A5 --> SPCLASS
  SPRO --> SRC
  CJ --> L1CH
  LF --> L1CH
  RMEAS --> L1CH
  SGERM --> L1SEP
  SPRO --> L1SEP
  L1CH --> L1SEP
  L1SEP --> L1FULL
  F0 --> L1FULL
  L1FULL --> L1PUB
  A2 --> L1PUB
  RAD --> L1PUB
  A5 --> L1PUB
  L1SEP --> XLOG
  KB --> IABS
  F0 --> IABS
  IABS --> IPHYS
  L1FULL --> IPHYS
  SPHASE --> IPHYS
  ATOM --> IPHYS
  RECORE --> IPHYS
  IPHYS --> IPUB
  A2 --> IPUB
  RAD --> IPUB
  A5 --> IPUB
  RGN --> NRATIO
  WDEC --> NRATIO
  PG --> SNORM
  TW --> SNORM
  IPHYS --> INACT
  NRATIO --> INACT
  SNORM --> ENVS
  PG --> STEX
  STEX --> ENVS
  ENVS --> INACT
  INACT --> IRELH
  A2 --> IRELH
  RAD --> IRELH
  A5 --> IRELH
  RCHOICE --> RGU
  RGU --> IUNIV
  INACT --> IUNIV
  RCS --> INEX
  CJ --> INEX
  INEX --> INCO
  CJ --> INCO
  INCO --> SADDLE
  KB --> XPAIR
  XPAIR --> XLOG
  PG --> SHARP
  TW --> SHARP
  SHARP --> XREL
  STEX --> XREL
  ENVS --> XREL
  XLOG --> XREL
  XADD --> XREL
  SPHASE --> XREL
  XREL --> XPUB
  A2 --> XPUB
  RAD --> XPUB
  A5 --> XPUB
  XREL --> SADDLE
  P --> CUT
  CUT --> OV
  CUT --> CWG
  RAD --> COER
  RAD --> EXT
  GRAPH --> EXT
  A2 --> EXT
  EXT --> COER
  CUT --> COER
  OV --> COER
  IMS0 --> COER
  COER --> OCOER
  IBP --> GRAPH
  GRAPH --> OCOER
  A2 --> OCOER
  OCOER --> ATOM
  GRAPH --> PDOM
  P --> PDOM
  PDOM --> ATOM
  CINV --> SCHG
  COMP --> SCHG
  SCHG --> ATOM
  GRAPH --> ATRANS
  A2 --> ATRANS
  ATRANS --> ATOM
  RAD --> ATOM
  A2 --> ATOM
  ATOM --> EN
  ATOM --> ASRC
  EN --> ASRC
  A3 --> ASRC
  RES --> ASRC
  INT --> ASRC
  IBP --> LOC
  LOC --> WLOC
  EN --> AREG
  P --> AREG
  WLOC --> AREG
  CUT --> AWEIGHT
  WLOC --> ADCT
  ADCT --> ATAIL
  AWEIGHT --> ATAIL
  AREG --> ATAIL
  ATAIL --> AGROUND
  ATOM --> AGROUND
  EN --> AGROUND
  COV --> DOVR
  COV --> DOVT
  DOVT --> DOVC
  AGROUND --> DOVC
  DOVC --> DOVH
  A2 --> DOVH
  RAD --> DOVH
  COV --> DWRES
  COV --> DWDOM
  GRAPH --> DWDOM
  A2 --> DWDOM
  DOVR --> PWTR
  PWTR --> PDTR
  DWDOM --> PDTR
  ATOM --> GSR1
  GSR1 --> ATR1
  GRAPH --> ATR1
  ATRANS --> ATR1
  ATR1 --> TRGAP
  COV --> TRGAP
  P --> DWLOC
  SEP --> DWLOC
  DWLOC --> LOV
  DOVT --> LOV
  DWLOC --> LFORM
  IMS0 --> IMS3
  DWLOC --> IMS3
  AGROUND --> DWABS
  EN --> DWABS
  TRGAP --> DWTEST
  LOV --> DWTEST
  LFORM --> DWTEST
  IMS3 --> DWTEST
  DWABS --> DWTEST
  GRAPH --> DWGRAPH
  DWGRAPH --> DWCOER
  DWTEST --> DWCOER
  A2 --> DWCOER
  DWCOER --> DWCLASS
  A2 --> DWCLASS
  RAD --> DWCLASS
  L2INV --> PARSEC
  A2 --> PARSEC
  PARSEC --> PTEST
  PTEST --> PEID
  PEID --> PCERT
  PARSEC --> PSCH
  COMP --> PSCH
  SCHG --> PSCH
  DWDOM --> PHYQ
  PWTR --> PHYQ
  PHYQ --> ERR
  PDTR --> PTRCOER
  DOVC --> PTRCOER
  DWCOER --> PTRCOER
  DWRES --> PTRLOW
  AGROUND --> PTRLOW
  DOVC --> PTRLOW
  PTRCOER --> PPHYS
  PTRLOW --> PPHYS
  PSCH --> PPHYS
  PCERT --> PPHYS
  PPHYS --> PFLOOR
  PTRCOER --> PFLOOR
  PPHYS --> PCLASS
  A2 --> PCLASS
  RAD --> PCLASS
  PTEST --> PCONT
  AGROUND --> DILCMP
  DILCMP --> CONT
  SPHASE --> CONT
  V --> CONT
  CONT --> CONTC
  A2 --> CONTC
  RAD --> CONTC
  PARSEC --> PDECOMP
  PPHYS --> PDECOMP
  PDECOMP --> GLOBAL2
  PFLOOR --> GLOBAL2
  PTEST --> GLOBAL2
  GLOBAL2 --> GCLASS
  A2 --> GCLASS
  RAD --> GCLASS
  PDECOMP --> GSPACE
  PPHYS --> GSPACE
  GLOBAL2 --> SREAL
  GSPACE --> SREAL
  SREAL --> SREALPUB
  A2 --> SREALPUB
  RAD --> SREALPUB
  SREAL --> MAINASM
  PTRCOER --> PSHIFT
  PTRLOW --> PSHIFT
  PSCH --> PSHIFT
  DWRES --> PSHIFT
  PSHIFT --> ERR
  DWRES --> OSMASS
  SCHG --> QSCH
  PDOM --> QSCH
  PDOM --> PRES
  AGROUND --> RDEC
  PRES --> RDEC
  RDEC --> ACMP
  RDEC --> CWP
  AGROUND --> CWP
  PDOM --> CWP
  COMP --> CWP
  QSCH --> ACMP
  OCOER --> ACMP
  PDOM --> ACMP
  ACMP --> ACMPH
  A2 --> ACMPH
  RAD --> ACMPH
  ACMP --> SRC
  INV --> SRC
  LP --> SRC
  SRC --> SADDLE
  LP --> SADDLE
  CLP --> SADDLE
  P --> LF
  P --> CJ
  LF --> CJ
  CJ --> SRC
  P --> CG
  CG --> SADDLE
  CG --> CW
  TW --> CW
  P --> CW
  CW --> SADDLE
  W --> PH
  PH --> CL
  W --> CE
  PH --> CE
  CL --> LN
  CL --> CA
  W --> PG
  PH --> PG
  CT --> LN
  CE --> LN
  P --> LN
  LN --> SADDLE
  CE --> TW
  LN --> TW
  TW --> SADDLE
  CA --> SADDLE
  PG --> SADDLE
  P --> F0
  F0 --> I00
  KB --> I00
  LF --> SRC
  SADDLE --> CAN
  INACT --> CAN
  XREL --> CAN
  CAN --> HOP
  ID --> HOP
  HOP --> HOPH
  A2 --> HOPH
  A3 --> HOPH
  RAD --> HOPH
  A5 --> HOPH
  SADDLE --> CH
  INACT --> CH
  ID --> CH
  L1FULL --> UL1
  RGN --> OSMASS
  UL1 --> OSMASS
  RES --> OSREC
  KB --> OSREC
  OSREC --> OSMASS
  OSMASS --> ERR
  OSENV --> ERR
  CAN --> ERR
  SCH --> ERR
  ERR --> TR
  CH --> TR
  CH --> MAINASM
  ERR --> MAINASM
  PCONT --> MAINASM
  CONT --> MAINASM
  TR --> OSC
  DATA --> ASM
  OSC --> ASM
  OP --> ASM
  OSC --> MAINASM
  OP --> MAINASM
  MAINASM --> MAINPROOF
  CAN --> MAINPROOF
  ERR --> MAINPROOF
  EX --> ELEMMAIN
  MAINPROOF --> ELEMMAIN
  A2 --> ELEMMAIN
  A3 --> ELEMMAIN
  RAD --> ELEMMAIN
  A5 --> ELEMMAIN
  ELEMMAIN --> TM
  classDef proved fill:#bce8ba,stroke:#367a35
  classDef definition fill:#c7dbef,stroke:#38658f
  classDef admitted fill:#f6aaaa,stroke:#aa3333
  classDef classical fill:#ffd18a,stroke:#a86c1d
  classDef open fill:#e5bbef,stroke:#824394
```

The remaining purple nodes concern stronger formulations or substatements unnecessary for the proved variant. `thm_main` now has a proof without a direct `sorry`, obtained from `elementaryPotential_main` for the literal `elementaryParameters`. Its four admitted classical inputs remain separately identified; no tunneling result is added to that list.

A002 concerns the [classical operator realization](CLASSICAL_OPERATOR_REALIZATION.md), A003 the [free resolvent kernel](CLASSICAL_LANDAU_RESOLVENT.md), A004 [harmonic approximation for the radial core alone](RADIAL_HARMONIC_CONTRACT.md), and A005 the [fixed-ball elliptic estimate](CLASSICAL_ELLIPTIC_INTERIOR.md). These four referenced admissions contain no tunneling estimate or nonradial-potential gap. The latter follows from the proved localization and Schur construction. The original obligations needed for the theorem are now assembled; their details and the limits of the variants used are in [ADMISSIONS.md](ADMISSIONS.md).

The connection to double-well trials now has separate proofs. [`ParityTrialStates`](../InfiniteZero/ParityTrialStates.lean) establishes reality of the overlap, exact masses `2(1±s)`, normalization, and orthogonality of even and odd trials. [`MagneticOverlapTail`](../InfiniteZero/MagneticOverlapTail.lean) bounds squared overlap by four times the radial exterior mass. [`CanonicalOverlapDecay`](../InfiniteZero/CanonicalOverlapDecay.lean) deduces `|sλ|≤C/λ exp(−dλ)`, with C,d,T chosen before all λ≥T and L≥4r₀. Both wrappers in [`ClassicalCanonicalOverlapDecay`](../InfiniteZero/ClassicalCanonicalOverlapDecay.lean) use exactly A002+A004; R<2L suffices for the zero limit since 8r₀<R. This is coarse exponential decay, without a fine action rate or a continuity hypothesis on the canonical-state choice.

[`DoubleWellResidual`](../InfiniteZero/DoubleWellResidual.lean) proves `(Hdouble−Eatom)φL=λ²vRφL` and its reflected identity, where Eatom is the same full well's energy, with no gauge error. [`DoubleWellTrialDomain`](../InfiniteZero/DoubleWellTrialDomain.lean) recovers these residuals in the actual L² domain by bounded perturbation under the displayed realizations. [`ParityTrialDomain`](../InfiniteZero/ParityTrialDomain.lean) also places the normalized trials there, with norm one and L² parity when |s|<1. These modules compile and are audited; the global check and export completed successfully.

[Coercivity on the complement of the two states](TWO_WELL_COERCIVITY.md) is now proved. `GroundStateRankOne`, `MagneticTestRankOne`, and `AtomicGroundRankOne` extract the exact full-ground-state gap from the certificate, then `MagneticTrialCovariance` and `TranslatedAtomicGap` transport it to both wells. `DoubleWellLocalizationCutoffs` constructs fixed cutoffs and bounds their errors; `LocalizedOverlap`, `MagneticLocalizedForm`, and `DoubleWellLocalizedEstimates` identify local forms and control both overlap losses. `MagneticIMSThree` and `DoubleWellCoercivityScalar` give the assembly `DoubleWellTestCoercivity`, then `MagneticGraphTwoModeLowerBound` transfers the same inequality to the actual domain in `DoubleWellOperatorCoercivity`. The coefficient is hRad.gap * λ / 4; the threshold precedes all L≥L₀, full ground states, and their L² representatives. The wrapper `ClassicalDoubleWellCoercivity.doubleWell_complement_coercivity` uses exactly A002+A004, without A003 or A005.

The [sector construction](PARITY_SPECTRAL_CONSTRUCTION.md) now extends this block. `L2ParitySectors` identifies `(I±J)/2` with orthogonal projections onto closed sectors. `DoubleWellInversionGraph` and `DoubleWellParityGraph` prove invariance of the actual graph; `ReducingSubspaceRestriction` then `DoubleWellParityOperator` give self-adjoint restrictions with exact domain and action. `ParityTrialL2`, `AtomicTranslatedOverlap`, and `ParityTrialCoercivity` retain the lower bound Eatom+γλ/4 on each trial's complement in its sector, with a common threshold before L.

`MagneticParityGraphLowerBound` projects the test graph before closure; `MagneticParityNormalization` handles normalization and nonemptiness. `ParityEnergyIdentification` then identifies a certified sector bottom with the actual test infimum `parityEnergy`. `ParityGroundCertificate` gives sector simplicity and smooth normalized representatives. `ParitySchurGroundConstruction` constructs such a certificate from a low trial and coercive complement in the actual restriction. `DoubleWellTrialResidualBound` and `ParityTrialEnergyBound` place actual trials below Eatom+γλ/8 using the atomic tail and uniform overlap. The physical assembly `DoubleWellParityGround` now compiles: certificates at `parityEnergy`, gap ≥γλ/8, and a threshold before λ and L. `EigenvectorComplementBound` preserves exactly the absolute lower bound Eatom+γλ/4 on the complements of actual modes in their sectors.

`ParityTrialRayleigh` now identifies the same trial's exact quotient: `a±=Eatom+(translatedDefect±Re(hopping))/(1±translatedOverlap)`. Diagonal integrals are identified by inversion, cross coefficients by actual residuals and symmetry, and normalization uses exact masses. The canonical version directly uses `canonicalDefect`, `canonicalOverlap`, and `canonicalHopping`. The result holds for every domain representative of the trial, without an asymptotic hypothesis or instantiated admission. At this milestone, the arrow toward relative errors was still dotted.

Trials remain distinct from reconstructed eigenvectors. `ParityOperatorDecomposition` proves decomposition of the actual domain and global lower bounds. `SecondEnergyParityUpper` uses two nearly minimizing tests of opposite parity; `SecondEnergyComplementLower` supplies a test orthogonal to the low mode in each two-dimensional space. `ParityGlobalMinmax` and `ConstructedGlobalMinmax` therefore identify the first two min–max levels with min/max; `doubleWell_global_minmax hp cert` instantiates A002+A004. These arrows are solid.

`ParityGroundEigenspaces` and `PhysicalParityModes` give the exact global eigenspaces and their normalized representatives; `ParityGlobalGroundGap` gives the gap even at crossings. `ParityDoubletRealization` then `ConstructedDoubleWellSpectral` assemble `TwoModeRealization`. `doubleWell_twoModeRealization hp cert` retains this package directly for `LocalChannelAnalyticData.modes`; `doubleWell_spectral_realization hp cert` deduces the spectral contract. Both supply the gap, with a threshold before L, via A002+A004.

`ParitySchurEnergyShift` and `ConstructedParitySchurEnergyBound` control the actual correction by residual²/(hRad.gap·λ/8). `PhysicalResidualMass` and `CanonicalParityCorrectionMass` reduce it to (32/hRad.gap)λ³ times the opposite-support mass. `AtomicOppositeSupportFineBounds` gives that mass with λ¹² and action 2(G+J); `CanonicalParityFineBound` therefore retains λ¹⁵. `OppositeSupportEnvelopeComparison` absorbs nine powers and the saddle cost into margin J, retaining exactly the same c,Γ. `CanonicalParityRelativeErrors` thus proves that the defect and corrections are o(A) for the same `ConcreteChannelWitnesses W` as the hopping. It does not assume the squared residual itself is o(A). See [OPPOSITE_SUPPORT_ESTIMATES.md](OPPOSITE_SUPPORT_ESTIMATES.md).
`ConstructedMainAssembly` combines these data with the actual modes and continuity results; `ConstructedMainProof` constructs the inputs. `elementaryPotential_main`, then `thm_main`, conclude for fixed parameters via A002–A005, with no direct `sorry` in either theorem.
`ClassicalDoubleWellParityGround.doubleWell_parityGrounds` instantiates exactly A002+A004 and keeps the threshold before λ and L. Its other two wrappers give [continuity by dilation](DILATION_AND_CONTINUITY.md) of `parityEnergy` and `signedSplitting` for every λ>0 at fixed admissible L. `MagneticDilationL2`, `UnitPhaseDistance`, then `AtomicGroundDilationComparison` compare actual ground states after dilation modulo a unit phase, with mass defect ≤C|λ−μ|. `HoppingContinuity` combines a bilinear bound with continuity of the integral at a fixed dilated reference: complex canonical hopping is continuous on `Ici T`, with a threshold before any separation L. This proof assumes no continuous phase choice. It retains hRad, hAcore, and hApot as arguments, and its targeted audit finds only standard axioms. The compiled wrapper `canonicalHopping_continuous hp`, in `ClassicalHoppingContinuity`, instantiates only A002+A004. At this milestone, the global audit of that stage was still in progress.

The [global Agmon proof](AGMON_DECAY.md), in [`MagneticAgmonBounded`](../InfiniteZero/MagneticAgmonBounded.lean), [`AtomicAgmonWeight`](../InfiniteZero/AtomicAgmonWeight.lean), and [`AtomicAgmonGlobal`](../InfiniteZero/AtomicAgmonGlobal.lean), gives an absolute tail with constants fixed before coupling. It does not give fine action rates, the weighted inverse, or source amplitudes. `SchurGroundEstimates`, `SchurResidualBounds`, and `SchurGroundQuantitative` supply quantitative controls retaining the certificate and correction from the same root. `AtomicGroundAgmon` applies the tail to actual ground states from radial data; `AtomicPerturbationTail` controls the concrete residual by exterior mass, without assuming residual decay. `AtomicResidualDecay` then `AtomicGroundComparison` now assemble exponential comparison of actual energies and normalized L² ground vectors, with positive real overlap. Wrappers in `Remaining` require only `BasicConditions`, modulo A002+A004. The [exact scope](ATOMIC_COMPARISON.md) excludes prescribed canonical phases, state continuity, and pointwise source amplitudes; no separate c_h→1 theorem is claimed.
The [weighted inverse](CUSP_WEIGHTED_INVERSE.md) is constructed separately for the exact Lipschitz weight, for E≤Ecore, with bound 12/(γλ) including the projection. This variant covers the full ground energy; it does not claim the TeX window above Ecore. The [weighted response](ATOMIC_WEIGHTED_RESPONSE.md) now uses the same resolvent and positive reference, whose gap is transferred by `RadialCoreGroundChoice`. `WeightedSchurCorrection` and `SchurResponseEquation` identify the actual correction and its domain equation. `AtomicGroundWeightedResponse` retains its bound by the effective forcing; `AtomicWeightedResidual` and `AtomicGroundWeightedDecay` give the first absolute exponential decay and c∈[1/2,1]. `AtomicResponseWavefunction` recovers actual smooth representatives and the pointwise PDE for exactly the same certificate. `AtomicGroundWeightedDecomposition` assembles these wavefunctions, orthogonality, and weighted mass of their difference. Constants precede coupling; states precede κ. These compiled connections require no further admission. At that milestone, arrows toward fine sources were still dotted.
The wrapper `CuspParameters.atomicGround_weighted_decomposition` requires only `BasicConditions` and supplies this decomposition via A002+A004; no free-resolvent representation A003 enters. The [fine assembly](CUSP_FINE_FORCING.md) now applies the same state's exact tail to the actual forcing: CΓh⁻²exp(−J/h−β₁log²(1/h)) for any 0<β₁<β. The same response retains cΓ, with polynomial cost h⁻³. `AtomicGroundFineDecomposition` preserves wavefunctions, orthogonality, the same tail coefficient, and PDE; its public wrapper depends only on A002 and A004, as the dependency export verifies. `AtomicEnergyShiftForcing` bounds the semiclassical shift by the single factor 3‖exp(κλT)Wφcore‖, using c≥1/2 and the scalar Schur equation.
The [full PDE data](ATOMIC_FINE_RESPONSE_DATA.md) are now controlled at every fixed order. An upper bound on the radial coefficient from normalized mass and the action gap give [weighted radial jets without Γ](RADIAL_WEIGHTED_JETS.md); the energy-shift term thus retains only one cΓ factor. The same assembly supplies the exact PDE, fine correction mass, and local L² masses and norms of all required right-hand-side jets on a fixed neighborhood. Its public wrapper `atomicGround_fine_response_data` uses only A002+A004. The [elliptic assembly](ATOMIC_RESPONSE_JETS.md) now controls jets of the same correction with prefactor cΓλ⁴, additionally via A005. Rescaling, uniform coefficients, and weight transport are proved separately. The [full scattered source](CUSP_SCATTERED_SOURCE.md) is now controlled for the same states: multiplication by λ²W retains both log-flat factors with polynomial cost λ⁶. Relative incoming profiles, the active integral, and its connection to hopping are now proved in the [channel assembly](ACTIVE_CHANNEL_ASYMPTOTIC.md).
Actual sector modes are constructed by Schur and identified with the first two global min–max levels; their corrections relative to the envelope are proved by the [opposite-support assembly](OPPOSITE_SUPPORT_ESTIMATES.md). The [local incoming bound and simultaneous assembly](CUSP_SOURCE_PROFILES.md) are proved: same cΓ, radial gain t/8, loss λ^(n+4), and the same states as for the scattered source. All three margins are independent; the extra threshold only fixes the core energy and scale needed for kernel jets.
The [L¹ norms](CUSP_SOURCE_L1.md) are now proved, with integrability of actual sources and identification with their L¹ classes. The chart change retains factor 2s₀ and Jacobian t²; reflection gives the same bound on the other cusp. Global and local costs of the scattered part add. The sum of full cusp components and the separate core bound are assembled for the same state. These bounds are applied to the seven inactive cells in `AtomicInactiveCells`, then compared with the envelope in `AtomicInactiveRelativeTex`.

The [exterior radial block](RADIAL_EXTERIOR_KERNEL.md) separately proves the integral kernel's ODE, radial L² property, and uniqueness of the real L² branch from the ODE alone. Derivatives have finite energy by Caccioppoli; this property is not a remaining input to final uniqueness. Application to the actual core state is now established: A004 supplies the classical positive radial choice, while differential reduction and the polar connection are proved in Lean. `CuspParameters.radialCore_kernel` concludes the exact exterior formula with Γ>0, modulo A004 alone. `RadialCoreProfileEstimates` proves profile decay and a uniform positive bound on [0,h]. `RadialCoreKernelComparison` compares the actual profile to the same ΓK on all r>0 through the Wronskian sign. `RadialCoreNormalizationLower` deduces Γ≥c h² and Γ⁻¹≤C h⁻², with constants before coupling, state, and coefficient. The wrapper `CuspParameters.radialCore_normalization_lower` supplies inputs via A002+A004 alone. This variant suffices for polynomial losses under strict exponential margins; B.1, the h^(3/2) power of B.2, and the harmonic limit are not claimed. The full `scripts/check.sh` check passed, including `Verification` and audit export.

The auxiliary identities `LandauExteriorConvolution`, `RadialCoreSourceRepresentation`, `RadialLandauAverage`, and `RadialCoreNormalization` give another branch: pointwise exterior representation and an exact polar coefficient formula, with explicit A003 for the physical representation. The Wronskian lower-bound proof does not use this branch. See [RADIAL_NORMALIZATION.md](RADIAL_NORMALIZATION.md).
