import NLS.ZakharovShabat.SourceAngularEtaCosineRepresentative
import NLS.ZakharovShabat.SourceAngularBetaTheorem13_1Series

/-!
# Local diagonal eta representatives on the common angular domain

The actual normalized psi extension, all of Theorem 13.1(i) and (iii),
and the terminal-normalized analytic diagonal cosine representatives
coexist on one common complex neighborhood of the whole real locus.
Every open real gap has a constructed local representative, including
either periodic Dirichlet terminal. The source chart is a neighborhood
in the full complex Banach space. Identification and gluing of general
admissible spectral-path values modulo pi are still required for (ii).
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Restrict the actual beta series data to any open subdomain. -/
theorem SourceAngularBetaSeriesData.mono
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W U : Set (CoeffPair p)}
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
    (D : SourceAngularBetaSeriesData hp hp1 W s) (hU : IsOpen U) (hUW : U ⊆ W) :
    SourceAngularBetaSeriesData hp hp1 U s := by
  refine ⟨⟨(fun ψ hψ => D.summable_norm ψ (hUW hψ)),?_,
    (fun n => (D.analytic_correction n).mono hUW)⟩,
    (fun ψ hψ => D.absolute_decay ψ (hUW hψ)),
    (fun ψ hψ => D.correction_decay ψ (hUW hψ))⟩
  intro φ hφ
  obtain ⟨V,hV,hφV,_,hconv⟩ := D.locally_uniform φ (hUW hφ)
  exact ⟨V ∩ U,hV.inter hU,⟨hφV,hφ⟩,inter_subset_right,
    fun n => (hconv n).mono inter_subset_left⟩

/-- One actual cosine chart and its analytic moving Dirichlet terminal.
All parameters are explicit, while the fields record their proved
geometry, sheet normalization, and source analyticity. -/
structure SourceAngularEtaCosineSourceChartData
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (W V U : Set (CoeffPair p)) (Ω : Set ℂ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (ε : CoeffPair p → ℂ) (κ : ℂ) : Prop where
  chart : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R
  source_open : IsOpen U
  source_subset : U ⊆ V
  sign : κ = 1 ∨ κ = -1
  angle_analytic : AnalyticOnNhd ℂ ε U
  terminal_coordinates : ∀ ψ ∈ U, ε ψ ∈ Ω ∧
    sourceCanonicalCosinePoint hp hp1 m (ε ψ,ψ) = canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∧
    Complex.sin (ε ψ) = κ * sourceAngularDirichletSine hp hp1 m ψ
  terminal_root : ∀ ψ ∈ U, sourceAngularCosineLiftedRoot hp hp1 m κ (ε ψ,ψ) =
    sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)
  eta_analytic : AnalyticOnNhd ℂ
    (fun ψ => sourceAngularEtaCosineRepresentative hp hp1 m s κ (ε ψ,ψ)) U

/-- All established angular data on one source domain. The eta field
asserts constructed local analytic cosine representatives near open
real gaps; it does not assert spectral-path independence modulo pi. -/
structure SourceAngularEtaLocalCommonDomainData
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W₀ W : Set (CoeffPair p))
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) : Prop where
  psi : SourcePsiSquaredGapComplexExtension hp hp1 W₀ s
  roots_analytic : ∀ b : BoundaryCondition, ∀ m : ℤ,
    AnalyticOnNhd ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ m) W
  boundary_analytic : ∀ b : BoundaryCondition,
    AnalyticOnNhd ℂ (sourceBoundaryDisplacement hp hp1 b) W
  symmetric_analytic : ∀ ψ ∈ W, ∀ m : ℤ,
    AnalyticAt ℂ (fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential χ) (periodOnePotential_mem χ) m) ψ ∧
    AnalyticAt ℂ (fun χ : CoeffPair p => (canonicalPeriodicGap hp hp1
      (periodOnePotential χ) (periodOnePotential_mem χ) m)^2) ψ
  beta_values : ∀ ψ ∈ W, ∀ n m : ℤ, m ≠ n →
    sourceAngularBeta hp hp1 n m s ψ ∈ sourceAngularBetaValues hp hp1 n m s ψ ∧
      ∀ b ∈ sourceAngularBetaValues hp hp1 n m s ψ, b = sourceAngularBeta hp hp1 n m s ψ
  beta_analytic : ∀ n m : ℤ, m ≠ n → AnalyticOnNhd ℂ (sourceAngularBeta hp hp1 n m s) W
  beta_bound : ∀ φ ∈ W, ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
    ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ U, ∀ n m : ℤ, m ≠ n →
      ‖sourceAngularBeta hp hp1 n m s ψ‖ ≤ C *
        (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ +
          ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m -
            sourceStandardRootMidpoint hp hp1 ψ m‖) / |((n-m : ℤ) : ℝ)|
  beta_series : SourceAngularBetaSeriesData hp hp1 W s
  eta_local_real : ∀ φ : realTypeSourceLocus p, ∀ m : ℤ,
    canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0 →
    ∃ V U : Set (CoeffPair p), ∃ Ω : Set ℂ, ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      ∃ ε : CoeffPair p → ℂ, ∃ κ : ℂ, φ.val ∈ U ∧
        ε φ.val ∈ segment ℝ (0 : ℂ) (Real.pi : ℂ) ∧
        SourceAngularEtaCosineSourceChartData hp hp1 m s W V U Ω c R ε κ

/-- The full beta theorem and the actual local diagonal cosine
representatives hold for the same normalized psi family on one open
complex neighborhood of every real source. -/
theorem exists_sourceAngularEta_local_common_domain
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W : Set (CoeffPair p), IsOpen W₀ ∧ IsSimplyConnected W₀ ∧
      realTypeSourceLocus p ⊆ W₀ ∧ IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ W₀ ∧
      ∃ s : (k : ℤ) → CoeffPair p → DeletedCoeff p k,
        SourceAngularEtaLocalCommonDomainData hp hp1 W₀ W s := by
  obtain ⟨W₀,B,hW₀,hW₀conn,hW₀real,hB,hBreal,hBW₀,s,hs,hroots,hboundary,hsym,hvalues,hbeta,hbound,D⟩ :=
    exists_sourceAngularBeta_theorem13_1_i_iii hp hp1
  obtain ⟨A,hA,_,hAreal,hprod⟩ := exists_global_source_analytic_omittedJointProduct hp hp1
  let W := B ∩ A
  have hW : IsOpen W := hB.inter hA
  have hWreal : realTypeSourceLocus p ⊆ W := fun φ hφ => ⟨hBreal hφ,hAreal hφ⟩
  have hWB : W ⊆ B := inter_subset_left
  have hWW₀ : W ⊆ W₀ := hWB.trans hBW₀
  refine ⟨W₀,W,hW₀,hW₀conn,hW₀real,hW,hWreal,hWW₀,s,⟨hs,
    (fun b m => (hroots b m).mono hWB),(fun b => (hboundary b).mono hWB),
    (fun ψ hψ => hsym ψ (hWB hψ)),(fun ψ hψ => hvalues ψ (hWB hψ)),
    (fun n m hmn => (hbeta n m hmn).mono hWB),?_,D.mono hW hWB,?_⟩⟩
  · intro φ hφ
    obtain ⟨U,hU,hφU,_,C,hC,hest⟩ := hbound φ (hWB hφ)
    exact ⟨U ∩ W,hU.inter hW,⟨hφU,hφ⟩,inter_subset_right,C,hC,
      fun ψ hψ => hest ψ hψ.1⟩
  · intro φ m hgap
    have hsub : sourceStandardRootOmittedJointDomain hp hp1 W m ⊆
        sourceStandardRootOmittedJointDomain hp hp1 A m := fun t ht => ⟨ht.1.2,ht.2⟩
    have heq : sourceStandardRootOmittedJointDomain hp hp1 W m =
        sourceStandardRootOmittedJointDomain hp hp1 A m ∩ (univ ×ˢ B) := by
      ext t
      exact ⟨fun ht => ⟨⟨ht.1.2,ht.2⟩,mem_univ _,ht.1.1⟩,
        fun ht => ⟨⟨ht.2.2,ht.1.1⟩,ht.1.2⟩⟩
    have hD : IsOpen (sourceStandardRootOmittedJointDomain hp hp1 W m) := by
      rw [heq]
      exact (hprod m).1.inter (isOpen_univ.prod hB)
    obtain ⟨V,Ω,c,R,hφV,C⟩ :=
      hs.toSourcePsiIsolatingComplexExtension.exists_local_canonical_cosine_angular_primitives
        W hW hWW₀ φ.val (hWreal φ.property) φ.property m hgap hD ((hprod m).2.1.mono hsub)
    obtain ⟨U,hU,hφU,hUV,ε,κ,hκ,hε,he,hterminal,hη⟩ :=
      C.exists_local_analytic_real_eta_cosine_representative φ.val hφV φ.property
    exact ⟨V,U,Ω,c,R,ε,κ,hφU,he,⟨C,hU,hUV,hκ,hε,
      (fun ψ hψ => ⟨(hterminal ψ hψ).1,(hterminal ψ hψ).2.1,(hterminal ψ hψ).2.2.1⟩),
      (fun ψ hψ => (hterminal ψ hψ).2.2.2),hη⟩⟩

end NLS.ZakharovShabat
