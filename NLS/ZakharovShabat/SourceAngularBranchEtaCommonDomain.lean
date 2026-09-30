import NLS.ZakharovShabat.SourceAngularBranchEtaTerminal
import NLS.ZakharovShabat.SourceAngularEtaLocalCommonDomain

/-! # Complex branch eta primitives on one actual source neighborhood

Every complex open gap on a common neighborhood has a constructed
jointly analytic endpoint-normalized primitive chart. Every complex
periodic Dirichlet terminal there has an analytic eta source value.
The original psi extension and all beta results are retained. Regular
terminal coverage beyond these angle charts and eta gluing modulo pi
remain separate requirements.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exists_sourceAngular_branch_eta_common_domain
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ B W : Set (CoeffPair p), IsOpen W₀ ∧ IsSimplyConnected W₀ ∧
      realTypeSourceLocus p ⊆ W₀ ∧ IsOpen B ∧ realTypeSourceLocus p ⊆ B ∧ B ⊆ W₀ ∧
      IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ B ∧
      ∃ s : (k : ℤ) → CoeffPair p → DeletedCoeff p k,
        SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s ∧
        ∀ φ ∈ W, ∀ m : ℤ, canonicalPeriodicGap hp hp1
          (periodOnePotential φ) (periodOnePotential_mem φ) m ≠ 0 →
          ∃ V : Set (CoeffPair p), ∃ Ω : Set ℂ, ∃ δ : CoeffPair p → ℂ,
            ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ, φ ∈ V ∧
              δ φ = canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m / 2 ∧
              SourceAngularBranchCosineChartData hp hp1 m s δ W V Ω c R ∧
              (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m ∈
                ({canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m,
                  canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m} : Set ℂ) →
                ∃ U : Set (CoeffPair p), ∃ ε : CoeffPair p → ℂ, φ ∈ U ∧
                  (ε φ = 0 ∨ ε φ = (Real.pi : ℂ)) ∧
                  SourceAngularBranchEtaTerminalData hp hp1 m s δ V U Ω ε) := by
  classical
  obtain ⟨W₀,B,hW₀,hW₀conn,hW₀real,hB,hBreal,hBW₀,s,D⟩ :=
    exists_sourceAngularEta_local_common_domain hp hp1
  obtain ⟨A,hA,_,hAreal,hprod⟩ := exists_global_source_analytic_omittedJointProduct hp hp1
  let O₀ := B ∩ A
  have hO₀ : IsOpen O₀ := hB.inter hA
  have hO₀real : realTypeSourceLocus p ⊆ O₀ := fun φ hφ => ⟨hBreal hφ,hAreal hφ⟩
  have hlocal (φ : realTypeSourceLocus p) :=
    D.psi.toSourcePsiIsolatingComplexExtension.exists_local_angular_dirichlet_disc_family
      φ O₀ hO₀ (hO₀real φ.property)
  choose ρ hρ hball c R hfamily using hlocal
  let W := ⋃ φ : realTypeSourceLocus p, ball φ.val (ρ φ)
  have hW : IsOpen W := isOpen_iUnion (fun _ => isOpen_ball)
  have hWreal : realTypeSourceLocus p ⊆ W := by
    intro φ hφ
    exact mem_iUnion.mpr ⟨⟨φ,hφ⟩,mem_ball_self (hρ ⟨φ,hφ⟩)⟩
  have hWO₀ : W ⊆ O₀ := by
    intro ψ hψ
    obtain ⟨φ,hψball⟩ := mem_iUnion.mp hψ
    exact hball φ hψball
  have hWB : W ⊆ B := hWO₀.trans inter_subset_left
  have hWA : W ⊆ A := hWO₀.trans inter_subset_right
  have heq (m : ℤ) : sourceStandardRootOmittedJointDomain hp hp1 W m =
      sourceStandardRootOmittedJointDomain hp hp1 A m ∩ (univ ×ˢ W) := by
    ext t
    exact ⟨fun ht => ⟨⟨hWA ht.1,ht.2⟩,mem_univ _,ht.1⟩,
      fun ht => ⟨ht.2.2,ht.1.2⟩⟩
  have hDom (m : ℤ) : IsOpen (sourceStandardRootOmittedJointDomain hp hp1 W m) := by
    rw [heq m]
    exact (hprod m).1.inter (isOpen_univ.prod hW)
  have hP (m : ℤ) : AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 m)
      (sourceStandardRootOmittedJointDomain hp hp1 W m) :=
    (hprod m).2.1.mono (fun t ht => ⟨hWA ht.1,ht.2⟩)
  refine ⟨W₀,B,W,hW₀,hW₀conn,hW₀real,hB,hBreal,hBW₀,hW,hWreal,hWB,s,D,?_⟩
  intro φ hφ m hgap
  obtain ⟨χ,hφball⟩ := mem_iUnion.mp hφ
  let O := ball χ.val (ρ χ) ∩ W
  have hO : IsOpen O := isOpen_ball.inter hW
  have hOW : O ⊆ W := inter_subset_right
  have hφO : φ ∈ O := ⟨hφball,hφ⟩
  have hτ : AnalyticOnNhd ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m) O :=
    fun ψ hψ => (D.symmetric_analytic ψ (hWB hψ.2) m).1
  obtain ⟨V,Ω,δ,hφV,hbase,C⟩ :=
    D.psi.toSourcePsiIsolatingComplexExtension.exists_local_branch_cosine_angular_primitives
      W O hW (hWB.trans hBW₀) hO hOW (c χ) (R χ) (fun ψ hψ => hfamily χ ψ hψ.1)
      m hτ φ hφO (D.symmetric_analytic φ (hWB hφ) m).2 hgap (hDom m) (hP m)
  refine ⟨V,Ω,δ,c χ,R χ,hφV,hbase,C,?_⟩
  intro hend
  apply C.exists_local_analytic_endpoint_eta φ hφV (D.roots_analytic .dirichlet m φ (hWB hφ))
  rw [sourcePeriodicEndpoint_pair_eq_of_halfGap_sq hp hp1 φ m (δ φ) (C.halfGap_sq φ hφV)]
  exact hend

end NLS.ZakharovShabat
