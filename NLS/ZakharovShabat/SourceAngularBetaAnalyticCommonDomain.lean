import NLS.ZakharovShabat.SourceAngularUniformAnnulusPrimitive

/-!
# Actual beta terms analytic on one common complex domain

Uniform distant annuli and finitely many central charts give one local
source neighborhood for every off-diagonal beta term. Their union over
the real locus is open and supports all terms at once. The actual beta
values and their uniqueness, both analytic boundary sequences, symmetric
periodic coordinates, and the full simply connected psi extension are
retained. The estimates and angular sum of Theorem 13.1 are separate.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourcePsiIsolatingComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- All numerator and selected-gap indices share one analytic source
neighborhood. The charts retain their actual spectral geometry and
prescribed-sheet terminal interpretation. -/
theorem exists_local_all_sourceAngularBeta_analytic
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWW₀ : W ⊆ W₀)
    (hA : ∀ ψ ∈ W, ∀ k : ℤ,
      AnalyticAt ℂ (fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
        (periodOnePotential χ) (periodOnePotential_mem χ) k) ψ ∧
      AnalyticAt ℂ (fun χ : CoeffPair p => (canonicalPeriodicGap hp hp1
        (periodOnePotential χ) (periodOnePotential_mem χ) k)^2) ψ)
    (hμ : ∀ m : ℤ, AnalyticOnNhd ℂ
      (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) W)
    (φ : CoeffPair p) (hφ : φ ∈ W) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ W ∧
      (∀ n m : ℤ, m ≠ n → AnalyticOnNhd ℂ (sourceAngularBeta hp hp1 n m s) V) ∧
      ∀ m : ℤ, ∃ c : ℤ → ℂ, ∃ T : ℤ → ℝ, ∃ r R : ℝ, ∃ z₀ : ℂ,
        SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀ := by
  obtain ⟨V,hV,hφV,hVW,hcharts⟩ := hs.exists_local_joint_angular_annulus_primitives_allIndices
    W hW hWW₀ hA φ hφ hreal
  refine ⟨V,hV,hφV,hVW,?_,hcharts⟩
  intro n m hmn
  obtain ⟨c,T,r,R,z₀,D⟩ := hcharts m
  exact D.analyticOnNhd_beta n hmn ((hμ m).mono hVW)

end SourcePsiIsolatingComplexExtension

/-- The analyticity assertion for the actual off-diagonal angular terms
in Theorem 13.1(i), on one common complex neighborhood and at every index.
This theorem does not assert its uniform quantitative bound. -/
theorem exists_sourceAngularBeta_analytic_common_domain
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W : Set (CoeffPair p), IsOpen W₀ ∧ IsSimplyConnected W₀ ∧
      realTypeSourceLocus p ⊆ W₀ ∧ IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ W₀ ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        SourcePsiSquaredGapComplexExtension hp hp1 W₀ s ∧
          (∀ b : BoundaryCondition, ∀ m : ℤ,
            AnalyticOnNhd ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ m) W) ∧
          (∀ b : BoundaryCondition, AnalyticOnNhd ℂ (sourceBoundaryDisplacement hp hp1 b) W) ∧
          (∀ ψ ∈ W, ∀ m : ℤ,
            AnalyticAt ℂ (fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
              (periodOnePotential χ) (periodOnePotential_mem χ) m) ψ ∧
            AnalyticAt ℂ (fun χ : CoeffPair p => (canonicalPeriodicGap hp hp1
              (periodOnePotential χ) (periodOnePotential_mem χ) m)^2) ψ) ∧
          (∀ ψ ∈ W, ∀ n m : ℤ, m ≠ n →
            sourceAngularBeta hp hp1 n m s ψ ∈ sourceAngularBetaValues hp hp1 n m s ψ ∧
              ∀ b ∈ sourceAngularBetaValues hp hp1 n m s ψ, b = sourceAngularBeta hp hp1 n m s ψ) ∧
          ∀ n m : ℤ, m ≠ n → AnalyticOnNhd ℂ (sourceAngularBeta hp hp1 n m s) W := by
  classical
  obtain ⟨W₀,B,hW₀,hW₀conn,hW₀real,hB,hBreal,hBW₀,s,hs,hroots,hbeta⟩ :=
    exists_sourceAngularBeta_common_domain_with_analyticBoundaryRoots hp hp1
  obtain ⟨A,hA,_,hAreal,hsym⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  let O := B ∩ A
  have hO : IsOpen O := hB.inter hA
  have hOreal : realTypeSourceLocus p ⊆ O := fun φ hφ => ⟨hBreal hφ,hAreal hφ⟩
  have hOW₀ : O ⊆ W₀ := inter_subset_left.trans hBW₀
  have hlocal (φ : realTypeSourceLocus p) :=
    hs.toSourcePsiIsolatingComplexExtension.exists_local_all_sourceAngularBeta_analytic
      O hO hOW₀ (fun ψ hψ => hsym ψ hψ.2)
      (fun m => (hroots .dirichlet m).mono inter_subset_left)
      φ.val (hOreal φ.property) φ.property
  choose V hV hφV hVO hVbeta _ using hlocal
  let W := ⋃ φ : realTypeSourceLocus p, V φ
  have hW : IsOpen W := isOpen_iUnion hV
  have hWreal : realTypeSourceLocus p ⊆ W := by
    intro φ hφ
    exact mem_iUnion.mpr ⟨⟨φ,hφ⟩,hφV ⟨φ,hφ⟩⟩
  have hWO : W ⊆ O := by
    intro ψ hψ
    obtain ⟨φ,hψV⟩ := mem_iUnion.mp hψ
    exact hVO φ hψV
  have hrootsW (b : BoundaryCondition) (m : ℤ) :
      AnalyticOnNhd ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ m) W :=
    (hroots b m).mono (hWO.trans inter_subset_left)
  refine ⟨W₀,W,hW₀,hW₀conn,hW₀real,hW,hWreal,hWO.trans hOW₀,s,hs,hrootsW,
    analyticOnNhd_sourceBoundaryDisplacement_of_roots hp hp1 W hW hrootsW,
    (fun ψ hψ => hsym ψ (hWO hψ).2),
    (fun ψ hψ => hbeta ψ (hWO hψ).1),?_⟩
  intro n m hmn ψ hψ
  obtain ⟨φ,hψV⟩ := mem_iUnion.mp hψ
  exact hVbeta φ n m hmn ψ hψV

end NLS.ZakharovShabat
