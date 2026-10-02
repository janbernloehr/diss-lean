import NLS.ZakharovShabat.SourceBirkhoffCoordinates
import NLS.ZakharovShabat.SourceAngularRealCharts

/-! # Scalar Birkhoff analyticity for a fixed root family

Every existing common angular family gives rectangular coordinates
analytic at all real sources, including closed gaps. The construction
uses local annular primitives without replacing that root family.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularEtaLocalCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Every signed gap-weighted eta coordinate is analytic at a real
point of an open angular domain, including closed gaps. -/
theorem gapWeightedEta_analyticAt_of_realType
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWB : W ⊆ B)
    (φ : CoeffPair p) (hφ : φ ∈ W) (hreal : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (sign : ℂ) :
    AnalyticAt ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s sign) φ := by
  obtain ⟨a,ha,_,_,_,_,hball,_⟩ := D.psi.isolation ⟨φ,hreal⟩
  let O := W ∩ ball φ a
  have hO : IsOpen O := hW.inter isOpen_ball
  have hOB : O ⊆ B := fun _ h => hWB h.1
  obtain ⟨V,c,T,r,R,z₀,hφV,C⟩ :=
    D.psi.toSourcePsiIsolatingComplexExtension.exists_local_joint_angular_annulus_primitives
      O hO (fun _ h => hball h.2) (fun ψ hψ => D.symmetric_analytic ψ (hOB hψ))
      φ ⟨hφ,mem_ball_self ha⟩ hreal n
  let ρ := (r+R)/2
  have hrρ : r < ρ := by dsimp only [ρ]; linarith [C.inner_lt_outer]
  have hρR : ρ < R := by dsimp only [ρ]; linarith [C.inner_lt_outer]
  exact C.analyticOnNhd_gapWeightedEtaCoordinate ρ hrρ hρR
    ((D.roots_analytic .dirichlet n).mono (C.source_subset.trans hOB))
    (fun ψ hψ => (D.symmetric_analytic ψ (hOB (C.source_subset hψ)) n).1) sign φ hφV

/-- Both actual rectangular coordinates are analytic at every real
point of an open angular domain, with no condition on the selected gap. -/
theorem birkhoffXY_analyticAt_of_realType
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWB : W ⊆ B)
    (φ : CoeffPair p) (hφ : φ ∈ W) (hreal : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    AnalyticAt ℂ (sourceBirkhoffX hp hp1 n s) φ ∧ AnalyticAt ℂ (sourceBirkhoffY hp hp1 n s) φ := by
  obtain ⟨A,_,hφA,hξ,_⟩ := exists_local_sourceNormalizedActionRoot_allIndices_analytic hp hp1 φ hreal
  exact analyticAt_sourceBirkhoffXY hp hp1 n s φ (hξ n φ hφA)
    (D.gapWeightedEta_analyticAt_of_realType W hW hWB φ hφ hreal n)
    (D.beta_series.analytic_correction n φ (hWB hφ))

end SourceAngularEtaLocalCommonDomainData
end NLS.ZakharovShabat
