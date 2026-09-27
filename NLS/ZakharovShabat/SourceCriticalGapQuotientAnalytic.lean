import NLS.ZakharovShabat.SourceCriticalPointsAnalytic
import NLS.ZakharovShabat.SourceCriticalGapQuotientContinuity
import NLS.ZakharovShabat.SourceSymmetricContour

/-!
# Analyticity of the critical squared-gap coefficient

Lemma 10.10 represents the critical-to-midpoint offset as a squared
periodic gap times a quotient of deleted-product derivatives. The
quotient does not divide by the gap, and its denominator is nonzero
at real-type sources. Analyticity of the critical coordinate and of
the deleted product now makes this coefficient analytic even when the
periodic gap collapses.
-/

noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Each squared-gap critical coefficient is analytic in the complex
source at every real-type potential, with no open-gap hypothesis. -/
theorem analyticAt_sourceCriticalGapQuotient_apply_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    AnalyticAt ℂ (fun ψ : CoeffPair p =>
      canonicalCriticalGapQuotient hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ := by
  let c (ψ : CoeffPair p) := canonicalCriticalPoints hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let τ (ψ : CoeffPair p) := canonicalPeriodicMidpoint hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let P (ψ : CoeffPair p) := canonicalDeletedPeriodicProduct hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n (c ψ)
  let d (ψ : CoeffPair p) := canonicalDeletedCriticalDerivative hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let C (ψ : CoeffPair p) := canonicalCriticalOffsetCoefficient hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  have hc : AnalyticAt ℂ c φ :=
    analyticAt_sourceCanonicalCriticalPoint_of_realType hp hp1 n φ hreal
  obtain ⟨Wτ,_,_,hrealτ,hτdata⟩ :=
    exists_global_source_analytic_midpoint_squaredGap hp hp1
  have hτ : AnalyticAt ℂ τ φ := (hτdata φ (hrealτ hreal) n).1
  obtain ⟨W,_,_,hWreal,hWdata⟩ :=
    exists_global_source_analytic_omittedJointProduct hp hp1
  obtain ⟨hDopen,hO,_,_⟩ := hWdata n
  have hPjoint := sourceDeletedPairJointProduct_analyticOnNhd_of_omitted
    hp hp1 W n hDopen hO
  have hdjoint := sourceDeletedPairJointSpectralDerivative_analyticOnNhd_of_omitted
    hp hp1 W n hDopen hO
  obtain ⟨N,ε,_,_,U,_,_,hφU,hcluster,hdisjoint⟩ :=
    exists_local_source_connected_isolating_discs hp hp1 φ hreal
  have hcdisc : c φ ∈ sourceIsolatingDisc hp hp1 φ N ε n :=
    hcluster φ hφU n (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have hcdomain : c φ ∈ sourceStandardRootOmittedDomain hp hp1 φ n :=
    sourceIsolatingDisc_subset_omittedDomain hp hp1 φ φ N ε
      (hcluster φ hφU) hdisjoint n hcdisc
  have hpoint : (c φ,φ) ∈ sourceStandardRootOmittedJointDomain hp hp1 W n :=
    ⟨hWreal hreal,hcdomain⟩
  have hmap : AnalyticAt ℂ (fun ψ : CoeffPair p => (c ψ,ψ)) φ :=
    hc.prod analyticAt_id
  have hP : AnalyticAt ℂ P φ := by
    exact (hPjoint (c φ,φ) hpoint).comp
      (f := fun ψ : CoeffPair p => (c ψ,ψ)) hmap
  have hd : AnalyticAt ℂ d φ := by
    exact (hdjoint (c φ,φ) hpoint).comp
      (f := fun ψ : CoeffPair p => (c ψ,ψ)) hmap
  have hC : AnalyticAt ℂ C φ := by
    have heq : C = (fun ψ : CoeffPair p =>
        2*P ψ+(c ψ-τ ψ)*d ψ) := by
      funext ψ
      simp only [C,canonicalCriticalOffsetCoefficient,
        canonicalCriticalMidpointOffset_apply,P,c,τ,d]
    rw [heq]
    exact (analyticAt_const.mul hP).add ((hc.sub hτ).mul hd)
  have hCne : C φ ≠ 0 :=
    sourceCriticalOffsetCoefficient_ne_zero_of_isolating hp hp1 φ φ N ε
      (hcluster φ hφU) hdisjoint n
  change AnalyticAt ℂ (fun ψ : CoeffPair p => d ψ/(4*C ψ)) φ
  exact hd.div (analyticAt_const.mul hC)
    (mul_ne_zero (by norm_num) hCne)

end NLS.ZakharovShabat
