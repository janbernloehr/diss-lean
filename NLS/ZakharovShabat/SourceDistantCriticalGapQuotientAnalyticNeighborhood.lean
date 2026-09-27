import NLS.ZakharovShabat.SourceDistantCriticalPointsAnalyticNeighborhood
import NLS.ZakharovShabat.SourceCriticalGapQuotientAnalytic

/-!
# Uniform source analyticity of distant critical gap quotients

The critical squared-gap quotient uses the selected critical coordinate,
the deleted periodic product and its spectral derivative, and the
periodic midpoint. Their analyticity and the nonzero offset coefficient
hold on one common complex neighborhood for all distant indices.
-/

noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A single complex source neighborhood supports analytic critical
squared-gap quotients at every sufficiently distant signed index. -/
theorem exists_local_source_distantCriticalGapQuotient_analytic
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ n : ℤ, K < n.natAbs →
        AnalyticAt ℂ (fun χ : CoeffPair p =>
          canonicalCriticalGapQuotient hp hp1
            (periodOnePotential χ) (periodOnePotential_mem χ) n) ψ := by
  obtain ⟨K,Vr,hVropen,hφVr,hroot⟩ :=
    exists_local_source_distantCanonicalCriticalPoints_analytic hp hp1 φ hreal
  obtain ⟨N,ε,_,_,Ui,hUiopen,_,hφUi,hcluster,hdisjoint⟩ :=
    exists_local_source_connected_isolating_discs hp hp1 φ hreal
  obtain ⟨Wτ,hWτopen,_,hrealτ,hτdata⟩ :=
    exists_global_source_analytic_midpoint_squaredGap hp hp1
  obtain ⟨Wp,hWpopen,_,hrealp,hWpData⟩ :=
    exists_global_source_analytic_omittedJointProduct hp hp1
  let V : Set (CoeffPair p) := Vr ∩ (Ui ∩ (Wτ ∩ Wp))
  have hVopen : IsOpen V :=
    hVropen.inter (hUiopen.inter (hWτopen.inter hWpopen))
  have hφV : φ ∈ V :=
    ⟨hφVr,hφUi,hrealτ hreal,hrealp hreal⟩
  refine ⟨K,V,hVopen,hφV,?_⟩
  intro ψ hψ n hn
  let c (χ : CoeffPair p) := canonicalCriticalPoints hp hp1
    (periodOnePotential χ) (periodOnePotential_mem χ) n
  let τ (χ : CoeffPair p) := canonicalPeriodicMidpoint hp hp1
    (periodOnePotential χ) (periodOnePotential_mem χ) n
  let P (χ : CoeffPair p) := canonicalDeletedPeriodicProduct hp hp1
    (periodOnePotential χ) (periodOnePotential_mem χ) n (c χ)
  let d (χ : CoeffPair p) := canonicalDeletedCriticalDerivative hp hp1
    (periodOnePotential χ) (periodOnePotential_mem χ) n
  let C (χ : CoeffPair p) := canonicalCriticalOffsetCoefficient hp hp1
    (periodOnePotential χ) (periodOnePotential_mem χ) n
  have hc : AnalyticAt ℂ c ψ := hroot ψ hψ.1 n hn
  have hτ : AnalyticAt ℂ τ ψ := (hτdata ψ hψ.2.2.1 n).1
  obtain ⟨hDopen,hO,_,_⟩ := hWpData n
  have hPjoint := sourceDeletedPairJointProduct_analyticOnNhd_of_omitted
    hp hp1 Wp n hDopen hO
  have hdjoint := sourceDeletedPairJointSpectralDerivative_analyticOnNhd_of_omitted
    hp hp1 Wp n hDopen hO
  have hcdisc : c ψ ∈ sourceIsolatingDisc hp hp1 φ N ε n :=
    hcluster ψ hψ.2.1 n (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have hcdomain : c ψ ∈ sourceStandardRootOmittedDomain hp hp1 ψ n :=
    sourceIsolatingDisc_subset_omittedDomain hp hp1 φ ψ N ε
      (hcluster ψ hψ.2.1) hdisjoint n hcdisc
  have hpoint : (c ψ,ψ) ∈ sourceStandardRootOmittedJointDomain hp hp1 Wp n :=
    ⟨hψ.2.2.2,hcdomain⟩
  have hmap : AnalyticAt ℂ (fun χ : CoeffPair p => (c χ,χ)) ψ :=
    hc.prod analyticAt_id
  have hP : AnalyticAt ℂ P ψ :=
    (hPjoint (c ψ,ψ) hpoint).comp
      (f := fun χ : CoeffPair p => (c χ,χ)) hmap
  have hd : AnalyticAt ℂ d ψ :=
    (hdjoint (c ψ,ψ) hpoint).comp
      (f := fun χ : CoeffPair p => (c χ,χ)) hmap
  have hC : AnalyticAt ℂ C ψ := by
    have heq : C = (fun χ : CoeffPair p =>
        2*P χ+(c χ-τ χ)*d χ) := by
      funext χ
      simp only [C,canonicalCriticalOffsetCoefficient,
        canonicalCriticalMidpointOffset_apply,P,c,τ,d]
    rw [heq]
    exact (analyticAt_const.mul hP).add ((hc.sub hτ).mul hd)
  have hCne : C ψ ≠ 0 :=
    sourceCriticalOffsetCoefficient_ne_zero_of_isolating hp hp1 φ ψ N ε
      (hcluster ψ hψ.2.1) hdisjoint n
  change AnalyticAt ℂ (fun χ : CoeffPair p => d χ/(4*C χ)) ψ
  exact hd.div (analyticAt_const.mul hC)
    (mul_ne_zero (by norm_num) hCne)

end NLS.ZakharovShabat
