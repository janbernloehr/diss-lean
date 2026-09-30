import NLS.ZakharovShabat.SourceAngularEtaCauchyTerminal
import NLS.ZakharovShabat.SourceAngularEtaLocalCommonDomain
import NLS.ZakharovShabat.SourceAngularUniformAnnulusPrimitive

/-!
# Analytic eta remainder charts on a common complex source domain

All gap indices have joint annular charts on one neighborhood of each
real source. The union of these neighborhoods contains the whole real
locus. At every complex source in the union, including collapsed gaps,
the actual Dirichlet remainder has an analytic Cauchy formula. Overlap
independence and the admissible spectral integral formula are supplied
by `SourceAngularEtaCauchyTerminal`.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One common neighborhood carries analytic actual remainder charts
at every complex source and every gap index. No open-gap condition or
restriction on the location of the complex terminal angle is needed.
The full beta theorem and real eta charts are retained on a larger
domain for the same actual normalized psi family. -/
theorem exists_sourceAngular_eta_remainder_cauchy_common_domain
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ B W : Set (CoeffPair p), IsOpen W₀ ∧ IsSimplyConnected W₀ ∧
      realTypeSourceLocus p ⊆ W₀ ∧ IsOpen B ∧ realTypeSourceLocus p ⊆ B ∧ B ⊆ W₀ ∧
      IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ B ∧
      ∃ s : (k : ℤ) → CoeffPair p → DeletedCoeff p k,
        SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s ∧
        ∀ φ ∈ W, ∀ m : ℤ, ∃ V : Set (CoeffPair p),
          ∃ c : ℤ → ℂ, ∃ T : ℤ → ℝ, ∃ r R : ℝ, ∃ z₀ : ℂ, ∃ ρ : ℝ,
            φ ∈ V ∧ V ⊆ W ∧ r < ρ ∧ ρ < R ∧
            SourceAngularJointAnnulusChartData hp hp1 m s B V c T r R z₀ ∧
            AnalyticOnNhd ℂ (sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c m) r R z₀ ρ) V := by
  classical
  obtain ⟨W₀,B,hW₀,hW₀conn,hW₀real,hB,hBreal,hBW₀,s,D⟩ :=
    exists_sourceAngularEta_local_common_domain hp hp1
  have hlocal (φ : realTypeSourceLocus p) :=
    D.psi.toSourcePsiIsolatingComplexExtension.exists_local_joint_angular_annulus_primitives_allIndices
      B hB hBW₀ D.symmetric_analytic φ.val (hBreal φ.property) φ.property
  choose V hV hφ hVB hcharts using hlocal
  let W := ⋃ φ : realTypeSourceLocus p, V φ
  have hW : IsOpen W := isOpen_iUnion hV
  have hWreal : realTypeSourceLocus p ⊆ W := by
    intro φ hreal
    exact mem_iUnion.mpr ⟨⟨φ,hreal⟩,hφ ⟨φ,hreal⟩⟩
  have hWB : W ⊆ B := by
    intro ψ hψ
    obtain ⟨φ,hψV⟩ := mem_iUnion.mp hψ
    exact hVB φ hψV
  refine ⟨W₀,B,W,hW₀,hW₀conn,hW₀real,hB,hBreal,hBW₀,hW,hWreal,hWB,s,D,?_⟩
  intro φ hφW m
  obtain ⟨χ,hφV⟩ := mem_iUnion.mp hφW
  obtain ⟨c,T,r,R,z₀,C⟩ := hcharts χ m
  let ρ := (r+R)/2
  have hrρ : r < ρ := by dsimp only [ρ]; linarith [C.inner_lt_outer]
  have hρR : ρ < R := by dsimp only [ρ]; linarith [C.inner_lt_outer]
  exact ⟨V χ,c,T,r,R,z₀,ρ,hφV,(fun ψ hψ => mem_iUnion.mpr ⟨χ,hψ⟩),hrρ,hρR,C,
    C.analyticOnNhd_etaRemainderCauchyCandidate ρ hrρ hρR
      ((D.roots_analytic .dirichlet m).mono (hVB χ))⟩

end NLS.ZakharovShabat
