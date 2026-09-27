import NLS.ZakharovShabat.SourceCriticalPointsAnalytic
import NLS.ZakharovShabat.SourceCriticalRootRatioFactorization
import NLS.ZakharovShabat.SourceCriticalRootRatioJointAnalytic
import NLS.ZakharovShabat.SourceStandardRootJointAnalytic

/-!
# Source analyticity of the deleted factor at an exterior spectral point

The deleted factor is defined through the full critical displacement
sequence. At a fixed spectral point outside all gaps, factorization
of the actual discriminant quotient expresses it instead through the
single selected critical point, the jointly analytic standard root,
and the jointly analytic discriminant derivative. This proves source
analyticity there without assuming analyticity of the whole sequence.
-/

noncomputable section
open Set Complex Filter Topology Metric NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At a real-type source the selected critical point belongs to
its closed periodic gap segment, including when the gap collapses. -/
theorem sourceCanonicalCriticalPoint_mem_periodicSegment_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    canonicalCriticalPoints hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) n ∈ sourcePeriodicSegment hp hp1 φ n := by
  let L := canonicalPeriodicLeft hp hp1 (periodOnePotential φ)
    (periodOnePotential_mem φ) n
  let R := canonicalPeriodicRight hp hp1 (periodOnePotential φ)
    (periodOnePotential_mem φ) n
  let c := canonicalCriticalPoints hp hp1 (periodOnePotential φ)
    (periodOnePotential_mem φ) n
  have hre : c.re ∈ Set.Icc L.re R.re :=
    canonicalCriticalPoints_mem_canonicalPeriodicGap hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ)
      (isRealType_periodOnePotential φ hreal) n
  have himL : L.im = 0 :=
    (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ)
      (isRealType_periodOnePotential φ hreal) n).1
  have himR : R.im = 0 :=
    (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ)
      (isRealType_periodOnePotential φ hreal) n).2
  have himc : c.im = 0 :=
    canonicalCriticalPoints_im_eq_zero hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ)
      (isRealType_periodOnePotential φ hreal) n
  obtain ⟨a,b,ha,hb,hab,hpoint⟩ := Icc_subset_segment hre
  change c ∈ segment ℝ L R
  refine ⟨a,b,ha,hb,hab,?_⟩
  apply Complex.ext
  · simpa only [Complex.add_re, Complex.smul_re, smul_eq_mul] using hpoint
  · simp [himc,himL,himR]

/-- At an exterior spectral point distinct from the selected
critical root, the deleted factor is analytic in the complex source
at every real-type potential. -/
theorem analyticAt_sourceCriticalRootRatioExtension_fixedSpectral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ)
    (hcrit : canonicalCriticalPoints hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) n - z ≠ 0) :
    AnalyticAt ℂ (fun ψ : CoeffPair p =>
      sourceCriticalRootRatioExtension hp hp1 n ψ z) φ := by
  let c (ψ : CoeffPair p) := canonicalCriticalPoints hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let Q (ψ : CoeffPair p) := sourceCriticalRootRatioJoint hp hp1 (z,ψ)
  let S (ψ : CoeffPair p) := sourceStandardRoot hp hp1 ψ n z
  let E (ψ : CoeffPair p) := sourceCriticalRootRatioExtension hp hp1 n ψ z
  have hc : AnalyticAt ℂ c φ :=
    analyticAt_sourceCanonicalCriticalPoint_of_realType hp hp1 n φ hreal
  obtain ⟨W₁,_,_,hreal₁,hDopen,hquot⟩ :=
    exists_global_sourceCriticalRootRatio_jointAnalytic hp hp1
  have hpoint : (z,φ) ∈ sourceCanonicalRootJointDomain hp hp1 W₁ :=
    ⟨hreal₁ hreal,hz⟩
  have hQ : AnalyticAt ℂ Q φ :=
    (hquot (z,φ) hpoint).comp
      (f := fun ψ : CoeffPair p => (z,ψ))
      (analyticAt_const.prod analyticAt_id)
  obtain ⟨W₂,_,_,hreal₂,hstd⟩ :=
    exists_global_source_analytic_standardRoot hp hp1
  have hS : AnalyticAt ℂ S φ :=
    (hstd φ (hreal₂ hreal) n z (hz n)).comp
      (f := fun ψ : CoeffPair p => (z,ψ))
      (analyticAt_const.prod analyticAt_id)
  have hden : AnalyticAt ℂ (fun ψ => c ψ - z) φ :=
    hc.sub analyticAt_const
  have hratio : AnalyticAt ℂ
      (fun ψ : CoeffPair p => Q ψ * S ψ / (c ψ - z)) φ :=
    (hQ.mul hS).div hden hcrit
  have hdomain : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      z ∈ sourceCanonicalRootDomain hp hp1 ψ := by
    have hmap : ContinuousAt (fun ψ : CoeffPair p => (z,ψ)) φ :=
      continuousAt_const.prodMk continuousAt_id
    have hnear := hmap.eventually (hDopen.mem_nhds hpoint)
    filter_upwards [hnear] with ψ hψ
    exact hψ.2
  have hcne : ∀ᶠ ψ : CoeffPair p in 𝓝 φ, c ψ - z ≠ 0 :=
    hden.continuousAt.eventually_ne hcrit
  have heq : (fun ψ : CoeffPair p => Q ψ * S ψ / (c ψ - z))
      =ᶠ[𝓝 φ] E := by
    filter_upwards [hdomain,hcne] with ψ hψdom hψc
    have hfact := sourceCriticalRootRatio_eq_selectedFactor_mul_extension
      hp hp1 ψ n z hψdom
    have hSnonzero : S ψ ≠ 0 :=
      sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z (hψdom n)
    change Q ψ = ((c ψ-z)/S ψ)*E ψ at hfact
    apply (div_eq_iff hψc).2
    rw [hfact]
    field_simp [hSnonzero]
  exact hratio.congr heq

/-- Every spectral point outside all periodic gaps automatically
satisfies the critical-root separation needed above. -/
theorem analyticAt_sourceCriticalRootRatioExtension_fixedSpectral_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ) :
    AnalyticAt ℂ (fun ψ : CoeffPair p =>
      sourceCriticalRootRatioExtension hp hp1 n ψ z) φ := by
  have hcrit : canonicalCriticalPoints hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) n - z ≠ 0 := by
    intro he
    have hcz : canonicalCriticalPoints hp hp1 (periodOnePotential φ)
        (periodOnePotential_mem φ) n = z := sub_eq_zero.mp he
    exact (hz n) (hcz ▸
      sourceCanonicalCriticalPoint_mem_periodicSegment_of_realType
        hp hp1 n φ hreal)
  exact analyticAt_sourceCriticalRootRatioExtension_fixedSpectral
    hp hp1 n φ hreal z hz hcrit

/-- One enclosing circle may be chosen so that the deleted factor is
source-analytic at every point of that circle. -/
theorem exists_sourceCriticalRootRatioExtension_sourceAnalytic_onEnclosingCircle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
      sourcePeriodicSegment hp hp1 φ n ⊆ ball c R ∧
      ∀ z ∈ sphere c R,
        AnalyticAt ℂ (fun ψ : CoeffPair p =>
          sourceCriticalRootRatioExtension hp hp1 n ψ z) φ := by
  obtain ⟨V,_,hφV,c,R,hR,hgeom⟩ :=
    exists_local_sourceCriticalRootRatio_uniformEnclosingCircle
      hp hp1 φ hreal n
  refine ⟨c,R,hR,(hgeom φ hφV).1,?_⟩
  intro z hz
  exact analyticAt_sourceCriticalRootRatioExtension_fixedSpectral_of_realType
    hp hp1 n φ hreal z ((hgeom φ hφV).2.2 hz)

end NLS.ZakharovShabat
