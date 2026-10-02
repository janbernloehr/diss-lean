import NLS.ZakharovShabat.SourceBirkhoffFixedFamilyAnalytic
import NLS.ZakharovShabat.SourceNormalizedActionExponent
import NLS.ZakharovShabat.SourceAngularEtaPhaseExponent

/-! # Rectangular coordinates agree across families and exponents

Actual normalized annular remainders agree even at closed gaps. Together
with spectral, action-root, and beta compatibility this identifies both
rectangular values, their complex germs, and their full derivatives.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
namespace SourceAngularEtaLocalCommonDomainData
variable {hp : p ≠ ⊤} {hq : q ≠ ⊤} {hp1 : 1 < p} {hq1 : 1 < q}
  {W₀ B : Set (CoeffPair p)} {V₀ C : Set (CoeffPair q)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {t : (k : ℤ) → CoeffPair q → DeletedCoeff q k}

/-- An annular chart for the existing family at any real source,
with no open-gap condition. -/
theorem exists_real_joint_annulus_chart
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWB : W ⊆ B)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ W) (n : ℤ) :
    ∃ O V : Set (CoeffPair p), ∃ c : ℤ → ℂ, ∃ T : ℤ → ℝ,
      ∃ r R : ℝ, ∃ z₀ : ℂ, ∃ ρ : ℝ, φ.val ∈ V ∧ r < ρ ∧ ρ < R ∧
        SourceAngularJointAnnulusChartData hp hp1 n s O V c T r R z₀ := by
  obtain ⟨a,ha,_,_,_,_,hball,_⟩ := D.psi.isolation φ
  let O := W ∩ ball φ.val a
  obtain ⟨V,c,T,r,R,z₀,hφV,E⟩ :=
    D.psi.toSourcePsiIsolatingComplexExtension.exists_local_joint_angular_annulus_primitives
      O (hW.inter isOpen_ball) (fun _ h => hball h.2)
      (fun ψ hψ => D.symmetric_analytic ψ (hWB hψ.1))
      φ.val ⟨hφ,mem_ball_self ha⟩ φ.property n
  exact ⟨O,V,c,T,r,R,z₀,(r+R)/2,hφV,by linarith [E.inner_lt_outer],by linarith [E.inner_lt_outer],E⟩

/-- The chosen chart-independent eta remainder agrees across exponents
and across the normalized root families of different constructions. -/
theorem etaRemainder_real_exponent
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (E : SourceAngularEtaLocalCommonDomainData hq hq1 V₀ C t)
    (W : Set (CoeffPair p)) (V : Set (CoeffPair q))
    (hW : IsOpen W) (hV : IsOpen V) (hWB : W ⊆ B) (hVC : V ⊆ C)
    (hpq : p ≤ q) (n : ℤ) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ W) (hφ' : CoeffPair.exponentInclusion hpq φ.val ∈ V) :
    sourceAngularEtaRemainder hp hp1 n s φ.val =
      sourceAngularEtaRemainder hq hq1 n t (CoeffPair.exponentInclusion hpq φ.val) := by
  obtain ⟨O,A,c,T,r,R,z₀,ρ,hφA,hrρ,hρR,H⟩ := D.exists_real_joint_annulus_chart W hW hWB φ hφ n
  obtain ⟨O',A',c',T',r',R',z₀',ρ',hφA',hrρ',hρR',H'⟩ :=
    E.exists_real_joint_annulus_chart V hV hVC (realTypeSourceExponentInclusion hpq φ) hφ' n
  rw [H.etaRemainder_eq_cauchyCandidate ρ hrρ hρR φ.val hφA,
    H'.etaRemainder_eq_cauchyCandidate ρ' hrρ' hρR' (CoeffPair.exponentInclusion hpq φ.val) hφA']
  exact H.etaRemainderCauchyCandidate_exponent H' hpq φ.val hφA hφA'
    (D.psi.toSourcePsiIsolatingComplexExtension.candidate_real_exponent_agreement
      E.psi.toSourcePsiIsolatingComplexExtension hpq n φ) ρ hrρ hρR ρ' hrρ' hρR'

/-- Both rectangular values agree at every real source, with no
condition on the selected gap or Dirichlet terminal. -/
theorem birkhoffXY_real_exponent
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (E : SourceAngularEtaLocalCommonDomainData hq hq1 V₀ C t)
    (W : Set (CoeffPair p)) (V : Set (CoeffPair q))
    (hW : IsOpen W) (hV : IsOpen V) (hWB : W ⊆ B) (hVC : V ⊆ C)
    (hpq : p ≤ q) (n : ℤ) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ W) (hφ' : CoeffPair.exponentInclusion hpq φ.val ∈ V) :
    sourceBirkhoffX hp hp1 n s φ.val = sourceBirkhoffX hq hq1 n t (CoeffPair.exponentInclusion hpq φ.val) ∧
    sourceBirkhoffY hp hp1 n s φ.val = sourceBirkhoffY hq hq1 n t (CoeffPair.exponentInclusion hpq φ.val) := by
  have hrem := D.etaRemainder_real_exponent E W V hW hV hWB hVC hpq n φ hφ hφ'
  have hβ := D.psi.toSourcePsiIsolatingComplexExtension.betaCorrection_real_exponent_agreement
    E.psi.toSourcePsiIsolatingComplexExtension hpq n φ
  have hμ := canonicalPeriodOneBoundaryRoots_exponent hp hq hp1 hq1 hpq .dirichlet φ.val
  have hsin : sourceDirichletEtaSineNumerator hp hp1 n φ.val =
      sourceDirichletEtaSineNumerator hq hq1 n (CoeffPair.exponentInclusion hpq φ.val) := by
    dsimp only [sourceDirichletEtaSineNumerator]
    rw [← hμ, ← sourceAntiDiscriminantCandidate_exponent hp hq hp1 hq1 hpq φ.val,
      ← sourceStandardRootOmittedProduct_exponent hp hq hp1 hq1 hpq n φ.val]
  have hw (sign : ℂ) : sourceBirkhoffWeightedCoordinate hp hp1 n s sign φ.val =
      sourceBirkhoffWeightedCoordinate hq hq1 n t sign (CoeffPair.exponentInclusion hpq φ.val) := by
    simp only [sourceBirkhoffWeightedCoordinate,sourceGapWeightedEtaCoordinate,
      sourceNormalizedActionRoot_real_exponent hp hq hp1 hq1 hpq n φ,
      hrem,hβ,hμ,hsin,canonicalPeriodicMidpoint_source_exponent hp hq hp1 hq1 hpq φ.val n]
  exact ⟨by simp only [sourceBirkhoffX,hw],by simp only [sourceBirkhoffY,hw]⟩

/-- Real agreement determines the full complex germs, including at closed gaps. -/
theorem eventually_birkhoffXY_exponent
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (E : SourceAngularEtaLocalCommonDomainData hq hq1 V₀ C t)
    (W : Set (CoeffPair p)) (V : Set (CoeffPair q))
    (hW : IsOpen W) (hV : IsOpen V) (hWB : W ⊆ B) (hVC : V ⊆ C)
    (hrW : realTypeSourceLocus p ⊆ W) (hrV : realTypeSourceLocus q ⊆ V)
    (hpq : p ≤ q) (n : ℤ) (φ : realTypeSourceSubmodule p) :
    sourceBirkhoffX hp hp1 n s =ᶠ[𝓝 φ.val]
      (sourceBirkhoffX hq hq1 n t ∘ CoeffPair.exponentInclusion hpq) ∧
    sourceBirkhoffY hp hp1 n s =ᶠ[𝓝 φ.val]
      (sourceBirkhoffY hq hq1 n t ∘ CoeffPair.exponentInclusion hpq) := by
  have hA := D.birkhoffXY_analyticAt_of_realType W hW hWB φ.val (hrW φ.property) φ.property n
  have hB := E.birkhoffXY_analyticAt_of_realType V hV hVC _
    (hrV (realTypeSourceExponentInclusion hpq φ).property) (realTypeSourceExponentInclusion hpq φ).property n
  have heq (ψ : realTypeSourceSubmodule p) := D.birkhoffXY_real_exponent E W V hW hV hWB hVC hpq n ψ
    (hrW ψ.property) (hrV (realTypeSourceExponentInclusion hpq ψ).property)
  exact ⟨eventuallyEq_source_of_analyticAt_of_real_agreement hp φ _ _ hA.1
      (hB.1.comp (f := CoeffPair.exponentInclusion hpq) ((CoeffPair.exponentInclusion hpq).analyticAt _)) (fun ψ => (heq ψ).1),
    eventuallyEq_source_of_analyticAt_of_real_agreement hp φ _ _ hA.2
      (hB.2.comp (f := CoeffPair.exponentInclusion hpq) ((CoeffPair.exponentInclusion hpq).analyticAt _)) (fun ψ => (heq ψ).2)⟩

/-- Compatibility of the complete rectangular cotangents, not only
of derivatives in real tangent directions. -/
theorem fderiv_birkhoffXY_exponent
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (E : SourceAngularEtaLocalCommonDomainData hq hq1 V₀ C t)
    (W : Set (CoeffPair p)) (V : Set (CoeffPair q))
    (hW : IsOpen W) (hV : IsOpen V) (hWB : W ⊆ B) (hVC : V ⊆ C)
    (hrW : realTypeSourceLocus p ⊆ W) (hrV : realTypeSourceLocus q ⊆ V)
    (hpq : p ≤ q) (n : ℤ) (φ : realTypeSourceSubmodule p) :
    fderiv ℂ (sourceBirkhoffX hp hp1 n s) φ.val =
      (fderiv ℂ (sourceBirkhoffX hq hq1 n t) (CoeffPair.exponentInclusion hpq φ.val)).comp (CoeffPair.exponentInclusion hpq) ∧
    fderiv ℂ (sourceBirkhoffY hp hp1 n s) φ.val =
      (fderiv ℂ (sourceBirkhoffY hq hq1 n t) (CoeffPair.exponentInclusion hpq φ.val)).comp (CoeffPair.exponentInclusion hpq) := by
  have hg := D.eventually_birkhoffXY_exponent E W V hW hV hWB hVC hrW hrV hpq n φ
  have hB := E.birkhoffXY_analyticAt_of_realType V hV hVC _
    (hrV (realTypeSourceExponentInclusion hpq φ).property) (realTypeSourceExponentInclusion hpq φ).property n
  constructor
  · rw [hg.1.fderiv_eq, fderiv_comp φ.val hB.1.differentiableAt
      (CoeffPair.exponentInclusion hpq).differentiableAt, ContinuousLinearMap.fderiv]
  · rw [hg.2.fderiv_eq, fderiv_comp φ.val hB.2.differentiableAt
      (CoeffPair.exponentInclusion hpq).differentiableAt, ContinuousLinearMap.fderiv]

end SourceAngularEtaLocalCommonDomainData
end NLS.ZakharovShabat
