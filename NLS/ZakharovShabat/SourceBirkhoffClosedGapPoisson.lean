import NLS.ZakharovShabat.SourceBirkhoffOpenGapPoisson
import NLS.ZakharovShabat.SourceBirkhoffFixedFamilyAnalytic
import NLS.ZakharovShabat.SourceOpenGapDensity

/-! # Rectangular source brackets across all real closed gaps

For exponents at least two, the physical source bivector is continuous
on the full cotangent space. Scalar rectangular analyticity and density
of the simultaneous open-gap locus extend the three canonical identities
to every real source. No closed-gap angle is defined or used.
-/

noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The rectangular functions are analytic at all real sources for
the same root family as the canonical action-angle theorem. -/
theorem birkhoffXY_analyticAt
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n : ℤ) (φ : realTypeSourceSubmodule p) :
    AnalyticAt ℂ (sourceBirkhoffX hp hp1 n s) φ.val ∧
      AnalyticAt ℂ (sourceBirkhoffY hp hp1 n s) φ.val :=
  D.toSourceAngularEtaLocalCommonDomainData.birkhoffXY_analyticAt_of_realType
    W D.source_open D.source_subset φ.val (D.real_subset φ.property) φ.property n

/-- All three canonical rectangular identities at every real source
for every finite exponent at least two, without any open-gap hypotheses. -/
theorem birkhoff_sourceBracket_canonical
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m : ℤ) (φ : realTypeSourceSubmodule p) :
    sourceBracket h2p (sourceBirkhoffX hp hp1 n s) (sourceBirkhoffX hp hp1 m s) φ.val = 0 ∧
    sourceBracket h2p (sourceBirkhoffX hp hp1 n s) (sourceBirkhoffY hp hp1 m s) φ.val =
      -(if n = m then 1 else 0) ∧
    sourceBracket h2p (sourceBirkhoffY hp hp1 n s) (sourceBirkhoffY hp hp1 m s) φ.val = 0 := by
  have hcont (F G : CoeffPair p → ℂ)
      (hF : ∀ ψ : realTypeSourceSubmodule p, AnalyticAt ℂ F ψ.val)
      (hG : ∀ ψ : realTypeSourceSubmodule p, AnalyticAt ℂ G ψ.val) :
      Continuous (fun ψ : realTypeSourceSubmodule p => sourceBracket h2p F G ψ.val) := by
    apply continuous_iff_continuousAt.mpr
    intro ψ
    exact (((sourceBivector h2p).analyticAt_bilinear _).comp₂
      (hF ψ).fderiv (hG ψ).fderiv).continuousAt.comp continuous_subtype_val.continuousAt
  have hopen (ψ : realTypeSourceSubmodule p) (hψ : ψ ∈ sourceFiniteOpenGapRealLocus hp hp1 {n,m}) :=
    D.birkhoff_sourceBracket_canonical_of_open_gaps h2p n m ψ (hψ n (by simp)) (hψ m (by simp))
  refine ⟨?_,?_,?_⟩
  · exact eq_of_continuousOn_of_sourceFiniteOpenGaps hp hp1 {n,m} isOpen_univ
      (hcont _ _ (fun ψ => (D.birkhoffXY_analyticAt n ψ).1)
        (fun ψ => (D.birkhoffXY_analyticAt m ψ).1)).continuousOn 0
      (fun ψ _ hψ => (hopen ψ hψ).1) φ (mem_univ _)
  · exact eq_of_continuousOn_of_sourceFiniteOpenGaps hp hp1 {n,m} isOpen_univ
      (hcont _ _ (fun ψ => (D.birkhoffXY_analyticAt n ψ).1)
        (fun ψ => (D.birkhoffXY_analyticAt m ψ).2)).continuousOn (-(if n = m then 1 else 0))
      (fun ψ _ hψ => (hopen ψ hψ).2.1) φ (mem_univ _)
  · exact eq_of_continuousOn_of_sourceFiniteOpenGaps hp hp1 {n,m} isOpen_univ
      (hcont _ _ (fun ψ => (D.birkhoffXY_analyticAt n ψ).2)
        (fun ψ => (D.birkhoffXY_analyticAt m ψ).2)).continuousOn 0
      (fun ψ _ hψ => (hopen ψ hψ).2.2) φ (mem_univ _)

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
