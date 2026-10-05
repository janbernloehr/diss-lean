import NLS.ZakharovShabat.SourceFrequencySmoothingDerivative
import NLS.SequenceSpaces.CompactActionDerivative

/-! # Corollary 18.2(ii): compact corrected frequency derivatives

Pitt's theorem turns the verified refined derivative factorization into
compactness at every complex point of the actual action domain.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- The actual action-frequency extension has compact corrected derivative
everywhere, on an action image containing all real-source actions and the
nonnegative summable cone. This is Corollary 18.2(ii). -/
theorem exists_sourceFrequency_compactDerivative (hp : p ≠ ⊤) (hp2 : 2 < p) :
    ∃ hp1 : 1 < p, ∃ W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ A : SourceAbelianMomentAtlas hp hp1 W s,
    ∃ P : Set (CoeffPair p), SourcePsiIsolatingComplexExtension hp hp1 P s ∧
    ∃ W₀ B X : Set (CoeffPair p), ∃ t : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ _D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t,
    ∃ V : Set (Coeff q), IsOpen V ∧ (0 : Coeff q) ∈ V ∧
      (∀ ψ : realTypeSourceSubmodule p, sourceActionSequence (q := q) hp hp1 t ψ.val ∈ V) ∧
      (∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) →
        Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b) ∈ V) ∧
      (∃ Y : Set (CoeffPair p), IsOpen Y ∧ realTypeSourceLocus p ⊆ Y ∧ Y ⊆ X ∧
        sourceActionSequence (q := q) hp hp1 t '' Y = V) ∧
      ∃ F : Coeff q → Coeff q, AnalyticOnNhd ℂ F V ∧ AnalyticOnNhd ℝ F V ∧ F 0 = 0 ∧
        (∀ ψ : realTypeSourceSubmodule p, ∀ n,
          F (sourceActionSequence (q := q) hp hp1 t ψ.val) n = A.renormalizedFrequency n ψ.val) ∧
        ∀ b ∈ V,
          IsCompactOperator (fderiv ℂ F b+(2 : ℂ) • ContinuousLinearMap.id ℂ (Coeff q)) := by
  obtain ⟨hp1,W,s,A,P,hs,W₀,B,X,t,D,V,hV,hzero,hcenter,hpos,himage,F,hF,hFR,hFzero,hrec,
    r,instR,hr,hr1,hrq,hpr,H,hH,hHR,hHzero,he,hDH,hfactor⟩ :=
    exists_sourceFrequency_smoothingDerivative (q := q) hp hp2
  refine ⟨hp1,W,s,A,P,hs,W₀,B,X,t,D,V,hV,hzero,hcenter,hpos,himage,F,hF,hFR,hFzero,hrec,?_⟩
  intro b hb
  exact Coeff.isCompactOperator_actionCorrection_fderiv (Coeff.doublingExponent_ne_top hp)
    hrq V hV F H hF hH he b hb

end NLS.ZakharovShabat
