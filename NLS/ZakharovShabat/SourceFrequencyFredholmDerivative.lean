import NLS.ZakharovShabat.SourceFrequencyCompactDerivative
import NLS.FunctionalAnalysis.CompactFredholm

/-! # Corollary 18.2(iii): Fredholm frequency derivatives of index zero

The compact corrected derivative gives a Fredholm derivative everywhere on
the actual action domain, with equal finite kernel and cokernel dimensions.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- The actual action-frequency derivative is Fredholm of index zero throughout
its complex action domain. Compactness and the source-recovery data are retained. -/
theorem exists_sourceFrequency_fredholmDerivative (hp : p ≠ ⊤) (hp2 : 2 < p) :
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
          IsCompactOperator (fderiv ℂ F b + (2 : ℂ) • ContinuousLinearMap.id ℂ (Coeff q)) ∧
          (fderiv ℂ F b).IsFredholm ∧
          Module.finrank ℂ (fderiv ℂ F b).ker =
            Module.finrank ℂ (Coeff q ⧸ (fderiv ℂ F b).range) := by
  obtain ⟨hp1,W,s,A,P,hs,W₀,B,X,t,D,V,hV,hzero,hcenter,hpos,himage,F,hF,hFR,hFzero,hrec,hcompact⟩ :=
    exists_sourceFrequency_compactDerivative (q := q) hp hp2
  refine ⟨hp1,W,s,A,P,hs,W₀,B,X,t,D,V,hV,hzero,hcenter,hpos,himage,F,hF,hFR,hFzero,hrec,?_⟩
  intro b hb
  refine ⟨hcompact b hb, ?_⟩
  apply CompactSpectrum.fredholm_index_zero_of_compact_sub_smul
    (fderiv ℂ F b) (c := -2) (by norm_num)
  rw [neg_smul, sub_neg_eq_add]
  convert hcompact b hb using 1
  · congr 1
  · ext x n
    rfl

end NLS.ZakharovShabat
