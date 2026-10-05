import NLS.ZakharovShabat.SourceFrequencyFredholmDerivative
import NLS.ZakharovShabat.SourceFrequencyDerivativeOrigin
import NLS.ComplexAnalysis.ScalarDerivativeInverse

/-! # Corollary 18.2(i): local analytic invertibility at zero

The actual first frequency coefficient is proved from its moment formula.
The analytic inverse theorem gives both local inverse identities and the
reciprocal derivative, retaining the full action domain and Fredholm result.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- The actual frequency map has derivative minus twice the identity at zero
and a two-sided analytic local inverse. Compactness and Fredholm index zero
still hold everywhere on the full action domain. -/
theorem exists_sourceFrequency_localInverse (hp : p ≠ ⊤) (hp2 : 2 < p) :
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
        (∀ b ∈ V,
          IsCompactOperator (fderiv ℂ F b + (2 : ℂ) • ContinuousLinearMap.id ℂ (Coeff q)) ∧
          (fderiv ℂ F b).IsFredholm ∧
          Module.finrank ℂ (fderiv ℂ F b).ker =
            Module.finrank ℂ (Coeff q ⧸ (fderiv ℂ F b).range)) ∧
        fderiv ℂ F 0 = (-2 : ℂ) • ContinuousLinearMap.id ℂ (Coeff q) ∧
        ∃ G : Coeff q → Coeff q, AnalyticAt ℂ G 0 ∧ G 0 = 0 ∧
          (∀ᶠ b in 𝓝 (0 : Coeff q), G (F b) = b) ∧
          (∀ᶠ c in 𝓝 (0 : Coeff q), F (G c) = c) ∧
          fderiv ℂ G 0 = (-2 : ℂ)⁻¹ • ContinuousLinearMap.id ℂ (Coeff q) := by
  obtain ⟨hp1,W,s,A,P,hs,W₀,B,X,t,D,V,hV,hzero,hcenter,hpos,himage,F,hF,hFR,hFzero,hrec,hFred⟩ :=
    exists_sourceFrequency_fredholmDerivative (q := q) hp hp2
  have hd := sourceFrequency_fderiv_zero A hs D hp2.le F
    (hF 0 hzero).differentiableAt hFzero hrec
  refine ⟨hp1,W,s,A,P,hs,W₀,B,X,t,D,V,hV,hzero,hcenter,hpos,himage,F,hF,hFR,hFzero,hrec,hFred,hd,?_⟩
  exact NLS.ComplexAnalysis.exists_analytic_localInverse_of_scalar_derivative
    F (hF 0 hzero) hFzero (-2) (by norm_num) hd

end NLS.ZakharovShabat
