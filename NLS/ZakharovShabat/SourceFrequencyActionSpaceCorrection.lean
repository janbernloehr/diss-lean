import NLS.SequenceSpaces.ActionCorrectionIdentity
import NLS.ZakharovShabat.SourceFrequencyActionSpaceMaps

/-! # Global analytic frequency and its exact refined correction

The global frequency and correction maps satisfy H(I) = F(I) + 2I at
every complex point of the common action domain, in their respective
sequence spaces. The domain is the image of an open source neighborhood
containing all real sources and contains the nonnegative l1 action cone.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- The actual analytic frequency has an analytic refined correction on
one common open action domain, with the literal correction identity everywhere. -/
theorem exists_sourceFrequency_actionSpace_correction (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p) :
    ∃ W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ A : SourceAbelianMomentAtlas hp hp1 W s,
    ∃ P : Set (CoeffPair p), SourcePsiIsolatingComplexExtension hp hp1 P s ∧
    ∃ W₀ B X : Set (CoeffPair p), ∃ t : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ _D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t,
    ∃ V : Set (Coeff q), IsOpen V ∧
      (∀ φ : realTypeSourceSubmodule p, sourceActionSequence (q := q) hp hp1 t φ.val ∈ V) ∧
      (∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) →
        Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b) ∈ V) ∧
      (∃ Y : Set (CoeffPair p), IsOpen Y ∧ realTypeSourceLocus p ⊆ Y ∧ Y ⊆ X ∧
        sourceActionSequence (q := q) hp hp1 t '' Y = V) ∧
      ∀ (r u : ℝ≥0∞) [Fact (1 ≤ r)] [Fact (1 ≤ u)],
        r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
        u ≠ ⊤ → 1 < u → ENNReal.ofReal (p.toReal/3) ≤ u →
        ∃ F : Coeff q → Coeff r, ∃ H : Coeff q → Coeff u,
          AnalyticOnNhd ℂ F V ∧ AnalyticOnNhd ℂ H V ∧
          (∀ b ∈ V, ∀ n, H b n = F b n+2*b n) ∧
          ∀ ψ : realTypeSourceSubmodule p,
            F (sourceActionSequence (q := q) hp hp1 t ψ.val) = A.frequencySequence r ψ.val ∧
            H (sourceActionSequence (q := q) hp hp1 t ψ.val) = A.actionFrequencyCorrectionSequence u ψ.val ∧
            ∀ n, F (sourceActionSequence (q := q) hp hp1 t ψ.val) n = A.renormalizedFrequency n ψ.val := by
  obtain ⟨W,s,A,P,hs,W₀,B,X,t,D,V,hV,hcenter,hpos,_,himage,huniq,hfreq,hcorr⟩ :=
    exists_sourceFrequency_actionSpace_maps (q := q) hp hp1 h2p
  refine ⟨W,s,A,P,hs,W₀,B,X,t,D,V,hV,hcenter,hpos,himage,?_⟩
  intro r u instR instU hr hr1 hpr hu hu1 hpu
  obtain ⟨F,hF,hrecF⟩ := hfreq r hr hr1 hpr
  obtain ⟨H,hH,hrecH⟩ := hcorr u hu hu1 hpu
  refine ⟨F,H,hF,hH,?_,fun ψ => ⟨(hrecF ψ).1,(hrecH ψ).1,(hrecF ψ).2⟩⟩
  apply Coeff.actionCorrection_eq_of_analytic_uniqueness
    (fun ψ : realTypeSourceSubmodule p => sourceActionSequence hp hp1 t ψ.val) V huniq F H hF hH
  intro ψ n
  rw [(hrecH ψ).2 n,(hrecF ψ).2 n]

end NLS.ZakharovShabat
