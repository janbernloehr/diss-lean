import NLS.SequenceSpaces.TailSquareDescentAnalyticLine
import NLS.ZakharovShabat.SourceFrequencyFiniteLineDescent

/-! # Analytic frequency slices in arbitrary sequence directions

The actual descended frequency and refined correction have analytic slices
in every complex sequence direction, in their full target norms. The proof
passes from finite directions to their limits using norm continuity. Joint
Fréchet analyticity and the descent to quadratic actions remain unproved.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- On one common open mixed-coordinate domain, both actual sequence maps
have analytic slices in every direction, with exact source recovery and
all admissible frequency and correction target exponents. -/
theorem exists_sourceFrequency_lineAnalyticTailSquareDescent (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ A : SourceAbelianMomentAtlas hp hp1 W s,
    ∃ W₀ B X : Set (CoeffPair p), ∃ t : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t,
    ∃ U : Set (CoeffPair p), IsOpen U ∧ realTypeSourceLocus p ⊆ U ∧
      ∀ φ : realTypeSourceSubmodule p, ∃ C : SourceBirkhoffInverseChart D φ U,
        ∃ S : Finset ℤ, ∃ R : ℝ,
        let c := Coeff.truncatePair S (sourceBirkhoffMap hp hp1 t φ.val)
        let V := ball c R
        let Q := Coeff.pairMixedSquare (q := q) S
        0 < R ∧ sourceBirkhoffMap hp hp1 t φ.val ∈ V ∧ V ⊆ C.target ∧
        IsOpen (Q '' V) ∧ Q (sourceBirkhoffMap hp hp1 t φ.val) ∈ Q '' V ∧
        (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
          let G := Coeff.tailSquareDescent (q := q) S (A.frequencySequence r ∘ C.inverse) V
          AnalyticOnNhd ℂ (A.frequencySequence r ∘ C.inverse) V ∧
          ContinuousOn G (Q '' V) ∧
          (∀ z ∈ V, AnalyticAt ℂ (fun b : Coeff q × Coeff q => G (Q z+Coeff.truncatePair S b)) 0) ∧
          (∀ (b d : Coeff q × Coeff q),
            AnalyticOnNhd ℂ (fun v : ℂ => G (b+v • d))
              ((fun v : ℂ => b+v • d) ⁻¹' (Q '' V))) ∧
          ∀ z ∈ V, G (Q z) = A.frequencySequence r (C.inverse z) ∧
            ∀ n, G (Q z) n = A.renormalizedFrequency n (C.inverse z)) ∧
        (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
          let G := Coeff.tailSquareDescent (q := q) S (A.actionFrequencyCorrectionSequence r ∘ C.inverse) V
          AnalyticOnNhd ℂ (A.actionFrequencyCorrectionSequence r ∘ C.inverse) V ∧
          ContinuousOn G (Q '' V) ∧
          (∀ z ∈ V, AnalyticAt ℂ (fun b : Coeff q × Coeff q => G (Q z+Coeff.truncatePair S b)) 0) ∧
          (∀ (b d : Coeff q × Coeff q),
            AnalyticOnNhd ℂ (fun v : ℂ => G (b+v • d))
              ((fun v : ℂ => b+v • d) ⁻¹' (Q '' V))) ∧
          ∀ z ∈ V, G (Q z) = A.actionFrequencyCorrectionSequence r (C.inverse z) ∧
            ∀ n, G (Q z) n = A.renormalizedFrequency n (C.inverse z)+z.1 n^2+z.2 n^2) := by
  obtain ⟨W,s,A,W₀,B,X,t,D,U,hU,hreal,hcharts⟩ :=
    exists_sourceFrequency_finiteLineAnalyticTailSquareDescent (q := q) hp hp1
  have hq : q ≠ ⊤ := Coeff.doublingExponent_ne_top hp
  refine ⟨W,s,A,W₀,B,X,t,D,U,hU,hreal,?_⟩
  intro φ
  obtain ⟨C,S,R,hR,hbase,hball,hQ,hbaseQ,hfreq,hcorr⟩ := hcharts φ
  refine ⟨C,S,R,hR,hbase,hball,hQ,hbaseQ,?_,?_⟩
  · intro r inst hr hr1 hpr
    obtain ⟨ha,hcont,hhead,hfinite,he⟩ := hfreq r hr hr1 hpr
    refine ⟨ha,hcont,hhead,?_,he⟩
    exact Coeff.analyticOnNhd_line_of_finiteLines hq _ _ hQ hcont (fun b _ => hfinite b)
  · intro r inst hr hr1 hpr
    obtain ⟨ha,hcont,hhead,hfinite,he⟩ := hcorr r hr hr1 hpr
    refine ⟨ha,hcont,hhead,?_,he⟩
    exact Coeff.analyticOnNhd_line_of_finiteLines hq _ _ hQ hcont (fun b _ => hfinite b)

end NLS.ZakharovShabat
