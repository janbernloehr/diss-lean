import NLS.SequenceSpaces.TailSquareDescentAnalytic
import NLS.ZakharovShabat.SourceFrequencyFrechetDescent

/-! # Jointly analytic actual frequency descent

The actual frequency and refined correction descend to jointly analytic
maps on one common open mixed-coordinate domain, in every admissible
target sequence norm. These are Banach power-series statements and retain
the exact source recovery formulas. Descent to quadratic actions and
gluing the local maps remain to be proved.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- The actual frequency and correction have joint Banach-space analytic
descents on a common open mixed-coordinate domain, with exact recovery. -/
theorem exists_sourceFrequency_analyticTailSquareDescent (hp : p ≠ ⊤) (hp1 : 1 < p) :
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
          AnalyticOnNhd ℂ G (Q '' V) ∧
          ∀ z ∈ V, G (Q z) = A.frequencySequence r (C.inverse z) ∧
            ∀ n, G (Q z) n = A.renormalizedFrequency n (C.inverse z)) ∧
        (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
          let G := Coeff.tailSquareDescent (q := q) S (A.actionFrequencyCorrectionSequence r ∘ C.inverse) V
          AnalyticOnNhd ℂ (A.actionFrequencyCorrectionSequence r ∘ C.inverse) V ∧
          AnalyticOnNhd ℂ G (Q '' V) ∧
          ∀ z ∈ V, G (Q z) = A.actionFrequencyCorrectionSequence r (C.inverse z) ∧
            ∀ n, G (Q z) n = A.renormalizedFrequency n (C.inverse z)+z.1 n^2+z.2 n^2) := by
  obtain ⟨W,s,A,W₀,B,X,t,D,U,hU,hreal,hcharts⟩ :=
    exists_sourceFrequency_frechetTailSquareDescent (q := q) hp hp1
  refine ⟨W,s,A,W₀,B,X,t,D,U,hU,hreal,?_⟩
  intro φ
  obtain ⟨C,S,R,hR,hbase,hball,hQ,hbaseQ,hfreq,hcorr⟩ := hcharts φ
  refine ⟨C,S,R,hR,hbase,hball,hQ,hbaseQ,?_,?_⟩
  · intro r inst hr hr1 hpr
    obtain ⟨ha,hC1,_,_,he⟩ := hfreq r hr hr1 hpr
    refine ⟨ha,?_,he⟩
    exact ComplexAnalysis.analyticOnNhd_of_complexDifferentiableOn _ _ hQ hC1.differentiableOn_one
  · intro r inst hr hr1 hpr
    obtain ⟨ha,hC1,_,_,he⟩ := hcorr r hr hr1 hpr
    refine ⟨ha,?_,he⟩
    exact ComplexAnalysis.analyticOnNhd_of_complexDifferentiableOn _ _ hQ hC1.differentiableOn_one

end NLS.ZakharovShabat
