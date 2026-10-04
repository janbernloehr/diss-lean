import NLS.SequenceSpaces.TailSquareDescentAnalyticSlice
import NLS.ZakharovShabat.SourceFrequencyCoordinateAnalyticDescent

/-! # Analytic sequence-valued coordinate slices of actual frequencies

The actual descended frequency and refined correction are analytic in their
full target sequence norms along every individual mixed-coordinate line.
Each statement holds on the entire open preimage of the common domain,
including zero tail coordinates. Joint source-space analyticity and descent
to quadratic actions remain to be proved.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- On one common mixed-coordinate domain, the actual frequency and
correction sequences have analytic coordinate slices in the full target
norm, retaining exact recovery and finite-head analyticity. -/
theorem exists_sourceFrequency_analyticSliceTailSquareDescent (hp : p ≠ ⊤) (hp1 : 1 < p) :
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
          (∀ (b : Coeff q × Coeff q) (second : Bool) (k : ℤ),
            AnalyticOnNhd ℂ (fun v : ℂ => G (b+Coeff.pairSingleCLM q second k v))
              ((fun v : ℂ => b+Coeff.pairSingleCLM q second k v) ⁻¹' (Q '' V))) ∧
          ∀ z ∈ V, G (Q z) = A.frequencySequence r (C.inverse z) ∧
            ∀ n, G (Q z) n = A.renormalizedFrequency n (C.inverse z)) ∧
        (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
          let G := Coeff.tailSquareDescent (q := q) S (A.actionFrequencyCorrectionSequence r ∘ C.inverse) V
          AnalyticOnNhd ℂ (A.actionFrequencyCorrectionSequence r ∘ C.inverse) V ∧
          ContinuousOn G (Q '' V) ∧
          (∀ z ∈ V, AnalyticAt ℂ (fun b : Coeff q × Coeff q => G (Q z+Coeff.truncatePair S b)) 0) ∧
          (∀ (b : Coeff q × Coeff q) (second : Bool) (k : ℤ),
            AnalyticOnNhd ℂ (fun v : ℂ => G (b+Coeff.pairSingleCLM q second k v))
              ((fun v : ℂ => b+Coeff.pairSingleCLM q second k v) ⁻¹' (Q '' V))) ∧
          ∀ z ∈ V, G (Q z) = A.actionFrequencyCorrectionSequence r (C.inverse z) ∧
            ∀ n, G (Q z) n = A.renormalizedFrequency n (C.inverse z)+z.1 n^2+z.2 n^2) := by
  obtain ⟨W,s,A,W₀,B,X,t,D,U,hU,hreal,hcharts⟩ :=
    exists_sourceFrequency_coordinateAnalyticTailSquareDescent (q := q) hp hp1
  refine ⟨W,s,A,W₀,B,X,t,D,U,hU,hreal,?_⟩
  intro φ
  obtain ⟨C,S,R,hR,hbase,hball,hQ,hbaseQ,hfreq,hcorr⟩ := hcharts φ
  refine ⟨C,S,R,hR,hbase,hball,hQ,hbaseQ,?_,?_⟩
  · intro r inst hr hr1 hpr
    obtain ⟨ha,hcont,hhead,hscalar,he⟩ := hfreq r hr hr1 hpr
    refine ⟨ha,hcont,hhead,?_,he⟩
    intro b second k
    apply Coeff.analyticOnNhd_sequenceSlice _ _ hQ hcont (Coeff.pairSingleCLM q second k) _ b
    rintro _ ⟨z,hz,rfl⟩ n
    exact hscalar z hz second k n
  · intro r inst hr hr1 hpr
    obtain ⟨ha,hcont,hhead,hscalar,he⟩ := hcorr r hr hr1 hpr
    refine ⟨ha,hcont,hhead,?_,he⟩
    intro b second k
    apply Coeff.analyticOnNhd_sequenceSlice _ _ hQ hcont (Coeff.pairSingleCLM q second k) _ b
    rintro _ ⟨z,hz,rfl⟩ n
    exact hscalar z hz second k n

end NLS.ZakharovShabat
