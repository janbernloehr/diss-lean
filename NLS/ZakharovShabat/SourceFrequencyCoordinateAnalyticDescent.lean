import NLS.SequenceSpaces.TailSquareDescentCoordinateAnalytic
import NLS.ZakharovShabat.SourceFrequencyComplexSignInvariance

/-! # Separate coordinate analyticity of descended frequencies

The actual frequency and refined correction have scalar components analytic
in every retained or squared coordinate, on the same open mixed-coordinate
domain. This includes zero tail entries. Joint Banach analyticity and descent
to quadratic actions are not claimed here.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- One common mixed-coordinate domain supports continuous frequency and
correction sequences, exact recovery, finite-head analyticity in norm, and
scalar separate analyticity in every coordinate of both components. -/
theorem exists_sourceFrequency_coordinateAnalyticTailSquareDescent (hp : p ≠ ⊤) (hp1 : 1 < p) :
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
          (∀ z ∈ V, ∀ (second : Bool) (k n : ℤ),
            AnalyticAt ℂ (fun v : ℂ => G (Q z+Coeff.pairSingleCLM q second k v) n) 0) ∧
          ∀ z ∈ V, G (Q z) = A.frequencySequence r (C.inverse z) ∧
            ∀ n, G (Q z) n = A.renormalizedFrequency n (C.inverse z)) ∧
        (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
          let G := Coeff.tailSquareDescent (q := q) S (A.actionFrequencyCorrectionSequence r ∘ C.inverse) V
          AnalyticOnNhd ℂ (A.actionFrequencyCorrectionSequence r ∘ C.inverse) V ∧
          ContinuousOn G (Q '' V) ∧
          (∀ z ∈ V, AnalyticAt ℂ (fun b : Coeff q × Coeff q => G (Q z+Coeff.truncatePair S b)) 0) ∧
          (∀ z ∈ V, ∀ (second : Bool) (k n : ℤ),
            AnalyticAt ℂ (fun v : ℂ => G (Q z+Coeff.pairSingleCLM q second k v) n) 0) ∧
          ∀ z ∈ V, G (Q z) = A.actionFrequencyCorrectionSequence r (C.inverse z) ∧
            ∀ n, G (Q z) n = A.renormalizedFrequency n (C.inverse z)+z.1 n^2+z.2 n^2) := by
  obtain ⟨W,s,A,W₀,B,X,t,D,U,hU,hreal,hcharts⟩ := exists_sourceFrequency_complexTailSignInvariant hp hp1
  refine ⟨W,s,A,W₀,B,X,t,D,U,hU,hreal,?_⟩
  intro φ
  obtain ⟨C,S,R,hR,hbase,hball,hfreq,hcorr⟩ := hcharts φ
  refine ⟨C,S,R,hR,hbase,hball,
    Coeff.isOpenMap_pairMixedSquare hp S _ isOpen_ball,⟨_,hbase,rfl⟩,?_,?_⟩
  · intro r inst hr hr1 hpr
    obtain ⟨ha,he,hi⟩ := hfreq r hr hr1 hpr
    refine ⟨ha,Coeff.continuousOn_tailSquareDescent hp S _ _ isOpen_ball ha.continuousOn hi,
      Coeff.analyticAt_tailSquareDescent_finiteHead S _ _ isOpen_ball ha hi,
      fun z hz second k n => Coeff.analyticAt_tailSquareDescent_coordinate S _ _ isOpen_ball ha hi
        z hz second k (lp.evalCLM ℂ (fun _ : ℤ => ℂ) r n),?_⟩
    intro z hz
    have h := Coeff.tailSquareDescent_apply (q := q) S (A.frequencySequence r ∘ C.inverse) _ hi z hz
    exact ⟨h,fun n => (congrArg (fun a : Coeff r => a n) h).trans (he z hz n)⟩
  · intro r inst hr hr1 hpr
    obtain ⟨ha,he,hi⟩ := hcorr r hr hr1 hpr
    refine ⟨ha,Coeff.continuousOn_tailSquareDescent hp S _ _ isOpen_ball ha.continuousOn hi,
      Coeff.analyticAt_tailSquareDescent_finiteHead S _ _ isOpen_ball ha hi,
      fun z hz second k n => Coeff.analyticAt_tailSquareDescent_coordinate S _ _ isOpen_ball ha hi
        z hz second k (lp.evalCLM ℂ (fun _ : ℤ => ℂ) r n),?_⟩
    intro z hz
    have h := Coeff.tailSquareDescent_apply (q := q) S (A.actionFrequencyCorrectionSequence r ∘ C.inverse) _ hi z hz
    exact ⟨h,fun n => (congrArg (fun a : Coeff r => a n) h).trans (he z hz n)⟩

end NLS.ZakharovShabat
