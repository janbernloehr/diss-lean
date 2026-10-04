import NLS.SequenceSpaces.LocalTailSumDescent
import NLS.SequenceSpaces.HeadRotationDescent
import NLS.ZakharovShabat.SourceFrequencyTailActionStationarity

/-! # Local analytic frequency maps in tail-sum coordinates

The actual frequency and refined correction factor analytically through
the retained finite head and one sequence of tail sums. One chart and one
open neighborhood serve every admissible target exponent. The retained
head has not yet been replaced by its quadratic actions.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

set_option maxHeartbeats 800000 in
/-- Local analytic factors through the tail sums, with exact recovery of
both actual sequence maps on one common open Birkhoff neighborhood, with
no zero pairs in the retained head. -/
theorem exists_sourceFrequency_headStationaryLocalTailSumDescent (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ A : SourceAbelianMomentAtlas hp hp1 W s,
    ∃ W₀ B X : Set (CoeffPair p), ∃ t : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t,
    ∃ U : Set (CoeffPair p), IsOpen U ∧ realTypeSourceLocus p ⊆ U ∧
      ∀ φ : realTypeSourceSubmodule p, ∃ C : SourceBirkhoffInverseChart D φ U,
        ∃ S : Finset ℤ, ∃ R : ℝ,
        let z₀ := sourceBirkhoffMap hp hp1 t φ.val
        let V := ball (Coeff.truncatePair S z₀) R
        let Q := Coeff.pairMixedSquare (p := p) (q := q) S
        ∃ L : Coeff.TailSumChart S (Q '' V) (Q z₀),
        let Z := V ∩ Q ⁻¹' L.source
        0 < R ∧ V ⊆ C.target ∧ IsOpen Z ∧ z₀ ∈ Z ∧ (∀ k ∈ S, z₀.1 k ≠ 0 ∨ z₀.2 k ≠ 0) ∧
        (∀ z ∈ Z, Coeff.tailSumCLM S (Q z) ∈ L.target) ∧
        (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
          let G := Coeff.tailSquareDescent (q := q) S (A.frequencySequence r ∘ C.inverse) V
          AnalyticOnNhd ℂ (A.frequencySequence r ∘ C.inverse) V ∧
          (∀ z ∈ V, ∀ k, fderiv ℂ (A.frequencySequence r ∘ C.inverse) z
            (Coeff.actionRotationVectorCLM p k z) = 0) ∧
          AnalyticOnNhd ℂ (L.factor G) L.target ∧
          (∀ w ∈ L.target, ∀ k : S, fderiv ℂ (L.factor G) w (Coeff.headRotationVector S k w) = 0) ∧
          ∀ z ∈ Z, L.factor G (Coeff.tailSumCLM S (Q z)) = A.frequencySequence r (C.inverse z) ∧
            ∀ n, L.factor G (Coeff.tailSumCLM S (Q z)) n = A.renormalizedFrequency n (C.inverse z)) ∧
        (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
          let G := Coeff.tailSquareDescent (q := q) S (A.actionFrequencyCorrectionSequence r ∘ C.inverse) V
          AnalyticOnNhd ℂ (A.actionFrequencyCorrectionSequence r ∘ C.inverse) V ∧
          (∀ z ∈ V, ∀ k, fderiv ℂ (A.actionFrequencyCorrectionSequence r ∘ C.inverse) z
            (Coeff.actionRotationVectorCLM p k z) = 0) ∧
          AnalyticOnNhd ℂ (L.factor G) L.target ∧
          (∀ w ∈ L.target, ∀ k : S, fderiv ℂ (L.factor G) w (Coeff.headRotationVector S k w) = 0) ∧
          ∀ z ∈ Z, L.factor G (Coeff.tailSumCLM S (Q z)) = A.actionFrequencyCorrectionSequence r (C.inverse z) ∧
            ∀ n, L.factor G (Coeff.tailSumCLM S (Q z)) n =
              A.renormalizedFrequency n (C.inverse z)+z.1 n^2+z.2 n^2) := by
  obtain ⟨W,s,A,W₀,B,X,t,D,U,hU,hreal,hcharts⟩ :=
    exists_sourceFrequency_nonzeroHeadTailActionDescent (q := q) hp hp1
  refine ⟨W,s,A,W₀,B,X,t,D,U,hU,hreal,?_⟩
  intro φ
  obtain ⟨C,S,R,hR,hbase,hball,hopen,himage,hhead,hfreq,hcorr⟩ := hcharts φ
  let z₀ := sourceBirkhoffMap hp hp1 t φ.val
  let V := ball (Coeff.truncatePair S z₀) R
  let Q := Coeff.pairMixedSquare (p := p) (q := q) S
  obtain ⟨L⟩ := Coeff.exists_tailSumChart S (Q '' V) hopen (Q z₀) himage
  have hQ : Continuous Q := continuousOn_univ.mp (Coeff.analyticOnNhd_pairMixedSquare S).continuousOn
  refine ⟨C,S,R,L,hR,hball,isOpen_ball.inter (L.source_open.preimage hQ),
    ⟨hbase,L.base_mem⟩,hhead,fun z hz => L.map_mem (Q z) hz.2,?_,?_⟩
  · intro r inst hr hr1 hpr
    obtain ⟨ha,hrot,hG,hD,_,he⟩ := hfreq r hr hr1 hpr
    refine ⟨ha,hrot,L.analyticOnNhd_factor _ hG,?_,?_⟩
    · intro w hw k
      exact Coeff.fderiv_tailSumFactor_headRotation_eq_zero (Coeff.doublingExponent_ne_top hp)
        S _ _ V isOpen_ball hopen ha.differentiableOn hG (fun z hz => (he z hz).1) hD hrot (Q z₀) L w hw k
    · intro z hz
      have hrec := L.factor_apply (Coeff.doublingExponent_ne_top hp) hopen _ hG.differentiableOn hD (Q z) hz.2
      obtain ⟨hs,hn⟩ := he z hz.1
      exact ⟨hrec.trans hs,fun n => (congrArg (fun a : Coeff r => a n) hrec).trans (hn n)⟩
  · intro r inst hr hr1 hpr
    obtain ⟨ha,hrot,hG,hD,_,he⟩ := hcorr r hr hr1 hpr
    refine ⟨ha,hrot,L.analyticOnNhd_factor _ hG,?_,?_⟩
    · intro w hw k
      exact Coeff.fderiv_tailSumFactor_headRotation_eq_zero (Coeff.doublingExponent_ne_top hp)
        S _ _ V isOpen_ball hopen ha.differentiableOn hG (fun z hz => (he z hz).1) hD hrot (Q z₀) L w hw k
    · intro z hz
      have hrec := L.factor_apply (Coeff.doublingExponent_ne_top hp) hopen _ hG.differentiableOn hD (Q z) hz.2
      obtain ⟨hs,hn⟩ := he z hz.1
      exact ⟨hrec.trans hs,fun n => (congrArg (fun a : Coeff r => a n) hrec).trans (hn n)⟩

/-- The nonzero-head chart remains available without exposing its
additional head-rotation stationarity identities. -/
theorem exists_sourceFrequency_nonzeroHeadLocalTailSumDescent (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ A : SourceAbelianMomentAtlas hp hp1 W s,
    ∃ W₀ B X : Set (CoeffPair p), ∃ t : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t,
    ∃ U : Set (CoeffPair p), IsOpen U ∧ realTypeSourceLocus p ⊆ U ∧
      ∀ φ : realTypeSourceSubmodule p, ∃ C : SourceBirkhoffInverseChart D φ U,
        ∃ S : Finset ℤ, ∃ R : ℝ,
        let z₀ := sourceBirkhoffMap hp hp1 t φ.val
        let V := ball (Coeff.truncatePair S z₀) R
        let Q := Coeff.pairMixedSquare (p := p) (q := q) S
        ∃ L : Coeff.TailSumChart S (Q '' V) (Q z₀),
        let Z := V ∩ Q ⁻¹' L.source
        0 < R ∧ V ⊆ C.target ∧ IsOpen Z ∧ z₀ ∈ Z ∧ (∀ k ∈ S, z₀.1 k ≠ 0 ∨ z₀.2 k ≠ 0) ∧
        (∀ z ∈ Z, Coeff.tailSumCLM S (Q z) ∈ L.target) ∧
        (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
          let G := Coeff.tailSquareDescent (q := q) S (A.frequencySequence r ∘ C.inverse) V
          AnalyticOnNhd ℂ (A.frequencySequence r ∘ C.inverse) V ∧
          (∀ z ∈ V, ∀ k, fderiv ℂ (A.frequencySequence r ∘ C.inverse) z
            (Coeff.actionRotationVectorCLM p k z) = 0) ∧
          AnalyticOnNhd ℂ (L.factor G) L.target ∧
          ∀ z ∈ Z, L.factor G (Coeff.tailSumCLM S (Q z)) = A.frequencySequence r (C.inverse z) ∧
            ∀ n, L.factor G (Coeff.tailSumCLM S (Q z)) n = A.renormalizedFrequency n (C.inverse z)) ∧
        (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
          let G := Coeff.tailSquareDescent (q := q) S (A.actionFrequencyCorrectionSequence r ∘ C.inverse) V
          AnalyticOnNhd ℂ (A.actionFrequencyCorrectionSequence r ∘ C.inverse) V ∧
          (∀ z ∈ V, ∀ k, fderiv ℂ (A.actionFrequencyCorrectionSequence r ∘ C.inverse) z
            (Coeff.actionRotationVectorCLM p k z) = 0) ∧
          AnalyticOnNhd ℂ (L.factor G) L.target ∧
          ∀ z ∈ Z, L.factor G (Coeff.tailSumCLM S (Q z)) = A.actionFrequencyCorrectionSequence r (C.inverse z) ∧
            ∀ n, L.factor G (Coeff.tailSumCLM S (Q z)) n =
              A.renormalizedFrequency n (C.inverse z)+z.1 n^2+z.2 n^2) := by
  obtain ⟨W,s,A,W₀,B,X,t,D,U,hU,hreal,hcharts⟩ :=
    exists_sourceFrequency_headStationaryLocalTailSumDescent (q := q) hp hp1
  refine ⟨W,s,A,W₀,B,X,t,D,U,hU,hreal,?_⟩
  intro φ
  obtain ⟨C,S,R,L,hR,hball,hZ,hbase,hhead,hmap,hfreq,hcorr⟩ := hcharts φ
  refine ⟨C,S,R,L,hR,hball,hZ,hbase,hhead,hmap,?_,?_⟩
  · intro r inst hr hr1 hpr
    obtain ⟨ha,hrot,hG,_,he⟩ := hfreq r hr hr1 hpr
    exact ⟨ha,hrot,hG,he⟩
  · intro r inst hr hr1 hpr
    obtain ⟨ha,hrot,hG,_,he⟩ := hcorr r hr hr1 hpr
    exact ⟨ha,hrot,hG,he⟩

/-- Compatibility form of local tail-sum descent, without the extra
nonzero-head guarantee. -/
theorem exists_sourceFrequency_localTailSumDescent (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ A : SourceAbelianMomentAtlas hp hp1 W s,
    ∃ W₀ B X : Set (CoeffPair p), ∃ t : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t,
    ∃ U : Set (CoeffPair p), IsOpen U ∧ realTypeSourceLocus p ⊆ U ∧
      ∀ φ : realTypeSourceSubmodule p, ∃ C : SourceBirkhoffInverseChart D φ U,
        ∃ S : Finset ℤ, ∃ R : ℝ,
        let z₀ := sourceBirkhoffMap hp hp1 t φ.val
        let V := ball (Coeff.truncatePair S z₀) R
        let Q := Coeff.pairMixedSquare (p := p) (q := q) S
        ∃ L : Coeff.TailSumChart S (Q '' V) (Q z₀),
        let Z := V ∩ Q ⁻¹' L.source
        0 < R ∧ V ⊆ C.target ∧ IsOpen Z ∧ z₀ ∈ Z ∧
        (∀ z ∈ Z, Coeff.tailSumCLM S (Q z) ∈ L.target) ∧
        (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
          let G := Coeff.tailSquareDescent (q := q) S (A.frequencySequence r ∘ C.inverse) V
          AnalyticOnNhd ℂ (A.frequencySequence r ∘ C.inverse) V ∧
          (∀ z ∈ V, ∀ k, fderiv ℂ (A.frequencySequence r ∘ C.inverse) z
            (Coeff.actionRotationVectorCLM p k z) = 0) ∧
          AnalyticOnNhd ℂ (L.factor G) L.target ∧
          ∀ z ∈ Z, L.factor G (Coeff.tailSumCLM S (Q z)) = A.frequencySequence r (C.inverse z) ∧
            ∀ n, L.factor G (Coeff.tailSumCLM S (Q z)) n = A.renormalizedFrequency n (C.inverse z)) ∧
        (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
          let G := Coeff.tailSquareDescent (q := q) S (A.actionFrequencyCorrectionSequence r ∘ C.inverse) V
          AnalyticOnNhd ℂ (A.actionFrequencyCorrectionSequence r ∘ C.inverse) V ∧
          (∀ z ∈ V, ∀ k, fderiv ℂ (A.actionFrequencyCorrectionSequence r ∘ C.inverse) z
            (Coeff.actionRotationVectorCLM p k z) = 0) ∧
          AnalyticOnNhd ℂ (L.factor G) L.target ∧
          ∀ z ∈ Z, L.factor G (Coeff.tailSumCLM S (Q z)) = A.actionFrequencyCorrectionSequence r (C.inverse z) ∧
            ∀ n, L.factor G (Coeff.tailSumCLM S (Q z)) n =
              A.renormalizedFrequency n (C.inverse z)+z.1 n^2+z.2 n^2) := by
  obtain ⟨W,s,A,W₀,B,X,t,D,U,hU,hreal,hcharts⟩ :=
    exists_sourceFrequency_nonzeroHeadLocalTailSumDescent (q := q) hp hp1
  refine ⟨W,s,A,W₀,B,X,t,D,U,hU,hreal,?_⟩
  intro φ
  obtain ⟨C,S,R,L,hR,hball,hZ,hbase,_,hmap,hfreq,hcorr⟩ := hcharts φ
  exact ⟨C,S,R,L,hR,hball,hZ,hbase,hmap,hfreq,hcorr⟩

end NLS.ZakharovShabat
