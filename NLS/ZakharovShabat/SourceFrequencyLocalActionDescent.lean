import NLS.SequenceSpaces.LocalHeadActionDescent
import NLS.ZakharovShabat.SourceFrequencyLocalTailSumDescent

/-! # Local analytic frequency maps on the full action space

The tail and head descents combine to give actual sequence-valued analytic
functions of the quadratic actions on one common open neighborhood of
each real base action. Recovery holds at every point of an open original
Birkhoff neighborhood, in all admissible target norms simultaneously.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

set_option maxHeartbeats 800000 in
/-- The actual frequency and refined correction have local analytic
factors through the full quadratic action sequence, with exact recovery. -/
theorem exists_sourceFrequency_normalizedLocalActionDescent (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ A : SourceAbelianMomentAtlas hp hp1 W s,
    ∃ P : Set (CoeffPair p), SourcePsiIsolatingComplexExtension hp hp1 P s ∧
    ∃ W₀ B X : Set (CoeffPair p), ∃ t : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t,
    ∃ U : Set (CoeffPair p), IsOpen U ∧ realTypeSourceLocus p ⊆ U ∧
      ∀ φ : realTypeSourceSubmodule p, ∃ C : SourceBirkhoffInverseChart D φ U,
        ∃ S : Finset ℤ, ∃ R : ℝ,
        let z₀ := sourceBirkhoffMap hp hp1 t φ.val
        let V := ball (Coeff.truncatePair S z₀) R
        let Q := Coeff.pairMixedSquare (p := p) (q := q) S
        ∃ L : Coeff.TailSumChart S (Q '' V) (Q z₀),
        ∃ K : Coeff.HeadActionChart S L.target (Coeff.tailSumCLM S (Q z₀)),
        let Z := (V ∩ Q ⁻¹' L.source) ∩ (fun z => Coeff.tailSumCLM S (Q z)) ⁻¹' K.source
        0 < R ∧ V ⊆ C.target ∧ IsOpen Z ∧ z₀ ∈ Z ∧
        quadraticActionsExponent (q := q) '' Z = K.target ∧
        (∀ z ∈ Z, quadraticActionsExponent (q := q) z ∈ K.target) ∧
        (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
          let G := L.factor (Coeff.tailSquareDescent (q := q) S (A.frequencySequence r ∘ C.inverse) V)
          AnalyticOnNhd ℂ (K.factor G) K.target ∧
          ∀ z ∈ Z, K.factor G (quadraticActionsExponent z) = A.frequencySequence r (C.inverse z) ∧
            ∀ n, K.factor G (quadraticActionsExponent z) n = A.renormalizedFrequency n (C.inverse z)) ∧
        (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
          let G := L.factor (Coeff.tailSquareDescent (q := q) S (A.actionFrequencyCorrectionSequence r ∘ C.inverse) V)
          AnalyticOnNhd ℂ (K.factor G) K.target ∧
          ∀ z ∈ Z, K.factor G (quadraticActionsExponent z) = A.actionFrequencyCorrectionSequence r (C.inverse z) ∧
            ∀ n, K.factor G (quadraticActionsExponent z) n =
              A.renormalizedFrequency n (C.inverse z)+z.1 n^2+z.2 n^2) := by
  obtain ⟨W,s,A,P,hs,W₀,B,X,t,D,U,hU,hreal,hcharts⟩ :=
    exists_sourceFrequency_normalizedLocalTailSumDescent (q := q) hp hp1
  refine ⟨W,s,A,P,hs,W₀,B,X,t,D,U,hU,hreal,?_⟩
  intro φ
  obtain ⟨C,S,R,L,hR,hball,hZ,hbase,hhead,hmap,hfreq,hcorr⟩ := hcharts φ
  let z₀ := sourceBirkhoffMap hp hp1 t φ.val
  let Q := Coeff.pairMixedSquare (p := p) (q := q) S
  let a := Coeff.tailSumCLM S (Q z₀)
  have ha : Coeff.HeadNonzero S a := Coeff.headNonzero_tailSum_mixedSquare S z₀ hhead
  obtain ⟨K⟩ := Coeff.exists_headActionChart S a ha L.target L.target_open (hmap z₀ hbase)
  have hQ : Continuous Q := continuousOn_univ.mp (Coeff.analyticOnNhd_pairMixedSquare S).continuousOn
  have hPQ : Continuous (fun z => Coeff.tailSumCLM S (Q z)) := (Coeff.tailSumCLM S).continuous.comp hQ
  refine ⟨C,S,R,L,K,hR,hball,hZ.inter (K.source_open.preimage hPQ),⟨hbase,K.base_mem⟩,?_,?_,?_,?_⟩
  · apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      simpa only [Q,Coeff.headActions_tailSum_mixedSquare] using K.map_mem (Coeff.tailSumCLM S (Q z)) hz.2
    · intro b hb
      let w := Coeff.headActionSection S a b
      have hw : w ∈ K.source := K.section_mem b hb
      obtain ⟨z,hz,hQz⟩ := L.source_subset (L.section_mem w (K.source_subset hw))
      change Q z = Coeff.tailSumSection S (Q z₀) w at hQz
      have hPz : Coeff.tailSumCLM S (Q z) = w := by rw [hQz,Coeff.tailSum_section]
      refine ⟨z,⟨⟨hz,?_⟩,?_⟩,?_⟩
      · change Q z ∈ L.source
        rw [hQz]
        exact L.section_mem w (K.source_subset hw)
      · change Coeff.tailSumCLM S (Q z) ∈ K.source
        simpa only [hPz] using hw
      · rw [← Coeff.headActions_tailSum_mixedSquare S z,hPz]
        exact Coeff.headActions_section S a K.head_nonzero b
  · intro z hz
    simpa only [Q,Coeff.headActions_tailSum_mixedSquare] using K.map_mem (Coeff.tailSumCLM S (Q z)) hz.2
  · intro r inst hr hr1 hpr
    obtain ⟨_,_,hG,hrot,he⟩ := hfreq r hr hr1 hpr
    refine ⟨K.analyticOnNhd_factor _ hG,?_⟩
    intro z hz
    have hrec := K.factor_apply L.target_open _ hG.differentiableOn hrot (Coeff.tailSumCLM S (Q z)) hz.2
    rw [Coeff.headActions_tailSum_mixedSquare] at hrec
    obtain ⟨hs,hn⟩ := he z hz.1
    exact ⟨hrec.trans hs,fun n => (congrArg (fun b : Coeff r => b n) hrec).trans (hn n)⟩
  · intro r inst hr hr1 hpr
    obtain ⟨_,_,hG,hrot,he⟩ := hcorr r hr hr1 hpr
    refine ⟨K.analyticOnNhd_factor _ hG,?_⟩
    intro z hz
    have hrec := K.factor_apply L.target_open _ hG.differentiableOn hrot (Coeff.tailSumCLM S (Q z)) hz.2
    rw [Coeff.headActions_tailSum_mixedSquare] at hrec
    obtain ⟨hs,hn⟩ := he z hz.1
    exact ⟨hrec.trans hs,fun n => (congrArg (fun b : Coeff r => b n) hrec).trans (hn n)⟩

/-- The original local descent interface, with the normalization witness omitted. -/
theorem exists_sourceFrequency_localActionDescent (hp : p ≠ ⊤) (hp1 : 1 < p) :
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
        ∃ K : Coeff.HeadActionChart S L.target (Coeff.tailSumCLM S (Q z₀)),
        let Z := (V ∩ Q ⁻¹' L.source) ∩ (fun z => Coeff.tailSumCLM S (Q z)) ⁻¹' K.source
        0 < R ∧ V ⊆ C.target ∧ IsOpen Z ∧ z₀ ∈ Z ∧
        quadraticActionsExponent (q := q) '' Z = K.target ∧
        (∀ z ∈ Z, quadraticActionsExponent (q := q) z ∈ K.target) ∧
        (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
          let G := L.factor (Coeff.tailSquareDescent (q := q) S (A.frequencySequence r ∘ C.inverse) V)
          AnalyticOnNhd ℂ (K.factor G) K.target ∧
          ∀ z ∈ Z, K.factor G (quadraticActionsExponent z) = A.frequencySequence r (C.inverse z) ∧
            ∀ n, K.factor G (quadraticActionsExponent z) n = A.renormalizedFrequency n (C.inverse z)) ∧
        (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
          let G := L.factor (Coeff.tailSquareDescent (q := q) S (A.actionFrequencyCorrectionSequence r ∘ C.inverse) V)
          AnalyticOnNhd ℂ (K.factor G) K.target ∧
          ∀ z ∈ Z, K.factor G (quadraticActionsExponent z) = A.actionFrequencyCorrectionSequence r (C.inverse z) ∧
            ∀ n, K.factor G (quadraticActionsExponent z) n =
              A.renormalizedFrequency n (C.inverse z)+z.1 n^2+z.2 n^2) := by
  obtain ⟨W,s,A,P,hs,hrest⟩ := exists_sourceFrequency_normalizedLocalActionDescent (q := q) hp hp1
  exact ⟨W,s,A,hrest⟩

end NLS.ZakharovShabat
