import NLS.ZakharovShabat.SourceRealActionLifting
import NLS.ZakharovShabat.SourceFrequencyLocalActionDescent

/-! # Local frequency maps compatible with every real action representative

The common local action domains can be restricted to balls on which every
nonnegative action has a real source representative. Each local frequency
or correction factor recovers its actual value at every real source with
actions in the ball, regardless of which inverse chart supplied the factor.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

set_option maxHeartbeats 800000 in
/-- One family of action balls supports all frequency and refined correction
targets, with real source realization and chart-independent real recovery. -/
theorem exists_sourceFrequency_realActionBalls (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ A : SourceAbelianMomentAtlas hp hp1 W s,
    ∃ P : Set (CoeffPair p), SourcePsiIsolatingComplexExtension hp hp1 P s ∧
    ∃ W₀ B X : Set (CoeffPair p), ∃ t : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ _D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t,
      (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
        ∀ ψ : realTypeSourceSubmodule p, ∀ n, A.frequencySequence r ψ.val n = A.renormalizedFrequency n ψ.val) ∧
      (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
        ∀ ψ : realTypeSourceSubmodule p, ∀ n, A.actionFrequencyCorrectionSequence r ψ.val n =
          A.renormalizedFrequency n ψ.val+2*sourceActionSequence (q := q) hp hp1 t ψ.val n) ∧
      ∀ φ : realTypeSourceSubmodule p, ∃ R : ℝ, 0 < R ∧
        (∀ b ∈ ball (sourceActionSequence (q := q) hp hp1 t φ.val) R,
          ∃ ψ ∈ X, sourceActionSequence (q := q) hp hp1 t ψ = b) ∧
        (∀ b ∈ ball (sourceActionSequence (q := q) hp hp1 t φ.val) R,
          b ∈ Coeff.nonnegativeLocus q → ∃ ψ : realTypeSourceSubmodule p,
            sourceActionSequence (q := q) hp hp1 t ψ.val = b) ∧
        (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
          ∃ F : Coeff q → Coeff r,
            AnalyticOnNhd ℂ F (ball (sourceActionSequence (q := q) hp hp1 t φ.val) R) ∧
            ∀ ψ : realTypeSourceSubmodule p, sourceActionSequence (q := q) hp hp1 t ψ.val ∈
              ball (sourceActionSequence (q := q) hp hp1 t φ.val) R →
              F (sourceActionSequence (q := q) hp hp1 t ψ.val) = A.frequencySequence r ψ.val) ∧
        (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
          ∃ H : Coeff q → Coeff r,
            AnalyticOnNhd ℂ H (ball (sourceActionSequence (q := q) hp hp1 t φ.val) R) ∧
            ∀ ψ : realTypeSourceSubmodule p, sourceActionSequence (q := q) hp hp1 t ψ.val ∈
              ball (sourceActionSequence (q := q) hp hp1 t φ.val) R →
              H (sourceActionSequence (q := q) hp hp1 t ψ.val) = A.actionFrequencyCorrectionSequence r ψ.val) := by
  obtain ⟨W,s,A,P,hs,W₀,B,X,t,D,U,_,_,hcharts⟩ :=
    exists_sourceFrequency_normalizedLocalActionDescent (q := q) hp hp1
  refine ⟨W,s,A,P,hs,W₀,B,X,t,D,?_,?_,?_⟩
  · intro r inst hr hr1 hpr ψ n
    obtain ⟨C,S,R,L,K,_,_,_,hbase,_,_,hfreq,_⟩ := hcharts ψ
    obtain ⟨_,hrec⟩ := hfreq r hr hr1 hpr
    obtain ⟨he, hn⟩ := hrec _ hbase
    have h := (congrArg (fun a : Coeff r => a n) he).symm.trans (hn n)
    simpa only [C.base_eq] using h
  · intro r inst hr hr1 hpr ψ n
    obtain ⟨C,S,R,L,K,_,_,_,hbase,_,_,_,hcorr⟩ := hcharts ψ
    obtain ⟨_,hrec⟩ := hcorr r hr hr1 hpr
    obtain ⟨he, hn⟩ := hrec _ hbase
    have h := (congrArg (fun a : Coeff r => a n) he).symm.trans (hn n)
    simp only [C.base_eq] at h
    rw [h, sourceActionSequence, quadraticActionsExponent_apply]
    ring
  · intro φ
    obtain ⟨C,S,R,L,K,_,hVC,hZ,hbase,himage,hmap,hfreq,hcorr⟩ := hcharts φ
    let z₀ := sourceBirkhoffMap hp hp1 t φ.val
    let V := ball (Coeff.truncatePair S z₀) R
    let Q := Coeff.pairMixedSquare (p := p) (q := q) S
    let Z := (V ∩ Q ⁻¹' L.source) ∩ (fun z => Coeff.tailSumCLM S (Q z)) ⁻¹' K.source
    have hZC : Z ⊆ C.target := fun _ hz => hVC hz.1.1
    obtain ⟨ρ,hρ,hball,hlift⟩ := D.exists_realAction_ball φ Z hZ hbase K.target K.target_open (hmap _ hbase)
    refine ⟨ρ,hρ,?_,?_,?_,?_⟩
    · intro b hb
      obtain ⟨z,hz,he⟩ := himage.symm ▸ hball hb
      exact ⟨C.inverse z,(C.image_subset (hZC hz)).1,(C.actionSequence_eq z (hZC hz)).trans he⟩
    · intro b hb hpos
      obtain ⟨z,⟨hz,hzr⟩,he⟩ := hlift ⟨hb,hpos⟩
      obtain ⟨w,hw⟩ := (Coeff.mem_realPairLocus_iff z).mp hzr
      have hreal : C.inverse z ∈ realTypeSourceLocus p := by
        rw [← hw]
        exact C.real_preserving w (hw.symm ▸ hZC hz)
      exact ⟨⟨C.inverse z,hreal⟩,(C.actionSequence_eq z (hZC hz)).trans he⟩
    · intro r inst hr hr1 hpr
      obtain ⟨ha,he⟩ := hfreq r hr hr1 hpr
      refine ⟨_,ha.mono hball,?_⟩
      intro ψ hψ
      exact C.recover_of_real_action_lift Z hZC _ _
        (fun a b hab => A.frequencySequence_real_eq_of_actions A hs hs a b hab r)
        (fun z hz => (he z hz).1) ψ
        (hlift ⟨hψ,D.actionSequence_mem_nonnegativeLocus ψ⟩)
    · intro r inst hr hr1 hpr
      obtain ⟨ha,he⟩ := hcorr r hr hr1 hpr
      refine ⟨_,ha.mono hball,?_⟩
      intro ψ hψ
      exact C.recover_of_real_action_lift Z hZC _ _
        (fun a b hab => A.actionFrequencyCorrectionSequence_real_eq_of_actions A hs hs a b hab r)
        (fun z hz => (he z hz).1) ψ
        (hlift ⟨hψ,D.actionSequence_mem_nonnegativeLocus ψ⟩)

end NLS.ZakharovShabat
