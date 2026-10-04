import NLS.SequenceSpaces.TailActionInvariance
import NLS.ZakharovShabat.SourceFrequencyComplexSignInvariance

/-! # Infinitesimal action invariance of the actual descended frequency

Both analytic mixed-coordinate descents are stationary under arbitrary
tail redistributions preserving the sum of the two squares. The identity
holds at zero tail entries and for infinite-support directions. Complex
rotation stationarity of the lifts follows from real action invariance.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- The actual frequency and correction have analytic descents whose
full derivatives annihilate every action-preserving tail redistribution. -/
theorem exists_sourceFrequency_tailActionStationaryDescent (hp : p ≠ ⊤) (hp1 : 1 < p) :
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
          (∀ z ∈ V, ∀ k, fderiv ℂ (A.frequencySequence r ∘ C.inverse) z
            (Coeff.actionRotationVectorCLM p k z) = 0) ∧
          AnalyticOnNhd ℂ G (Q '' V) ∧
          (∀ b ∈ Q '' V, ∀ k ∉ S,
            fderiv ℂ G b (Coeff.actionSplitDirection q k) = 0) ∧
          (∀ b ∈ Q '' V, ∀ v : Coeff q, (∀ k ∈ S, v k = 0) →
            fderiv ℂ G b (-v,v) = 0) ∧
          ∀ z ∈ V, G (Q z) = A.frequencySequence r (C.inverse z) ∧
            ∀ n, G (Q z) n = A.renormalizedFrequency n (C.inverse z)) ∧
        (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
          let G := Coeff.tailSquareDescent (q := q) S (A.actionFrequencyCorrectionSequence r ∘ C.inverse) V
          AnalyticOnNhd ℂ (A.actionFrequencyCorrectionSequence r ∘ C.inverse) V ∧
          (∀ z ∈ V, ∀ k, fderiv ℂ (A.actionFrequencyCorrectionSequence r ∘ C.inverse) z
            (Coeff.actionRotationVectorCLM p k z) = 0) ∧
          AnalyticOnNhd ℂ G (Q '' V) ∧
          (∀ b ∈ Q '' V, ∀ k ∉ S,
            fderiv ℂ G b (Coeff.actionSplitDirection q k) = 0) ∧
          (∀ b ∈ Q '' V, ∀ v : Coeff q, (∀ k ∈ S, v k = 0) →
            fderiv ℂ G b (-v,v) = 0) ∧
          ∀ z ∈ V, G (Q z) = A.actionFrequencyCorrectionSequence r (C.inverse z) ∧
            ∀ n, G (Q z) n = A.renormalizedFrequency n (C.inverse z)+z.1 n^2+z.2 n^2) := by
  obtain ⟨W,P,s,A,hs,W₀,B,X,t,D,U,hU,hreal,_,hcharts⟩ := exists_sourceFrequency_birkhoffCharts hp hp1
  refine ⟨W,s,A,W₀,B,X,t,D,U,hU,hreal,?_⟩
  intro φ
  obtain ⟨C,hfreq,hcorr,_⟩ := hcharts φ
  obtain ⟨S,R,hR,hbase,hball⟩ := Coeff.exists_finiteCenter_ball hp C.target C.target_open _ C.center_mem
  let c := Coeff.truncatePair S (sourceBirkhoffMap hp hp1 t φ.val)
  have hc : c ∈ Coeff.realPairLocus p :=
    Coeff.truncatePair_mem_realPairLocus S _ ((Coeff.mem_realPairLocus_iff _).mpr
      ⟨sourceRealBirkhoffMap hp hp1 t φ,D.real_map_complex_inclusion φ⟩)
  have hopen := Coeff.isOpenMap_pairMixedSquare (q := q) hp S (ball c R) isOpen_ball
  refine ⟨C,S,R,hR,hbase,hball,hopen,⟨_,hbase,rfl⟩,?_,?_⟩
  · intro r inst hr hr1 hpr
    obtain ⟨ha,he⟩ := hfreq r hr hr1 hpr
    have hrealInv := fun a b hab => A.frequencySequence_real_eq_of_actions A hs hs a b hab r
    have hsign : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
        ∀ z ∈ ball c R, (A.frequencySequence r ∘ C.inverse) (Coeff.pairSignChange e d z) =
          (A.frequencySequence r ∘ C.inverse) z := by
      intro e d he hd z hz
      exact C.complex_sign_invariance _ ha hrealInv c hc R hR hball e d
        (Coeff.pairSignChange_truncatePair S _ e d he hd) z hz
    have hrot : ∀ z ∈ ball c R, ∀ k, fderiv ℂ (A.frequencySequence r ∘ C.inverse) z
        (Coeff.actionRotationVectorCLM p k z) = 0 := by
      intro z hz k
      exact Coeff.fderiv_actionRotationVector_eq_zero_of_real_action_invariance _ _ isOpen_ball
        (convex_ball c R) c (mem_ball_self hR) hc (ha.mono hball)
        (fun a ha b hb har hbr he => C.lifted_real_action_invariance _ hrealInv a b
          (hball ha) (hball hb) har hbr he) z hz k
    have hsplit := Coeff.fderiv_tailSquareDescent_actionSplit_eq_zero (q := q) hp S
      (A.frequencySequence r ∘ C.inverse) (ball c R) isOpen_ball (ha.mono hball) hsign hrot
    refine ⟨ha.mono hball,hrot,Coeff.analyticOnNhd_tailSquareDescent hp S _ _ isOpen_ball (ha.mono hball) hsign,
      hsplit,?_,?_⟩
    · intro b hb v hv
      exact Coeff.clm_tailSplit_eq_zero (Coeff.doublingExponent_ne_top hp) _ S (hsplit b hb) v hv
    · intro z hz
      have hrec := Coeff.tailSquareDescent_apply (q := q) S (A.frequencySequence r ∘ C.inverse)
        (ball c R) hsign z hz
      refine ⟨hrec,?_⟩
      intro n
      rw [hrec]
      exact he z (hball hz) n
  · intro r inst hr hr1 hpr
    obtain ⟨ha,he⟩ := hcorr r hr hr1 hpr
    have hrealInv := fun a b hab => A.actionFrequencyCorrectionSequence_real_eq_of_actions A hs hs a b hab r
    have hsign : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
        ∀ z ∈ ball c R, (A.actionFrequencyCorrectionSequence r ∘ C.inverse) (Coeff.pairSignChange e d z) =
          (A.actionFrequencyCorrectionSequence r ∘ C.inverse) z := by
      intro e d he hd z hz
      exact C.complex_sign_invariance _ ha hrealInv c hc R hR hball e d
        (Coeff.pairSignChange_truncatePair S _ e d he hd) z hz
    have hrot : ∀ z ∈ ball c R, ∀ k, fderiv ℂ (A.actionFrequencyCorrectionSequence r ∘ C.inverse) z
        (Coeff.actionRotationVectorCLM p k z) = 0 := by
      intro z hz k
      exact Coeff.fderiv_actionRotationVector_eq_zero_of_real_action_invariance _ _ isOpen_ball
        (convex_ball c R) c (mem_ball_self hR) hc (ha.mono hball)
        (fun a ha b hb har hbr he => C.lifted_real_action_invariance _ hrealInv a b
          (hball ha) (hball hb) har hbr he) z hz k
    have hsplit := Coeff.fderiv_tailSquareDescent_actionSplit_eq_zero (q := q) hp S
      (A.actionFrequencyCorrectionSequence r ∘ C.inverse) (ball c R) isOpen_ball (ha.mono hball) hsign hrot
    refine ⟨ha.mono hball,hrot,Coeff.analyticOnNhd_tailSquareDescent hp S _ _ isOpen_ball (ha.mono hball) hsign,
      hsplit,?_,?_⟩
    · intro b hb v hv
      exact Coeff.clm_tailSplit_eq_zero (Coeff.doublingExponent_ne_top hp) _ S (hsplit b hb) v hv
    · intro z hz
      have hrec := Coeff.tailSquareDescent_apply (q := q) S (A.actionFrequencyCorrectionSequence r ∘ C.inverse)
        (ball c R) hsign z hz
      refine ⟨hrec,?_⟩
      intro n
      rw [hrec]
      exact he z (hball hz) n

end NLS.ZakharovShabat
