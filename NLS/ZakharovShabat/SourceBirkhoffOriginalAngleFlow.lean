import NLS.ZakharovShabat.SourceSection16Original
import NLS.ZakharovShabat.SourceHilbertAngleDisplacement

/-!
# The original Hilbert angle flow

The map and angle use the same original root family. The actual theta
Hamiltonian lowers the selected action at unit speed, conserves the
others, and has a unique full-interval flow with continuous displacement
in every finite source exponent above one.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceSection16OriginalData
variable {W₀ W V : Set (CoeffPair 2)}
  {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Equation (3.9) with the inward sign in both rectangular components. -/
theorem equation3_9
    (D : SourceSection16OriginalData (p := 2) (by simp) (by norm_num) W₀ W V s)
    (k : ℤ) (φ : realTypeSourceSubmodule 2)
    (hk : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) k ≠ 0) :
    sourceBirkhoffJacobian (by simp) (by norm_num) s φ.val
      (sourceAngularThetaHamiltonianVector (by simp) (by norm_num) (le_refl 2) k s φ.val) =
    ((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2))
      (RealCoeff.actionReductionVector (D.complex.hilbertRealHomeomorph φ) k) :=
  D.complex.hilbert_jacobian_thetaHamiltonian D.previous.original_theta_common_domain k φ hk

/-- Lemma 17.4 for the original angle Hamiltonian, with all displacement exponents. -/
theorem lemma17_4
    (D : SourceSection16OriginalData (p := 2) (by simp) (by norm_num) W₀ W V s)
    (k : ℤ) (φ : realTypeSourceSubmodule 2)
    (hk : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) k ≠ 0) :
    let a := (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re
    ∃ f : ℝ → realTypeSourceSubmodule 2,
      f 0 = φ ∧ ContDiffOn ℝ 1 f (Iio a) ∧
      (∀ t < a, HasDerivAt (fun t => (f t).val)
        (sourceAngularThetaHamiltonianVector (by simp) (by norm_num) (le_refl 2) k s (f t).val) t) ∧
      (∀ g : ℝ → CoeffPair 2, g 0 = φ.val →
        (∀ t < a, HasDerivAt g
          (sourceAngularThetaHamiltonianVector (by simp) (by norm_num) (le_refl 2) k s (g t)) t) →
        EqOn g (fun t => (f t).val) (Iio a)) ∧
      Tendsto (fun t => (sourceRealAction (by simp) (by norm_num) (f t).val (f t).property k).re)
        (𝓝[<] a) (𝓝 0) ∧
      ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r →
        ∃ d : Iio a → realTypeSourceSubmodule r, Continuous d ∧ ∀ t : Iio a, ∀ n : ℤ,
          (d t).val.fst n = (f t.val).val.fst n-φ.val.fst n ∧
          (d t).val.snd n = (f t.val).val.snd n-φ.val.snd n :=
  D.complex.lemma17_4 D.previous.original_theta_common_domain k φ hk


/-- The same explicit flow lowers exactly its selected action and conserves all others. -/
theorem angleFlow_action_law
    (D : SourceSection16OriginalData (p := 2) (by simp) (by norm_num) W₀ W V s)
    (k : ℤ) (φ : realTypeSourceSubmodule 2)
    (hk : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) k ≠ 0)
    (t : ℝ) (ht : t ≤ (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re) (n : ℤ) :
    (sourceRealAction (by simp) (by norm_num) (D.complex.hilbertActionReduction φ k t).val
      (D.complex.hilbertActionReduction φ k t).property n).re =
        (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re - if n = k then t else 0 := by
  by_cases hn : n = k
  · subst n
    simpa only [ite_true] using D.complex.hilbertActionReduction_action_same φ k
      (SourceBirkhoffMapComplexData.hilbert_action_pos_of_gap_ne_zero φ k hk) t ht
  · simpa only [if_neg hn,sub_zero] using D.complex.hilbertActionReduction_action_ne φ k n hn t

/-- The flow has a source-norm limit at the selected collapse time, with that gap closed. -/
theorem angleFlow_collapse
    (D : SourceSection16OriginalData (p := 2) (by simp) (by norm_num) W₀ W V s)
    (k : ℤ) (φ : realTypeSourceSubmodule 2)
    (hk : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) k ≠ 0) :
    let a := (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re
    Tendsto (D.complex.hilbertActionReduction φ k) (𝓝[<] a)
      (𝓝 (D.complex.hilbertActionReduction φ k a)) ∧
    sourcePeriodicGapDisplacement (by simp) (by norm_num)
      (D.complex.hilbertActionReduction φ k a).val k = 0 :=
  ⟨D.complex.tendsto_hilbertActionReduction_at_collapse φ k,
    D.complex.hilbertActionReduction_gap_zero_at_collapse φ k
      (SourceBirkhoffMapComplexData.hilbert_action_pos_of_gap_ne_zero φ k hk)⟩

end NLS.ZakharovShabat.SourceSection16OriginalData
