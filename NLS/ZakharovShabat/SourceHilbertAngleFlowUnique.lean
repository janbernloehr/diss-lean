import NLS.FunctionalAnalysis.AutonomousODEUniqueness
import NLS.ZakharovShabat.SourceHilbertAngleHamiltonian

/-! # Existence and uniqueness of the Hilbert angle flow before collapse

The explicit lifted curve is the unique solution of the actual angle
Hamiltonian equation on the entire interval `(-∞, I_k(φ₀))`. Its selected
action tends to zero, as required in Lemma 17.4(i). The stronger-exponent
regularity of the source displacement in part (ii) remains separate.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ZakharovShabat
namespace SourceBirkhoffMapComplexData
variable {W₀ B W V₀ C V : Set (CoeffPair 2)}
  {s u : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- Uniqueness against any solution of the original angle Hamiltonian
on the complete time interval before collapse. -/
theorem hilbertActionReduction_thetaHamiltonian_unique
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (k : ℤ) (φ : realTypeSourceSubmodule 2)
    (ha : 0 < (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re)
    (g : ℝ → CoeffPair 2) (hzero : g 0 = φ.val)
    (hg : ∀ t < (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re,
      HasDerivAt g (sourceAngularThetaHamiltonianVector (by simp) (by norm_num) (le_refl 2) k u (g t)) t) :
    EqOn g (fun t => (D.hilbertActionReduction φ k t).val)
      (Iio (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re) := by
  apply EqOn.symm
  apply NLS.FunctionalAnalysis.eqOn_of_autonomous_hasDerivAt isOpen_Iio isPreconnected_Iio
    (v := sourceAngularThetaHamiltonianVector (by simp) (by norm_num) (le_refl 2) k u)
    (t₀ := 0)
  · intro t ht
    have hgap := D.hilbertActionReduction_gap_ne_zero k φ ha ht
    exact ((E.analyticOnNhd_thetaHamiltonian (le_refl 2) k
      (D.hilbertActionReduction φ k t).val
      ⟨E.real_subset (D.hilbertActionReduction φ k t).property,hgap⟩).restrictScalars (𝕜 := ℝ)).contDiffAt
  · intro t ht
    exact D.hasDerivAt_hilbertActionReduction_thetaHamiltonian E k φ ha ht
  · exact hg
  · exact ha
  · simpa only [D.hilbertActionReduction_zero] using hzero.symm

/-- The open-gap hypothesis in the dissertation gives strictly positive action. -/
theorem hilbert_action_pos_of_gap_ne_zero
    (φ : realTypeSourceSubmodule 2) (k : ℤ)
    (hk : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) k ≠ 0) :
    0 < (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re := by
  have h := sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num) φ.val φ.property k
  apply lt_of_le_of_ne h.1
  intro hz
  have ha : sourceRealAction (by simp) (by norm_num) φ.val φ.property k = 0 := by
    apply Complex.ext
    · exact hz.symm
    · exact h.2.1
  exact hk (by simpa only [sourcePeriodicGapDisplacement_apply] using h.2.2.mp ha)

/-- Lemma 17.4's initial value problem and part (i), for the actual
Hamiltonian vector field and an arbitrary real open-gap source. -/
theorem hilbert_angleFlow_exists_unique_and_action_limit
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (k : ℤ) (φ : realTypeSourceSubmodule 2)
    (hk : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) k ≠ 0) :
    let a := (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re
    ∃ f : ℝ → realTypeSourceSubmodule 2,
      f 0 = φ ∧ ContDiffOn ℝ 1 f (Iio a) ∧
      (∀ t < a, HasDerivAt (fun t => (f t).val)
        (sourceAngularThetaHamiltonianVector (by simp) (by norm_num) (le_refl 2) k u (f t).val) t) ∧
      (∀ g : ℝ → CoeffPair 2, g 0 = φ.val →
        (∀ t < a, HasDerivAt g
          (sourceAngularThetaHamiltonianVector (by simp) (by norm_num) (le_refl 2) k u (g t)) t) →
        EqOn g (fun t => (f t).val) (Iio a)) ∧
      Tendsto (fun t => (sourceRealAction (by simp) (by norm_num) (f t).val (f t).property k).re)
        (𝓝[<] a) (𝓝 0) := by
  have ha := hilbert_action_pos_of_gap_ne_zero φ k hk
  refine ⟨D.hilbertActionReduction φ k,D.hilbertActionReduction_zero φ k,?_,
    fun t ht => D.hasDerivAt_hilbertActionReduction_thetaHamiltonian E k φ ha ht,
    fun g hzero hg => D.hilbertActionReduction_thetaHamiltonian_unique E k φ ha g hzero hg,
    D.tendsto_action_hilbertActionReduction φ k ha⟩
  intro t ht
  exact ((D.contDiffAt_hilbertActionReduction φ k ha ht).of_le (by simp)).contDiffWithinAt

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
