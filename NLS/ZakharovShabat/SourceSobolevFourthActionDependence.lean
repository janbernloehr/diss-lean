import NLS.ZakharovShabat.SourceSobolevFourthBirkhoff
import NLS.ZakharovShabat.SourceFiniteGapHamiltonianIsospectral
import NLS.SequenceSpaces.WeightedRealTruncation

/-! # Physical H₄ depends only on the actions on the full H^(3/2) domain

Simultaneous weighted Birkhoff truncations preserve every retained action.
Their actual inverse sources are finite-gap and converge in the fractional
source norm. The physical Hamiltonians agree there by the exterior trace,
so continuity gives the same action dependence throughout the full domain.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The native fractional inverse has exactly the original unweighted real coordinates. -/
theorem fourthSobolev_inverse_real_map
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (z : FourthSobolevBirkhoffTarget) :
    sourceRealBirkhoffMap (by simp) (by norm_num) s
      (originalWeightedRealSource fourthSobolevSpectralWeight
        ((D.originalWeightedRealSobolevEquiv (by rfl) (3/2) (by norm_num)).symm z)) =
      originalWeightedRealTarget fourthSobolevSpectralWeight z := by
  have hmap := D.originalWeightedRealTarget_map fourthSobolevSpectralWeight
    ((D.originalWeightedRealSobolevEquiv (by rfl) (3/2) (by norm_num)).symm z)
  have he : D.originalWeightedRealMap fourthSobolevSpectralWeight
      ((D.originalWeightedRealSobolevEquiv (by rfl) (3/2) (by norm_num)).symm z) = z :=
    (D.originalWeightedRealSobolevEquiv (by rfl) (3/2) (by norm_num)).apply_symm_apply z
  rw [he] at hmap
  exact hmap.symm

/-- A native target cutoff has an actual finite-gap inverse source. -/
theorem fourthSobolev_inverse_truncate_finiteGap
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (S : Finset ℤ) (z : FourthSobolevBirkhoffTarget) :
    originalWeightedRealSource fourthSobolevSpectralWeight
      ((D.originalWeightedRealSobolevEquiv (by rfl) (3/2) (by norm_num)).symm
        (WeightedRealCoeff.truncatePair (sourceFrequencyWeight fourthSobolevSpectralWeight) S z)) ∈
      sourceFiniteGapLocus (by simp) (by norm_num) := by
  apply D.finiteGap_of_real_map_eq_truncatePair _ S
    (originalWeightedRealTarget fourthSobolevSpectralWeight z)
  rw [D.fourthSobolev_inverse_real_map]
  exact WeightedRealCoeff.forget_truncatePair (sourceFrequencyWeight fourthSobolevSpectralWeight)
    (fun n => fourthSobolevSpectralWeight.one_le (2*n)) S z

/-- The native inverse retains the exact original quadratic action normalization. -/
theorem fourthSobolev_inverse_action
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (z : FourthSobolevBirkhoffTarget) (n : ℤ) :
    (sourceRealAction (by simp) (by norm_num)
      (originalWeightedRealSource fourthSobolevSpectralWeight
        ((D.originalWeightedRealSobolevEquiv (by rfl) (3/2) (by norm_num)).symm z)).val
      (originalWeightedRealSource fourthSobolevSpectralWeight
        ((D.originalWeightedRealSobolevEquiv (by rfl) (3/2) (by norm_num)).symm z)).property n).re =
      RealCoeff.pairAction (originalWeightedRealTarget fourthSobolevSpectralWeight z) n := by
  rw [← D.hilbert_pairAction_eq]
  change RealCoeff.pairAction (sourceRealBirkhoffMap (by simp) (by norm_num) s _) n = _
  rw [D.fourthSobolev_inverse_real_map]

/-- Equal raw quadratic actions determine physical H₄ on the entire original
fractional Birkhoff target, including infinitely many nonzero actions. -/
theorem sobolevFourthBirkhoffHamiltonian_eq_of_actions
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (z r : FourthSobolevBirkhoffTarget)
    (h : ∀ n : ℤ,
      RealCoeff.pairAction (originalWeightedRealTarget fourthSobolevSpectralWeight r) n =
        RealCoeff.pairAction (originalWeightedRealTarget fourthSobolevSpectralWeight z) n) :
    D.sobolevFourthBirkhoffHamiltonian r = D.sobolevFourthBirkhoffHamiltonian z := by
  let w := sourceFrequencyWeight fourthSobolevSpectralWeight
  let Z := fun S : Finset ℤ => WeightedRealCoeff.truncatePair w S z
  let R := fun S : Finset ℤ => WeightedRealCoeff.truncatePair w S r
  let φ := fun a : FourthSobolevBirkhoffTarget => originalWeightedRealSource fourthSobolevSpectralWeight
    ((D.originalWeightedRealSobolevEquiv (by rfl) (3/2) (by norm_num)).symm a)
  have htrunc (a : FourthSobolevBirkhoffTarget) (S : Finset ℤ) :
      originalWeightedRealTarget fourthSobolevSpectralWeight (WeightedRealCoeff.truncatePair w S a) =
        RealCoeff.truncatePair S (originalWeightedRealTarget fourthSobolevSpectralWeight a) :=
    WeightedRealCoeff.forget_truncatePair w (fun n => fourthSobolevSpectralWeight.one_le (2*n)) S a
  have heq (S : Finset ℤ) : D.sobolevFourthBirkhoffHamiltonian (R S) =
      D.sobolevFourthBirkhoffHamiltonian (Z S) := by
    have hf := D.fourthSobolev_inverse_truncate_finiteGap S z
    have hg := D.fourthSobolev_inverse_truncate_finiteGap S r
    have hlevel : φ (R S) ∈ sourceRealActionLevelSet (by simp) (by norm_num) (φ (Z S)) := by
      intro n
      rw [D.fourthSobolev_inverse_action,D.fourthSobolev_inverse_action]
      rw [htrunc r S,htrunc z S,RealCoeff.pairAction_truncatePair,RealCoeff.pairAction_truncatePair,h n]
    exact (sourceSobolevFourthHamiltonian_eq_finiteGap _ hg).trans
      ((sourceFiniteGapNLSHamiltonian_eq_of_actions (by simp) (by norm_num)
        (φ (Z S)) (φ (R S)) hf hg hlevel 4).trans
        (sourceSobolevFourthHamiltonian_eq_finiteGap _ hf).symm)
  have hcont : Continuous D.sobolevFourthBirkhoffHamiltonian :=
    continuous_iff_continuousAt.mpr fun a =>
      (D.analyticOnNhd_sobolevFourthBirkhoffHamiltonian a (mem_univ _)).continuousAt
  have hz : Tendsto (fun S => D.sobolevFourthBirkhoffHamiltonian (Z S)) atTop
      (𝓝 (D.sobolevFourthBirkhoffHamiltonian z)) :=
    (hcont.tendsto z).comp (WeightedRealCoeff.tendsto_truncatePair w (by simp : (2:ℝ≥0∞) ≠ ⊤) z)
  have hr : Tendsto (fun S => D.sobolevFourthBirkhoffHamiltonian (R S)) atTop
      (𝓝 (D.sobolevFourthBirkhoffHamiltonian r)) :=
    (hcont.tendsto r).comp (WeightedRealCoeff.tendsto_truncatePair w (by simp : (2:ℝ≥0∞) ≠ ⊤) r)
  have hfunctions : (fun S => D.sobolevFourthBirkhoffHamiltonian (R S)) =
      fun S => D.sobolevFourthBirkhoffHamiltonian (Z S) := funext heq
  rw [hfunctions] at hr
  exact tendsto_nhds_unique hr hz

/-- The physical fractional Hamiltonian is constant on the original full
source action level sets, in the same H^(3/2) topology. -/
theorem sourceSobolevFourthHamiltonian_eq_of_actions
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a b : NativeFourthSobolevSource)
    (h : originalWeightedRealSource fourthSobolevSpectralWeight b ∈
      sourceRealActionLevelSet (by simp) (by norm_num)
        (originalWeightedRealSource fourthSobolevSpectralWeight a)) :
    sourceSobolevFourthHamiltonian b = sourceSobolevFourthHamiltonian a := by
  rw [← D.sobolevFourthBirkhoffHamiltonian_map b,← D.sobolevFourthBirkhoffHamiltonian_map a]
  apply D.sobolevFourthBirkhoffHamiltonian_eq_of_actions
  intro n
  rw [D.originalWeightedRealTarget_map,D.originalWeightedRealTarget_map]
  change RealCoeff.pairAction (D.hilbertRealHomeomorph _) n =
    RealCoeff.pairAction (D.hilbertRealHomeomorph _) n
  rw [D.hilbert_pairAction_eq,D.hilbert_pairAction_eq]
  exact h n

/-- The genuine real scalar H₄ has the same full source action dependence. -/
theorem sourceRealSobolevFourthHamiltonian_eq_of_actions
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a b : NativeFourthSobolevSource)
    (h : originalWeightedRealSource fourthSobolevSpectralWeight b ∈
      sourceRealActionLevelSet (by simp) (by norm_num)
        (originalWeightedRealSource fourthSobolevSpectralWeight a)) :
    sourceRealSobolevFourthHamiltonian b = sourceRealSobolevFourthHamiltonian a :=
  congrArg Complex.re (D.sourceSobolevFourthHamiltonian_eq_of_actions a b h)

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
