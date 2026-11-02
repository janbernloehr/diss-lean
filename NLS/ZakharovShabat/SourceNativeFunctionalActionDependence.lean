import NLS.ZakharovShabat.SourceSobolevFourthActionDependence

/-! # Native action dependence from physical finite-gap approximation

Any continuous fractional source functional constant on actual finite-gap
source action levels is constant on all native action levels after inversion.
The same physical raw actions and original weighted source norm are retained.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Actual weighted inverse cutoffs extend physical finite-gap action
invariance to the full original fractional target. -/
theorem nativeFunctional_inverse_eq_of_actions
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (H : NativeFourthSobolevSource → ℂ) (hH : Continuous H)
    (hfinite : ∀ a b : NativeFourthSobolevSource,
      originalWeightedRealSource fourthSobolevSpectralWeight a ∈ sourceFiniteGapLocus (by simp) (by norm_num) →
      originalWeightedRealSource fourthSobolevSpectralWeight b ∈ sourceFiniteGapLocus (by simp) (by norm_num) →
      originalWeightedRealSource fourthSobolevSpectralWeight b ∈ sourceRealActionLevelSet (by simp) (by norm_num)
        (originalWeightedRealSource fourthSobolevSpectralWeight a) → H b = H a)
    (z r : FourthSobolevBirkhoffTarget)
    (h : ∀ n : ℤ, RealCoeff.pairAction (originalWeightedRealTarget fourthSobolevSpectralWeight r) n =
      RealCoeff.pairAction (originalWeightedRealTarget fourthSobolevSpectralWeight z) n) :
    H ((D.originalWeightedRealSobolevEquiv (by rfl) (3/2) (by norm_num)).symm r) =
      H ((D.originalWeightedRealSobolevEquiv (by rfl) (3/2) (by norm_num)).symm z) := by
  let w := sourceFrequencyWeight fourthSobolevSpectralWeight
  let Z := fun S : Finset ℤ => WeightedRealCoeff.truncatePair w S z
  let R := fun S : Finset ℤ => WeightedRealCoeff.truncatePair w S r
  let φ := fun a : FourthSobolevBirkhoffTarget => originalWeightedRealSource fourthSobolevSpectralWeight
    ((D.originalWeightedRealSobolevEquiv (by rfl) (3/2) (by norm_num)).symm a)
  have htrunc (a : FourthSobolevBirkhoffTarget) (S : Finset ℤ) :
      originalWeightedRealTarget fourthSobolevSpectralWeight (WeightedRealCoeff.truncatePair w S a) =
        RealCoeff.truncatePair S (originalWeightedRealTarget fourthSobolevSpectralWeight a) :=
    WeightedRealCoeff.forget_truncatePair w (fun n => fourthSobolevSpectralWeight.one_le (2*n)) S a
  have heq (S : Finset ℤ) : H ((D.originalWeightedRealSobolevEquiv (by rfl) (3/2) (by norm_num)).symm (R S)) =
      H ((D.originalWeightedRealSobolevEquiv (by rfl) (3/2) (by norm_num)).symm (Z S)) := by
    have hf := D.fourthSobolev_inverse_truncate_finiteGap S z
    have hg := D.fourthSobolev_inverse_truncate_finiteGap S r
    have hlevel : φ (R S) ∈ sourceRealActionLevelSet (by simp) (by norm_num) (φ (Z S)) := by
      intro n
      rw [D.fourthSobolev_inverse_action,D.fourthSobolev_inverse_action]
      rw [htrunc r S,htrunc z S,RealCoeff.pairAction_truncatePair,RealCoeff.pairAction_truncatePair,h n]
    exact hfinite _ _ hf hg hlevel
  let J : FourthSobolevBirkhoffTarget → ℂ := fun y =>
    H ((D.originalWeightedRealSobolevEquiv (by rfl) (3/2) (by norm_num)).symm y)
  have hcont : Continuous J := hH.comp
    (continuous_iff_continuousAt.mpr fun y =>
      (D.originalWeightedRealSobolevEquiv_symm_analytic (by rfl) (3/2) (by norm_num) y (mem_univ _)).continuousAt)
  have hz : Tendsto (fun S => H ((D.originalWeightedRealSobolevEquiv (by rfl) (3/2) (by norm_num)).symm (Z S))) atTop
      (𝓝 (J z)) :=
    (hcont.tendsto z).comp (WeightedRealCoeff.tendsto_truncatePair w (by simp : (2:ℝ≥0∞) ≠ ⊤) z)
  have hr : Tendsto (fun S => H ((D.originalWeightedRealSobolevEquiv (by rfl) (3/2) (by norm_num)).symm (R S))) atTop
      (𝓝 (J r)) :=
    (hcont.tendsto r).comp (WeightedRealCoeff.tendsto_truncatePair w (by simp : (2:ℝ≥0∞) ≠ ⊤) r)
  have hfunctions : (fun S => H ((D.originalWeightedRealSobolevEquiv (by rfl) (3/2) (by norm_num)).symm (R S))) =
      fun S => H ((D.originalWeightedRealSobolevEquiv (by rfl) (3/2) (by norm_num)).symm (Z S)) := funext heq
  rw [hfunctions] at hr
  exact tendsto_nhds_unique hr hz

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
