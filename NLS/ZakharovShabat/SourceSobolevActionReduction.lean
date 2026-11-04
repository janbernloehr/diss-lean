import NLS.SequenceSpaces.WeightedRealActionReduction
import NLS.ZakharovShabat.SourceFiniteGapSobolevOpening

/-! # Physical action reduction in the original Sobolev topology

The actual global weighted inverse lifts the native radial curve at every
nonnegative real regularity. Its original coefficients are exactly the
previous Hilbert curve. The source derivative exists in the stronger norm.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Lift the actual raw-action reduction through the global Sobolev inverse. -/
def sobolevActionReduction
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ)) (n : ℤ) (t : ℝ) :
    weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ) :=
  (D.originalWeightedRealSobolevEquiv (by rfl) σ hσ).symm
    (WeightedRealCoeff.actionReduction (sourceFrequencyWeight (sourceSobolevSpectralWeight σ hσ))
      (fun k => (sourceSobolevSpectralWeight σ hσ).one_le (2*k))
      (D.originalWeightedRealMap (sourceSobolevSpectralWeight σ hσ) a) n t)

@[simp] theorem sobolevActionReduction_zero
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ)) (n : ℤ) :
    D.sobolevActionReduction σ hσ a n 0 = a := by
  exact (congrArg (D.originalWeightedRealSobolevEquiv (by rfl) σ hσ).symm
    (WeightedRealCoeff.actionReduction_zero (sourceFrequencyWeight (sourceSobolevSpectralWeight σ hσ))
      (fun k => (sourceSobolevSpectralWeight σ hσ).one_le (2*k))
      (D.originalWeightedRealMap (sourceSobolevSpectralWeight σ hσ) a) n)).trans
    ((D.originalWeightedRealSobolevEquiv (by rfl) σ hσ).symm_apply_apply a)

/-- The stronger-norm lift is exactly the original physical Hilbert action curve. -/
theorem originalWeightedRealSource_sobolevActionReduction
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ)) (n : ℤ) (t : ℝ) :
    originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) (D.sobolevActionReduction σ hσ a n t) =
      D.hilbertActionReduction (originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) a) n t := by
  apply D.hilbertRealHomeomorph.injective
  rw [D.hilbertRealHomeomorph_actionReduction]
  change (D.realHomeomorph (by rfl)) _ = _
  unfold sobolevActionReduction
  rw [D.originalWeightedRealSource_sobolevEquiv_symm]
  rw [(D.realHomeomorph (by rfl)).apply_symm_apply]
  change originalWeightedRealTarget (sourceSobolevSpectralWeight σ hσ)
    (WeightedRealCoeff.actionReduction _ _ _ n t) = _
  erw [WeightedRealCoeff.forget_actionReduction]
  change RealCoeff.actionReduction (originalWeightedRealTarget (sourceSobolevSpectralWeight σ hσ)
    (D.originalWeightedRealMap (sourceSobolevSpectralWeight σ hσ) a)) n t =
      RealCoeff.actionReduction (sourceRealBirkhoffMap (by simp) (by norm_num) s
        (originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) a)) n t
  rw [D.originalWeightedRealTarget_map]

/-- The source derivative is the actual bounded inverse derivative applied
to the native raw-action radial vector, in the full Sobolev norm. -/
theorem hasDerivAt_sobolevActionReduction_zero
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ)) (n : ℤ) :
    HasDerivAt (D.sobolevActionReduction σ hσ a n)
      (fderiv ℝ (D.originalWeightedRealSobolevEquiv (by rfl) σ hσ).symm
        (D.originalWeightedRealMap (sourceSobolevSpectralWeight σ hσ) a)
        ((-1/(2*RealCoeff.pairAction (originalWeightedRealTarget (sourceSobolevSpectralWeight σ hσ)
          (D.originalWeightedRealMap (sourceSobolevSpectralWeight σ hσ) a)) n)) •
            WeightedRealCoeff.pairModeCLM (sourceFrequencyWeight (sourceSobolevSpectralWeight σ hσ)) n
              (D.originalWeightedRealMap (sourceSobolevSpectralWeight σ hσ) a))) 0 := by
  let w := sourceSobolevSpectralWeight σ hσ
  let z := D.originalWeightedRealMap w a
  let γ := WeightedRealCoeff.actionReduction (sourceFrequencyWeight w) (fun k => w.one_le (2*k)) z n
  have hγ := WeightedRealCoeff.hasDerivAt_actionReduction_zero
    (sourceFrequencyWeight w) (fun k => w.one_le (2*k)) z n
  have hi : HasFDerivAt (D.originalWeightedRealSobolevEquiv (by rfl) σ hσ).symm
      (fderiv ℝ (D.originalWeightedRealSobolevEquiv (by rfl) σ hσ).symm z) (γ 0) := by
    have hzero : γ 0 = z := WeightedRealCoeff.actionReduction_zero
      (sourceFrequencyWeight w) (fun k => w.one_le (2*k)) z n
    exact hzero.symm ▸
      (D.originalWeightedRealSobolevEquiv_symm_analytic (by rfl) σ hσ z (mem_univ _)).differentiableAt.hasFDerivAt
  exact hi.comp_hasDerivAt 0 hγ

/-- Finite-gap is preserved along the entire Sobolev action-reduction curve. -/
theorem sobolevActionReduction_mem_finiteGap
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ))
    (hf : originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) a ∈
      sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℤ) (t : ℝ) :
    originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) (D.sobolevActionReduction σ hσ a n t) ∈
      sourceFiniteGapLocus (by simp) (by norm_num) := by
  rw [D.originalWeightedRealSource_sobolevActionReduction]
  exact D.hilbertActionReduction_mem_finiteGap _ hf n t

/-- The selected original source action decreases at exactly unit speed. -/
theorem sobolevActionReduction_action_same
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ)) (n : ℤ)
    (ha : 0 < (sourceRealAction (by simp) (by norm_num)
      (originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) a).val
      (originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) a).property n).re)
    (t : ℝ) (ht : t ≤ (sourceRealAction (by simp) (by norm_num)
      (originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) a).val
      (originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) a).property n).re) :
    (sourceRealAction (by simp) (by norm_num)
      (originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) (D.sobolevActionReduction σ hσ a n t)).val
      (originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) (D.sobolevActionReduction σ hσ a n t)).property n).re =
      (sourceRealAction (by simp) (by norm_num)
        (originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) a).val
        (originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) a).property n).re-t := by
  rw [D.originalWeightedRealSource_sobolevActionReduction]
  exact D.hilbertActionReduction_action_same _ n ha t ht

/-- The original source actions at every other index are unchanged. -/
theorem sobolevActionReduction_action_ne
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ))
    (n k : ℤ) (hkn : k ≠ n) (t : ℝ) :
    (sourceRealAction (by simp) (by norm_num)
      (originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) (D.sobolevActionReduction σ hσ a n t)).val
      (originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) (D.sobolevActionReduction σ hσ a n t)).property k).re =
      (sourceRealAction (by simp) (by norm_num)
        (originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) a).val
        (originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) a).property k).re := by
  rw [D.originalWeightedRealSource_sobolevActionReduction]
  exact D.hilbertActionReduction_action_ne _ n k hkn t

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
