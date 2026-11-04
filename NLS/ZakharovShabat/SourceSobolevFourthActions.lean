import NLS.ZakharovShabat.SourceSobolevFourthComplexGerm
import NLS.SequenceSpaces.WeightedNonnegativeActions
import NLS.SequenceSpaces.QuadraticActionsExponent

/-! # The original weighted actions on the full H^(3/2) Birkhoff target

The action weight is exactly (1+|n|)^3, the square of the physical field
weight. Normalizing those actions gives the existing Hilbert quadratic
map into ell1; every raw coordinate is the original physical action.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The original order-three weight on physical H₄ actions. -/
def fourthSobolevActionWeight : Weight := Weight.sobolev 3

/-- The actual complex ell^(3,1) action space, retaining raw coefficients. -/
abbrev FourthSobolevActions := WeightedCoeff fourthSobolevActionWeight 1

/-- The action weight is the exact square of the original physical field weight. -/
theorem fourthSobolevActionWeight_eq_square (n : ℤ) :
    fourthSobolevActionWeight n = (sourceFrequencyWeight fourthSobolevSpectralWeight n)^2 := by
  have hw : sourceFrequencyWeight fourthSobolevSpectralWeight = Weight.sobolev (3/2) :=
    sourceFrequencyWeight_sobolev (3/2) (by norm_num)
  rw [hw]
  have hs : (3/2:ℝ)+(3/2) = 3 := by norm_num
  have h := Weight.sobolev_add (3/2) (3/2) n
  rw [hs] at h
  exact h.trans (pow_two _).symm

/-- The physical raw action sequence on every native fractional real target. -/
def fourthSobolevActions (z : FourthSobolevBirkhoffTarget) : FourthSobolevActions :=
  (WeightedCoeff.weightIsometry fourthSobolevActionWeight 1).symm
    (quadraticActionsExponent (q := 1)
      (((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2))
        (NLS.Birkhoff.weightedRealCoordinates (sourceFrequencyWeight fourthSobolevSpectralWeight) z)))

/-- Normalizing the raw weighted actions recovers the exact quadratic Hilbert map. -/
theorem fourthSobolevActions_weighted (z : FourthSobolevBirkhoffTarget) :
    WeightedCoeff.weightIsometry fourthSobolevActionWeight 1 (fourthSobolevActions z) =
      quadraticActionsExponent (q := 1)
        (((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2))
          (NLS.Birkhoff.weightedRealCoordinates (sourceFrequencyWeight fourthSobolevSpectralWeight) z)) :=
  (WeightedCoeff.weightIsometry fourthSobolevActionWeight 1).apply_symm_apply _

/-- Every raw weighted coordinate is exactly the original physical quadratic action. -/
theorem fourthSobolevActions_apply (z : FourthSobolevBirkhoffTarget) (n : ℤ) :
    (fourthSobolevActions z).val n =
      (RealCoeff.pairAction (originalWeightedRealTarget fourthSobolevSpectralWeight z) n : ℂ) := by
  let w := sourceFrequencyWeight fourthSobolevSpectralWeight
  let x := NLS.Birkhoff.weightedRealCoordinates w z
  have hq : quadraticActionsExponent (q := 1)
      (((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2)) x) n =
      (RealCoeff.pairAction x n : ℂ) := by
    rw [quadraticActionsExponent_apply]
    change ((x.1 n:ℂ)^2+(x.2 n:ℂ)^2)/2 = (((x.1 n)^2+(x.2 n)^2)/2:ℝ)
    simp only [Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_pow,Complex.ofReal_ofNat]
  have hx : RealCoeff.pairAction x n = fourthSobolevActionWeight n*
      RealCoeff.pairAction (originalWeightedRealTarget fourthSobolevSpectralWeight z) n := by
    rw [fourthSobolevActionWeight_eq_square]
    exact NLS.Birkhoff.weightedRealCoordinates_pairAction w
      (fun k => fourthSobolevSpectralWeight.one_le (2*k)) z n
  change quadraticActionsExponent (q := 1)
    (((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2)) x) n/(fourthSobolevActionWeight n:ℂ) = _
  rw [hq,hx,Complex.ofReal_mul]
  exact mul_div_cancel_left₀ _ (fourthSobolevActionWeight.complex_ne_zero n)

/-- The physical actions belong to the entire nonnegative weighted cone,
including all zero-coordinate boundary points. -/
theorem fourthSobolevActions_nonnegative (z : FourthSobolevBirkhoffTarget) :
    fourthSobolevActions z ∈ WeightedCoeff.nonnegativeLocus fourthSobolevActionWeight 1 := by
  intro n
  rw [fourthSobolevActions_apply]
  refine ⟨rfl,?_⟩
  change 0 ≤ RealCoeff.pairAction (originalWeightedRealTarget fourthSobolevSpectralWeight z) n
  dsimp only [RealCoeff.pairAction]
  positivity

/-- The actual physical action map is real analytic into the weighted ell1 target. -/
theorem analyticOnNhd_fourthSobolevActions : AnalyticOnNhd ℝ fourthSobolevActions univ := by
  intro z _
  let w := sourceFrequencyWeight fourthSobolevSpectralWeight
  let R := NLS.Birkhoff.weightedRealCoordinates (p := 2) w
  let J := (RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2)
  have hQ := (analyticOnNhd_quadraticActionsExponent (p := 2) (q := 1) (J (R z)) (mem_univ _)).restrictScalars (𝕜 := ℝ)
  have hQR : AnalyticAt ℝ (fun y : FourthSobolevBirkhoffTarget => quadraticActionsExponent (q := 1) (J (R y))) z :=
    hQ.comp (f := fun y : FourthSobolevBirkhoffTarget => J (R y))
      ((J.analyticAt (R z)).comp (R.analyticAt z))
  let A := ((WeightedCoeff.weightIsometry fourthSobolevActionWeight 1).symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ
  exact (A.analyticAt _).comp hQR

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The native weighted action map has the exact original source actions,
with no change of physical normalization or Fourier index. -/
theorem fourthSobolevActions_realMap_apply
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) (n : ℤ) :
    (fourthSobolevActions (D.originalWeightedRealMap fourthSobolevSpectralWeight a)).val n =
      ((sourceRealAction (by simp) (by norm_num)
        (originalWeightedRealSource fourthSobolevSpectralWeight a).val
        (originalWeightedRealSource fourthSobolevSpectralWeight a).property n).re : ℂ) := by
  rw [fourthSobolevActions_apply,D.originalWeightedRealTarget_map]
  change (RealCoeff.pairAction (D.hilbertRealHomeomorph _) n : ℂ) = _
  rw [D.hilbert_pairAction_eq]

/-- These same raw coordinates equal the original complex action on the real source. -/
theorem fourthSobolevActions_realMap_eq_complexAction
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) (n : ℤ) :
    (fourthSobolevActions (D.originalWeightedRealMap fourthSobolevSpectralWeight a)).val n =
      sourceComplexAction (by simp) (by norm_num) n
        (originalWeightedRealSource fourthSobolevSpectralWeight a).val := by
  rw [D.fourthSobolevActions_realMap_apply,
    sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) n _
      (originalWeightedRealSource fourthSobolevSpectralWeight a).property]
  apply Complex.ext
  · rfl
  · simpa using (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num)
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val
      (originalWeightedRealSource fourthSobolevSpectralWeight a).property n).2.1.symm

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
