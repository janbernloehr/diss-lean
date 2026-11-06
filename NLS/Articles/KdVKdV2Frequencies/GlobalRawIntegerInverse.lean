import NLS.Articles.KdVKdV2Frequencies.GlobalNativeIntegerInverse
import NLS.SequenceSpaces.PhysicalRealMeanZeroWeighted

/-! # The SAME inverse on literal raw integer Sobolev target domains

The raw real target h^(s+1/2) is normalized by its explicit linear
isometry, then evaluated by the ALREADY-FIXED weak inverse restricted to
H^s. Every signed coefficient is recovered exactly, in the original norms.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

private theorem analytic_real_clm_precomp
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] F) (f : F → G) (a : E) (hf : AnalyticAt ℝ f (L a)) :
    AnalyticAt ℝ (fun b => f (L b)) a := hf.comp (f := L) (L.analyticAt a)

def integerTargetNormalization (s : ℕ) :
    physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((s : ℝ)+1/2)) →L[ℝ]
      physicalRealDeletedSubmodule :=
  (physicalRealMeanZeroWeightedIsometry _ (Weight.sobolev_neg ((s : ℝ)+1/2))).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- Actual raw native source of the SAME weak global inverse. -/
def rawIntegerInverseSource (D : GlobalRoughAbelianForwardData) (s : ℕ)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((s : ℝ)+1/2))) : ScalarSobolev s :=
  D.nativeIntegerInverseSource s (integerTargetNormalization s z)

theorem rawIntegerInverseSource_real (D : GlobalRoughAbelianForwardData) (s : ℕ)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((s : ℝ)+1/2))) :
    ∀ n : ℤ, (D.rawIntegerInverseSource s z).val (-n)=conj ((D.rawIntegerInverseSource s z).val n) :=
  D.nativeIntegerInverseSource_real s _

theorem rawIntegerInverseSource_zero (D : GlobalRoughAbelianForwardData) (s : ℕ)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((s : ℝ)+1/2))) :
    (D.rawIntegerInverseSource s z).val 0=0 := D.nativeIntegerInverseSource_zero s _

/-- Real analyticity uses BOTH literal raw native Sobolev norms. -/
theorem rawIntegerInverseSource_analytic (D : GlobalRoughAbelianForwardData) (s : ℕ) :
    AnalyticOnNhd ℝ (D.rawIntegerInverseSource s) univ := by
  intro z _
  simpa only [rawIntegerInverseSource] using! analytic_real_clm_precomp
    (E := physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((s : ℝ)+1/2)))
    (F := physicalRealDeletedSubmodule) (G := ScalarSobolev s)
    (integerTargetNormalization s) (D.nativeIntegerInverseSource s) z
    (D.nativeIntegerInverseSource_analytic s (integerTargetNormalization s z) (mem_univ _))

/-- FULL signed output recovery in the exact raw target h^(s+1/2),
including both signs, phases and central zero. -/
theorem rawIntegerInverseSource_signed (D : GlobalRoughAbelianForwardData) (s : ℕ)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((s : ℝ)+1/2))) :
    D.signed (WeightedCoeff.sobolevInclusion
        (by have := Nat.cast_nonneg (α := ℝ) s; linarith : (-1 : ℝ)≤s) (D.rawIntegerInverseSource s z))=
      WeightedCoeff.sobolevInclusion
        (by have := Nat.cast_nonneg (α := ℝ) s; linarith : (-1/2 : ℝ)≤(s : ℝ)+1/2) z.val := by
  have h := D.nativeIntegerInverseSource_signed s (integerTargetNormalization s z)
  have hL : WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev ((s : ℝ)+1/2))
      (integerTargetNormalization s z).val=z.val :=
    WeightedCoeff.meanZeroWeightedLift_projection _ z.val z.property.2
  apply Subtype.ext
  funext j
  have hj := congrArg (fun b : WeightedCoeff (Weight.sobolev (-1/2)) 2 => b.val j) h
  have hLj := congrArg (fun b : WeightedCoeff (Weight.sobolev ((s : ℝ)+1/2)) 2 => b.val j) hL
  simp only [WeightedCoeff.sobolevInclusion_apply,WeightedCoeff.meanZeroWeightedLift_apply] at hj hLj ⊢
  simp only [show (s : ℝ)+1-1/2=(s : ℝ)+1/2 by ring] at hj
  exact hj.trans hLj

/-- Every actual real mean-zero H^s source matching a raw native signed
target is EXACTLY this source of the SAME global inverse. -/
theorem rawIntegerInverseSource_eq_of_signed_eq (D : GlobalRoughAbelianForwardData) (s : ℕ)
    (q : ScalarSobolev s) (hq : ∀ n : ℤ, q.val (-n)=conj (q.val n)) (hm : q.val 0=0)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((s : ℝ)+1/2)))
    (h : D.signed (WeightedCoeff.sobolevInclusion
        (by have := Nat.cast_nonneg (α := ℝ) s; linarith : (-1 : ℝ)≤s) q)=
      WeightedCoeff.sobolevInclusion
        (by have := Nat.cast_nonneg (α := ℝ) s; linarith : (-1/2 : ℝ)≤(s : ℝ)+1/2) z.val) :
    D.rawIntegerInverseSource s z=q := by
  let I : ScalarSobolev s →L[ℂ] PeriodOneHminusOne := WeightedCoeff.sobolevInclusion (by have := Nat.cast_nonneg (α := ℝ) s; linarith : (-1 : ℝ)≤s)
  have hreal (a : ScalarSobolev s) (ha : ∀ n : ℤ, a.val (-n)=conj (a.val n)) :
      IsRealPeriodOneHminusOne (I a) := by
    intro j
    simpa only [I,WeightedCoeff.sobolevInclusion_apply] using ha j
  apply WeightedCoeff.sobolevInclusion_injective (by have := Nat.cast_nonneg (α := ℝ) s; linarith : (-1 : ℝ)≤s)
  apply D.signed_injective_real_meanZero _ _
    (hreal _ (D.rawIntegerInverseSource_real s z)) (hreal q hq)
  · simpa only [I,WeightedCoeff.sobolevInclusion_apply] using D.rawIntegerInverseSource_zero s z
  · simpa only [I,WeightedCoeff.sobolevInclusion_apply] using hm
  · exact (D.rawIntegerInverseSource_signed s z).trans h.symm

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
