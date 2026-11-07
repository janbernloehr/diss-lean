import NLS.Articles.KdVPseudomeasures.OriginalHillL2MomentumTrace
import NLS.SequenceSpaces.PhysicalCoefficientCompactness
import NLS.SequenceSpaces.CoeffLowerTopology

/-! Bounded actual L2 sources have physical coefficient limits in the
SAME L2 space, and their native Hminus inclusions converge strongly.
The ACTUAL KdV momentum trace prevents loss of the L2 norm. -/
noncomputable section
open Set Filter Topology NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

theorem hillL2SourceInclusion_lowerCoefficients (u : HillRealL2BanachSource) :
    WeightedCoeff.lowerOfCoefficients (q:=2) (-1) (by simp) (by norm_num)
      (hillL2SourceCoefficients u)=(hillL2SourceInclusion u).val.val := by
  apply Subtype.ext
  funext k
  rw [WeightedCoeff.lowerOfCoefficients_apply,hillL2SourceCoefficients_apply]
  exact (hillL2SourceInclusion_apply u k).symm

theorem tendsto_hillL2SourceInclusion_of_bounded_coefficients
    {α : Type*} {l : Filter α} (a : α → HillRealL2BanachSource) (b : HillRealL2BanachSource)
    (hb : Bornology.IsBounded (range a))
    (ht : ∀ n : ℤ, Tendsto (fun k => (a k).val.val.val n) l (𝓝 (b.val.val.val n))) :
    Tendsto (fun k => hillL2SourceInclusion (a k)) l (𝓝 (hillL2SourceInclusion b)) := by
  have hb' : Bornology.IsBounded (range (fun k => hillL2SourceCoefficients (a k))) := by
    obtain ⟨C,hC⟩ := hb.exists_norm_le
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨C,?_⟩
    rintro _ ⟨k,rfl⟩
    rw [norm_hillL2SourceCoefficients]
    exact hC _ ⟨k,rfl⟩
  have hcoeff : ∀ n : ℤ, Tendsto (fun k => hillL2SourceCoefficients (a k) n) l
      (𝓝 (hillL2SourceCoefficients b n)) := by
    intro n
    simpa only [hillL2SourceCoefficients_apply] using ht n
  have hw := WeightedCoeff.tendsto_lowerOfCoefficients_of_bounded_coefficients (q:=2)
    (-1) (by simp) (by norm_num) (fun k => hillL2SourceCoefficients (a k))
    (hillL2SourceCoefficients b) hb' hcoeff
  simp_rw [hillL2SourceInclusion_lowerCoefficients] at hw
  apply tendsto_subtype_rng.mpr
  apply tendsto_subtype_rng.mpr
  exact hw

theorem hillL2_source_bounded_of_nativeMap_bounded {α : Type*} (a : α → HillRealL2BanachSource)
    (hb : Bornology.IsBounded (range (fun k => hillL2NativeMap (a k)))) :
    Bornology.IsBounded (range a) := by
  obtain ⟨C,hC⟩ := hb.exists_norm_le
  let D := 2*Real.pi*(max C 0)^2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨D+1,?_⟩
  rintro _ ⟨k,rfl⟩
  have hk : ‖hillL2NativeMap (a k)‖ ≤ max C 0 := (hC _ ⟨k,rfl⟩).trans (le_max_left C 0)
  have hs : ‖a k‖^2 ≤ D := by
    rw [norm_sq_hillL2NativeMap]
    dsimp [D]
    exact mul_le_mul_of_nonneg_left (sq_le_sq₀ (norm_nonneg _) (le_max_right C 0) |>.mpr hk)
      (by positivity)
  change ‖a k‖ ≤ D+1
  calc
    ‖a k‖ ≤ ‖a k‖^2+1 := by nlinarith [sq_nonneg (‖a k‖-1),norm_nonneg (a k)]
    _ ≤ D+1 := by linarith

theorem tendsto_hillL2_of_coefficients_of_nativeMap
    {α : Type*} {l : Filter α} (a : α → HillRealL2BanachSource) (b : HillRealL2BanachSource)
    (ht : ∀ n : ℤ, Tendsto (fun k => (a k).val.val.val n) l (𝓝 (b.val.val.val n)))
    (hF : Tendsto (fun k => hillL2NativeMap (a k)) l (𝓝 (hillL2NativeMap b))) :
    Tendsto a l (𝓝 b) := by
  apply WeightedCoeff.tendsto_fourierRealZero_of_coefficientwise_of_norm_sq (Weight.signedSobolev 0) a b ht
  simp_rw [norm_sq_hillL2NativeMap]
  exact (hF.norm.pow 2).const_mul (2*Real.pi)

end NLS.Articles.KdVPseudomeasures
