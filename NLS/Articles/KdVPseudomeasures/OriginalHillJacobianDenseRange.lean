import NLS.Articles.KdVPseudomeasures.OriginalHillNativeSignedGardner
import NLS.KdV.HillNativeMeanZeroDerivative
import NLS.Poisson.GardnerHamiltonianZeroMode
import NLS.SequenceSpaces.ZeroModeSingleDenseRange

/-! Actual source preimages of every signed nonzero target mode and
dense range of the complex mean-zero Birkhoff derivative at EVERY
physical source. No closed range or Fredholm hypothesis is assumed. -/
noncomputable section
open Set Complex NLS.KdV NLS.Poisson
namespace NLS.Articles.KdVPseudomeasures

theorem hillRealNativeJacobian_single_preimage (q : HillRealMeanZeroSource) (k : ℤ) (hk : k ≠ 0) :
    ∃ v : HillMeanZeroSource, (fderiv ℂ hillMeanZeroComplexMap q.val) v=
      WeightedCoeff.zeroModeSingle (p := 2) (Weight.signedSobolev (-1/2)) k hk 1 := by
  let Q := hillRealMeanZeroInclusion q
  let V := gardnerHamiltonianDirection (fderiv ℂ (hillHminusNativeCoordinate (-k)) Q)
  have hV : V.val 0=0 := gardnerHamiltonianDirection_zero_mode _
  let v : HillMeanZeroSource := ⟨V,hV⟩
  let c : ℂ := if 0 < k then I else -I
  have hc : c ≠ 0 := by
    dsimp only [c]
    split_ifs
    · exact I_ne_zero
    · exact neg_ne_zero.mpr I_ne_zero
  have hq : q.val ∈ hillMeanZeroComplexDomain :=
    real_mem_hillMeanZeroComplexDomain q.val q.property
  refine ⟨c⁻¹ • v,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext j
  rw [fderiv_hillMeanZeroComplexMap_coordinate q.val hq (c⁻¹ • v) j]
  change (fderiv ℂ (hillHminusNativeCoordinate j) Q) (c⁻¹ • V)=_
  rw [map_smul,smul_eq_mul,apply_gardnerHamiltonianDirection]
  change c⁻¹*hillHminusNativeGardnerBracket j (-k) Q= _
  rw [hillRealNativeGardner_signed_canonical j (-k) q,WeightedCoeff.zeroModeSingle_apply]
  simp only [Pi.single_apply]
  by_cases hj : j=k
  · subst j
    rw [if_neg hk,if_pos rfl,if_pos rfl]
    exact inv_mul_cancel₀ hc
  · rw [if_neg hj]
    by_cases hj0 : j=0
    · rw [if_pos hj0,mul_zero]
    · rw [if_neg hj0,if_neg (by intro he; exact hj (neg_injective he).symm),mul_zero]

theorem hillRealNativeJacobian_denseRange (q : HillRealMeanZeroSource) :
    DenseRange (fderiv ℂ hillMeanZeroComplexMap q.val) := by
  apply WeightedCoeff.denseRange_of_zeroModeSingle_mem_range (Weight.signedSobolev (-1/2)) (by simp)
  intro k hk
  exact hillRealNativeJacobian_single_preimage q k hk

theorem original_Hill_native_Jacobian_denseRange (q : OriginalHminusOnePotential) :
    DenseRange (fderiv ℂ hillMeanZeroComplexMap (originalHillRealMeanZeroSource q).val) :=
  hillRealNativeJacobian_denseRange (originalHillRealMeanZeroSource q)

end NLS.Articles.KdVPseudomeasures
