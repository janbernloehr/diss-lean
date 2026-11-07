import NLS.KdV.HillHminusPhysicalSourceDensity
import NLS.SequenceSpaces.SobolevSignedCompletion

/-! Every real native original L2 source is the EXACT original Fourier
source of a physical Hill potential; no density approximation is needed. -/
noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

theorem native_l2_source_eq_physical
    (q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)
    (hr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion 1 (by norm_num) q)) :
    ∃ p : RealPeriodOneHillPotential, hillOriginalHminusSource p.val=
      periodOneSobolevImageInclusion 1 (by norm_num) q := by
  let u := WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1-1) q
  have hu : ∀ j : ℤ,u (-j)=conj (u j) := by
    intro j
    simpa only [u,WeightedCoeff.sobolevToL2_apply,periodOneSobolevImageInclusion_apply] using hr j
  obtain ⟨p,hp⟩ := periodOneRealL2Inclusion_mem_range_physical ⟨u,hu⟩
  refine ⟨p,?_⟩
  have he := congrArg Subtype.val hp
  exact he.trans (by
    apply Subtype.ext
    funext j
    simp only [periodOneRealL2Inclusion,periodOneL2Inclusion_apply,
      periodOneSobolevImageInclusion_apply,u,WeightedCoeff.sobolevToL2_apply])

theorem native_l2_inclusion_real_of_fixed
    (q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)
    (hr : WeightedCoeff.conjugateReflection (Weight.sobolev ((1:ℝ)-1)) (Weight.sobolev_neg _) q=q) :
    IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion 1 (by norm_num) q) := by
  intro j
  have h := congrArg (fun a : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 => a.val (-j)) hr
  simpa only [WeightedCoeff.conjugateReflection_apply,neg_neg,periodOneSobolevImageInclusion_apply] using h.symm

end NLS.KdV
