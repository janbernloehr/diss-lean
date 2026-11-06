import NLS.SequenceSpaces.SobolevSignedAnalyticGerms
import NLS.SequenceSpaces.SignedCompletionDerivative

/-! # Full native signed Sobolev germs with actual compact derivatives

A positive weighted germ and its compact principal difference at BOTH
actual conjugate source points give a genuine full native signed germ.
The exact half-order target inclusion and derivative are retained.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS

/-- Full native signed compact derivative germs, with exact inclusion to
the SAME weak completion on a genuine open complex neighborhood. -/
theorem exists_sobolev_signedTargetLift_compact_germ
    (t : ℝ) (ht : 0≤t) (Y : PeriodOneHminusOne → Coeff 2) (η : ℝ)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hr : ∀ k : ℤ, (periodOneSobolevImageInclusion t ht q).val (-k)=
      conj ((periodOneSobolevImageInclusion t ht q).val k))
    (U : Set (WeightedCoeff (Weight.sobolev (t-1)) 2)) (hU : IsOpen U) (hqU : q∈U)
    (M : ℝ) (hM : 0≤M) (H : WeightedCoeff (Weight.sobolev (t-1)) 2 → Coeff 2)
    (hHa : AnalyticOnNhd ℂ H U)
    (hdata : ∀ p∈U, periodOneSobolevImageInclusion t ht p∈ball (0 : PeriodOneHminusOne) η ∧
      ‖H p‖≤M ∧ ∀ n : ℤ, H p n=(Weight.sobolev t n : ℂ)*Y (periodOneSobolevImageInclusion t ht p) n)
    (A : WeightedCoeff (Weight.sobolev (t-1)) 2 →
      WeightedCoeff (Weight.sobolev (t-1)) 2 →L[ℂ] Coeff 2)
    (hc : ∀ p∈U, IsCompactOperator (fderiv ℂ H p-A p)) :
    ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧ V⊆U ∧
      (∀ p∈V, WeightedCoeff.conjugateReflection (Weight.sobolev (t-1)) (Weight.sobolev_neg (t-1)) p∈V) ∧
      ∃ C : ℝ, ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev (t-1/2)) 2,
        0≤C ∧ AnalyticOnNhd ℂ g V ∧ ∀ p∈V,
          periodOneSobolevImageInclusion t ht p∈ball (0 : PeriodOneHminusOne) η ∧ ‖g p‖≤C ∧
          WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) (g p)=
            WeightedCoeff.signedTargetLift (Weight.sobolev (-1)) (Weight.sobolev (-1/2)) Y
              (periodOneSobolevImageInclusion t ht p) ∧
          IsCompactOperator (fderiv ℂ g p-WeightedCoeff.nativeSignedPrincipal
            (Weight.sobolev (t-1)) (Weight.sobolev (t-1/2)) (Weight.sobolev_neg (t-1))
            (A p) (A (WeightedCoeff.conjugateReflection (Weight.sobolev (t-1)) (Weight.sobolev_neg (t-1)) p))) := by
  let v := Weight.sobolev (t-1)
  let J := WeightedCoeff.conjugateReflection (p := 2) v (Weight.sobolev_neg (t-1))
  let V := U∩J ⁻¹' U
  have hV : IsOpen V := hU.inter (hU.preimage
    (WeightedCoeff.continuous_conjugateReflection v (Weight.sobolev_neg (t-1))))
  have hJq : J q=q := sobolev_conjugateReflection_fixed_of_real_inclusion t ht q hr
  have hqV : q∈V := ⟨hqU,by change J q∈U;rw [hJq];exact hqU⟩
  have hJclosed : ∀ p∈V, J p∈V := by
    intro p hp
    refine ⟨hp.2,?_⟩
    change J (J p)∈U
    simpa only [J,WeightedCoeff.conjugateReflection_involutive] using hp.1
  let g := WeightedCoeff.signedTargetLift v (Weight.sobolev (t-1/2)) H
  refine ⟨V,hV,hqV,inter_subset_left,hJclosed,2*M,g,by positivity,
    WeightedCoeff.analyticOnNhd_signedTargetLift v (Weight.sobolev (t-1/2))
      (Weight.sobolev_neg (t-1)) H U hHa,?_⟩
  intro p hp
  refine ⟨(hdata p hp.1).1,?_,?_,?_⟩
  · rw [WeightedCoeff.norm_signedTargetLift]
    exact WeightedCoeff.norm_normalizedSignedCompletion_le v (Weight.sobolev_neg (t-1)) H p M
      (hdata p hp.1).2.1 (hdata (J p) hp.2).2.1
  · apply signedTargetLift_sobolev_inclusion t ht Y H p
    apply normalizedSignedCompletion_sobolev_apply t ht Y H p (hdata p hp.1).2.2
    intro n
    have h := (hdata (J p) hp.2).2.2 n
    simpa only [J,v,periodOneSobolevImageInclusion_conjugateReflection] using h
  · exact WeightedCoeff.isCompactOperator_fderiv_signedTargetLift_sub v (Weight.sobolev (t-1/2))
      (Weight.sobolev_neg (t-1)) H p (hHa p hp.1).differentiableAt (hHa (J p) hp.2).differentiableAt
      (A p) (A (J p)) (hc p hp.1) (hc (J p) hp.2)

end NLS
