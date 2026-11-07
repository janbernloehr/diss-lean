import NLS.Articles.KdVPseudomeasures.OriginalHillAnglePairCommutation
import NLS.KdV.HillNativeProductPhase

/-! The actual signed-coordinate Gardner matrix on the joint original
open-gap locus. Full native coordinate cotangents are expanded using
the proved actual action, intrinsic phase and exact product identities. -/
noncomputable section
open Set Complex NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_native_Gardner_own_positive_negative (n : ℕ+) (q : OriginalHminusOnePotential)
    (hn : hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients q) ≠ 0) :
    hillHminusNativeGardnerBracket (n:ℤ) (-(n:ℤ)) (originalPeriodOneCoefficients q)=I := by
  let Q := originalPeriodOneCoefficients q
  let A := fderiv ℂ (hillHminusCanonicalAction n) Q
  let T := hillHminusCompletePhaseCotangent n Q
  let B := NLS.Poisson.gardnerCotangentBivector
  have hr := originalPeriodOneCoefficients_real q
  have hAA : B A A=0 := hillHminusCanonicalActions_Gardner_commute_of_real Q hr n n
  have hTT : B T T=0 := original_Hill_complete_angle_pair_Gardner_commute n n q hn hn
  have hTA : B T A=-(1:ℂ) := by
    simpa only [hillHminusCompletePhaseFunctionalBracket,if_pos rfl,ite_true] using
      hillHminusCompletePhaseFunctionalBracket_action_of_real n n Q hr hn
  have hAT : B A T=1 := by
    rw [show B A T= -B T A from NLS.Poisson.gardnerCotangentBivector_antisymm A T,hTA,neg_neg]
  have hd := fderiv_hillHminusNativeCoordinates_from_action_phase n Q hr hn
  have hp : hillHminusNativeCoordinate (n:ℤ) Q*hillHminusNativeCoordinate (-(n:ℤ)) Q=hillHminusCanonicalAction n Q :=
    hillHminusNativeComplexMap_action_identity Q (real_mem_hillHminusActionAngleNativeDomain Q hr) n
  have hi : hillHminusCanonicalAction n Q ≠ 0 :=
    fun he => hn ((hillHminusCanonicalAction_eq_zero_iff_gapSquare_of_real Q hr n).mp he)
  change B (fderiv ℂ (hillHminusNativeCoordinate (n:ℤ)) Q) (fderiv ℂ (hillHminusNativeCoordinate (-(n:ℤ))) Q)=I
  rw [hd.1,hd.2]
  change B (_ • ((2*hillHminusCanonicalAction n Q)⁻¹ • A-I • T))
    (_ • ((2*hillHminusCanonicalAction n Q)⁻¹ • A+I • T))=I
  simp only [map_smul,map_add,map_sub,smul_apply,sub_apply,smul_eq_mul,
    hAA,hTT,hTA,hAT,mul_zero,sub_zero,zero_sub,mul_one,mul_neg_one]
  field_simp [hi]
  linear_combination 2*hp

theorem original_Hill_native_Gardner_distinct_open (n m : ℕ+) (hnm : n ≠ m)
    (q : OriginalHminusOnePotential)
    (hn : hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients q) ≠ 0)
    (hm : hillHminusCanonicalGapSquare m (originalPeriodOneCoefficients q) ≠ 0) :
    hillHminusNativeGardnerBracket (n:ℤ) (m:ℤ) (originalPeriodOneCoefficients q)=0 ∧
    hillHminusNativeGardnerBracket (-(n:ℤ)) (-(m:ℤ)) (originalPeriodOneCoefficients q)=0 ∧
    hillHminusNativeGardnerBracket (n:ℤ) (-(m:ℤ)) (originalPeriodOneCoefficients q)=0 := by
  let Q := originalPeriodOneCoefficients q
  let An := fderiv ℂ (hillHminusCanonicalAction n) Q
  let Am := fderiv ℂ (hillHminusCanonicalAction m) Q
  let Tn := hillHminusCompletePhaseCotangent n Q
  let Tm := hillHminusCompletePhaseCotangent m Q
  let B := NLS.Poisson.gardnerCotangentBivector
  have hr := originalPeriodOneCoefficients_real q
  have hAA : B An Am=0 := hillHminusCanonicalActions_Gardner_commute_of_real Q hr n m
  have hTT : B Tn Tm=0 := original_Hill_complete_angle_pair_Gardner_commute n m q hn hm
  have hTA : B Tn Am=0 := by
    simpa only [hillHminusCompletePhaseFunctionalBracket,if_neg hnm.symm,neg_zero] using
      hillHminusCompletePhaseFunctionalBracket_action_of_real n m Q hr hn
  have hAT : B An Tm=0 := by
    have he : B Tm An=0 := by
      simpa only [hillHminusCompletePhaseFunctionalBracket,if_neg hnm,neg_zero] using
        hillHminusCompletePhaseFunctionalBracket_action_of_real m n Q hr hm
    rw [show B An Tm= -B Tm An from NLS.Poisson.gardnerCotangentBivector_antisymm An Tm,he,neg_zero]
  have hdn := fderiv_hillHminusNativeCoordinates_from_action_phase n Q hr hn
  have hdm := fderiv_hillHminusNativeCoordinates_from_action_phase m Q hr hm
  change B (fderiv ℂ (hillHminusNativeCoordinate (n:ℤ)) Q) (fderiv ℂ (hillHminusNativeCoordinate (m:ℤ)) Q)=0 ∧
    B (fderiv ℂ (hillHminusNativeCoordinate (-(n:ℤ))) Q) (fderiv ℂ (hillHminusNativeCoordinate (-(m:ℤ))) Q)=0 ∧
    B (fderiv ℂ (hillHminusNativeCoordinate (n:ℤ)) Q) (fderiv ℂ (hillHminusNativeCoordinate (-(m:ℤ))) Q)=0
  rw [hdn.1,hdn.2,hdm.1,hdm.2]
  change B (_ • (_ • An-I • Tn)) (_ • (_ • Am-I • Tm))=0 ∧
    B (_ • (_ • An+I • Tn)) (_ • (_ • Am+I • Tm))=0 ∧
    B (_ • (_ • An-I • Tn)) (_ • (_ • Am+I • Tm))=0
  simp only [map_smul,map_add,map_sub,smul_apply,add_apply,sub_apply,smul_eq_mul,
    hAA,hTT,hTA,hAT,mul_zero,add_zero,sub_zero,and_self]

theorem original_Hill_native_Gardner_open_matrix (n m : ℕ+) (q : OriginalHminusOnePotential)
    (hn : hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients q) ≠ 0)
    (hm : hillHminusCanonicalGapSquare m (originalPeriodOneCoefficients q) ≠ 0) :
    hillHminusNativeGardnerBracket (n:ℤ) (m:ℤ) (originalPeriodOneCoefficients q)=0 ∧
    hillHminusNativeGardnerBracket (-(n:ℤ)) (-(m:ℤ)) (originalPeriodOneCoefficients q)=0 ∧
    hillHminusNativeGardnerBracket (n:ℤ) (-(m:ℤ)) (originalPeriodOneCoefficients q)=if n=m then I else 0 := by
  by_cases he : n=m
  · subst m
    exact ⟨hillHminusNativeGardnerBracket_self _ _,hillHminusNativeGardnerBracket_self _ _,by
      rw [if_pos rfl]; exact original_Hill_native_Gardner_own_positive_negative n q hn⟩
  · simpa only [if_neg he] using original_Hill_native_Gardner_distinct_open n m he q hn hm

end NLS.Articles.KdVPseudomeasures
