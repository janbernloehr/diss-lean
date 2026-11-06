import NLS.SequenceSpaces.SobolevSignedCompletion

/-! # Full native signed Sobolev germs from actual positive germs

Both conjugate points lie in an explicit complex open intersection.
The original half-order target shift, exact rough inclusion and a common
native norm bound are retained before every signed coordinate.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal ComplexConjugate
namespace NLS

/-- A genuine native positive germ yields a COMPLEX ANALYTIC full signed
H^(t-1)-to-h^(t-1/2) germ at every eligible real source, with EXACT
inclusion to the same original rough signed completion. -/
theorem exists_sobolev_signedTargetLift_germ
    (t : ℝ) (ht : 0≤t) (P : PeriodOneHminusOne → Coeff 2) (η : ℝ)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hr : ∀ k : ℤ, (periodOneSobolevImageInclusion t ht q).val (-k)=
      conj ((periodOneSobolevImageInclusion t ht q).val k))
    (U : Set (WeightedCoeff (Weight.sobolev (t-1)) 2)) (hU : IsOpen U) (hqU : q∈U)
    (M : ℝ) (hM : 0≤M) (F : WeightedCoeff (Weight.sobolev (t-1)) 2 → Coeff 2)
    (hFa : AnalyticOnNhd ℂ F U)
    (hdata : ∀ p∈U, periodOneSobolevImageInclusion t ht p∈ball (0 : PeriodOneHminusOne) η ∧
      ‖F p‖≤M ∧ ∀ n : ℤ, F p n=(Weight.sobolev t n : ℂ)*P (periodOneSobolevImageInclusion t ht p) n) :
    ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
      ∃ C : ℝ, ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev (t-1/2)) 2,
        0≤C ∧ AnalyticOnNhd ℂ g V ∧ ∀ p∈V,
          periodOneSobolevImageInclusion t ht p∈ball (0 : PeriodOneHminusOne) η ∧ ‖g p‖≤C ∧
          WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) (g p)=
            WeightedCoeff.signedTargetLift (Weight.sobolev (-1)) (Weight.sobolev (-1/2)) P
              (periodOneSobolevImageInclusion t ht p) := by
  let v := Weight.sobolev (t-1)
  let J := WeightedCoeff.conjugateReflection (p := 2) v (Weight.sobolev_neg (t-1))
  let V := U∩J ⁻¹' U
  have hV : IsOpen V := hU.inter (hU.preimage
    (WeightedCoeff.continuous_conjugateReflection v (Weight.sobolev_neg (t-1))))
  have hJq : J q=q := sobolev_conjugateReflection_fixed_of_real_inclusion t ht q hr
  have hqV : q∈V := ⟨hqU,by change J q∈U;rw [hJq];exact hqU⟩
  let g := WeightedCoeff.signedTargetLift v (Weight.sobolev (t-1/2)) F
  refine ⟨V,hV,hqV,2*M,g,by positivity,
    WeightedCoeff.analyticOnNhd_signedTargetLift v (Weight.sobolev (t-1/2))
      (Weight.sobolev_neg (t-1)) F U hFa,?_⟩
  intro p hp
  refine ⟨(hdata p hp.1).1,?_,?_⟩
  · rw [WeightedCoeff.norm_signedTargetLift]
    exact WeightedCoeff.norm_normalizedSignedCompletion_le v (Weight.sobolev_neg (t-1)) F p M
      (hdata p hp.1).2.1 (hdata (J p) hp.2).2.1
  · apply signedTargetLift_sobolev_inclusion t ht P F p
    apply normalizedSignedCompletion_sobolev_apply t ht P F p (hdata p hp.1).2.2
    intro n
    have hj : periodOneSobolevImageInclusion t ht (J p)=
        periodOneHminusConjugation (periodOneSobolevImageInclusion t ht p) :=
      periodOneSobolevImageInclusion_conjugateReflection t ht p
    exact ((hdata (J p) hp.2).2.2 n).trans
      (congrArg (fun a : PeriodOneHminusOne => (Weight.sobolev t n : ℂ)*P a n) hj)

end NLS
