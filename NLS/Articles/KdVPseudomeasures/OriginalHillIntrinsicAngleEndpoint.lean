import NLS.Articles.KdVPseudomeasures.OriginalHillAnglePairIsospectral
import NLS.KdV.HillIntrinsicAngleEndpointZero

/-! The complete original Abelian angle differential is intrinsic
and agrees with every actual local phase chart as a complex germ.
Its pair bracket has the proved endpoint zero value and commutes with
every discriminant at all real sources on its open-gap domain. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier

theorem original_Hill_complete_angle_cotangent_chart (q : OriginalHminusOnePotential) (n : ℕ+)
    (hg : hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients q) ≠ 0) :
    ∃ P : HillProductEquationPatch, ∃ C : HillPhysicalOnIndexPhaseChart P n,
      C.center=originalPeriodOneCoefficients q ∧ originalPeriodOneCoefficients q ∈ C.source ∧
      hillHminusCompletePhaseCotangent n =ᶠ[𝓝 (originalPeriodOneCoefficients q)] fderiv ℂ C.completePhase := by
  have hr := originalPeriodOneCoefficients_real q
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch (originalPeriodOneCoefficients q) hr
  obtain ⟨C,hcenter,hCq⟩ := exists_hillPhysicalOnIndexPhaseChart P n (originalPeriodOneCoefficients q)
    (P.real_mem_physicalDirichletSource _ hq hr) hr hg
  exact ⟨P,C,hcenter,hCq,C.eventually_completePhaseCotangent_eq_fderiv _ hCq hr⟩

theorem original_Hill_intrinsic_complete_angle_mixed_brackets (q : OriginalHminusOnePotential) (n : ℕ+)
    (hg : hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients q) ≠ 0) :
    (∀ k : ℕ+, hillHminusCompletePhaseFunctionalBracket n (hillHminusCanonicalAction k)
      (originalPeriodOneCoefficients q)=-(if k=n then (1:ℂ) else 0)) ∧
    ∀ E : ℂ, hillHminusCompletePhaseFunctionalBracket n (fun p => hillHminusDiscriminant p E)
      (originalPeriodOneCoefficients q)=(1/2:ℂ)*hillHminusCanonicalPsi n (E,originalPeriodOneCoefficients q) :=
  ⟨(fun k => hillHminusCompletePhaseFunctionalBracket_action_of_real n k _ (originalPeriodOneCoefficients_real q) hg),
    (fun E => hillHminusCompletePhaseFunctionalBracket_discriminant_of_real n E _ (originalPeriodOneCoefficients_real q) hg)⟩

theorem original_Hill_intrinsic_angle_pair_discriminant_stationarity (q : OriginalHminusOnePotential) (n m : ℕ+)
    (hn : hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients q) ≠ 0)
    (hm : hillHminusCanonicalGapSquare m (originalPeriodOneCoefficients q) ≠ 0) (E : ℂ) :
    NLS.Poisson.hminusGardnerBracket (hillHminusCompletePhasePairBracket n m)
      (fun p => hillHminusDiscriminant p E) (originalPeriodOneCoefficients q)=0 :=
  hillHminusCompletePhasePair_discriminant_Gardner_eq_zero_of_real n m E _ (originalPeriodOneCoefficients_real q) hn hm

theorem original_Hill_complete_angle_pair_zero_at_all_endpoints (q : OriginalHminusOnePotential) (n m : ℕ+)
    (hn : hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients q) ≠ 0)
    (hm : hillHminusCanonicalGapSquare m (originalPeriodOneCoefficients q) ≠ 0)
    (hterminal : ∀ j : ℕ+, hillHminusDirichletSheet j (originalPeriodOneCoefficients q)=0) :
    hillHminusCompletePhasePairBracket n m (originalPeriodOneCoefficients q)=0 :=
  hillHminusCompletePhasePairBracket_eq_zero_at_all_endpoints n m _ (originalPeriodOneCoefficients_real q) hn hm hterminal

end NLS.Articles.KdVPseudomeasures
