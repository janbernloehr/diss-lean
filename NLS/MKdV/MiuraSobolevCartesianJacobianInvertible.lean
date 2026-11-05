import NLS.MKdV.MiuraSobolevCartesianJacobianCompact
import NLS.MKdV.MiuraSobolevCartesianComplexCompatibility
import NLS.MKdV.MiuraCartesianJacobianInvertible

/-! # Native Sobolev Cartesian derivatives and inverse charts at every real profile

The native complex germ commutes with the coefficient-preserving L²
inclusions. Its derivative is injective by the checked L² theorem at H¹
profiles, and the compact remainder gives native Banach bijectivity.
-/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraSobolevCartesianJacobian_injective (s : ℕ) (hs : 1 ≤ s) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    Function.Injective (fderiv ℂ (miuraSobolevPositiveCartesianMap s) a) := by
  let b := hierarchySobolevToScalarDomain s hs a
  have hb : ∀ j, b.val j = conj (b.val (-j)) := by
    intro j
    simpa only [b,hierarchySobolevToScalarDomain_apply] using ha j
  have he : hierarchySobolevJetL2 s 0 (Nat.zero_le s) a = scalarInclusion b := by
    ext n
    simp only [hierarchySobolevJetL2_apply,pow_zero,one_mul,scalarInclusion_apply,b,hierarchySobolevToScalarDomain_apply]
  intro h k hhk
  have ht := congrArg (miuraPositiveSobolevL2CartesianInclusion s) hhk
  have hd := congrArg (fun T : ScalarSobolev s →L[ℂ] MiuraPositiveCartesianTarget => T h)
    (miuraSobolevCartesianJacobian_L2 s a ha)
  have hd' := congrArg (fun T : ScalarSobolev s →L[ℂ] MiuraPositiveCartesianTarget => T k)
    (miuraSobolevCartesianJacobian_L2 s a ha)
  rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,he] at hd hd'
  have hi := (miuraCartesianJacobian_bijective_H1 b hb).1 ((hd.symm.trans ht).trans hd')
  apply Subtype.ext
  funext n
  simpa only [hierarchySobolevJetL2_apply,pow_zero,one_mul] using congrArg (fun c : Coeff 2 => c n) hi

/-- Full complex derivative bijectivity in H^s and h^(s+1/2), at every
real H^s profile for s>=1, with closed gaps and every signed mean. -/
theorem miuraSobolevCartesianJacobian_bijective (s : ℕ) (hs : 1 ≤ s) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    Function.Bijective (fderiv ℂ (miuraSobolevPositiveCartesianMap s) a) :=
  NLS.FunctionalAnalysis.bijective_of_injective_of_compact_sub_equiv
    (miuraSobolevCartesianFreeEquiv s) _
    (isCompactOperator_miuraSobolevCartesianJacobian_sub_free s a ha)
    (miuraSobolevCartesianJacobian_injective s hs a ha)

theorem exists_miuraSobolevCartesian_derivative_equiv (s : ℕ) (hs : 1 ≤ s) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    ∃ L : ScalarSobolev s ≃L[ℂ] MiuraPositiveSobolevTarget s,
      L.toContinuousLinearMap = fderiv ℂ (miuraSobolevPositiveCartesianMap s) a :=
  NLS.FunctionalAnalysis.exists_equiv_of_injective_of_compact_sub_equiv
    (miuraSobolevCartesianFreeEquiv s) _
    (isCompactOperator_miuraSobolevCartesianJacobian_sub_free s a ha)
    (miuraSobolevCartesianJacobian_injective s hs a ha)

/-- Genuine complex analytic inverse neighborhoods in the native
Sobolev norms at arbitrary physical profiles. -/
theorem exists_miuraSobolevPositiveCartesian_analytic_chart (s : ℕ) (hs : 1 ≤ s) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    ∃ P : OpenPartialHomeomorph (ScalarSobolev s) (MiuraPositiveSobolevTarget s),
      (P : ScalarSobolev s → MiuraPositiveSobolevTarget s) = miuraSobolevPositiveCartesianMap s ∧
      a ∈ P.source ∧ AnalyticOnNhd ℂ (miuraSobolevPositiveCartesianMap s) P.source ∧
        AnalyticOnNhd ℂ P.symm P.target := by
  obtain ⟨L,hL⟩ := exists_miuraSobolevCartesian_derivative_equiv s hs a ha
  exact NLS.ComplexAnalysis.exists_analytic_openPartialHomeomorph_of_fderiv_equiv
    (analyticAt_miuraSobolevPositiveCartesianMap s a ha) L hL.symm

end NLS.MKdV
