import NLS.KdV.HillPhysicalOffIndexAbelianValue
import NLS.ComplexAnalysis.PrescribedAnalyticSquareRoot

/-! A local regular spectral sheet through the ACTUAL physical
Dirichlet divisor. Its full denominator squares to the ORIGINAL Hill
radicand and equals the physical norming sheet at the divisor. The
Abelian value is the continuation of the genuine endpoint integral. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_physicalAbelian_regular_germ (P : HillProductEquationPatch) (n m : ℕ+) (hmn : m ≠ n)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource)
    (hne : P.physicalDirichletRootCoefficient m q ≠ 0) :
    ∃ U : Set ℂ, IsOpen U ∧ P.physicalDirichletFrequency ((m:ℕ):ℤ) q ∈ U ∧
      U ⊆ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) ∧
      ∃ R F : ℂ → ℂ, AnalyticOnNhd ℂ R U ∧ AnalyticOnNhd ℂ F U ∧
        R (P.physicalDirichletFrequency ((m:ℕ):ℤ) q) = P.physicalDirichletRootCoefficient m q ∧
        F (P.physicalDirichletFrequency ((m:ℕ):ℤ) q) = P.physicalOffIndexAbelianValue n m q ∧
        (∀ z ∈ U, R z ≠ 0 ∧ R z^2 = sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) z ∧
          HasDerivAt F ((2*z*hillHminusCanonicalPsi n (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),q))/
            (P.abelianGapRootMultiplier m (z,q)*R z)) z ∧
          (P.abelianGapRootMultiplier m (z,q)*R z)^2 = hillHminusRadicand q (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ))) ∧
        P.abelianGapRootMultiplier m (P.physicalDirichletFrequency ((m:ℕ):ℤ) q,q)*
          R (P.physicalDirichletFrequency ((m:ℕ):ℤ) q) = hillHminusDirichletSheet m q ∧
        ∀ z ∈ U, z ∈ P.abelianGapDisc m q → F z =
          (sourceStandardRoot (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) z/R z)*P.offIndexAbelianEndpointIntegral n m q z := by
  let μ := P.physicalDirichletFrequency ((m:ℕ):ℤ) q
  let w := P.physicalDirichletRootCoefficient m q
  let f := sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)
  have hf : AnalyticOnNhd ℂ f univ := by
    intro z _
    unfold f sourceAngularSelectedPolynomial quadraticRootPolynomial
    fun_prop
  have hbase : f μ = w^2 := (P.physicalDirichletRootCoefficient_sq m q hq).symm
  let U := ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) ∩ prescribedSquareRootDomain f w
  let R := prescribedSquareRoot f w
  let H : ℂ → ℂ := fun z => P.offIndexAbelianFilledQuotient n m (z,q)
  let F : ℂ → ℂ := fun z => R z*H z
  have hU : IsOpen U := isOpen_ball.inter (isOpen_prescribedSquareRootDomain f w hf.continuous)
  have hμU : μ ∈ U := ⟨P.physicalDirichletFrequency_mem_disc q hq _,mem_prescribedSquareRootDomain f w hne μ hbase⟩
  have hsub : U ⊆ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) := inter_subset_left
  have hR : AnalyticOnNhd ℂ R U := (analyticOnNhd_prescribedSquareRoot f w hf).mono inter_subset_right
  have hH : AnalyticOnNhd ℂ H U := by
    intro z hz
    exact (P.analytic_offIndexAbelianFilledQuotient n m hmn (z,q) ⟨hz.1,hq.1⟩).comp
      (f := fun t : ℂ => (t,q)) (analyticAt_id.prod analyticAt_const)
  have hRbase : R μ = w := prescribedSquareRoot_base f w hne μ hbase
  have hRne (z : ℂ) (hz : z ∈ U) : R z ≠ 0 := prescribedSquareRoot_ne_zero f w hne z hz.2
  have hRsq (z : ℂ) : R z^2 = f z := prescribedSquareRoot_sq f w hne z
  refine ⟨U,hU,hμU,hsub,R,F,hR,hR.mul hH,hRbase,?_,?_,?_,?_⟩
  · change R μ*H μ = w*H μ
    rw [hRbase]
  · intro z hz
    refine ⟨hRne z hz,hRsq z,?_,?_⟩
    · have hd := P.hasDerivAt_offIndexAbelianRegularSheetPrimitive n m hmn (fun t => R t.1)
        q hq.1 U hU hsub hR hRne (fun z _ => hRsq z) z hz
      simpa only [offIndexAbelianRegularSheetPrimitive, F, H, abelianGapNumerator,
        abelianFrequencyNumerator, abelianGapRootMultiplier, div_div] using hd
    · rw [mul_pow,hRsq z]
      exact P.abelianGapRootMultiplier_sq_mul_polynomial m (z,q) ⟨hz.1,hq.1⟩
  · rw [hRbase]
    exact P.physicalDirichletRootCoefficient_preserves_sheet m q hq
  · intro z hz hcut
    have hs : R z^2 = (sourceStandardRoot (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) z)^2 :=
      (hRsq z).trans ((sourceStandardRoot_sq_of_not_mem_segment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) z hcut.2).trans
        (sourceAngularSelectedPolynomial_eq_endpoint_factor (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) z).symm).symm
    have he := P.offIndexAbelianRegularSheetPrimitive_root_ratio n m (fun t => R t.1) (z,q) (hRne z hz) hs
    rw [← P.offIndexAbelianEndpointIntegral_eq_filled_root_product n m hmn q hq.1 z hcut] at he
    exact he

end NLS.KdV.HillProductEquationPatch
