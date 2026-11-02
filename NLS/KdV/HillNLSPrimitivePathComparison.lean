import NLS.KdV.ClassicalHillBandNormalization
import NLS.ZakharovShabat.SourceAbelianSourceContinuity
import NLS.ZakharovShabat.SourceCanonicalRootNormalization

/-! # Comparing the actual Hill and NLS sheets along real source paths

Equality of actual traces fixes the root sign and the logarithm period by
continuity from the free potential. The Hill path need not be straight;
in particular the quadratic Miura image of a straight mKdV path is allowed.
-/
noncomputable section
open Set Complex Filter Topology NLS.LinearVolterra NLS.ComplexAnalysis
open NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem classicalHillContinuedRoot_eq_NLS_along_path
    (ψ : ℝ → realTypeSourceSubmodule 2) (hψ : Continuous ψ) (hψ0 : ψ 0 = 0)
    (q : ℝ → Curve ℂ) (hq : Continuous q) (hq0 : q 0 = 0)
    (hqr : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t, (q s t).im = 0)
    (z : ℂ) (hzr : 0 < z.re) (hzi : z.im ≠ 0)
    (htrace : ∀ s ∈ Icc (0 : ℝ) 1,
      classicalHillDiscriminant (q s) (z^2) =
        canonicalDiscriminant (by simp) (periodOnePotential (ψ s).val) z) :
    EqOn (fun s => classicalHillContinuedRoot (z^2,q s))
      (fun s => sourceCanonicalRoot (by simp) (by norm_num) (ψ s).val z) (Icc 0 1) := by
  have him : (z^2).im ≠ 0 := by
    simp only [pow_two,mul_im]
    intro h
    apply mul_ne_zero (ne_of_gt hzr) hzi
    nlinarith [h]
  have hH (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      (z^2,q s) ∈ classicalHillContinuationDomain :=
    mem_classicalHillContinuationDomain_of_im_ne_zero _ (hqr s hs) _ him
  have hN (s : ℝ) : z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (ψ s).val :=
    sourceCanonicalRootDomain_of_im_ne_zero _ _ _ (ψ s).property z hzi
  have hcH : ContinuousOn (fun s => classicalHillContinuedRoot (z^2,q s)) (Icc 0 1) :=
    analyticOnNhd_classicalHillContinuedRoot.continuousOn.comp
      (continuous_const.prodMk hq).continuousOn hH
  obtain ⟨W,_,_,hreal,_,hroot⟩ :=
    exists_global_source_analytic_canonicalRoot (p := 2) (by simp) (by norm_num)
  have hcN : Continuous (fun s => sourceCanonicalRoot (by simp) (by norm_num) (ψ s).val z) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    simpa only [Function.comp_def] using!
      ((hroot (z,(ψ s).val) ⟨hreal (ψ s).property,hN s⟩).continuousAt.comp
        (f := fun r : ℝ => (z,(ψ r).val))
        (continuous_const.prodMk (continuous_subtype_val.comp hψ)).continuousAt)
  apply isPreconnected_Icc.eq_of_sq_eq hcH hcN.continuousOn
    (fun s hs => by
      change classicalHillContinuedRoot (z^2,q s)^2 =
        sourceCanonicalRoot (by simp) (by norm_num) (ψ s).val z ^ 2
      rw [classicalHillContinuedRoot_sq _ (hH s hs),
        sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four _ _ _ _ (hN s)]
      change classicalHillDiscriminant (q s) (z^2)^2-4 = _
      rw [htrace s hs])
    (fun {s} _ => sourceCanonicalRoot_ne_zero_off_gaps _ _ _ _ (hN s))
    (y := (0 : ℝ)) (by constructor <;> norm_num)
  rw [hq0,hψ0]
  simp only [ZeroMemClass.coe_zero,classicalHillContinuedRoot_base,
    sourceCanonicalRoot_zero_source_eq_free_sine (p := 2) (by simp) (by norm_num) 0,
    classicalHillFreeRoot,classicalHillFreePrimitive_sq_of_re_pos z hzr]
  rw [neg_mul,sinh_neg,mul_comm I z,sinh_mul_I]
  ring

theorem classicalHillContinuedPrimitive_eq_NLS_along_path
    (ψ : ℝ → realTypeSourceSubmodule 2) (hψ : Continuous ψ) (hψ0 : ψ 0 = 0)
    (q : ℝ → Curve ℂ) (hq : Continuous q) (hq0 : q 0 = 0)
    (hqr : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t, (q s t).im = 0)
    (z : ℂ) (hzr : 0 < z.re) (hzi : z.im ≠ 0)
    (htrace : ∀ s ∈ Icc (0 : ℝ) 1,
      classicalHillDiscriminant (q s) (z^2) =
        canonicalDiscriminant (by simp) (periodOnePotential (ψ s).val) z) :
    EqOn (fun s => classicalHillContinuedPrimitive (z^2,q s))
      (fun s => sourceAbelianPrimitive (by simp) (by norm_num) (ψ s).val (ψ s).property z)
      (Icc 0 1) := by
  have him : (z^2).im ≠ 0 := by
    simp only [pow_two,mul_im]
    intro h
    apply mul_ne_zero (ne_of_gt hzr) hzi
    nlinarith [h]
  have hH (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      (z^2,q s) ∈ classicalHillContinuationDomain :=
    mem_classicalHillContinuationDomain_of_im_ne_zero _ (hqr s hs) _ him
  have hN (s : ℝ) : z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (ψ s).val :=
    sourceCanonicalRootDomain_of_im_ne_zero _ _ _ (ψ s).property z hzi
  have hcH : ContinuousOn (fun s => classicalHillContinuedPrimitive (z^2,q s)) (Icc 0 1) :=
    analyticOnNhd_classicalHillContinuedPrimitive.continuousOn.comp
      (continuous_const.prodMk hq).continuousOn hH
  have hcN : Continuous (fun s =>
      sourceAbelianPrimitive (by simp) (by norm_num) (ψ s).val (ψ s).property z) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact (continuousAt_sourceAbelianPrimitive_source _ _ (ψ s) z (hN s)).comp hψ.continuousAt
  have hroot := classicalHillContinuedRoot_eq_NLS_along_path ψ hψ hψ0 q hq hq0 hqr z hzr hzi htrace
  apply continuousLogarithms_eqOn _ _ _ isPreconnected_Icc hcH hcN.continuousOn
    (fun s hs => by
      rw [exp_classicalHillContinuedPrimitive _ (hH s hs),sourceAbelianPrimitive_exp (p := 2) (by simp) (by norm_num) (ψ s).val (ψ s).property z
        (sourceCanonicalRootDomain_subset_openGapComplement _ _ _ (hN s))]
      dsimp only [classicalHillContinuedMultiplier,sourceFloquetMultiplier]
      rw [htrace s hs]
      exact congrArg (fun r : ℂ =>
        (canonicalDiscriminant (by simp) (periodOnePotential (ψ s).val) z+r)/2) (hroot hs))
    0 (by constructor <;> norm_num)
  simp only [hq0,hψ0,ZeroMemClass.coe_zero,classicalHillContinuedPrimitive_base,
    sourceAbelianPrimitive_zero,classicalHillFreePrimitive_sq_of_re_pos z hzr]

end NLS.KdV
