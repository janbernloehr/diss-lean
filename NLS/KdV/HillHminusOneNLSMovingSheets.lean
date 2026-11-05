import NLS.KdV.HillHminusOneReality
import NLS.KdV.ClassicalHillBandNormalization
import NLS.ZakharovShabat.SourceAbelianSourceContinuity
import NLS.ZakharovShabat.SourceCanonicalRootNormalization

/-! # Actual H-minus-one Hill and Dirac sheets along moving-energy paths

The energy may move while the real source path starts at the free point.
The actual trace identity and continuous nonzero roots fix the root sign;
the free value also fixes the additive logarithm period of the primitive.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

theorem hillHminusContinuedRoot_eq_NLS_along_energy_path
    (ψ : ℝ → realTypeSourceSubmodule 2) (hψ : Continuous ψ) (hψ0 : ψ 0 = 0)
    (q : ℝ → PeriodOneHminusOne) (hq : Continuous q) (hq0 : q 0 = 0)
    (hqr : ∀ s ∈ Icc (0 : ℝ) 1, IsRealPeriodOneHminusOne (q s))
    (E : ℝ → ℂ) (hE : Continuous E) (hEi : ∀ s ∈ Icc (0 : ℝ) 1, (E s).im ≠ 0)
    (z : ℂ) (hzr : 0 < z.re) (hzi : z.im ≠ 0) (hE0 : E 0 = z^2)
    (htrace : ∀ s ∈ Icc (0 : ℝ) 1, hillHminusDiscriminant (q s) (E s) =
      canonicalDiscriminant (by simp) (periodOnePotential (ψ s).val) z) :
    EqOn (fun s => hillHminusContinuedRoot (E s,q s))
      (fun s => sourceCanonicalRoot (by simp) (by norm_num) (ψ s).val z) (Icc 0 1) := by
  have hH (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : (E s,q s) ∈ hillHminusContinuationDomain :=
    mem_hillHminusContinuationDomain_of_im_ne_zero (q s) (hqr s hs) (E s) (hEi s hs)
  have hN (s : ℝ) : z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (ψ s).val :=
    sourceCanonicalRootDomain_of_im_ne_zero _ _ _ (ψ s).property z hzi
  have hcH : ContinuousOn (fun s => hillHminusContinuedRoot (E s,q s)) (Icc 0 1) :=
    analyticOnNhd_hillHminusContinuedRoot.continuousOn.comp (hE.prodMk hq).continuousOn hH
  obtain ⟨W,_,_,hreal,_,hroot⟩ := exists_global_source_analytic_canonicalRoot (p := 2) (by simp) (by norm_num)
  have hcN : Continuous (fun s => sourceCanonicalRoot (by simp) (by norm_num) (ψ s).val z) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact ((hroot (z,(ψ s).val) ⟨hreal (ψ s).property,hN s⟩).continuousAt.comp
      (f := fun r : ℝ => (z,(ψ r).val))
      (continuous_const.prodMk (continuous_subtype_val.comp hψ)).continuousAt)
  apply isPreconnected_Icc.eq_of_sq_eq hcH hcN.continuousOn
    (fun s hs => by
      change hillHminusContinuedRoot (E s,q s)^2 = sourceCanonicalRoot (by simp) (by norm_num) (ψ s).val z^2
      rw [hillHminusContinuedRoot_sq _ (hH s hs),
        sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four _ _ _ _ (hN s)]
      dsimp only [hillHminusRadicand]
      rw [htrace s hs])
    (fun {s} _ => sourceCanonicalRoot_ne_zero_off_gaps _ _ _ _ (hN s))
    (y := (0 : ℝ)) (by constructor <;> norm_num)
  rw [hq0,hψ0,hE0]
  have hb := hillHminusSourceFamily.root_base (z^2)
  change hillHminusContinuedRoot (z^2,0) = 2*sinh (classicalHillFreePrimitive (z^2)) at hb
  rw [hb,classicalHillFreePrimitive_sq_of_re_pos z hzr]
  simp only [ZeroMemClass.coe_zero,sourceCanonicalRoot_zero_source_eq_free_sine (p := 2) (by simp) (by norm_num) 0,
    neg_mul,sinh_neg,mul_comm I z,sinh_mul_I]
  ring

theorem hillHminusContinuedPrimitive_eq_NLS_along_energy_path
    (ψ : ℝ → realTypeSourceSubmodule 2) (hψ : Continuous ψ) (hψ0 : ψ 0 = 0)
    (q : ℝ → PeriodOneHminusOne) (hq : Continuous q) (hq0 : q 0 = 0)
    (hqr : ∀ s ∈ Icc (0 : ℝ) 1, IsRealPeriodOneHminusOne (q s))
    (E : ℝ → ℂ) (hE : Continuous E) (hEi : ∀ s ∈ Icc (0 : ℝ) 1, (E s).im ≠ 0)
    (z : ℂ) (hzr : 0 < z.re) (hzi : z.im ≠ 0) (hE0 : E 0 = z^2)
    (htrace : ∀ s ∈ Icc (0 : ℝ) 1, hillHminusDiscriminant (q s) (E s) =
      canonicalDiscriminant (by simp) (periodOnePotential (ψ s).val) z) :
    EqOn (fun s => hillHminusContinuedPrimitive (E s,q s))
      (fun s => sourceAbelianPrimitive (by simp) (by norm_num) (ψ s).val (ψ s).property z) (Icc 0 1) := by
  have hH (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : (E s,q s) ∈ hillHminusContinuationDomain :=
    mem_hillHminusContinuationDomain_of_im_ne_zero (q s) (hqr s hs) (E s) (hEi s hs)
  have hN (s : ℝ) : z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (ψ s).val :=
    sourceCanonicalRootDomain_of_im_ne_zero _ _ _ (ψ s).property z hzi
  have hcH : ContinuousOn (fun s => hillHminusContinuedPrimitive (E s,q s)) (Icc 0 1) :=
    analyticOnNhd_hillHminusContinuedPrimitive.continuousOn.comp (hE.prodMk hq).continuousOn hH
  have hcN : Continuous (fun s => sourceAbelianPrimitive (by simp) (by norm_num) (ψ s).val (ψ s).property z) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact (continuousAt_sourceAbelianPrimitive_source _ _ (ψ s) z (hN s)).comp hψ.continuousAt
  have hroot := hillHminusContinuedRoot_eq_NLS_along_energy_path ψ hψ hψ0 q hq hq0 hqr E hE hEi z hzr hzi hE0 htrace
  apply continuousLogarithms_eqOn _ _ _ isPreconnected_Icc hcH hcN.continuousOn
    (fun s hs => by
      have he : exp (hillHminusContinuedPrimitive (E s,q s)) =
          (hillHminusDiscriminant (q s) (E s)+hillHminusContinuedRoot (E s,q s))/2 :=
        hillHminusSourceFamily.exp_primitive (E s,q s) (hH s hs)
      rw [he,sourceAbelianPrimitive_exp (p := 2) (by simp) (by norm_num) (ψ s).val (ψ s).property z
        (sourceCanonicalRootDomain_subset_openGapComplement _ _ _ (hN s))]
      dsimp only [sourceFloquetMultiplier]
      have hr : hillHminusContinuedRoot (E s,q s) = sourceCanonicalRoot (by simp) (by norm_num) (ψ s).val z := hroot hs
      rw [htrace s hs,hr])
    0 (by constructor <;> norm_num)
  rw [hq0,hψ0,hE0,hillHminusContinuedPrimitive_base]
  simpa only [ZeroMemClass.coe_zero,sourceAbelianPrimitive_zero,classicalHillFreePrimitive] using
    classicalHillFreePrimitive_sq_of_re_pos z hzr

end NLS.KdV
