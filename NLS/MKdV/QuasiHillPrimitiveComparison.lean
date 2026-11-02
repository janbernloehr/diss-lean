import NLS.MKdV.QuasiHillSourcePrimitive
import NLS.MKdV.MiuraHillPrimitiveComparison

/-! # The independent Miura sheets agree with NLS on continuous real profiles

This comparison needs no classical derivative of u. In particular it
applies to the physical continuous representative of every real H¹ input.
The independent construction agrees with the shared scalar Hill sheets
whenever u is C¹ and periodic.
-/
noncomputable section
open Set Complex Filter Topology NLS.LinearVolterra NLS.ComplexAnalysis
open NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ContDiff
namespace NLS.MKdV

theorem quasiHill_sheets_eq_NLS (U : Curve ℂ) (hr : ∀ t, (U t).im = 0)
    (z : ℂ) (hzr : 0 < z.re) (hzi : z.im ≠ 0) :
    miuraHillRoot (z^2,U) =
      sourceCanonicalRoot (by simp) (by norm_num) (miuraRealDiagonalSource U hr).val z ∧
    miuraHillPrimitive (z^2,U) = sourceAbelianPrimitive (by simp) (by norm_num)
      (miuraRealDiagonalSource U hr).val (miuraRealDiagonalSource U hr).property z := by
  let D := quasiHillPrimitiveData
  let φ := miuraRealDiagonalSource U hr
  let ψ : ℝ → realTypeSourceSubmodule 2 := fun s => s • φ
  have him : (z^2).im ≠ 0 := by
    simp only [pow_two,mul_im]
    intro h
    apply mul_ne_zero (ne_of_gt hzr) hzi
    nlinarith [h]
  have hslit : z^2 ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inr him)
  have hscaled (s : ℝ) (t : Icc (0 : ℝ) 1) : (((s : ℂ) • U) t).im = 0 := by
    simp only [ContinuousMap.smul_apply,smul_eq_mul,mul_im,ofReal_re,ofReal_im,
      hr t,mul_zero,zero_mul,add_zero]
  have hH (s : ℝ) : (z^2,(s : ℂ) • U) ∈ D.continuationDomain :=
    mem_miuraHillContinuationDomain_of_real _ (hscaled s) z hslit hzi
  have hψ : Continuous ψ := by fun_prop
  have hN (s : ℝ) : z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (ψ s).val :=
    sourceCanonicalRootDomain_of_im_ne_zero _ _ _ (ψ s).property z hzi
  have htrace (s : ℝ) : D.discriminant (z^2,(s : ℂ) • U) =
      canonicalDiscriminant (by simp) (periodOnePotential (ψ s).val) z := by
    change quasiHillDiscriminant ((s : ℂ) • U) (z^2) =
      canonicalDiscriminant (by simp) (periodOnePotential ((s : ℂ) • miuraDiagonalSourceCLM U)) z
    rw [← map_smul,canonicalDiscriminant_miuraDiagonalSource]
  have hcpath : Continuous (fun s : ℝ => (z^2,(s : ℂ) • U)) := by fun_prop
  have hcR : ContinuousOn (fun s : ℝ => D.root (z^2,(s : ℂ) • U)) (Icc 0 1) :=
    D.root_analytic.continuousOn.comp hcpath.continuousOn (fun s _ => hH s)
  obtain ⟨W,_,_,hreal,_,hroot⟩ :=
    exists_global_source_analytic_canonicalRoot (p := 2) (by simp) (by norm_num)
  have hcN : Continuous (fun s => sourceCanonicalRoot (by simp) (by norm_num) (ψ s).val z) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    simpa only [Function.comp_def] using!
      ((hroot (z,(ψ s).val) ⟨hreal (ψ s).property,hN s⟩).continuousAt.comp
        (f := fun r : ℝ => (z,(ψ r).val))
        (continuous_const.prodMk (continuous_subtype_val.comp hψ)).continuousAt)
  have hψ0 : ψ 0 = 0 := zero_smul ℝ φ
  have hR := isPreconnected_Icc.eq_of_sq_eq hcR hcN.continuousOn (by
    intro s _hs
    change D.root (z^2,(s : ℂ) • U)^2 =
      sourceCanonicalRoot (by simp) (by norm_num) (ψ s).val z ^ 2
    rw [D.root_sq _ (hH s),sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four _ _ _ _ (hN s)]
    dsimp only [SourceDiscriminantData.radicand]
    rw [htrace s])
    (fun {s} _ => sourceCanonicalRoot_ne_zero_off_gaps _ _ _ _ (hN s))
    (y := (0 : ℝ)) (by constructor <;> norm_num) (by
      rw [hψ0,ofReal_zero,zero_smul ℂ U,D.root_base]
      change 2*sinh (classicalHillFreePrimitive (z^2)) =
        sourceCanonicalRoot (by simp) (by norm_num) (0 : CoeffPair 2) z
      rw [classicalHillFreePrimitive_sq_of_re_pos z hzr,
        sourceCanonicalRoot_zero_source_eq_free_sine (p := 2) (by simp) (by norm_num) 0,
        neg_mul,sinh_neg,mul_comm I z,sinh_mul_I]
      ring)
  have hcF : ContinuousOn (fun s : ℝ => D.primitive (z^2,(s : ℂ) • U)) (Icc 0 1) :=
    D.primitive_analytic.continuousOn.comp hcpath.continuousOn (fun s _ => hH s)
  have hcA : Continuous (fun s =>
      sourceAbelianPrimitive (by simp) (by norm_num) (ψ s).val (ψ s).property z) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact (continuousAt_sourceAbelianPrimitive_source _ _ (ψ s) z (hN s)).comp hψ.continuousAt
  have hF := continuousLogarithms_eqOn _ _ _ isPreconnected_Icc hcF hcA.continuousOn (by
    intro s hs
    rw [D.exp_primitive _ (hH s),sourceAbelianPrimitive_exp (p := 2)
      (by simp) (by norm_num) (ψ s).val (ψ s).property z
      (sourceCanonicalRootDomain_subset_openGapComplement _ _ _ (hN s))]
    dsimp only [SourceDiscriminantData.multiplier,sourceFloquetMultiplier]
    rw [htrace s]
    exact congrArg (fun r : ℂ =>
      (canonicalDiscriminant (by simp) (periodOnePotential (ψ s).val) z+r)/2) (hR hs))
    0 (by constructor <;> norm_num) (by
      rw [hψ0,ofReal_zero,zero_smul ℂ U,D.primitive_base]
      change classicalHillFreePrimitive (z^2) =
        sourceAbelianPrimitive (by simp) (by norm_num) (0 : CoeffPair 2) (by simp) z
      rw [classicalHillFreePrimitive_sq_of_re_pos z hzr,sourceAbelianPrimitive_zero])
  have ht : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hψ1 : ψ 1 = φ := one_smul ℝ φ
  have hR1 := hR ht
  have hF1 := hF ht
  dsimp only at hR1 hF1
  rw [ofReal_one,one_smul,hψ1] at hR1 hF1
  exact ⟨hR1,hF1⟩

theorem quasiHill_sheets_eq_classicalHill (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u)
    (hr : ∀ x, (u x).im = 0) (hp : Function.Periodic u 1)
    (z : ℂ) (hzr : 0 < z.re) (hzi : z.im ≠ 0) :
    miuraHillRoot (z^2,miuraProfileCurve u hu.continuous) =
      classicalHillContinuedRoot (z^2,miuraHillProfileCurve u hu) ∧
    miuraHillPrimitive (z^2,miuraProfileCurve u hu.continuous) =
      classicalHillContinuedPrimitive (z^2,miuraHillProfileCurve u hu) := by
  have hQ := quasiHill_sheets_eq_NLS (miuraProfileCurve u hu.continuous) (fun t => hr t) z hzr hzi
  have hC := miuraHill_sheets_eq_NLS u hu hr hp z hzr hzi
  exact ⟨hQ.1.trans hC.1.symm,hQ.2.trans hC.2.symm⟩

end NLS.MKdV
