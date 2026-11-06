import NLS.KdV.HillIsospectralAbelianPeriods
import NLS.KdV.HillMixedSupportedPeriodMap

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.LinearVolterra NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



private theorem coefficient_fderiv (F : Coeff 2 → Coeff 2) (p h : Coeff 2)
    (hF : DifferentiableAt ℂ F p) (k : ℤ) :
    ((fderiv ℂ F p) h) k=(fderiv ℂ (fun b : Coeff 2 => F b k) p) h := by
  let ev : Coeff 2 →L[ℂ] ℂ := lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k
  have hd := ev.hasFDerivAt.comp p hF.hasFDerivAt
  exact (congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L h) hd.fderiv).symm

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The whole genuine mixed Hilbert period sequence has zero source
variation in an isospectral direction, not only its individual finite head. -/
theorem hillMixedComplexPeriodSequence_isospectral_potential_fderiv
    (N n : ℕ) (hn : 1≤n) (B D : ℝ)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖≤B)
    (a h : Coeff 2)
    (hiso : ∀ E : ℂ, (fderiv ℂ (fun b : Coeff 2 => hillL2Discriminant b E) (SpectralWeight.one.toCoeff q)) h=0)
    (hF : DifferentiableAt ℂ (fun b : Coeff 2 =>
      hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a,b)) (SpectralWeight.one.toCoeff q)) :
    (fderiv ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a,b))
      (SpectralWeight.one.toCoeff q)) h=0 := by
  let p := SpectralWeight.one.toCoeff q
  have hlow (k : ℕ) (hk : 1≤k) :=
    hillAbelianComplexPeriod_isospectral_potential_fderiv q hq hr n k hk a p h hiso
      (fun E hE => mem_hillAbelianComplexRootDomain_base q hq hr E (hillRealGapContour_sphere_subset q hq hr k hk hE))
  have hhigh (k : ℕ) (hk : 1≤k) (hkN : N≤k) :=
    hillAbelianComplexPeriod_isospectral_potential_fderiv 0 h0q h0r n k hk a p h hiso
      ((hc p hp).1 k hkN)
  apply lp.ext
  funext k
  change ((fderiv ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a,b)) p) h) k=0
  rw [coefficient_fderiv _ p h hF k]
  by_cases hbad : k≤0 ∨ k=(n : ℤ)
  · have he : (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a,b) k)=
        (fun _ : Coeff 2 => (0 : ℂ)) :=
      funext (fun b => hillMixedComplexPeriodSequence_apply_unsupported q hq hr h0q h0r N n hn (a,b) k hbad)
    rw [he,fderiv_const_apply,zero_apply]
  · have hk : 1≤k.toNat := by omega
    have hkn : k.toNat≠n := by omega
    have hcast : (k.toNat : ℤ)=k := by omega
    rw [← hcast]
    have he : (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a,b) (k.toNat : ℤ))=
        (fun b : Coeff 2 => (((freeHillValue k.toNat : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
          (if k.toNat<N then hillAbelianComplexPeriod q hq hr n k.toNat (a,b)
            else hillAbelianComplexPeriod 0 h0q h0r n k.toNat (a,b))) := by
      funext b
      rw [hillMixedComplexPeriodSequence_apply_nat q hq hr h0q h0r N n k.toNat hn hk,if_pos hkn]
    rw [he]
    by_cases hkN : k.toNat<N
    · simp only [if_pos hkN]
      rw [fderiv_const_mul (hlow k.toNat hk).1]
      simp only [smul_apply,smul_eq_mul,(hlow k.toNat hk).2,mul_zero]
    · simp only [if_neg hkN]
      rw [fderiv_const_mul (hhigh k.toNat hk (by omega)).1]
      simp only [smul_apply,smul_eq_mul,(hhigh k.toNat hk (by omega)).2,mul_zero]

theorem hillMixedSupportedPeriodMap_isospectral_parameter_kernel
    (N n : ℕ) (hn : 1≤n) (B D : ℝ)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖≤B)
    (a h : Coeff 2)
    (hiso : ∀ E : ℂ, (fderiv ℂ (fun b : Coeff 2 => hillL2Discriminant b E) (SpectralWeight.one.toCoeff q)) h=0)
    (hF : AnalyticAt ℂ (hillMixedComplexPeriodSequence q hq hr h0q h0r N n) (a,SpectralWeight.one.toCoeff q))
    (hG : AnalyticAt ℂ (hillMixedSupportedPeriodMap q hq hr h0q h0r N n a) (0,SpectralWeight.one.toCoeff q)) :
    (fderiv ℂ (hillMixedSupportedPeriodMap q hq hr h0q h0r N n a) (0,SpectralWeight.one.toCoeff q)) (0,h)=0 := by
  let p := SpectralWeight.one.toCoeff q
  let F := fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a,b)
  let G := hillMixedSupportedPeriodMap q hq hr h0q h0r N n a
  let pr := Coeff.positiveDeletedProjectionTo 2 (n : ℤ)
  have hFa : AnalyticAt ℂ F p := hF.comp (f := fun b : Coeff 2 => (a,b)) (analyticAt_const.prod analyticAt_id)
  have hz := hillMixedComplexPeriodSequence_isospectral_potential_fderiv q hq hr h0q h0r N n hn B D hc hp a h hiso hFa.differentiableAt
  change (fderiv ℂ F p) h=0 at hz
  have hp1 := pr.hasFDerivAt.comp p hFa.differentiableAt.hasFDerivAt
  have hp2 := hG.differentiableAt.hasFDerivAt.comp (f := fun b : Coeff 2 => ((0 : PositiveDeletedCoeff 2 (n : ℤ)),b)) p
    (hasFDerivAt_prodMk_right (0 : PositiveDeletedCoeff 2 (n : ℤ)) p)
  have he : (fun b : Coeff 2 => G (0,b))=fun b => pr (F b) := by
    funext b
    simp only [G,hillMixedSupportedPeriodMap,ZeroMemClass.coe_zero,add_zero,F,pr]
  change HasFDerivAt (fun b : Coeff 2 => G (0,b))
    ((fderiv ℂ G (0,p)).comp (ContinuousLinearMap.inr ℂ (PositiveDeletedCoeff 2 (n : ℤ)) (Coeff 2))) p at hp2
  rw [he] at hp2
  have hv := congrArg (fun L : Coeff 2 →L[ℂ] PositiveDeletedCoeff 2 (n : ℤ) => L h) (hp2.unique hp1)
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,hz,map_zero] using hv

end NLS.KdV
