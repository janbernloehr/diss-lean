import NLS.KdV.HillIsospectralGapInvariants
import NLS.KdV.HillLocalDeflatedComplexRoot
import NLS.ComplexAnalysis.CauchyTransformSourceStationarity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.LinearVolterra NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem analyticAt_hillLocalGapPolynomial_joint_base (k : ℕ) (hk : 1≤k) (E : ℂ) :
    AnalyticAt ℂ (fun t : ℂ × Coeff 2 => hillLocalGapPolynomial q hq hr k t.2 t.1)
      (E,SpectralWeight.one.toCoeff q) := by
  obtain ⟨U,_,hpU,hM,hS,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood q hq hr k hk
  have hMj : AnalyticAt ℂ (fun t : ℂ × Coeff 2 => hillLocalGapMidpoint q hq hr k t.2)
      (E,SpectralWeight.one.toCoeff q) :=
    (hM _ hpU).comp (x := (E,SpectralWeight.one.toCoeff q)) (f := fun t : ℂ × Coeff 2 => t.2) analyticAt_snd
  have hSj : AnalyticAt ℂ (fun t : ℂ × Coeff 2 => hillLocalGapSquare q hq hr k t.2)
      (E,SpectralWeight.one.toCoeff q) :=
    (hS _ hpU).comp (x := (E,SpectralWeight.one.toCoeff q)) (f := fun t : ℂ × Coeff 2 => t.2) analyticAt_snd
  exact ((analyticAt_fst.sub hMj).pow 2).sub hSj.div_const

theorem hillLocalGapPolynomial_isospectral_fderiv (k : ℕ) (hk : 1≤k) (h : Coeff 2)
    (hiso : ∀ E : ℂ, (fderiv ℂ (fun b : Coeff 2 => hillL2Discriminant b E) (SpectralWeight.one.toCoeff q)) h=0)
    (E : ℂ) :
    (fderiv ℂ (fun b : Coeff 2 => hillLocalGapPolynomial q hq hr k b E) (SpectralWeight.one.toCoeff q)) h=0 := by
  obtain ⟨U,_,hpU,hM,hS,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood q hq hr k hk
  have hz := hillLocalGapSymmetricData_isospectral_fderiv q hq hr k hk h hiso
  have hd := (((hasFDerivAt_const E (SpectralWeight.one.toCoeff q)).fun_sub
    (hM _ hpU).differentiableAt.hasFDerivAt).pow 2).fun_sub
      ((hS _ hpU).differentiableAt.hasFDerivAt.mul_const (4 : ℂ)⁻¹)
  change HasFDerivAt (𝕜 := ℂ) (fun b : Coeff 2 => hillLocalGapPolynomial q hq hr k b E) _
    (SpectralWeight.one.toCoeff q) at hd
  rw [hd.fderiv]
  simp only [sub_apply,smul_apply,smul_eq_mul,zero_apply,hz.1,hz.2,sub_self,mul_zero]

private theorem polynomial_boundary_ne_zero (k : ℕ) (hk : 1≤k) (E : ℂ)
    (hE : E∈sphere (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)) :
    hillLocalGapPolynomial q hq hr k (SpectralWeight.one.toCoeff q) E≠0 := by
  obtain ⟨U,_,hpU,hpair⟩ := exists_hillComplexGapPair_neighborhood q hq hr k hk
  obtain ⟨hb,a,ha,b,hb',_,_,hm⟩ := hpair _ hpU
  rw [hillLocalGapPolynomial_eq_of_pair q hq hr k hk _ hb ha hb' hm]
  exact mul_ne_zero (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hE ha))
    (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hE hb'))

/-- The actual Cauchy-deflated unit is stationary throughout its
original gap disc, including both periodic endpoints and collapsed gaps. -/
theorem hillLocalGapUnit_isospectral_fderiv (k : ℕ) (hk : 1≤k) (h : Coeff 2)
    (hiso : ∀ E : ℂ, (fderiv ℂ (fun b : Coeff 2 => hillL2Discriminant b E) (SpectralWeight.one.toCoeff q)) h=0)
    (z : ℂ) (hz : z∈ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)) :
    (fderiv ℂ (fun b : Coeff 2 => hillLocalGapUnit q hq hr k (z,b)) (SpectralWeight.one.toCoeff q)) h=0 := by
  let F : ℂ × Coeff 2 → ℂ := fun t => hillL2Radicand t.2 t.1/hillLocalGapPolynomial q hq hr k t.2 t.1
  let c : ℂ := hillRealGapCenter q hq hr k
  let r := hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k
  have hF (w : ℂ) (hw : w∈sphere c r) : AnalyticAt ℂ F (w,SpectralWeight.one.toCoeff q) :=
    (analyticOnNhd_hillL2Radicand_joint _ (mem_univ _)).div
      (analyticAt_hillLocalGapPolynomial_joint_base q hq hr k hk w) (polynomial_boundary_ne_zero q hq hr k hk w hw)
  have hker (w : ℂ) (hw : w∈sphere c r) :
      (fderiv ℂ (fun b : Coeff 2 => F (w,b)) (SpectralWeight.one.toCoeff q)) h=0 := by
    have hRad : AnalyticAt ℂ (fun b : Coeff 2 => hillL2Radicand b w) (SpectralWeight.one.toCoeff q) :=
      (analyticOnNhd_hillL2Radicand_joint _ (mem_univ _)).comp
        (f := fun b : Coeff 2 => (w,b)) (analyticAt_const.prod analyticAt_id)
    have hPol : AnalyticAt ℂ (fun b : Coeff 2 => hillLocalGapPolynomial q hq hr k b w) (SpectralWeight.one.toCoeff q) :=
      (analyticAt_hillLocalGapPolynomial_joint_base q hq hr k hk w).comp
        (f := fun b : Coeff 2 => (w,b)) (analyticAt_const.prod analyticAt_id)
    change (fderiv ℂ (fun b : Coeff 2 => hillL2Radicand b w/hillLocalGapPolynomial q hq hr k b w)
      (SpectralWeight.one.toCoeff q)) h=0
    rw [fderiv_div_apply _ _ _ hRad.differentiableAt hPol.differentiableAt
      (polynomial_boundary_ne_zero q hq hr k hk w hw) h,
      hillL2Radicand_isospectral_fderiv _ h hiso w,hillLocalGapPolynomial_isospectral_fderiv q hq hr k hk h hiso w]
    simp only [zero_mul,mul_zero,sub_zero,zero_div]
  exact (parametricCircleCauchyTransform_source_fderiv_eq_zero F c r
    (add_nonneg (hillRealGapContour_geometry q hq hr k hk).1 (hillRealGapContour_geometry q hq hr k hk).2.1.le)
    _ h hF hker z (fun hs => sphere_disjoint_ball.le_bot ⟨hs,hz⟩)).2

/-- The continued deflated square root has zero actual source variation
at every energy in the original gap disc, without excluding endpoints. -/
theorem hillLocalDeflatedComplexRoot_isospectral_fderiv (k : ℕ) (hk : 1≤k) (h : Coeff 2)
    (hiso : ∀ E : ℂ, (fderiv ℂ (fun b : Coeff 2 => hillL2Discriminant b E) (SpectralWeight.one.toCoeff q)) h=0)
    (z : ℂ) (hz : z∈ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)) :
    (fderiv ℂ (fun b : Coeff 2 => hillLocalDeflatedComplexRoot q hq hr k (z,b))
      (SpectralWeight.one.toCoeff q)) h=0 := by
  have ht := mem_hillLocalDeflatedRootDomain_base q hq hr k hk z hz
  have hR : AnalyticAt ℂ (fun b : Coeff 2 => hillLocalDeflatedComplexRoot q hq hr k (z,b)) (SpectralWeight.one.toCoeff q) :=
    (analyticOnNhd_hillLocalDeflatedComplexRoot q hq hr k hk _ ht).comp
      (f := fun b : Coeff 2 => (z,b)) (analyticAt_const.prod analyticAt_id)
  have hF : AnalyticAt ℂ (fun b : Coeff 2 => hillLocalGapUnit q hq hr k (z,b)) (SpectralWeight.one.toCoeff q) :=
    ht.1.1.comp (f := fun b : Coeff 2 => (z,b)) (analyticAt_const.prod analyticAt_id)
  apply squareRoot_source_fderiv_eq_zero _ _ _ h hR hF ?_
    (hillLocalDeflatedComplexRoot_ne_zero q hq hr k hk _ ht)
    (hillLocalGapUnit_isospectral_fderiv q hq hr k hk h hiso z hz)
  have hdom : ∀ᶠ b in 𝓝 (SpectralWeight.one.toCoeff q), (z,b)∈hillLocalDeflatedRootDomain q hq hr k :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      ((isOpen_hillLocalDeflatedRootDomain q hq hr k hk).mem_nhds ht)
  filter_upwards [hdom] with b hb
  exact hillLocalDeflatedComplexRoot_sq q hq hr k hk (z,b) hb

end NLS.KdV
