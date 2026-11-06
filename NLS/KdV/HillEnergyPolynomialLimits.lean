import NLS.KdV.HillEnergyRadicandProduct
import Mathlib.Analysis.Analytic.Polynomial
import NLS.ComplexAnalysis.RealRootedDerivatives
import NLS.ComplexAnalysis.NonvanishingLocallyUniformLimit
import NLS.ComplexAnalysis.AnalyticZeroCount

/-! # Locally uniform energy products, real-rooted polynomial approximants and nonreal nonvanishing of the radicand derivative. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
open NLS.ZakharovShabat NLS.ComplexAnalysis
open Polynomial
namespace NLS.KdV

theorem tendstoLocallyUniformlyOn_hillEnergyPeriodicPartialProduct
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    TendstoLocallyUniformlyOn (fun N z => hillEnergyPeriodicPartialProduct q hq hr z N)
      (hillL2Radicand (SpectralWeight.one.toCoeff q)) atTop univ := by
  have hs (z : ℂ) : (Complex.sqrt z)^2 = z := by
    have h := Complex.cpow_nat_inv_pow z (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  have hf := tendstoLocallyUniformlyOn_entireSpectralPairProduct
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) _ _
    (memℓp_hillSignedEnergyRoot_displacement q hq hr false)
    (memℓp_hillSignedEnergyRoot_displacement q hq hr true)
  intro u hu z _
  let R := ‖z‖+2
  have hmap : MapsTo Complex.sqrt (ball z 1) (closedBall 0 R) := by
    intro w hw
    rw [mem_closedBall,dist_zero_right]
    have hw' : ‖w‖ < ‖z‖+1 := by
      have h : ‖w‖ ≤ ‖w-z‖+‖z‖ := by simpa only [sub_add_cancel] using norm_add_le (w-z) z
      have hdist : ‖w-z‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hw
      linarith
    have hsq := congrArg norm (hs w)
    rw [norm_pow] at hsq
    have hn := norm_nonneg (Complex.sqrt w)
    dsimp only [R]
    nlinarith [norm_nonneg z]
  have hc := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_closedBall (0 : ℂ) R)).mp
    (hf.mono (subset_univ _))
  have hp := (hc.comp Complex.sqrt).mono hmap
  have he := hp u hu
  refine ⟨ball z 1,nhdsWithin_le_nhds (ball_mem_nhds z (by norm_num)),?_⟩
  filter_upwards [he] with N hN w hw
  have h := hN w hw
  dsimp only [Function.comp_apply] at h
  simp only [spectralPairPartialProduct_hillSignedEnergyRoot,hs] at h
  rw [entireSpectralPairProduct_hillSignedEnergyRoot q hq hr,
    canonicalPeriodic_eq_discriminant_sq_sub_four _ (hillL2CoefficientPotential_even _),
    canonicalDiscriminant_hillL2CoefficientPotential,hs] at h
  exact h

def hillEnergyPeriodicPolynomial
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (N : ℕ) : Polynomial ℂ :=
  C (-4) * (X-C (hillRealLabels q hq hr 0 : ℂ)) * ∏ k ∈ Finset.range N,
    (C (hillRealLabels q hq hr (2*(k+1)-1) : ℂ)-X)*
    (C (hillRealLabels q hq hr (2*(k+1)) : ℂ)-X)*C ((freeHillValue (k+1) : ℂ)^2)⁻¹

theorem hillEnergyPeriodicPolynomial_eval
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (N : ℕ) (z : ℂ) :
    (hillEnergyPeriodicPolynomial q hq hr N).eval z = hillEnergyPeriodicPartialProduct q hq hr z N := by
  simp only [hillEnergyPeriodicPolynomial,eval_mul,eval_C,eval_sub,eval_X,eval_prod,
    hillEnergyPeriodicPartialProduct,div_eq_mul_inv]

theorem hillEnergyPeriodicPartialProduct_ne_zero_of_im_ne_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (N : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    hillEnergyPeriodicPartialProduct q hq hr z N ≠ 0 := by
  have hleft (x : ℝ) : (x : ℂ)-z ≠ 0 := by
    intro he
    have hi := congrArg Complex.im (sub_eq_zero.mp he)
    simpa only [ofReal_im] using hz hi.symm
  have hright (x : ℝ) : z-(x : ℂ) ≠ 0 := by
    intro he
    exact hleft x (sub_eq_zero.mpr (sub_eq_zero.mp he).symm)
  unfold hillEnergyPeriodicPartialProduct
  apply mul_ne_zero (mul_ne_zero (by norm_num) (hright _))
  apply Finset.prod_ne_zero_iff.mpr
  intro k _
  apply div_ne_zero (mul_ne_zero (hleft _) (hleft _))
  apply pow_ne_zero
  apply ofReal_ne_zero.mpr
  unfold freeHillValue
  apply mul_ne_zero (pow_ne_zero _ Real.pi_ne_zero) (pow_ne_zero _ _)
  exact_mod_cast (show (k+1 : ℤ) ≠ 0 by omega)

theorem deriv_hillEnergyPeriodicPartialProduct_ne_zero_of_im_ne_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (N : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    deriv (fun w => hillEnergyPeriodicPartialProduct q hq hr w N) z ≠ 0 := by
  let P := hillEnergyPeriodicPolynomial q hq hr N
  have he (w : ℂ) : P.eval w = hillEnergyPeriodicPartialProduct q hq hr w N :=
    hillEnergyPeriodicPolynomial_eval q hq hr N w
  have hP : P ≠ 0 := by
    intro hP
    have hi := he I
    rw [hP,eval_zero] at hi
    exact hillEnergyPeriodicPartialProduct_ne_zero_of_im_ne_zero q hq hr N I (by simp) hi.symm
  have hroot : P.eval (hillRealLabels q hq hr 0 : ℂ) = 0 := by
    rw [he]
    simp only [hillEnergyPeriodicPartialProduct,sub_self,mul_zero,zero_mul]
  have hdeg : 0 < P.degree := degree_pos_of_root hP hroot
  have hreal (w : ℂ) (hw : P.eval w = 0) : w.im = 0 := by
    by_contra hi
    exact hillEnergyPeriodicPartialProduct_ne_zero_of_im_ne_zero q hq hr N w hi ((he w).symm.trans hw)
  rw [show (fun w => hillEnergyPeriodicPartialProduct q hq hr w N) = P.eval by exact (funext he).symm,P.deriv]
  exact fun hzero => hz (polynomial_derivative_im_eq_zero hdeg hreal hzero)


theorem analyticOnNhd_hillEnergyPeriodicPartialProduct
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (N : ℕ) :
    AnalyticOnNhd ℂ (fun z => hillEnergyPeriodicPartialProduct q hq hr z N) univ := by
  rw [show (fun z => hillEnergyPeriodicPartialProduct q hq hr z N) =
    (hillEnergyPeriodicPolynomial q hq hr N).eval by exact (funext (hillEnergyPeriodicPolynomial_eval q hq hr N)).symm]
  exact AnalyticOnNhd.eval_polynomial _

theorem exists_deriv_hillL2Radicand_ne_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    ∃ z : ℂ, deriv (hillL2Radicand (SpectralWeight.one.toCoeff q)) z ≠ 0 := by
  have ha := (hillRealLabels_spec q hq hr).root 0
  have hi : hillL2Radicand (SpectralWeight.one.toCoeff q) I ≠ 0 := by
    intro he
    obtain ⟨j,hj⟩ := (hillRealLabels_root_iff q hq hr I).mp he
    have h := congrArg Complex.im hj
    norm_num at h
  by_contra! h
  have he := is_const_of_deriv_eq_zero
    (fun z => (analyticOnNhd_hillL2Radicand (SpectralWeight.one.toCoeff q) z (mem_univ z)).differentiableAt)
    h (hillRealLabels q hq hr 0 : ℂ) I
  exact hi (he.symm.trans ha)

theorem deriv_hillL2Radicand_ne_zero_of_im_ne_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) (hz : z.im ≠ 0) :
    deriv (hillL2Radicand (SpectralWeight.one.toCoeff q)) z ≠ 0 := by
  let F (N : ℕ) := deriv (fun w => hillEnergyPeriodicPartialProduct q hq hr w N)
  have han := (analyticOnNhd_hillL2Radicand (SpectralWeight.one.toCoeff q)).deriv
  obtain ⟨a,ha⟩ := exists_deriv_hillL2Radicand_ne_zero q hq hr
  apply limit_ne_zero_on_open_of_finite_order F _
    (U := {w : ℂ | w.im ≠ 0}) (isOpen_ne.preimage continuous_im) hz
  · intro N w
    exact ((analyticOnNhd_hillEnergyPeriodicPartialProduct q hq hr N).deriv w (mem_univ w)).differentiableAt
  · intro N w hw
    exact deriv_hillEnergyPeriodicPartialProduct_ne_zero_of_im_ne_zero q hq hr N w hw
  · exact han.mono (subset_univ _)
  · exact analyticOrderAt_ne_top_on_connected isPreconnected_univ han (mem_univ a) ha (mem_univ z)
  · exact ((tendstoLocallyUniformlyOn_hillEnergyPeriodicPartialProduct q hq hr).deriv
      (Eventually.of_forall (fun N => (analyticOnNhd_hillEnergyPeriodicPartialProduct q hq hr N).differentiableOn))
      isOpen_univ).mono (subset_univ _)


end NLS.KdV
