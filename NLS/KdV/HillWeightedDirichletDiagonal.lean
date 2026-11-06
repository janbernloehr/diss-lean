import NLS.KdV.HillBoundaryDenominator
import NLS.KdV.HillWeightIndependence

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



/-- The individual effective coefficients, not only the determinant, are
independent of the auxiliary Fourier weight. -/
theorem hillEffectiveCoefficients_weight_independent (w : SpectralWeight)
    (q : WeightedCoeff w.toWeight 2) (n : ℕ) (hn : 1 ≤ n) (E : ℂ)
    (hz : E ∈ reducedHillStrip n) (hc : 8*‖q‖ ≤ (n : ℝ))
    (hc1 : 8*‖hillForgetWeight w 2 q‖ ≤ (n : ℝ)) :
    hillDiagonal w q n hn E hz hc =
      hillDiagonal SpectralWeight.one (hillForgetWeight w 2 q) n hn E hz hc1 ∧
    hillUpperCoupling w q n hn E hz hc =
      hillUpperCoupling SpectralWeight.one (hillForgetWeight w 2 q) n hn E hz hc1 ∧
    hillLowerCoupling w q n hn E hz hc =
      hillLowerCoupling SpectralWeight.one (hillForgetWeight w 2 q) n hn E hz hc1 := by
  have he := hillReducedOperator_weight_independent w q n hn E hz hc hc1
  have hp := congrArg (fun T : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) => T (1,0)) he
  have hm := congrArg (fun T : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) => T (0,1)) he
  rw [hillReducedOperator_apply,hillReducedOperator_apply] at hp hm
  simp only [mul_one,mul_zero,sub_zero,zero_sub] at hp hm
  refine ⟨?_,neg_injective (congrArg Prod.fst hm),neg_injective (congrArg Prod.snd hp)⟩
  have hh := congrArg Prod.fst hp
  linear_combination -hh

/-- The actual complex Dirichlet diagonal is controlled by weighted Fourier
coefficients and the true weighted tail error. The common cutoff precedes
the weight quantifier, and no complex interlacing assumption is used. -/
theorem exists_hillDirichlet_weighted_diagonal_bound (B : ℝ) (hB : 0 ≤ B) :
    ∃ N : ℕ, 1 ≤ N ∧ 8*B ≤ (N : ℝ) ∧
      ∀ w : SpectralWeight, ∀ q : WeightedCoeff w.toWeight 2, ‖q‖ ≤ B →
      w.toCoeff q ∈ Coeff.paritySubspace 0 →
      ∀ n : ℕ, N ≤ n → ∀ hn1 : 1 ≤ n, ∀ E : ℂ, ∀ hz : E ∈ reducedHillStrip n,
      hillL2DirichletCharacteristic (w.toCoeff q) E=0 →
      ‖E-(freeHillValue n : ℂ)‖ ≤ 24*(Real.exp (1/2))^2*B →
      ∀ hc : 8*‖q‖ ≤ (n : ℝ),
      w (2*(n : ℤ))*‖E-(freeHillValue n : ℂ)-hillDiagonal w q n hn1 E hz hc‖ ≤
        (2*B+4)*(w (2*(n : ℤ))*‖q.val (2*(n : ℤ))‖+
          w (2*(n : ℤ))*‖q.val (-(2*(n : ℤ)))‖+16*‖q‖^2/(n : ℝ)) := by
  obtain ⟨N,hN,hN8,hcommon⟩ := exists_hillBoundaryScalarDenominator_uniform_lower_bound B hB
  refine ⟨N,hN,hN8,?_⟩
  intro w q hqB hq n hn hn1 E hz hzero hnear hc
  let q1 := hillForgetWeight w 2 q
  have hq1 : ‖q1‖ ≤ B := (norm_hillForgetWeight_le w 2 q).trans hqB
  have hc1 : 8*‖q1‖ ≤ (n : ℝ) := by nlinarith [norm_hillForgetWeight_le w 2 q]
  have hpar : SpectralWeight.one.toCoeff q1 ∈ Coeff.paritySubspace 0 := by
    simpa only [q1,toCoeff_hillForgetWeight] using hq
  have hzero1 : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q1) E=0 := by
    simpa only [q1,toCoeff_hillForgetWeight] using hzero
  obtain ⟨hden,hap,ham,hBp,hBm,ht⟩ := hcommon q1 hq1 n hn hn1 E hz hnear hc1
  let d := E-(freeHillValue n : ℂ)-hillDiagonal SpectralWeight.one q1 n hn1 E hz hc1
  let bp := hillUpperCoupling SpectralWeight.one q1 n hn1 E hz hc1
  let bm := hillLowerCoupling SpectralWeight.one q1 n hn1 E hz hc1
  let ap := 1+(hillBoundaryGreenPotential q1 n hn1 n E hz hc1).val n
  let am := 1+(hillBoundaryGreenPotential q1 n hn1 n E hz hc1).val (-(n : ℤ))
  let Bp := hillReconstructionBoundaryRow SpectralWeight.one n (q1,E) (1,0)
  let Bm := hillReconstructionBoundaryRow SpectralWeight.one n (q1,E) (0,1)
  let t := hillBoundaryGreenTrace q1 n hn1 n E hz hc1
  have hbalance : d*(Bp*ap+Bm*am+t*d)=t*bp*bm-(Bp*bp*am+Bm*bm*ap) :=
    hillDirichlet_boundary_scalar_balance q1 hpar E hzero1 n hn1 hz hc1
  have hbm : ‖bm‖ ≤ 2*B := (hillUnitCorrectedMode_coefficient_le q1 n hn1 E hz hc1 n (-(n : ℤ))).trans
    (mul_le_mul_of_nonneg_left hq1 (by norm_num))
  have hp := weighted_diagonal_le_of_augmented_boundary_balance d bp bm ap am Bp Bm t
    (w (2*(n : ℤ))) (2*B) (w.positive _).le (by positivity) hbalance hden hap ham hBp hBm ht hbm
  obtain ⟨hd,hbp,hbm'⟩ := hillEffectiveCoefficients_weight_independent w q n hn1 E hz hc hc1
  have hupper : w (2*(n : ℤ))*‖bp‖ ≤
      w (2*(n : ℤ))*‖q.val (2*(n : ℤ))‖+8*‖q‖^2/(n : ℝ) := by
    dsimp only [bp]
    rw [← hbp]
    exact hillUpperCoupling_le w q n hn1 E hz hc
  have hlower : w (2*(n : ℤ))*‖bm‖ ≤
      w (2*(n : ℤ))*‖q.val (-(2*(n : ℤ)))‖+8*‖q‖^2/(n : ℝ) := by
    dsimp only [bm]
    rw [← hbm']
    exact hillLowerCoupling_le w q n hn1 E hz hc
  rw [hd]
  change w (2*(n : ℤ))*‖d‖ ≤ _
  calc
    _ ≤ (2*B+4)*(w (2*(n : ℤ))*‖bp‖+w (2*(n : ℤ))*‖bm‖) := hp
    _ ≤ (2*B+4)*((w (2*(n : ℤ))*‖q.val (2*(n : ℤ))‖+8*‖q‖^2/(n : ℝ))+
        (w (2*(n : ℤ))*‖q.val (-(2*(n : ℤ)))‖+8*‖q‖^2/(n : ℝ))) :=
      mul_le_mul_of_nonneg_left (add_le_add hupper hlower) (by positivity)
    _ = _ := by ring

end NLS.KdV
