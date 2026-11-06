import NLS.KdV.HillDirichletCoefficientBounds
import NLS.KdV.HillWeightedDirichletDiagonal

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



private theorem weighted_source_le_of_resonant_row (d bp u v J ap : ℂ)
    (n W C : ℝ) (hn : 0 ≤ n) (hW : 0 ≤ W)
    (hrow : d*u-bp*v = -J*ap) (hap : 1/2 ≤ ‖ap‖)
    (hu : n*‖u‖ ≤ C) (hv : n*‖v‖ ≤ C) :
    n*W*‖J‖ ≤ 2*C*(W*‖d‖+W*‖bp‖) := by
  have hnorm : ‖J‖*‖ap‖ ≤ ‖d‖*‖u‖+‖bp‖*‖v‖ := by
    have hh := norm_sub_le (d*u) (bp*v)
    rw [hrow,norm_mul,norm_neg,norm_mul,norm_mul] at hh
    exact hh
  calc
    _ ≤ 2*(n*W*(‖J‖*‖ap‖)) := by
      nlinarith [mul_le_mul_of_nonneg_left hap (by positivity : 0 ≤ n*W*‖J‖)]
    _ ≤ 2*(n*W*(‖d‖*‖u‖+‖bp‖*‖v‖)) := by gcongr
    _ = 2*((W*‖d‖)*(n*‖u‖)+(W*‖bp‖)*(n*‖v‖)) := by ring
    _ ≤ 2*((W*‖d‖)*C+(W*‖bp‖)*C) := by gcongr
    _ = _ := by ring

/-- The original normalized Dirichlet derivative jump satisfies a genuine
weighted Fourier bound after scaling by the coordinate index. -/
theorem exists_hillDirichlet_boundary_jump_weighted_bound (B : ℝ) (hB : 0 ≤ B) :
    ∃ N : ℕ, 1 ≤ N ∧ 8*B ≤ (N : ℝ) ∧
      ∀ w : SpectralWeight, ∀ q : WeightedCoeff w.toWeight 2, ‖q‖ ≤ B →
      w.toCoeff q ∈ Coeff.paritySubspace 0 →
      ∀ n : ℕ, N ≤ n → ∀ E : ℂ, E ∈ reducedHillStrip n →
      hillL2DirichletCharacteristic (w.toCoeff q) E=0 →
      ‖E-(freeHillValue n : ℂ)‖ ≤ 24*(Real.exp (1/2))^2*B →
      (n : ℝ)*w (2*(n : ℤ))*‖hillL2DirichletBoundaryJump (w.toCoeff q) E n‖ ≤
        (8*Real.exp (1/2)*(2*B+5))*(w (2*(n : ℤ))*‖q.val (2*(n : ℤ))‖+
          w (2*(n : ℤ))*‖q.val (-(2*(n : ℤ)))‖+16*‖q‖^2/(n : ℝ)) := by
  obtain ⟨Nd,hNd,hNd8,hdef⟩ := exists_hillDirichlet_weighted_diagonal_bound B hB
  obtain ⟨Ng,hNg,hNg8,hgreen⟩ := exists_hillBoundaryGreen_uniform_small B (1/2) (by norm_num)
  let C : ℝ := 24*(Real.exp (1/2))^2
  obtain ⟨M,hM⟩ := exists_nat_gt (max (8*Real.exp (1/2)*B) (2*C*B))
  refine ⟨max Nd (max Ng M),hNd.trans (le_max_left _ _),
    hNd8.trans (by exact_mod_cast le_max_left Nd (max Ng M)),?_⟩
  intro w q hq hpar n hn E hz hzero hnear
  have hnD : Nd ≤ n := (le_max_left _ _).trans hn
  have hnG : Ng ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnM : M ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hn1 : 1 ≤ n := hNd.trans hnD
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hlarge : max (8*Real.exp (1/2)*B) (2*C*B) ≤ (n : ℝ) :=
    hM.le.trans (by exact_mod_cast hnM)
  let q1 := hillForgetWeight w 2 q
  let p := SpectralWeight.one.toCoeff q1
  have hq1 : ‖q1‖ ≤ B := (norm_hillForgetWeight_le w 2 q).trans hq
  have hpB : ‖p‖ ≤ B := (SpectralWeight.one.norm_toCoeff_le q1).trans hq1
  have hp : p=w.toCoeff q := toCoeff_hillForgetWeight w 2 q
  have hc : 8*‖q‖ ≤ (n : ℝ) := (mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 8)).trans
    (hNd8.trans (by exact_mod_cast hnD))
  have hc1 : 8*‖q1‖ ≤ (n : ℝ) := by nlinarith [norm_hillForgetWeight_le w 2 q]
  have hcp : 8*‖p‖ ≤ (n : ℝ) := by nlinarith [SpectralWeight.one.norm_toCoeff_le q1]
  have hsmall : 4*Real.exp (1/2)*‖p‖ ≤ (n : ℝ)/2 := by
    have hh := (le_max_left (8*Real.exp (1/2)*B) (2*C*B)).trans hlarge
    nlinarith [mul_le_mul_of_nonneg_left hpB (by positivity : 0 ≤ 4*Real.exp (1/2))]
  have hnear' : ‖E-(freeHillValue n : ℂ)‖ ≤ (n : ℝ)*Real.pi/2 := by
    have hh := (le_max_right (8*Real.exp (1/2)*B) (2*C*B)).trans hlarge
    change ‖E-(freeHillValue n : ℂ)‖ ≤ C*B at hnear
    nlinarith [Real.pi_gt_three]
  have hzero1 : hillL2DirichletCharacteristic p E=0 := by rw [hp];exact hzero
  have hpar1 : p ∈ Coeff.paritySubspace 0 := by rw [hp];exact hpar
  let u := hillL2DirichletResonantModes p E n
  let J := hillL2DirichletBoundaryJump p E n
  let d := E-(freeHillValue n : ℂ)-hillDiagonal SpectralWeight.one q1 n hn1 E hz hc1
  let bp := hillUpperCoupling SpectralWeight.one q1 n hn1 E hz hc1
  let ap := 1+(hillBoundaryGreenPotential q1 n hn1 n E hz hc1).val n
  have hP := (hgreen q1 hq1 n hnG hn1 n E hz hc1).1
  have hcoef : ‖(hillBoundaryGreenPotential q1 n hn1 n E hz hc1).val n‖ ≤ 1/2 := by
    have hh := WeightedCoeff.norm_apply_le SpectralWeight.one.toWeight 2
      (hillBoundaryGreenPotential q1 n hn1 n E hz hc1) n
    simp only [SpectralWeight.one_apply,div_one] at hh
    exact hh.trans hP.le
  have hap : 1/2 ≤ ‖ap‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) ap
    have he : 1-ap = -(hillBoundaryGreenPotential q1 n hn1 n E hz hc1).val n := by dsimp only [ap];ring
    rw [norm_one,he,norm_neg] at hh
    linarith
  have hR := hillL2DirichletResonantModes_reduced p hpar1 E hzero1 n hn1 hz hcp
  simp only [p,hillUnitWeightLift_toCoeff] at hR
  rw [hillReducedOperator_apply] at hR
  have hrow : d*u.1-bp*u.2 = -J*ap := by
    have hh := congrArg Prod.fst hR
    exact hh
  obtain ⟨hu,hv⟩ := hillL2DirichletResonantModes_scaled_bound p n hn1 E hzero1 hnear' hsmall
  have hJ := weighted_source_le_of_resonant_row d bp u.1 u.2 J ap n
    (w (2*(n : ℤ))) (4*Real.exp (1/2)) hnpos.le (w.positive _).le hrow hap hu hv
  obtain ⟨hd,hbp,_⟩ := hillEffectiveCoefficients_weight_independent w q n hn1 E hz hc hc1
  have hdb := hdef w q hq hpar n hnD hn1 E hz hzero hnear hc
  have hb := hillUpperCoupling_le w q n hn1 E hz hc
  rw [hd] at hdb
  rw [hbp] at hb
  change w (2*(n : ℤ))*‖d‖ ≤ _ at hdb
  change w (2*(n : ℤ))*‖bp‖ ≤ _ at hb
  have hW : 0 ≤ w (2*(n : ℤ)) := (w.positive _).le
  have htail : 0 ≤ w (2*(n : ℤ))*‖q.val (-(2*(n : ℤ)))‖+8*‖q‖^2/(n : ℝ) := by positivity
  let T := w (2*(n : ℤ))*‖q.val (2*(n : ℤ))‖+
    w (2*(n : ℤ))*‖q.val (-(2*(n : ℤ)))‖+16*‖q‖^2/(n : ℝ)
  have hbT : w (2*(n : ℤ))*‖bp‖ ≤ T := by
    calc
      _ ≤ w (2*(n : ℤ))*‖q.val (2*(n : ℤ))‖+8*‖q‖^2/(n : ℝ) := hb
      _ ≤ (w (2*(n : ℤ))*‖q.val (2*(n : ℤ))‖+8*‖q‖^2/(n : ℝ))+
          (w (2*(n : ℤ))*‖q.val (-(2*(n : ℤ)))‖+8*‖q‖^2/(n : ℝ)) := le_add_of_nonneg_right htail
      _ = T := by dsimp only [T];ring
  rw [← hp]
  change (n : ℝ)*w (2*(n : ℤ))*‖J‖ ≤ _
  calc
    _ ≤ 2*(4*Real.exp (1/2))*(w (2*(n : ℤ))*‖d‖+w (2*(n : ℤ))*‖bp‖) := hJ
    _ ≤ 2*(4*Real.exp (1/2))*((2*B+4)*T+T) := by gcongr
    _ = _ := by dsimp only [T];ring

end NLS.KdV
