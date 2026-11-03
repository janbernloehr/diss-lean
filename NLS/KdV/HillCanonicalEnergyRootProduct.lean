import NLS.KdV.HillGlobalMomentBounds
import NLS.KdV.HillCanonicalFreeLabels
import NLS.ComplexAnalysis.EndpointRootBounds
import NLS.ComplexAnalysis.AbsoluteProductConvergence
import Mathlib.Analysis.PSeries

/-! # The absolutely convergent actual energy-indexed standard-root product, its square, nonvanishing and exact free normalization. Actual radicand identification remains separate. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open NLS.ComplexAnalysis
namespace NLS.KdV
def hillEnergyRootFactor
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (z : ℂ) : ℂ :=
  endpointRoot (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)) z /
    (freeHillValue n : ℂ)

theorem summable_norm_hillEnergyRootFactor_sub_one
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) :
    Summable (fun k : ℕ => ‖hillEnergyRootFactor q hq hr (k+1) z-1‖) := by
  let D : ℝ := 4*‖q‖
  let C : ℝ := D+‖z‖+2*D^2
  have hD : 0 ≤ D := by positivity
  have hC : 0 ≤ C := by positivity
  have hs0 : Summable (fun n : ℕ => 1/(n : ℝ)^2) := Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs : Summable (fun k : ℕ => C/(k+1 : ℕ)^2) := by
    simpa only [div_eq_mul_inv,one_mul] using ((summable_nat_add_iff 1).mpr hs0).mul_left C
  apply hs.of_norm_bounded_eventually_nat
  obtain ⟨N,hN⟩ := exists_nat_gt (16*‖q‖+2*(D+‖z‖)+2)
  filter_upwards [eventually_atTop.mpr ⟨N,fun k hk => hk⟩] with k hk
  simp only [norm_norm]
  have hkR : (N : ℝ) ≤ k := by exact_mod_cast hk
  have hn2 : 2 ≤ k+1 := by
    have hn : (2 : ℝ) < k := by linarith [norm_nonneg q,norm_nonneg z]
    exact_mod_cast (show (2 : ℝ) ≤ (k+1 : ℕ) by push_cast; linarith)
  have hn : (1 : ℝ) ≤ (k+1 : ℕ) := by exact_mod_cast (show 1 ≤ k+1 by omega)
  have hcut : 16*‖q‖ ≤ (k+1 : ℕ) := by push_cast; linarith [norm_nonneg z]
  obtain ⟨p,hl,hu⟩ := hillRealLabels_high_pair q hq hr (k+1) hn2 hcut
  have hloc := p.localization q hq (k+1) (by omega) (by linarith [norm_nonneg q])
  have hlo : |hillRealLabels q hq hr (2*(k+1)-1)-freeHillValue (k+1)| ≤ D := by simpa only [hl,D,Nat.cast_add,Nat.cast_one] using hloc.1
  have hup : |hillRealLabels q hq hr (2*(k+1))-freeHillValue (k+1)| ≤ D := by simpa only [hu,D,Nat.cast_add,Nat.cast_one] using hloc.2
  have hnle : (k+1 : ℝ)^2 ≤ freeHillValue (k+1) := by
    have h := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ Real.pi^2 by nlinarith [Real.pi_gt_three])
      (sq_nonneg (k+1 : ℝ))
    simpa only [one_mul,freeHillValue,Int.cast_add,Int.cast_natCast,Int.cast_one] using h
  have hc : 1 ≤ freeHillValue (k+1) := by
    have hp : (1 : ℝ) ≤ (k+1 : ℝ)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k,sq_nonneg (k : ℝ)]
    exact hp.trans hnle
  have hlarge : 2*(D+‖z‖) < freeHillValue (k+1) := by
    have hsq : (k+1 : ℝ) ≤ (k+1 : ℝ)^2 := by nlinarith
    have hnR : 2*(D+‖z‖) < (k+1 : ℝ) := by linarith [norm_nonneg q]
    exact hnR.trans_le (hsq.trans hnle)
  have hf := norm_endpointRoot_div_sub_one_le
    (hillRealLabels q hq hr (2*(k+1)-1)) (hillRealLabels q hq hr (2*(k+1)))
    (freeHillValue (k+1)) D z hc hlo hup hlarge
  change ‖hillEnergyRootFactor q hq hr (k+1) z-1‖ ≤ C/((k+1 : ℕ) : ℝ)^2
  exact hf.trans (div_le_div_of_nonneg_left hC (by positivity) (by exact_mod_cast hnle))

theorem multipliable_hillEnergyRootFactors
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) :
    Multipliable (fun k : ℕ => hillEnergyRootFactor q hq hr (k+1) z) := by
  have h := multipliable_one_add_of_summable (summable_norm_hillEnergyRootFactor_sub_one q hq hr z)
  convert! h using 1
  funext k
  ring

def hillEnergyRootProduct
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) : ℂ :=
  ∏' k : ℕ, hillEnergyRootFactor q hq hr (k+1) z

def hillEnergyCanonicalRootProduct
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) : ℂ :=
  -2*I*Complex.sqrt (z-hillRealLabels q hq hr 0)*hillEnergyRootProduct q hq hr z

theorem hillEnergyRootFactor_sq
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (z : ℂ)
    (hz : z ∉ segment ℝ (hillRealLabels q hq hr (2*n-1) : ℂ) (hillRealLabels q hq hr (2*n) : ℂ)) :
    hillEnergyRootFactor q hq hr n z^2 =
      ((hillRealLabels q hq hr (2*n-1) : ℂ)-z)*((hillRealLabels q hq hr (2*n) : ℂ)-z)/(freeHillValue n : ℂ)^2 := by
  rw [hillEnergyRootFactor,div_pow,endpointRoot_sq _ _ _ hz]
  ring

theorem hillEnergyRootProduct_ne_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ)
    (hz : ∀ n : ℕ, 1 ≤ n → z ∉ segment ℝ
      (hillRealLabels q hq hr (2*n-1) : ℂ) (hillRealLabels q hq hr (2*n) : ℂ)) :
    hillEnergyRootProduct q hq hr z ≠ 0 := by
  have hs := summable_norm_hillEnergyRootFactor_sub_one q hq hr z
  have hf (k : ℕ) : hillEnergyRootFactor q hq hr (k+1) z ≠ 0 := by
    unfold hillEnergyRootFactor
    apply div_ne_zero
    · have hseg := hz (k+1) (by omega)
      intro he
      have hsq := endpointRoot_sq
        (hillRealLabels q hq hr (2*(k+1)-1)) (hillRealLabels q hq hr (2*(k+1))) z hseg
      rw [he,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
      rcases mul_eq_zero.mp hsq.symm with hl | hu
      · exact hseg ((sub_eq_zero.mp hl) ▸ left_mem_segment ℝ _ _)
      · exact hseg ((sub_eq_zero.mp hu) ▸ right_mem_segment ℝ _ _)
    · apply Complex.ofReal_ne_zero.mpr
      dsimp only [freeHillValue]
      exact mul_ne_zero (pow_ne_zero _ Real.pi_ne_zero) (pow_ne_zero _ (by exact_mod_cast (show (k+1 : ℤ) ≠ 0 by omega)))
  have hp := (tprod_one_add_ne_zero_iff (fun k => hillEnergyRootFactor q hq hr (k+1) z-1) hs).mpr
    (fun k => by convert! hf k using 1; ring)
  unfold hillEnergyRootProduct
  convert! hp using 1
  congr 1
  funext k
  ring

theorem hillEnergyCanonicalRootProduct_sq
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ)
    (hz : ∀ n : ℕ, 1 ≤ n → z ∉ segment ℝ
      (hillRealLabels q hq hr (2*n-1) : ℂ) (hillRealLabels q hq hr (2*n) : ℂ)) :
    hillEnergyCanonicalRootProduct q hq hr z^2 = -4*(z-hillRealLabels q hq hr 0)*
      (∏' k : ℕ, ((hillRealLabels q hq hr (2*(k+1)-1) : ℂ)-z)*
        ((hillRealLabels q hq hr (2*(k+1)) : ℂ)-z)/(freeHillValue (k+1) : ℂ)^2) := by
  have hp := (multipliable_hillEnergyRootFactors q hq hr z).tprod_pow 2
  have hf (k : ℕ) := hillEnergyRootFactor_sq q hq hr (k+1) z (hz (k+1) (by omega))
  rw [funext hf] at hp
  have hs : (Complex.sqrt (z-hillRealLabels q hq hr 0))^2 = z-hillRealLabels q hq hr 0 := by
    have h := Complex.cpow_nat_inv_pow (z-hillRealLabels q hq hr 0) (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  simp only [hillEnergyCanonicalRootProduct,mul_pow,hillEnergyRootProduct,hs]
  rw [← hp]
  simp only [I_sq,Nat.cast_add,Nat.cast_one]
  ring

theorem hillEnergyRootFactor_zero
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) :
    hillEnergyRootFactor 0 hq hr n z = 1-z/(freeHillValue n : ℂ) := by
  have hL := hillRealLabels_zero hq hr (2*n-1)
  have hU := hillRealLabels_zero hq hr (2*n)
  have hi : (2*n-1+1)/2 = n := by omega
  have hj : (2*n+1)/2 = n := by omega
  rw [hi] at hL
  rw [hj] at hU
  unfold hillEnergyRootFactor
  rw [hL,hU]
  have he : endpointRoot (freeHillValue n : ℂ) (freeHillValue n : ℂ) z = (freeHillValue n : ℂ)-z := by
    unfold endpointRoot
    rw [sub_self,zero_pow (by norm_num : (2 : ℕ) ≠ 0),normalizedStandardRoot_zeroGap]
    congr 1
    ring
  rw [he,sub_div,div_self]
  apply Complex.ofReal_ne_zero.mpr
  dsimp only [freeHillValue]
  exact mul_ne_zero (pow_ne_zero _ Real.pi_ne_zero) (pow_ne_zero _ (by exact_mod_cast (show (n : ℤ) ≠ 0 by omega)))

theorem hillEnergyCanonicalRootProduct_zero
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (z : ℂ) : hillEnergyCanonicalRootProduct 0 hq hr z = -2*I*Complex.sin (Complex.sqrt z) := by
  let w := Complex.sqrt z
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : w^2 = z := by
    have h := Complex.cpow_nat_inv_pow z (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [w,Complex.sqrt,one_div] using h
  have he := (Complex.tendsto_euler_sin_prod (w/(Real.pi : ℂ))).const_mul (-2*I)
  rw [mul_div_cancel₀ _ hpi] at he
  have hp := ((multipliable_hillEnergyRootFactors 0 hq hr z).hasProd.tendsto_prod_nat).const_mul (-2*I*w)
  have hf (N : ℕ) : (-2*I*w)*(∏ k ∈ Finset.range N, hillEnergyRootFactor 0 hq hr (k+1) z) =
      (-2*I)*(w*∏ k ∈ Finset.range N, (1-(w/(Real.pi : ℂ))^2/((k : ℂ)+1)^2)) := by
    rw [mul_assoc]
    congr 1
    congr 1
    apply Finset.prod_congr rfl
    intro k _
    rw [hillEnergyRootFactor_zero hq hr (k+1) (by omega)]
    rw [div_pow,div_div,hs]
    congr 2
    simp only [freeHillValue,ofReal_mul,ofReal_pow,ofReal_intCast,Nat.cast_add,Nat.cast_one]
    push_cast
    ring
  rw [funext hf] at hp
  have hval := tendsto_nhds_unique hp he
  change (-2*I*w)*hillEnergyRootProduct 0 hq hr z = -2*I*sin w at hval
  simpa only [hillEnergyCanonicalRootProduct,hillRealLabels_zero_ground hq hr,ofReal_zero,sub_zero] using hval

def hillEnergyCanonicalRootPartialProduct
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) (N : ℕ) : ℂ :=
  -2*I*Complex.sqrt (z-hillRealLabels q hq hr 0)*
    ∏ k ∈ Finset.range N, hillEnergyRootFactor q hq hr (k+1) z

theorem tendsto_hillEnergyCanonicalRootPartialProduct
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) :
    Tendsto (hillEnergyCanonicalRootPartialProduct q hq hr z) atTop
      (𝓝 (hillEnergyCanonicalRootProduct q hq hr z)) :=
  ((multipliable_hillEnergyRootFactors q hq hr z).hasProd.tendsto_prod_nat).const_mul _

end NLS.KdV
