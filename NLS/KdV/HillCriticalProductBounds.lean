import NLS.KdV.HillEnergyChiPositivity
import NLS.KdV.HillLowCriticalProductBound
import NLS.KdV.HillChiActionFormula
import NLS.ComplexAnalysis.ProductExponentialBound
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! # Explicit ground-normalized low-product and exponential-tail Hill action bounds. -/

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
open Metric Complex
open NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillEnergyChi_le_low_times_exp
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n K : ℕ) (hK : 1 ≤ K) (hKn : K<n)
    (hcut : 8*‖q‖ ≤ (K+1 : ℕ)) (x : ℝ)
    (hx : x ∈ Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)))
    (hsum : Summable (fun k : ℕ =>
      (hillRealLabels q hq hr (2*(k+K+1))-hillRealLabels q hq hr (2*(k+K+1)-1))/
        (4*|((k+K+1 : ℕ) : ℝ)^2-(n : ℝ)^2|))) :
    ‖hillEnergyChi q hq hr n x‖ ≤
      (‖(hillGapCriticalPoint q hq hr 1 : ℂ)-(x : ℂ)‖ /
        ‖endpointRoot (hillRealLabels q hq hr (2*K-1)) (hillRealLabels q hq hr (2*K)) x‖) /
        Real.sqrt (x-hillRealLabels q hq hr 0) *
      Real.exp (∑' k : ℕ,
        (hillRealLabels q hq hr (2*(k+K+1))-hillRealLabels q hq hr (2*(k+K+1)-1))/
          (4*|((k+K+1 : ℕ) : ℝ)^2-(n : ℝ)^2|)) := by
  let F := hillOmittedEnergyCriticalRootFactor q hq hr n
  let a : ℕ → ℝ := fun k =>
    (hillRealLabels q hq hr (2*(k+K+1))-hillRealLabels q hq hr (2*(k+K+1)-1))/
      (4*|((k+K+1 : ℕ) : ℝ)^2-(n : ℝ)^2|)
  have ha0 (k : ℕ) : 0 ≤ a k := by
    exact div_nonneg (sub_nonneg.mpr (monotone_hillRealLabels q hq hr (by omega))) (by positivity)
  have hdev := (summable_norm_hillOmittedEnergyCriticalRootFactor_sub_one q hq hr n (x : ℂ)).comp_injective
    (i := fun k : ℕ => k+K) (by intro i j h; dsimp only at h; omega)
  have hprod : Multipliable (fun k : ℕ => F (k+K) (x : ℂ)) := by
    have h := multipliable_one_add_of_summable hdev
    convert! h using 1
    funext k
    dsimp only [Function.comp_def,F]
    ring
  have hnorm (k : ℕ) : ‖F (k+K) (x : ℂ)‖ ≤ 1+a k := by
    dsimp only [F,hillOmittedEnergyCriticalRootFactor]
    split_ifs with he
    · simp only [norm_one]
      linarith [ha0 k]
    · exact hillHighGap_critical_root_ratio_le q hq hr n (k+K+1) (by omega) (by omega)
        (hcut.trans (by exact_mod_cast (show K+1≤n by omega)))
        (hcut.trans (by exact_mod_cast (show K+1≤k+K+1 by omega))) he x hx
  have htail := norm_hasProd_le_exp_sum (fun k : ℕ => F (k+K) (x : ℂ)) _ a hprod.hasProd hsum ha0 hnorm
  have hsplit := Multipliable.prod_mul_tprod_nat_mul' (f := fun k : ℕ => F k (x : ℂ)) (k := K) hprod
  have hhead : (∏ k ∈ Finset.range K, F k (x : ℂ)) =
      ∏ k ∈ Finset.range K, hillEnergyCriticalRootRatio q hq hr (k+1) x := by
    apply Finset.prod_congr rfl
    intro k hk
    dsimp only [F,hillOmittedEnergyCriticalRootFactor]
    rw [if_neg (by have hh := Finset.mem_range.mp hk; omega)]
  rw [hhead] at hsplit
  have hlow := hillLowCriticalRootProduct_bound q hq hr n K hK hKn x hx
  have hfull : ‖hillOmittedEnergyCriticalRootProduct q hq hr n x‖ ≤
      (‖(hillGapCriticalPoint q hq hr 1 : ℂ)-(x : ℂ)‖ /
        ‖endpointRoot (hillRealLabels q hq hr (2*K-1)) (hillRealLabels q hq hr (2*K)) x‖)*Real.exp (∑' k, a k) := by
    change ‖∏' k, F k (x : ℂ)‖ ≤ _
    rw [← hsplit,norm_mul]
    exact mul_le_mul hlow htail (norm_nonneg _) (by positivity)
  have hx0 : hillRealLabels q hq hr 0 < x := by
    have hband := hillRealLabels_band_strict q hq hr 0
    simp only [mul_zero,zero_add] at hband
    exact hband.trans_le ((monotone_hillRealLabels q hq hr (by omega)).trans hx.1)
  have hs : Complex.sqrt ((x : ℂ)-hillRealLabels q hq hr 0) =
      (Real.sqrt (x-hillRealLabels q hq hr 0) : ℂ) := by
    rw [← ofReal_sub,Complex.sqrt_of_nonneg (by exact_mod_cast (show 0≤x-hillRealLabels q hq hr 0 by linarith))]
    simp only [ofReal_re]
  rw [hillEnergyChi,norm_mul,norm_inv,hs,norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ (Real.sqrt (x-hillRealLabels q hq hr 0))⁻¹ *
      ((‖(hillGapCriticalPoint q hq hr 1 : ℂ)-(x : ℂ)‖ /
        ‖endpointRoot (hillRealLabels q hq hr (2*K-1)) (hillRealLabels q hq hr (2*K)) x‖)*Real.exp (∑' k, a k)) :=
      mul_le_mul_of_nonneg_left hfull (by positivity)
    _ = _ := by dsimp only [a]; ring

theorem hillLowCriticalProduct_ground_bound
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n K : ℕ) (hK : 2 ≤ K) (hKn : K<n)
    (hcut : 8*‖q‖ ≤ (K : ℝ)) (x : ℝ)
    (hx : x ∈ Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n))) :
    (‖(hillGapCriticalPoint q hq hr 1 : ℂ)-(x : ℂ)‖ /
      ‖endpointRoot (hillRealLabels q hq hr (2*K-1)) (hillRealLabels q hq hr (2*K)) x‖) /
      Real.sqrt (x-hillRealLabels q hq hr 0) ≤ ((K : ℝ)+1)/(n : ℝ) := by
  let energy0 := hillRealLabels q hq hr 0
  let root := endpointRoot (hillRealLabels q hq hr (2*K-1)) (hillRealLabels q hq hr (2*K)) x
  let d : ℝ := (n : ℝ)^2-(K : ℝ)^2
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hnr : (K : ℝ)+1 ≤ n := by exact_mod_cast (show K+1≤n by omega)
  have hn0 : (0 : ℝ)<n := by linarith
  have hd : 0<d := by dsimp only [d]; nlinarith
  have hKd : (K : ℝ) ≤ d := by dsimp only [d]; nlinarith
  have hxK : hillRealLabels q hq hr (2*K) < x :=
    (hillRealLabels_band_strict q hq hr K).trans_le
      ((monotone_hillRealLabels q hq hr (by omega)).trans hx.1)
  have hrbound : x-hillRealLabels q hq hr (2*K) ≤ ‖root‖ :=
    norm_endpointRoot_ge_right_distance _ _ x (monotone_hillRealLabels q hq hr (by omega)) hxK
  have hxb := abs_le.mp (hillRealGap_point_high_bound q hq hr n (by omega)
    (hcut.trans (by exact_mod_cast (show K≤n by omega))) x hx)
  have hkb := abs_le.mp (hillRealLabels_high_endpoint_bounds q hq hr K hK hcut).2
  have hpilo : (9 : ℝ)<Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hpiup : Real.pi^2<16 := by nlinarith [Real.pi_lt_four,Real.pi_pos]
  simp only [freeHillValue,Int.cast_natCast] at hxb hkb
  have hrlo : 8*d ≤ ‖root‖ := by
    have hp := mul_le_mul_of_nonneg_right hpilo.le hd.le
    dsimp only [d] at hp ⊢
    nlinarith
  have hrpos : 0<‖root‖ := (mul_pos (by norm_num : (0 : ℝ)<8) hd).trans_le hrlo
  have hground := hillL2Radicand_re_lower_bound q hq K (by omega) hcut
    (hillRealLabels q hq hr 0 : ℂ) ((hillRealLabels_spec q hq hr).root 0)
  simp only [ofReal_re] at hground
  have hx0 : energy0 < x := by
    exact (hillRealLabels_band_strict q hq hr 0).trans_le
      ((monotone_hillRealLabels q hq hr (by omega)).trans hx.1)
  have hspos : 0<Real.sqrt (x-energy0) := Real.sqrt_pos.mpr (sub_pos.mpr hx0)
  have hxup : x-energy0 ≤ (5*(n : ℝ))^2 := by
    have hpi := mul_le_mul_of_nonneg_right hpiup.le (sq_nonneg (n : ℝ))
    have hKsq : (K : ℝ)^2 ≤ (n : ℝ)^2 := by nlinarith
    dsimp only [energy0]
    nlinarith
  have hsbound : Real.sqrt (x-energy0) ≤ 5*(n : ℝ) :=
    (Real.sqrt_le_iff).mpr ⟨by positivity,hxup⟩
  have hc := (hillGapCriticalPoint_spec q hq hr 1 (by omega)).1
  have hc0 : energy0 ≤ hillGapCriticalPoint q hq hr 1 :=
    (monotone_hillRealLabels q hq hr (by omega : 0≤2*1-1)).trans hc.1
  have hcx : hillGapCriticalPoint q hq hr 1 < x :=
    hc.2.trans_lt ((hillRealLabels_band_strict q hq hr 1).trans_le
      ((monotone_hillRealLabels q hq hr (by omega)).trans hx.1))
  have hnum : ‖(hillGapCriticalPoint q hq hr 1 : ℂ)-(x : ℂ)‖ ≤ x-energy0 := by
    rw [← ofReal_sub,norm_real,Real.norm_eq_abs,abs_of_neg (sub_neg.mpr hcx)]
    linarith
  change (_/‖root‖)/Real.sqrt (x-energy0) ≤ _
  calc
    _ ≤ ((x-energy0)/‖root‖)/Real.sqrt (x-energy0) :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hnum hrpos.le) hspos.le
    _ = Real.sqrt (x-energy0)/‖root‖ := by
      have hh := Real.sq_sqrt (sub_nonneg.mpr hx0.le)
      field_simp [ne_of_gt hrpos,ne_of_gt hspos]
      nlinarith
    _ ≤ (5*(n : ℝ))/(8*d) :=
      div_le_div₀ (by positivity : 0≤5*(n : ℝ)) hsbound (mul_pos (by norm_num : (0 : ℝ)<8) hd) hrlo
    _ ≤ ((K : ℝ)+1)/(n : ℝ) := by
      apply (div_le_div_iff₀ (by positivity : 0<8*d) hn0).mpr
      have hpoly : (n : ℝ)^2 ≤ ((K : ℝ)+1)*d := by
        have hh : (K : ℝ)*((K : ℝ)+1) ≤ (n : ℝ)^2 := by nlinarith
        have hh' := mul_le_mul_of_nonneg_left hh (by positivity : 0≤(K : ℝ))
        dsimp only [d]
        nlinarith
      nlinarith

theorem hillEnergyChi_le_exp_tail
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n K : ℕ) (hK : 2≤K) (hKn : K<n)
    (hcut : 8*‖q‖ ≤ (K : ℝ)) (x : ℝ)
    (hx : x ∈ Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)))
    (hsum : Summable (fun k : ℕ =>
      (hillRealLabels q hq hr (2*(k+K+1))-hillRealLabels q hq hr (2*(k+K+1)-1))/
        (4*|((k+K+1 : ℕ) : ℝ)^2-(n : ℝ)^2|))) :
    ‖hillEnergyChi q hq hr n x‖ ≤ ((K : ℝ)+1)/(n : ℝ)*
      Real.exp (∑' k : ℕ,
        (hillRealLabels q hq hr (2*(k+K+1))-hillRealLabels q hq hr (2*(k+K+1)-1))/
          (4*|((k+K+1 : ℕ) : ℝ)^2-(n : ℝ)^2|)) := by
  exact (hillEnergyChi_le_low_times_exp q hq hr n K (by omega) hKn
    (hcut.trans (by exact_mod_cast (show K≤K+1 by omega))) x hx hsum).trans
      (mul_le_mul_of_nonneg_right (hillLowCriticalProduct_ground_bound q hq hr n K hK hKn hcut x hx)
        (Real.exp_pos _).le)

theorem hillRealGapIntegral_le_exp_tail
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n K : ℕ) (hK : 2≤K) (hKn : K<n)
    (hcut : 8*‖q‖ ≤ (K : ℝ))
    (hsum : Summable (fun k : ℕ =>
      (hillRealLabels q hq hr (2*(k+K+1))-hillRealLabels q hq hr (2*(k+K+1)-1))/
        (4*|((k+K+1 : ℕ) : ℝ)^2-(n : ℝ)^2|))) :
    (n : ℝ)*hillRealGapIntegral q hq hr n 0 ≤ ((K : ℝ)+1)*
      Real.exp (∑' k : ℕ,
        (hillRealLabels q hq hr (2*(k+K+1))-hillRealLabels q hq hr (2*(k+K+1)-1))/
          (4*|((k+K+1 : ℕ) : ℝ)^2-(n : ℝ)^2|))*
      (hillRealLabels q hq hr (2*n)-hillRealLabels q hq hr (2*n-1))^2 := by
  have hn : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have h := hillRealGapIntegral_le_chi_bound q hq hr n (by omega)
    (((K : ℝ)+1)/(n : ℝ)*Real.exp (∑' k : ℕ,
      (hillRealLabels q hq hr (2*(k+K+1))-hillRealLabels q hq hr (2*(k+K+1)-1))/
        (4*|((k+K+1 : ℕ) : ℝ)^2-(n : ℝ)^2|))) (by positivity)
    (fun x hx => (Complex.re_le_norm _).trans (hillEnergyChi_le_exp_tail q hq hr n K hK hKn hcut x hx hsum))
  have hh := mul_le_mul_of_nonneg_left h hn.le
  convert! hh using 1
  field_simp [ne_of_gt hn]

end NLS.KdV
