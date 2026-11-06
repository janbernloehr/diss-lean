import NLS.KdV.HillDirichletSheetRoot
import NLS.KdV.HillDirichletParityForcing

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.Fourier NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



/-- The actual Dirichlet sheet is controlled by its original fixed-phase
derivative jump near the free slope, using the original Wronskian. -/
theorem norm_hillDirichletSheetRoot_le_five_jump (q : Coeff 2) (E : ℂ)
    (hzero : hillL2DirichletCharacteristic q E=0) (n : ℤ)
    (hsmall : ‖hillL2DirichletBoundaryJump q E n‖ ≤ 1/2) :
    ‖hillDirichletSheetRoot q E‖ ≤ 5*‖hillL2DirichletBoundaryJump q E n‖ := by
  let z := Complex.sqrt E
  let t : Icc (0 : ℝ) 1 := ⟨1,by norm_num⟩
  let c := (hillL2FrequencyStateCurve q z (1,0) t).1
  let d := hillL2DirichletSlope q E
  let σ := wave (-n) 1
  let J := d*σ-1
  have hσ : σ^2=1 := by
    dsimp only [σ]
    rw [pow_two,← wave_add,show -n+-n=2*(-n) by ring,wave_even_at_one]
  have hσnorm : ‖σ‖=1 := by simp [σ,wave,Complex.norm_exp]
  have hb : (hillL2FrequencyStateCurve q z (0,1) t).1=0 := hzero
  have hw := hillL2FrequencyStateCurve_wronskian q z t
  rw [hb,zero_mul,sub_zero] at hw
  have hprod : c*d=1 := hw
  have htrace : c+d=hillL2Discriminant q E := by
    have ht := hillL2FrequencyStateCurve_trace q z
    rw [← hillL2Discriminant_sq,complex_sqrt_sq E] at ht
    exact ht
  have hsheet : hillDirichletSheetRoot q E=d-c := by
    rw [hillDirichletSheetRoot,← htrace]
    dsimp only [d]
    ring
  have hsmall' : ‖J‖ ≤ 1/2 := hsmall
  have hlo : 1/2 ≤ ‖d‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) (d*σ)
    rw [norm_one,norm_mul,hσnorm,mul_one,norm_sub_rev] at hh
    change 1-‖d‖ ≤ ‖J‖ at hh
    linarith
  have hplus : ‖d*σ+1‖ ≤ 5/2 := by
    have hh := norm_add_le J (2 : ℂ)
    rw [show J+2=d*σ+1 by dsimp only [J];ring,norm_ofNat] at hh
    linarith
  have hfactor : (d-c)*d=(d*σ-1)*(d*σ+1) := by
    linear_combination -hprod-d^2*hσ
  have hnorm := congrArg norm hfactor
  rw [norm_mul,norm_mul] at hnorm
  have hh := mul_le_mul_of_nonneg_left hplus (norm_nonneg J)
  have hl := mul_le_mul_of_nonneg_left hlo (norm_nonneg (d-c))
  rw [hsheet]
  change ‖d-c‖ ≤ 5*‖J‖
  change ‖J‖*‖d*σ+1‖ ≤ ‖J‖*(5/2) at hh
  nlinarith

end NLS.KdV
