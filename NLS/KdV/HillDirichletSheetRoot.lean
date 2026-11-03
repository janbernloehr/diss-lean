import NLS.KdV.HillDirichletNormingData
import NLS.KdV.HillDirichletAnalyticNorming

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



def hillDirichletSheetRoot (q : Coeff 2) (E : ℂ) : ℂ :=
  2*hillL2DirichletSlope q E-hillL2Discriminant q E

theorem analyticOnNhd_hillDirichletSheetRoot_joint :
    AnalyticOnNhd ℂ (fun t : ℂ × Coeff 2 => hillDirichletSheetRoot t.2 t.1) univ :=
  (analyticOnNhd_const.mul analyticOnNhd_hillL2DirichletSlope_joint).sub analyticOnNhd_hillL2Discriminant_joint

theorem hillDirichletSheetRoot_sq_of_characteristic_zero (q : Coeff 2) (E : ℂ)
    (hzero : hillL2DirichletCharacteristic q E = 0) :
    hillDirichletSheetRoot q E^2 = hillL2Radicand q E := by
  let z := Complex.sqrt E
  let t : Icc (0 : ℝ) 1 := ⟨1,by norm_num⟩
  let c := (hillL2FrequencyStateCurve q z (1,0) t).1
  let d := hillL2DirichletSlope q E
  have hb : (hillL2FrequencyStateCurve q z (0,1) t).1 = 0 := hzero
  have hw := hillL2FrequencyStateCurve_wronskian q z t
  rw [hb,zero_mul,sub_zero] at hw
  have hprod : c*d = 1 := hw
  have htrace : c+d = hillL2Discriminant q E := by
    have ht := hillL2FrequencyStateCurve_trace q z
    rw [← hillL2Discriminant_sq,complex_sqrt_sq E] at ht
    exact ht
  unfold hillDirichletSheetRoot hillL2Radicand
  rw [← htrace]
  change (2*d-(c+d))^2 = (c+d)^2-4
  linear_combination -4*hprod

theorem hillDirichletSheetRoot_at_dirichlet_eq_norming
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) :
    hillDirichletSheetRoot (SpectralWeight.one.toCoeff q) (hillDirichletEnergy q hq hr n hn) =
      (((-1 : ℝ)^n*2*Real.sinh (hillDirichletLogMultiplier q hq hr n hn) : ℝ) : ℂ) := by
  let p := SpectralWeight.one.toCoeff q
  let μ := hillDirichletEnergy q hq hr n hn
  let A := hillDirichletMultiplier q hq hr n hn
  let s : ℝ := (-1)^n
  have hs : s^2 = 1 := by dsimp [s];rw [← pow_mul,Nat.mul_comm n 2,pow_mul];norm_num
  have hrealD : (hillL2DirichletSlope p μ).im = 0 := hillL2DirichletSlope_real p hr μ
  have hrealT : (hillL2Discriminant p μ).im = 0 := hillL2Discriminant_real p hr μ
  have hmul : s*A = (hillL2DirichletSlope p μ).re := by
    change s*(s*(hillL2DirichletSlope p μ).re) = _
    rw [← mul_assoc,← pow_two,hs,one_mul]
  have htr : s*(A+1/A) = (hillL2Discriminant p μ).re := by
    have he := congrArg (fun x : ℝ => s*x) (hillDirichletMultiplier_trace q hq hr n hn)
    change s*(A+1/A) = s*(s*(hillL2Discriminant p μ).re) at he
    rwa [← mul_assoc,← pow_two,hs,one_mul] at he
  have hsinh : 2*Real.sinh (hillDirichletLogMultiplier q hq hr n hn) = A-1/A := by
    rw [hillDirichletLogMultiplier,Real.sinh_eq,Real.exp_neg,Real.exp_log (hillDirichletMultiplier_pos q hq hr n hn)]
    dsimp only [A]
    ring
  have hD : hillL2DirichletSlope p μ = ((s*A : ℝ) : ℂ) := by
    apply Complex.ext
    · exact hmul.symm
    · exact hrealD
  have hT : hillL2Discriminant p μ = ((s*(A+1/A) : ℝ) : ℂ) := by
    apply Complex.ext
    · exact htr.symm
    · exact hrealT
  have hresult : 2*(s*A)-s*(A+1/A) = s*2*Real.sinh (hillDirichletLogMultiplier q hq hr n hn) := by
    rw [show s*2*Real.sinh (hillDirichletLogMultiplier q hq hr n hn) =
      s*(2*Real.sinh (hillDirichletLogMultiplier q hq hr n hn)) by ring,hsinh]
    ring
  unfold hillDirichletSheetRoot
  rw [hD,hT]
  change (2 : ℂ)*((s*A : ℝ) : ℂ)-((s*(A+1/A) : ℝ) : ℂ) =
    ((s*2*Real.sinh (hillDirichletLogMultiplier q hq hr n hn) : ℝ) : ℂ)
  calc
    _ = ((2*(s*A)-s*(A+1/A) : ℝ) : ℂ) := by simp only [ofReal_sub,ofReal_mul,ofReal_ofNat]
    _ = _ := congrArg Complex.ofReal hresult

end NLS.KdV
