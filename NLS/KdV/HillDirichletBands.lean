import NLS.KdV.HillStateMonodromy
import NLS.KdV.HillRealBands

/-! # The rough Dirichlet characteristic excludes every open spectral band. -/

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory Matrix
open scoped ComplexConjugate ENNReal
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillL2DirichletCharacteristic_zero_discriminant_sq_ge_four
    (q : Coeff 2) (hq : IsRealHillPotential q) (energy : ℂ)
    (hz : hillL2DirichletCharacteristic q energy=0) : 4≤(hillL2Discriminant q energy).re^2 := by
  let z := Complex.sqrt energy
  let t : Icc (0 : ℝ) 1 := ⟨1,by norm_num⟩
  have hs : z^2=energy := NLS.ComplexAnalysis.complex_sqrt_sq _
  have he : (z^2).im=0 := by rw [hs]; exact hillL2DirichletCharacteristic_zero_real q hq energy hz
  have hD : (hillL2FrequencyStateCurve q z (0,1) t).1=0 := hz
  have hc := (hillL2FrequencyStateCurve_real q hq z he (1,0) (by norm_num) t).1
  have hd := (hillL2FrequencyStateCurve_real q hq z he (0,1) (by norm_num) t).2
  have hW := hillL2FrequencyStateCurve_wronskian q z t
  rw [hD,zero_mul,sub_zero] at hW
  have hprod := congrArg Complex.re hW
  simp only [mul_re,hc,hd,mul_zero,sub_zero,one_re] at hprod
  have hT := congrArg Complex.re (hillL2FrequencyStateCurve_trace q z)
  simp only [add_re] at hT
  rw [← hillL2Discriminant_sq,hs] at hT
  change (hillL2FrequencyStateCurve q z (1,0) t).1.re+
    (hillL2FrequencyStateCurve q z (0,1) t).2.re=(hillL2Discriminant q energy).re at hT
  rw [← hT]
  nlinarith only [hprod,sq_nonneg ((hillL2FrequencyStateCurve q z (1,0) t).1.re-
    (hillL2FrequencyStateCurve q z (0,1) t).2.re)]

theorem hillL2DirichletCharacteristic_ne_zero_on_open_band
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (x : ℝ)
    (hx : x ∈ Ioo (hillRealLabels q hq hr (2*n)) (hillRealLabels q hq hr (2*n+1))) :
    hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) x≠0 := by
  intro hzero
  have h := hillL2DirichletCharacteristic_zero_discriminant_sq_ge_four (SpectralWeight.one.toCoeff q) hr x hzero
  have hb := hillL2Discriminant_open_band_bounds q hq hr n x hx
  nlinarith [mul_pos (by linarith : 0<(hillL2Discriminant (SpectralWeight.one.toCoeff q) x).re+2)
    (by linarith : 0<2-(hillL2Discriminant (SpectralWeight.one.toCoeff q) x).re)]

end NLS.KdV
