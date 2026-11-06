import NLS.KdV.HillActionGapFactor
import NLS.KdV.HillDeflatedTraceChi
import NLS.KdV.HillLocalGapPhysicalMatching
import NLS.KdV.HillOpenGapHalfLength
import NLS.ComplexAnalysis.QuadraticGapActionRatio
import NLS.ComplexAnalysis.CosineGapNeighborhood

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat MeasureTheory
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillLocalActionGapRatio (n : ℕ) : Coeff 2 → ℂ :=
  quadraticGapActionRatio (hillLocalDeflatedTraceNumerator q hq hr n)
    (hillLocalGapMidpoint q hq hr n) (fun p => hillLocalGapSquare q hq hr n p/4)

theorem analyticAt_hillLocalActionGapRatio_of_collapse (n : ℕ) (hn : 1 ≤ n)
    (hc : hillRealLabels q hq hr (2*n-1) = hillRealLabels q hq hr (2*n)) :
    AnalyticAt ℂ (hillLocalActionGapRatio q hq hr n) (SpectralWeight.one.toCoeff q) := by
  obtain ⟨A,_,hqA,hM,hS,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood q hq hr n hn
  have hdata := hillLocalGapSymmetricData_eq_physical_of_geometry q hq hr q hq hr n hn
    (hillRealGapContour_band_bounds q hq hr n hn) (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr n hn)
  have hs0 : hillLocalGapSquare q hq hr n (SpectralWeight.one.toCoeff q)/4 = 0 := by
    have hδ : hillRealGapHalfLength q hq hr n = 0 := by simp only [hillRealGapHalfLength,hc,sub_self,zero_div]
    rw [hdata.2,hδ,ofReal_zero,mul_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_div]
  have hrad : 0 < hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n :=
    add_pos_of_nonneg_of_pos (hillRealGapContour_geometry q hq hr n hn).1 (hillRealGapContour_geometry q hq hr n hn).2.1
  have hbase : (hillLocalGapMidpoint q hq hr n (SpectralWeight.one.toCoeff q),SpectralWeight.one.toCoeff q) ∈
      hillLocalDeflatedRootDomain q hq hr n := by
    rw [hdata.1]
    exact mem_hillLocalDeflatedRootDomain_base q hq hr n hn _ (mem_ball_self hrad)
  exact analyticAt_quadraticGapActionRatio_of_collapse _ _ _ _
    (analyticOnNhd_hillLocalDeflatedTraceNumerator q hq hr n hn _ hbase) (hM _ hqA) ((hS _ hqA).div_const) hs0

theorem hillLocalActionGapRatio_eventually_eq_physical (n : ℕ) (hn : 1 ≤ n) :
    ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      hillLocalActionGapRatio q hq hr n (SpectralWeight.one.toCoeff p.val) = hillActionGapRatio p.val p.property.1 p.property.2 n := by
  obtain ⟨E,V,hE,hV,hgapE,hqV,hHmatch⟩ := exists_hillLocalDeflatedTraceNumerator_physical_neighborhood q hq hr n hn
  have hgeom := hillRealGapContour_geometry q hq hr n hn
  obtain ⟨W,hW,hqW,hcos⟩ := exists_open_cosineGapPoint_real_neighborhood
    (fun p : RealPeriodOneHillPotential => (hillRealGapCenter p.val p.property.1 p.property.2 n : ℂ))
    (fun p : RealPeriodOneHillPotential => (hillRealGapHalfLength p.val p.property.1 p.property.2 n : ℂ))
    (continuous_ofReal.comp (continuous_hillRealGapCenter n))
    (continuous_ofReal.comp (continuous_hillRealGapHalfLength n)) E hE
    (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) (by
      simpa only [← ofReal_sub,← ofReal_add,hgeom.2.2.1,hgeom.2.2.2.1] using hgapE)
  obtain ⟨T,hT,hqT,hdata⟩ := exists_hillLocalGapSymmetricData_physical_neighborhood q hq hr n hn
  filter_upwards [hV.mem_nhds hqV,hW.mem_nhds hqW,hT.mem_nhds hqT] with p hpV hpW hpT
  let P := SpectralWeight.one.toCoeff p.val
  let δ : ℂ := hillRealGapHalfLength p.val p.property.1 p.property.2 n
  have hsq : (Complex.sqrt (hillLocalGapSquare q hq hr n P/4))^2 = δ^2 := by
    rw [complex_sqrt_sq,(hdata p hpT).2]
    change (2*δ)^2/4 = δ^2
    ring
  have hroot : parametricSineSquareCosineMean
      (fun x : ℂ × Coeff 2 => deriv (fun w => hillLocalDeflatedTraceNumerator q hq hr n (w,x.2)) x.1)
      (hillLocalGapMidpoint q hq hr n) (Complex.sqrt (hillLocalGapSquare q hq hr n P/4),P) =
    parametricSineSquareCosineMean
      (fun x : ℂ × Coeff 2 => deriv (fun w => hillLocalDeflatedTraceNumerator q hq hr n (w,x.2)) x.1)
      (hillLocalGapMidpoint q hq hr n) (δ,P) := by
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with he | he
    · rw [he]
    · rw [he,parametricSineSquareCosineMean_neg]
  dsimp only [hillLocalActionGapRatio,quadraticGapActionRatio]
  rw [hroot]
  congr 1
  unfold parametricSineSquareCosineMean
  rw [(hdata p hpT).1]
  apply intervalIntegral.integral_congr
  intro θ hθ
  have hθ' : θ ∈ Icc (0 : ℝ) Real.pi := by simpa only [uIcc_of_le Real.pi_pos.le] using hθ
  let z : ℂ := (hillRealGapCenter p.val p.property.1 p.property.2 n : ℂ)+δ*(Real.cos θ : ℂ)
  have hz : z ∈ E := by simpa only [z,δ,cosineGapPoint,← ofReal_cos] using hcos p hpW θ hθ'
  have he : (fun w => hillLocalDeflatedTraceNumerator q hq hr n (w,P)) =ᶠ[𝓝 z]
      hillDeflatedTraceNumerator p.val p.property.1 p.property.2 n := by
    filter_upwards [hE.mem_nhds hz] with w hw
    exact (hHmatch p hpV w hw).2.2
  exact congrArg (fun v : ℂ => (Real.sin θ : ℂ)^2*v) he.deriv_eq

theorem hillActionGapRatio_at_collapse (n : ℕ) (hn : 1 ≤ n)
    (hc : hillRealLabels q hq hr (2*n-1) = hillRealLabels q hq hr (2*n)) :
    hillActionGapRatio q hq hr n = hillEnergyChi q hq hr n (hillRealLabels q hq hr (2*n-1) : ℂ)/2 := by
  have hδ : hillRealGapHalfLength q hq hr n = 0 := by simp only [hillRealGapHalfLength,hc,sub_self,zero_div]
  have hτ : hillRealGapCenter q hq hr n = hillRealLabels q hq hr (2*n-1) := by
    dsimp only [hillRealGapCenter]
    rw [← hc]
    ring
  have hm := parametricSineSquareCosineMean_zero
    (fun x : ℂ × Unit => deriv (hillDeflatedTraceNumerator q hq hr n) x.1)
    (fun _ : Unit => (hillRealGapCenter q hq hr n : ℂ)) ()
  simp only [parametricSineSquareCosineMean,zero_mul,add_zero] at hm
  unfold hillActionGapRatio
  simp only [hδ,ofReal_zero,zero_mul,add_zero]
  rw [hm]
  have he : (-2*I/(Real.pi : ℂ))*((Real.pi : ℂ)/2*deriv (hillDeflatedTraceNumerator q hq hr n) (hillRealGapCenter q hq hr n : ℂ)) =
      -I*deriv (hillDeflatedTraceNumerator q hq hr n) (hillRealGapCenter q hq hr n : ℂ) := by field_simp
  rw [he,hτ]
  exact neg_I_mul_deriv_hillDeflatedTraceNumerator_at_closed_gap q hq hr n hn hc

theorem hillActionGapRatio_real_positive (n : ℕ) (hn : 1 ≤ n) :
    0 < (hillActionGapRatio q hq hr n).re ∧ (hillActionGapRatio q hq hr n).im = 0 := by
  by_cases hc : hillRealLabels q hq hr (2*n-1) = hillRealLabels q hq hr (2*n)
  · have hχ := hillEnergyChi_real_positive q hq hr n hn (hillRealLabels q hq hr (2*n-1)) ⟨le_rfl,hc.le⟩
    rw [hillActionGapRatio_at_collapse q hq hr n hn hc]
    change 0 < (hillEnergyChi q hq hr n (hillRealLabels q hq hr (2*n-1) : ℂ)/(2 : ℝ)).re ∧
      (hillEnergyChi q hq hr n (hillRealLabels q hq hr (2*n-1) : ℂ)/(2 : ℝ)).im = 0
    rw [div_ofReal_re,div_ofReal_im,hχ.2,zero_div]
    exact ⟨div_pos hχ.1 (by norm_num),rfl⟩
  · have hδ : hillRealGapHalfLength q hq hr n ≠ 0 := by
      intro hd
      unfold hillRealGapHalfLength at hd
      exact hc (by linarith)
    have hδsq : 0 < (hillRealGapHalfLength q hq hr n)^2 := sq_pos_of_ne_zero hδ
    have hI := (hillRealGapIntegral_pos_iff q hq hr n hn).mpr
      (lt_of_le_of_ne (monotone_hillRealLabels q hq hr (by omega)) hc)
    have h := hillRealGapIntegral_eq_halfLength_sq_mul_ratio q hq hr n hn
    rw [← ofReal_pow] at h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp only [ofReal_re,mul_re,ofReal_im,zero_mul,sub_zero] at hre
    simp only [ofReal_im,mul_im,ofReal_re,zero_mul,add_zero] at him
    refine ⟨(mul_pos_iff_of_pos_left hδsq).mp (hre ▸ hI),?_⟩
    exact (mul_eq_zero.mp him.symm).resolve_left hδsq.ne'

end NLS.KdV
