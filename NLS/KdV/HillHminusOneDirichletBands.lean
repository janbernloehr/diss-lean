import NLS.KdV.HillHminusOneDirichletRealColumn
import NLS.KdV.HillHminusOneRealBands

/-! # Rough Dirichlet roots avoid every open canonical band

The actual terminal quasi-derivative at a Dirichlet zero is real and
is a Floquet multiplier of the original discriminant. Its determinant-one
quadratic forces the real trace square to be at least four. This excludes
every open band in the original H^-1 topology, without L2 labels as input.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory hiding extend
open scoped ComplexConjugate
open NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV NLS.FunctionalAnalysis
namespace NLS.KdV

theorem HillHminusMiuraChart.physicalMomentum_dirichlet_terminal_star_real
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (hr : IsRealPeriodOneHminusOne q) (x : ℝ) (hz : hillHminusDirichlet q x = 0) :
    conj (extend (C.physicalMomentum q x (0,1)) 1) = extend (C.physicalMomentum q x (0,1)) 1 := by
  let y := C.physicalPosition q x (0,1)
  have hy := C.physicalSolution_scalar_H1 q x (0,1)
  have hys : star y = y := C.physicalPosition_dirichlet_star_real q hq hr x
  have hy₀ : extend y 0 = 0 := l2QuasiHillPosition_initial _ _ _
  have hy₁ : extend y 1 = 0 := (C.hillHminusDirichlet_eq_physicalPosition q hq x).symm.trans hz
  let φ := unitIntervalAffineCurve 0 1
  have hφ := unitIntervalAffineCurve_H1 0 1
  have hφe := unitIntervalAffineCurve_endpoints 0 1
  have hφs : star φ = φ := unitIntervalAffineCurve_star_real 0 1
  have hend : extend y 1*extend φ 1 = extend y 0*extend φ 0 := by rw [hy₀,hy₁,zero_mul,zero_mul]
  have hf := hillHminusWeakForm_conj q hr y φ hy.1 hφ.1 hy.2.1 hφ.2 hend
  rw [hys,hφs] at hf
  have hm : conj (∫ s in (0 : ℝ)..1, extend y s*extend φ s) =
      ∫ s in (0 : ℝ)..1, extend y s*extend φ s := by
    rw [← intervalIntegral.intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro s _
    have hs := congrArg (fun f : Curve ℂ => extend f s) hys
    have ht := congrArg (fun f : Curve ℂ => extend f s) hφs
    change conj (extend y s) = extend y s at hs
    change conj (extend φ s) = extend φ s at ht
    change conj (NLS.LinearVolterra.extend y s*NLS.LinearVolterra.extend φ s) =
      NLS.LinearVolterra.extend y s*NLS.LinearVolterra.extend φ s
    rw [map_mul,hs,ht]
  have hg := C.intrinsic_green_identity q hq x (0,1) φ hφ.1 hφ.2 hend
  rw [hφe.1,hφe.2,mul_zero,mul_one,sub_zero] at hg
  have hc := congrArg (starRingEnd ℂ) hg
  change conj (hillHminusWeakForm q y φ) = _ at hc
  rw [hf,map_add,map_mul,conj_ofReal,hm] at hc
  linear_combination hg-hc

theorem HillHminusMiuraChart.dirichlet_terminal_multiplier
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (lambda : ℂ) (hz : hillHminusDirichlet q lambda = 0) :
    (extend (C.physicalMomentum q lambda (0,1)) 1)^2-
      hillHminusDiscriminant q lambda*extend (C.physicalMomentum q lambda (0,1)) 1+1 = 0 := by
  apply (C.hillHminusDiscriminant_multiplier_iff q hq lambda _).mpr
  refine ⟨(0,1),by simp,?_⟩
  let t : Icc (0 : ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  apply Prod.ext
  · have he := (C.hillHminusDirichlet_eq_physicalPosition q hq lambda).symm.trans hz
    change (extend (C.physicalSolution q lambda (0,1)) t.val).1 = 0 at he
    rw [extend_coe] at he
    simpa only [Prod.smul_fst,smul_eq_mul,mul_zero] using he
  · change (C.physicalSolution q lambda (0,1) t).2 = extend (C.physicalMomentum q lambda (0,1)) 1*1
    rw [mul_one]
    exact (extend_coe (C.physicalMomentum q lambda (0,1)) t).symm

theorem hillHminusDirichlet_zero_discriminant_sq_ge_four
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (x : ℝ)
    (hz : hillHminusDirichlet q x = 0) : 4 ≤ (hillHminusDiscriminant q x).re^2 := by
  let C := hillHminusMiuraChartAt q
  have hq : q ∈ C.domain := mem_hillHminusMiuraChartAt q
  let s := extend (C.physicalMomentum q x (0,1)) 1
  have hs := C.physicalMomentum_dirichlet_terminal_star_real q hq hr x hz
  have hsi : s.im = 0 := by
    have hi := congrArg Complex.im hs
    change -s.im = s.im at hi
    linarith
  have he := congrArg Complex.re (C.dirichlet_terminal_multiplier q hq x hz)
  change (s^2-hillHminusDiscriminant q x*s+1).re = 0 at he
  have heq : s.re^2-(hillHminusDiscriminant q x).re*s.re+1 = 0 := by
    simpa only [pow_two,mul_re,sub_re,add_re,hsi,mul_zero,zero_mul,sub_zero,one_re,zero_re] using he
  nlinarith [sq_nonneg ((hillHminusDiscriminant q x).re-2*s.re)]

theorem hillHminusDirichlet_ne_zero_on_open_band
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (x : ℝ)
    (hx : x ∈ Ioo (hillHminusRealLabels q hr (2*n)) (hillHminusRealLabels q hr (2*n+1))) :
    hillHminusDirichlet q x ≠ 0 := by
  intro hz
  have h := hillHminusDirichlet_zero_discriminant_sq_ge_four q hr x hz
  have hb := hillHminusDiscriminant_open_band_bounds q hr n x hx
  nlinarith [mul_pos (by linarith : 0 < (hillHminusDiscriminant q x).re+2)
    (by linarith : 0 < 2-(hillHminusDiscriminant q x).re)]

end NLS.KdV
