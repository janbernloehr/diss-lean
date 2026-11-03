import NLS.KdV.HillHminusOneWeakSpectrumReality
import NLS.MKdV.L2QuasiHillDirichletDerivative
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Analytic.Order

/-! # Every real H^-1 Dirichlet zero has analytic multiplicity one

Conjugation preserves the intrinsic weak Dirichlet problem at a real
potential and its necessarily real energy. Geometric simplicity then
relates the conjugate normalized column to that same column. Its scalar
square integral cannot vanish, because the physical L2 mass is nonzero.
The exact two-energy derivative identity proves nonvanishing of the
original entire characteristic derivative, with all chart shifts retained.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open scoped ComplexConjugate
open NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV NLS.FunctionalAnalysis
namespace NLS.KdV

theorem intrinsic_dirichlet_star (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (lambda : ℂ) (y : Curve ℂ) (hy : IsIntrinsicHillDirichletEigenfunction q lambda y) :
    IsIntrinsicHillDirichletEigenfunction q lambda (star y) := by
  have him := intrinsic_dirichlet_energy_im_zero q hr lambda y hy
  have hreal : conj lambda = lambda := by apply Complex.ext <;> simp [him]
  obtain ⟨hyn,hyAC,hy₂,hy₀,hy₁,hw⟩ := hy
  refine ⟨star_ne_zero.mpr hyn,absolutelyContinuous_curve_star y hyAC,memLp_deriv_curve_star y hy₂,
    ?_,?_,?_⟩
  · change conj (extend y 0) = 0
    rw [hy₀,map_zero]
  · change conj (extend y 1) = 0
    rw [hy₁,map_zero]
  intro φ hφ hφ₂ hφ₀ hφ₁
  have hφs := absolutelyContinuous_curve_star φ hφ
  have hφs₂ := memLp_deriv_curve_star φ hφ₂
  have he := congrArg (starRingEnd ℂ) (hw (star φ) hφs hφs₂
    (by change conj (extend φ 0) = 0; rw [hφ₀,map_zero])
    (by change conj (extend φ 1) = 0; rw [hφ₁,map_zero]))
  have hcon := hillHminusWeakForm_conj q hr y (star φ) hyAC hφs hy₂ hφs₂
    (by change extend y 1*conj (extend φ 1) = extend y 0*conj (extend φ 0)
        rw [hφ₀,hφ₁,map_zero,mul_zero,mul_zero])
  rw [star_star] at hcon
  rw [hcon,map_mul,hreal,← intervalIntegral.intervalIntegral_conj] at he
  convert he using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  change conj (NLS.LinearVolterra.extend y s)*NLS.LinearVolterra.extend φ s =
    conj (NLS.LinearVolterra.extend y s*conj (NLS.LinearVolterra.extend φ s))
  rw [map_mul,conj_conj]

theorem HillHminusMiuraChart.dirichlet_column_square_integral_ne_zero
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (hr : IsRealPeriodOneHminusOne q) (lambda : ℂ) (hz : hillHminusDirichlet q lambda = 0) :
    (∫ s in (0 : ℝ)..1, extend (C.physicalPosition q lambda (0,1)) s*
      extend (C.physicalPosition q lambda (0,1)) s) ≠ 0 := by
  let y := C.physicalPosition q lambda (0,1)
  have hy := C.physicalPosition_intrinsic_dirichlet_of_zero q hq lambda hz
  obtain ⟨c,_,he⟩ := C.intrinsic_dirichlet_eq_scalar_column q hq lambda (star y)
    (intrinsic_dirichlet_star q hr lambda y hy)
  have hm : (∫ s in (0 : ℝ)..1, extend y s*conj (extend y s)) =
      c*(∫ s in (0 : ℝ)..1, extend y s*extend y s) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    have hs := congrArg (fun f : Curve ℂ => extend f s) he
    change conj (extend y s) = c*extend y s at hs
    change extend y s*conj (extend y s) = c*(extend y s*extend y s)
    rw [hs]
    ring
  intro hzI
  have hmass := integral_curve_mul_conj_ne_zero y hy.1
  apply hmass
  rw [hm,hzI,mul_zero]

/-- Exact original-energy derivative identity in every shifted-Miura
chart, for arbitrary complex potentials and complex Dirichlet roots. -/
theorem HillHminusMiuraChart.hillHminusDirichlet_derivative_identity
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (lambda : ℂ) (hz : hillHminusDirichlet q lambda = 0) :
    extend (C.physicalMomentum q lambda (0,1)) 1*deriv (hillHminusDirichlet q) lambda =
      ∫ s in (0 : ℝ)..1, extend (C.physicalPosition q lambda (0,1)) s*
        extend (C.physicalPosition q lambda (0,1)) s := by
  have he : hillHminusDirichlet q = fun mu : ℂ =>
      extend (l2QuasiHillPosition (C.physicalProfile q) (mu+C.energyShift) (0,1)) 1 :=
    funext (fun mu => C.hillHminusDirichlet_eq_physicalPosition q hq mu)
  have hzero : extend (l2QuasiHillPosition (C.physicalProfile q) (lambda+C.energyShift) (0,1)) 1 = 0 :=
    (C.hillHminusDirichlet_eq_physicalPosition q hq lambda).symm.trans hz
  rw [he,deriv_comp_add_const (fun mu : ℂ =>
    extend (l2QuasiHillPosition (C.physicalProfile q) mu (0,1)) 1) C.energyShift lambda]
  exact l2QuasiHillDirichlet_derivative_identity _ _ hzero

theorem hillHminusDirichlet_deriv_ne_zero_at_real_root (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (lambda : ℂ) (hz : hillHminusDirichlet q lambda = 0) :
    deriv (hillHminusDirichlet q) lambda ≠ 0 := by
  let C := hillHminusMiuraChartAt q
  have hq : q ∈ C.domain := mem_hillHminusMiuraChartAt q
  have he := C.hillHminusDirichlet_derivative_identity q hq lambda hz
  intro hd
  rw [hd,mul_zero] at he
  exact C.dirichlet_column_square_integral_ne_zero q hq hr lambda hz he.symm

/-- The actual original Dirichlet entire function, not an auxiliary
determinant, has a simple analytic zero at every one of its real-input roots. -/
theorem hillHminusDirichlet_analyticOrderAt_eq_one (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (lambda : ℂ) (hz : hillHminusDirichlet q lambda = 0) :
    analyticOrderAt (hillHminusDirichlet q) lambda = 1 := by
  have ha : AnalyticAt ℂ (hillHminusDirichlet q) lambda :=
    (analyticOnNhd_hillHminusDirichlet_joint (lambda,q) (mem_univ _)).comp
      (f := fun mu : ℂ => (mu,q)) (analyticAt_id.prod analyticAt_const)
  exact ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz
    (hillHminusDirichlet_deriv_ne_zero_at_real_root q hr lambda hz)

end NLS.KdV
