import NLS.KdV.HillDirichletSheetRoot

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



private theorem signed_sinh_of_product (c d s g : ℂ)
    (hprod : c*d=1) (hs : s^2=1) (he : Complex.exp g=s*d) :
    d-c=s*2*Complex.sinh g := by
  have hinv : Complex.exp (-g)=s*c := by
    apply mul_left_cancel₀ (Complex.exp_ne_zero g)
    rw [←Complex.exp_add,add_neg_cancel,Complex.exp_zero,he]
    calc
      _ = s^2*(c*d) := by rw [hs,hprod,mul_one]
      _ = _ := by ring
  rw [Complex.sinh,he,hinv]
  calc
    d-c = s^2*d-s^2*c := by rw [hs,one_mul,one_mul]
    _ = _ := by ring

/-- At any complex Dirichlet characteristic zero, every logarithmic branch of
the signed slope gives the genuine terminal sheet through the hyperbolic formula. -/
theorem hillDirichletSheetRoot_eq_signed_sinh_of_exp
    (p : Coeff 2) (E G : ℂ) (n : ℕ)
    (hz : hillL2DirichletCharacteristic p E=0)
    (he : Complex.exp G=(-1 : ℂ)^n*hillL2DirichletSlope p E) :
    hillDirichletSheetRoot p E=(-1 : ℂ)^n*2*Complex.sinh G := by
  let z := Complex.sqrt E
  let t : Icc (0 : ℝ) 1 := ⟨1,by norm_num⟩
  let c := (hillL2FrequencyStateCurve p z (1,0) t).1
  let d := hillL2DirichletSlope p E
  have hb : (hillL2FrequencyStateCurve p z (0,1) t).1=0 := hz
  have hw := hillL2FrequencyStateCurve_wronskian p z t
  rw [hb,zero_mul,sub_zero] at hw
  have hprod : c*d=1 := hw
  have htrace : c+d=hillL2Discriminant p E := by
    have ht := hillL2FrequencyStateCurve_trace p z
    rw [←hillL2Discriminant_sq,complex_sqrt_sq E] at ht
    exact ht
  have hs : ((-1 : ℂ)^n)^2=1 := by
    rw [←pow_mul,Nat.mul_comm n 2,pow_mul]
    norm_num
  have h := signed_sinh_of_product c d ((-1 : ℂ)^n) G hprod hs he
  rw [hillDirichletSheetRoot,←htrace]
  change 2*d-(c+d)=_
  linear_combination h

/-- The literal signed-slope logarithm on any actual analytic Dirichlet branch
is analytic at a real physical source and has its actual physical norming value. -/
theorem hillDirichletLogBranch_analytic_base
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n)
    (a : Coeff 2 → ℂ) (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val))
    (ha0 : a (SpectralWeight.one.toCoeff q.val)=(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ)) :
    AnalyticAt ℂ (fun p => Complex.log ((-1 : ℂ)^n*hillL2DirichletSlope p (a p)))
      (SpectralWeight.one.toCoeff q.val) ∧
    Complex.log ((-1 : ℂ)^n*hillL2DirichletSlope (SpectralWeight.one.toCoeff q.val)
      (a (SpectralWeight.one.toCoeff q.val)))=
      (hillDirichletLogMultiplier q.val q.property.1 q.property.2 n hn : ℂ) := by
  let M : Coeff 2 → ℂ := fun p => (-1 : ℂ)^n*hillL2DirichletSlope p (a p)
  have hM : AnalyticAt ℂ M (SpectralWeight.one.toCoeff q.val) :=
    analyticAt_const.mul ((analyticOnNhd_hillL2DirichletSlope_joint
      (a (SpectralWeight.one.toCoeff q.val),SpectralWeight.one.toCoeff q.val) (mem_univ _)).comp
        (f := fun p : Coeff 2 => (a p,p)) (ha.prod analyticAt_id))
  have hM0 : M (SpectralWeight.one.toCoeff q.val)=
      (hillDirichletMultiplier q.val q.property.1 q.property.2 n hn : ℂ) := by
    dsimp only [M]
    rw [ha0,←hillDirichletMultiplier_ofReal]
  have hslit : M (SpectralWeight.one.toCoeff q.val)∈Complex.slitPlane := by
    rw [hM0]
    exact Complex.ofReal_mem_slitPlane.mpr (hillDirichletMultiplier_pos q.val q.property.1 q.property.2 n hn)
  refine ⟨hM.clog hslit,?_⟩
  change Complex.log (M (SpectralWeight.one.toCoeff q.val))=_
  rw [hM0,←Complex.ofReal_log (hillDirichletMultiplier_pos q.val q.property.1 q.property.2 n hn).le]
  rfl

end NLS.KdV
