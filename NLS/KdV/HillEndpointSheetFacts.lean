import NLS.KdV.HillRealGapSigns
import NLS.KdV.HillDirichletSheetRoot

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The actual Hill discriminant derivative is real on the physical axis. -/
theorem hillL2Discriminant_deriv_real (p : Coeff 2) (hr : IsRealHillPotential p) (x : ℝ) :
    (deriv (hillL2Discriminant p) (x : ℂ)).im=0 := by
  have hd := (analyticOnNhd_hillL2Discriminant p (x : ℂ) (mem_univ _)).differentiableAt.hasDerivAt
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hd.comp_ofReal
  have he : (fun y : ℝ => (hillL2Discriminant p (y : ℂ)).im)=(fun _ => (0 : ℝ)) :=
    funext (hillL2Discriminant_real p hr)
  change HasDerivAt (fun y : ℝ => (hillL2Discriminant p (y : ℂ)).im)
    (deriv (hillL2Discriminant p) (x : ℂ)).im x at hi
  rw [he] at hi
  exact hi.unique (hasDerivAt_const x (0 : ℝ))

/-- The actual full Dirichlet sheet is real at every physical terminal. -/
theorem hillDirichletSheetRoot_at_dirichlet_real
    (q : RealPeriodOneHillPotential) (k : ℕ) (hk : 1≤k) :
    (hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 k hk)).im=0 := by
  rw [hillDirichletSheetRoot_at_dirichlet_eq_norming]
  exact ofReal_im _

/-- The actual trace derivative cannot vanish at either endpoint of an
open physical Hill gap, by its checked simple radicand zero order. -/
theorem hillL2Discriminant_deriv_ne_zero_open_gap_endpoints
    (q : RealPeriodOneHillPotential) (k : ℕ) (hk : 1≤k)
    (hopen : hillRealLabels q.val q.property.1 q.property.2 (2*k-1)≠
      hillRealLabels q.val q.property.1 q.property.2 (2*k)) :
    deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q.val))
      (hillRealLabels q.val q.property.1 q.property.2 (2*k-1) : ℂ)≠0 ∧
    deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q.val))
      (hillRealLabels q.val q.property.1 q.property.2 (2*k) : ℂ)≠0 := by
  have horders := hillRealLabels_open_gap_orders q.val q.property.1 q.property.2 k hk hopen
  have hne (x : ℂ) (hx : analyticOrderNatAt (hillL2Radicand (SpectralWeight.one.toCoeff q.val)) x=1) :
      deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q.val)) x≠0 := by
    have hR := deriv_ne_zero_of_analyticOrderNatAt_eq_one
      (hillL2Radicand (SpectralWeight.one.toCoeff q.val)) x
      (analyticOnNhd_hillL2Radicand _ x (mem_univ _)) hx
    intro hz
    have hd := (analyticOnNhd_hillL2Discriminant (SpectralWeight.one.toCoeff q.val) x (mem_univ _)).differentiableAt.hasDerivAt
    have hzero : HasDerivAt (hillL2Radicand (SpectralWeight.one.toCoeff q.val)) 0 x := by
      convert! (hd.mul hd).sub_const 4 using 1
      · funext y
        simp only [hillL2Radicand,pow_two,Pi.mul_apply]
      · rw [hz]
        ring
    exact hR hzero.deriv
  exact ⟨hne _ horders.1,hne _ horders.2⟩

/-- Vanishing of the full actual sheet is exactly vanishing of the physical
log-norming coordinate, with the original sign normalization. -/
theorem hillDirichletSheetRoot_eq_zero_iff_logMultiplier_eq_zero
    (q : RealPeriodOneHillPotential) (k : ℕ) (hk : 1≤k) :
    hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 k hk)=0 ↔
      hillDirichletLogMultiplier q.val q.property.1 q.property.2 k hk=0 := by
  rw [hillDirichletSheetRoot_at_dirichlet_eq_norming,ofReal_eq_zero]
  have hfac : (-1 : ℝ)^k*2≠0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) (by norm_num)
  constructor
  · intro hz
    have hs : Real.sinh (hillDirichletLogMultiplier q.val q.property.1 q.property.2 k hk)=0 :=
      (mul_eq_zero.mp hz).resolve_left hfac
    exact Real.sinh_injective (by simpa only [Real.sinh_zero] using hs)
  · intro hz
    rw [hz,Real.sinh_zero,mul_zero]

end NLS.KdV
