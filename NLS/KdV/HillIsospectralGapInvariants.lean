import NLS.ComplexAnalysis.LogarithmicMomentSourceStationarity
import NLS.ComplexAnalysis.SquareRootSourceStationarity
import NLS.KdV.HillOpenGapHalfLength

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.LinearVolterra NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



theorem hillL2Radicand_isospectral_fderiv (p h : Coeff 2)
    (hiso : ∀ E : ℂ, (fderiv ℂ (fun b : Coeff 2 => hillL2Discriminant b E) p) h=0) (E : ℂ) :
    (fderiv ℂ (fun b : Coeff 2 => hillL2Radicand b E) p) h=0 := by
  have hT : AnalyticAt ℂ (fun b : Coeff 2 => hillL2Discriminant b E) p :=
    (analyticOnNhd_hillL2Discriminant_joint (E,p) (mem_univ _)).comp
      (f := fun b : Coeff 2 => (E,b)) (analyticAt_const.prod analyticAt_id)
  have hd := (hT.differentiableAt.hasFDerivAt.mul hT.differentiableAt.hasFDerivAt).sub_const 4
  simp only [hillL2Radicand,pow_two]
  change HasFDerivAt (𝕜 := ℂ) (fun b : Coeff 2 => hillL2Discriminant b E*hillL2Discriminant b E-4) _ p at hd
  rw [hd.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,hiso E,mul_zero,add_zero]

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- Both symmetric gap invariants have zero genuine source variation
at every original real gap, with no gap-opening assumption. -/
theorem hillLocalGapSymmetricData_isospectral_fderiv (k : ℕ) (hk : 1≤k) (h : Coeff 2)
    (hiso : ∀ E : ℂ, (fderiv ℂ (fun b : Coeff 2 => hillL2Discriminant b E) (SpectralWeight.one.toCoeff q)) h=0) :
    (fderiv ℂ (hillLocalGapMidpoint q hq hr k) (SpectralWeight.one.toCoeff q)) h=0 ∧
      (fderiv ℂ (hillLocalGapSquare q hq hr k) (SpectralWeight.one.toCoeff q)) h=0 := by
  let F : ℂ × Coeff 2 → ℂ := fun t => hillL2Radicand t.2 t.1
  let c : ℂ := hillRealGapCenter q hq hr k
  let r := hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k
  have hrad := hillL2Radicand_isospectral_fderiv _ h hiso
  have hb (E : ℂ) (hE : E∈sphere c r) : F (E,SpectralWeight.one.toCoeff q)≠0 :=
    hillL2Radicand_ne_zero_on_realCutDomain q hq hr E (hillRealGapContour_sphere_subset q hq hr k hk hE)
  have hradius : 0≤r := add_nonneg (hillRealGapContour_geometry q hq hr k hk).1
    (hillRealGapContour_geometry q hq hr k hk).2.1.le
  have h1 := logarithmicCircleMoment_source_fderiv_eq_zero F analyticOnNhd_hillL2Radicand_joint c r hradius 1
    (SpectralWeight.one.toCoeff q) h hb hrad
  have h2 := logarithmicCircleMoment_source_fderiv_eq_zero F analyticOnNhd_hillL2Radicand_joint c r hradius 2
    (SpectralWeight.one.toCoeff q) h hb hrad
  constructor
  · change (fderiv ℂ (fun p : Coeff 2 => logarithmicCircleMoment F c r 1 p/2) (SpectralWeight.one.toCoeff q)) h=0
    have hd := h1.1.hasFDerivAt.mul_const (2 : ℂ)⁻¹
    rw [show (fun p : Coeff 2 => logarithmicCircleMoment F c r 1 p/2)=
      (fun p => logarithmicCircleMoment F c r 1 p*(2 : ℂ)⁻¹) from rfl,hd.fderiv]
    simp only [smul_apply,smul_eq_mul,h1.2,mul_zero]
  · have hd := (h2.1.hasFDerivAt.const_mul (2 : ℂ)).fun_sub (h1.1.hasFDerivAt.pow 2)
    change HasFDerivAt (𝕜 := ℂ) (hillLocalGapSquare q hq hr k) _ (SpectralWeight.one.toCoeff q) at hd
    rw [hd.fderiv]
    simp only [sub_apply,smul_apply,smul_eq_mul,h1.2,h2.2,mul_zero,sub_zero]

theorem hillGapHalfLength_isospectral_fderiv (k : ℕ) (hk : 1≤k)
    (d : Coeff 2 → ℂ) (hd : AnalyticAt ℂ d (SpectralWeight.one.toCoeff q))
    (hd0 : d (SpectralWeight.one.toCoeff q)≠0)
    (heq : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q), d p^2=hillLocalGapSquare q hq hr k p/4)
    (h : Coeff 2)
    (hiso : ∀ E : ℂ, (fderiv ℂ (fun b : Coeff 2 => hillL2Discriminant b E) (SpectralWeight.one.toCoeff q)) h=0) :
    (fderiv ℂ d (SpectralWeight.one.toCoeff q)) h=0 := by
  obtain ⟨U,_,hpU,_,hS,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood q hq hr k hk
  have hF : AnalyticAt ℂ (fun p : Coeff 2 => hillLocalGapSquare q hq hr k p/4) (SpectralWeight.one.toCoeff q) :=
    (hS _ hpU).div_const
  apply squareRoot_source_fderiv_eq_zero d _ _ h hd hF heq hd0
  have ht := ((hS _ hpU).differentiableAt.hasFDerivAt.mul_const (4 : ℂ)⁻¹).fderiv
  change fderiv ℂ (fun p : Coeff 2 => hillLocalGapSquare q hq hr k p/4) _=_ at ht
  rw [ht]
  simp only [smul_apply,smul_eq_mul,(hillLocalGapSymmetricData_isospectral_fderiv q hq hr k hk h hiso).2,mul_zero]

end NLS.KdV
