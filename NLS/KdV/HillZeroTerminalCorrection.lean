import NLS.KdV.HillPhysicalCosinePath

noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory NLS.ComplexAnalysis
namespace NLS.KdV

/-- The ORIGINAL off-index scalar correction vanishes at a zero physical
terminal sheet, including open-gap endpoints and collapsed gaps. -/
theorem hillRegularAbelianCorrection_eq_zero_of_sheet_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (hkn : k≠n)
    (hw : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q)
      (hillDirichletEnergy q hq hr k hk)=0) :
    hillRegularAbelianCorrection q hq hr n hn k hk=0 := by
  by_cases hgap : hillRealGapHalfLength q hq hr k=0
  · exact hillRegularAbelianCorrection_closed q hq hr n hn k hk hgap
  let θ := hillDirichletSelectedRealAngle q hq hr k hk hgap
  have hspec := hillDirichletSelectedRealAngle_spec q hq hr k hk hgap
  have hs : Real.sin θ=0 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sin]
    change Complex.sin (θ:ℂ)=0
    rw [hspec.2.2,hillDirichletGapSine,hw,mul_zero,zero_div]
  have hF0 : hillAbelianCosinePrimitive q hq hr n hn k (0:ℂ)=0 := by
    rw [show (0:ℂ)=((0:ℝ):ℂ) by rfl,hillAbelianCosinePrimitive_real_eq_intervalIntegral,
      intervalIntegral.integral_symm,integral_hillAbelianCosineDifferential q hq hr n hn k hk,
      if_neg hkn,mul_zero,neg_zero]
    rfl
  have hFm : hillAbelianCosinePrimitive q hq hr n hn k ((-Real.pi:ℝ):ℂ)=0 := by
    simpa only [realCosineArcAnchor,if_pos (neg_lt_zero.mpr Real.pi_pos)] using
      hillAbelianCosinePrimitive_arc_anchor_zero q hq hr n k hn hk hkn (-Real.pi)
  rw [hillRegularAbelianCorrection,dif_neg hgap,hillRegularAbelianPrimitive,if_neg hkn,zero_mul,sub_zero]
  change hillAbelianCosinePrimitive q hq hr n hn k (θ:ℂ)=0
  by_cases hm : θ= -Real.pi
  · rw [hm]
    exact hFm
  by_cases hp : θ=Real.pi
  · rw [hp]
    exact hillAbelianCosinePrimitive_pi q hq hr n hn k
  have hθ0 : θ=0 := (Real.sin_eq_zero_iff_of_lt_of_lt
    (lt_of_le_of_ne hspec.1.1 (Ne.symm hm)) (lt_of_le_of_ne hspec.1.2 hp)).mp hs
  rw [hθ0,ofReal_zero]
  exact hF0

end NLS.KdV
