import NLS.KdV.HillPrescribedCosineSheet
import NLS.ComplexAnalysis.RealCosineArc
import NLS.ComplexAnalysis.HolomorphicPathPullback
import NLS.ComplexAnalysis.HorizontalSegmentIntegral

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory NLS.ComplexAnalysis
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
  (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
  (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- The actual scalar energy path obtained from a signed real angle
segment. Its initial angle is chosen at the appropriate left endpoint. -/
def hillPhysicalCosineEnergyPath (k : ℕ) (a θ : ℝ) :
    Path (cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) (a:ℂ))
      (cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) (θ:ℂ)) :=
  (Path.segment (a:ℂ) (θ:ℂ)).map (show Continuous
    (cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k)) by
      change Continuous (fun e : ℂ => (hillRealGapCenter q hq hr k:ℂ)+
        (hillRealGapHalfLength q hq hr k:ℂ)*Complex.cos e)
      fun_prop)

theorem hillDirichletGapSine_ne_zero_of_regular_sheet (k : ℕ) (hk : 1≤k)
    (hgap : hillRealGapHalfLength q hq hr k≠0)
    (hw : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q)
      (hillDirichletEnergy q hq hr k hk)≠0) :
    hillDirichletGapSine q hq hr k hk≠0 := by
  have hspec := hillDirichletSelectedRealAngle_spec q hq hr k hk hgap
  have hfill := hillCosineGapPoint_mem_filledDomain q hq hr k hk
    (hillDirichletSelectedRealAngle q hq hr k hk hgap)
  rw [hspec.2.1] at hfill
  exact div_ne_zero (mul_ne_zero I_ne_zero hw)
    (mul_ne_zero (ofReal_ne_zero.mpr hgap)
      (hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr k hk _ hfill))

theorem hillAbelianCosinePrimitive_arc_anchor_zero (n k : ℕ) (hn : 1≤n) (hk : 1≤k)
    (hkn : k≠n) (θ : ℝ) :
    hillAbelianCosinePrimitive q hq hr n hn k (realCosineArcAnchor θ:ℂ)=0 := by
  by_cases hneg : θ<0
  · rw [realCosineArcAnchor,if_pos hneg]
    have h := hillAbelianCosinePrimitive_real_add_int_period q hq hr n hn k hk Real.pi (-1)
    have he : Real.pi+(-1:ℤ) • (2*Real.pi)= -Real.pi := by
      simp only [zsmul_eq_mul,Int.cast_neg,Int.cast_one]
      ring
    simpa only [he,if_neg hkn,mul_zero,add_zero,hillAbelianCosinePrimitive_pi] using h
  · rw [realCosineArcAnchor,if_neg hneg]
    exact hillAbelianCosinePrimitive_pi q hq hr n hn k

/-- The ORIGINAL scalar off-index terminal correction is the actual
integral of its fixed normalized numerator over the terminal-prescribed
physical energy sheet, along its actual signed cosine energy path.
No substitute phase, path integral hypothesis or primitive is supplied. -/
theorem hillRegularAbelianCorrection_eq_prescribed_cosine_path (n k : ℕ)
    (hn : 1≤n) (hk : 1≤k) (hkn : k≠n)
    (hgap : hillRealGapHalfLength q hq hr k≠0)
    (hw : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q)
      (hillDirichletEnergy q hq hr k hk)≠0) :
    let θ := hillDirichletSelectedRealAngle q hq hr k hk hgap
    let f := fun E : ℂ => hillAbelianSelectedGlobalPsi q hq hr n hn E/
      prescribedSquareRoot (hillL2Radicand (SpectralWeight.one.toCoeff q))
        (hillDirichletSheetRoot (SpectralWeight.one.toCoeff q) (hillDirichletEnergy q hq hr k hk)) E
    CurveIntegrable (holomorphicOneForm f)
      (hillPhysicalCosineEnergyPath q hq hr k (realCosineArcAnchor θ) θ) ∧
      (∫ᶜ E in hillPhysicalCosineEnergyPath q hq hr k (realCosineArcAnchor θ) θ,
        holomorphicOneForm f E)=hillRegularAbelianCorrection q hq hr n hn k hk := by
  dsimp only
  let θ := hillDirichletSelectedRealAngle q hq hr k hk hgap
  let a := realCosineArcAnchor θ
  let D := hillAbelianCosineDifferential q hq hr n hn k
  let F := hillAbelianCosinePrimitive q hq hr n hn k
  let T := cosineGapPoint (hillRealGapCenter q hq hr k:ℂ) (hillRealGapHalfLength q hq hr k:ℂ)
  let f := fun E : ℂ => hillAbelianSelectedGlobalPsi q hq hr n hn E/
    prescribedSquareRoot (hillL2Radicand (SpectralWeight.one.toCoeff q))
      (hillDirichletSheetRoot (SpectralWeight.one.toCoeff q) (hillDirichletEnergy q hq hr k hk)) E
  let γ := Path.segment (a:ℂ) (θ:ℂ)
  have hspec := hillDirichletSelectedRealAngle_spec q hq hr k hk hgap
  have hs : Complex.sin (θ:ℂ)≠0 := by
    rw [hspec.2.2]
    exact hillDirichletGapSine_ne_zero_of_regular_sheet q hq hr k hk hgap hw
  have hθ0 : θ≠0 := by intro h; apply hs; rw [h,ofReal_zero,Complex.sin_zero]
  have hθp : θ≠Real.pi := by intro h; apply hs; rw [h,Complex.sin_pi]
  have hθm : θ≠-Real.pi := by
    intro h
    apply hs
    rw [h,ofReal_neg,Complex.sin_neg,Complex.sin_pi,neg_zero]
  have hθ : θ∈Ioo (-Real.pi) Real.pi :=
    ⟨lt_of_le_of_ne hspec.1.1 (Ne.symm hθm),lt_of_le_of_ne hspec.1.2 hθp⟩
  obtain ⟨S,hS,heS,hreal,hSin,hγS⟩ := exists_regular_real_cosine_arc θ hθ hθ0
  have hpull := hillPrescribedDirichletDifferential_cosine_pullback q hq hr n k hn hk hgap
    S hS hreal hSin (θ:ℂ) heS hspec.2.1 hspec.2.2 hw
  have hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1) := contDiffOn_segment_extend _ _
  have hDc : ContinuousOn D {z : ℂ | z.im=0} := by
    intro z hz
    have he : z=(z.re:ℂ) := Complex.ext rfl (by simpa using hz)
    rw [he]
    exact (analyticAt_hillAbelianCosineDifferential_real q hq hr n hn k hk z.re).continuousAt.continuousWithinAt
  have hγreal : ∀ t : unitInterval, γ t∈{z : ℂ | z.im=0} := by
    intro t
    change (AffineMap.lineMap (a:ℂ) (θ:ℂ) (t:ℝ)).im=0
    simp [AffineMap.lineMap_apply_module',Complex.real_smul]
  have hInt : CurveIntegrable (holomorphicOneForm D) γ :=
    (hDc.smul continuousOn_const).curveIntegrable_of_contDiffOn hγ hγreal
  have hT : Continuous T := by
    change Continuous (fun e : ℂ => (hillRealGapCenter q hq hr k:ℂ)+
      (hillRealGapHalfLength q hq hr k:ℂ)*Complex.cos e)
    fun_prop
  have h := holomorphicPathPullback_integral_and_integrability f D T
    (fun e => -(hillRealGapHalfLength q hq hr k:ℂ)*Complex.sin e) hT γ hγ
    (fun t _ => hasDerivAt_cosineGapPoint _ _ _) (fun t ht => hpull _ (hγS t ht))
  have hF : (∫ᶜ z in γ, holomorphicOneForm D z)=F (θ:ℂ) := by
    have hhor : (∫ᶜ z in γ, holomorphicOneForm D z)=∫ x in a..θ, D (x:ℂ) := by
      change (∫ᶜ z in Path.segment (a:ℂ) (θ:ℂ), holomorphicOneForm D z)=_
      rw [curveIntegral_segment,← real_affine_complex_integral_eq_intervalIntegral D a θ]
      apply intervalIntegral.integral_congr
      intro t _
      simp only [holomorphicOneForm_apply,AffineMap.lineMap_apply_module',Complex.real_smul]
      ring_nf
    rw [hhor]
    have hi (b c : ℝ) : IntervalIntegrable (fun x : ℝ => D (x:ℂ)) volume b c :=
      (continuous_hillAbelianCosineDifferential_real q hq hr n hn k hk).intervalIntegrable b c
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hi Real.pi a) (hi a θ)
    rw [← hillAbelianCosinePrimitive_real_eq_intervalIntegral q hq hr n hn k a,
      ← hillAbelianCosinePrimitive_real_eq_intervalIntegral q hq hr n hn k θ,
      hillAbelianCosinePrimitive_arc_anchor_zero q hq hr n k hn hk hkn θ] at hadd
    simpa only [zero_add] using hadd
  have hvalue : F (θ:ℂ)=hillRegularAbelianCorrection q hq hr n hn k hk := by
    rw [hillRegularAbelianCorrection_eq_of_terminal q hq hr n k hn hk hgap θ hspec.2.1 hspec.2.2,
      hillRegularAbelianPrimitive,if_neg hkn,zero_mul,sub_zero]
  exact ⟨h.1.mpr hInt,h.2.trans (hF.trans hvalue)⟩

end NLS.KdV
