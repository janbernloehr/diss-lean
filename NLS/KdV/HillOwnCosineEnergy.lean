import NLS.KdV.HillSelectedCosineArc

noncomputable section
set_option autoImplicit false
open Set Complex Metric MeasureTheory NLS.ComplexAnalysis
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
  (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
  (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- The own-index primitive at the negative anchor carries its actual
NONZERO period. The positive anchor has the prescribed zero value. -/
theorem hillAbelianCosinePrimitive_own_arc_anchor (n : ℕ) (hn : 1≤n) (θ : ℝ) :
    hillAbelianCosinePrimitive q hq hr n hn n (realCosineArcAnchor θ:ℂ)=
      -(if θ<0 then 2*(Real.pi:ℂ) else 0) := by
  by_cases hneg : θ<0
  · rw [realCosineArcAnchor,if_pos hneg,if_pos hneg]
    have h := hillAbelianCosinePrimitive_real_add_int_period q hq hr n hn n hn Real.pi (-1)
    have he : Real.pi+(-1:ℤ) • (2*Real.pi)= -Real.pi := by
      simp only [zsmul_eq_mul,Int.cast_neg,Int.cast_one]
      ring
    simpa only [he,ite_true,mul_one,hillAbelianCosinePrimitive_pi,zero_add,Int.cast_neg,
      Int.cast_one,neg_one_mul] using h
  · rw [realCosineArcAnchor,if_neg hneg,if_neg hneg,neg_zero]
    exact hillAbelianCosinePrimitive_pi q hq hr n hn n

/-- The ORIGINAL own-index energy integral includes the actual 2*pi
anchor period for a negative selected angle. It is not silently zeroed. -/
theorem hillOwnCosineEnergyPath_integral (n : ℕ) (hn : 1≤n)
    (hgap : hillRealGapHalfLength q hq hr n≠0)
    (hw : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q)
      (hillDirichletEnergy q hq hr n hn)≠0) :
    let θ := hillDirichletSelectedRealAngle q hq hr n hn hgap
    let f := fun E => hillAbelianSelectedGlobalPsi q hq hr n hn E/
      prescribedSquareRoot (hillL2Radicand (SpectralWeight.one.toCoeff q))
        (hillDirichletSheetRoot (SpectralWeight.one.toCoeff q) (hillDirichletEnergy q hq hr n hn)) E
    CurveIntegrable (holomorphicOneForm f)
      (hillPhysicalCosineEnergyPath q hq hr n (realCosineArcAnchor θ) θ) ∧
      (∫ᶜ E in hillPhysicalCosineEnergyPath q hq hr n (realCosineArcAnchor θ) θ,
        holomorphicOneForm f E)=hillAbelianCosinePrimitive q hq hr n hn n (θ:ℂ)+
          (if θ<0 then 2*(Real.pi:ℂ) else 0) := by
  dsimp only
  let θ := hillDirichletSelectedRealAngle q hq hr n hn hgap
  let a := realCosineArcAnchor θ
  let D := hillAbelianCosineDifferential q hq hr n hn n
  let F := hillAbelianCosinePrimitive q hq hr n hn n
  let T := cosineGapPoint (hillRealGapCenter q hq hr n:ℂ) (hillRealGapHalfLength q hq hr n:ℂ)
  let f := fun E => hillAbelianSelectedGlobalPsi q hq hr n hn E/
    prescribedSquareRoot (hillL2Radicand (SpectralWeight.one.toCoeff q))
      (hillDirichletSheetRoot (SpectralWeight.one.toCoeff q) (hillDirichletEnergy q hq hr n hn)) E
  let γ := Path.segment (a:ℂ) (θ:ℂ)
  obtain ⟨S,hS,hθS,hreal,hSin,hline⟩ := exists_hillDirichlet_selected_regular_arc q hq hr n hn hgap hw
  have hspec := hillDirichletSelectedRealAngle_spec q hq hr n hn hgap
  have hpull := hillPrescribedDirichletDifferential_cosine_pullback q hq hr n n hn hn hgap
    S hS hreal hSin (θ:ℂ) hθS hspec.2.1 hspec.2.2 hw
  have hγ := contDiffOn_segment_extend (a:ℂ) (θ:ℂ)
  have hDc : ContinuousOn D {z : ℂ | z.im=0} := by
    intro z hz
    have he : z=(z.re:ℂ) := Complex.ext rfl (by simpa using hz)
    rw [he]
    exact (analyticAt_hillAbelianCosineDifferential_real q hq hr n hn n hn z.re).continuousAt.continuousWithinAt
  have hγreal (t : unitInterval) : γ t∈{z : ℂ | z.im=0} := by
    change (AffineMap.lineMap (a:ℂ) (θ:ℂ) (t:ℝ)).im=0
    simp [AffineMap.lineMap_apply_module',Complex.real_smul]
  have hInt : CurveIntegrable (holomorphicOneForm D) γ :=
    (hDc.smul continuousOn_const).curveIntegrable_of_contDiffOn hγ hγreal
  have hT : Continuous T := by
    change Continuous (fun e : ℂ => (hillRealGapCenter q hq hr n:ℂ)+
      (hillRealGapHalfLength q hq hr n:ℂ)*Complex.cos e)
    fun_prop
  have h := holomorphicPathPullback_integral_and_integrability f D T
    (fun e => -(hillRealGapHalfLength q hq hr n:ℂ)*Complex.sin e) hT γ hγ
    (fun t _ => hasDerivAt_cosineGapPoint _ _ _) (fun t ht => by
      apply hpull
      rw [Path.extend_apply _ (Ioo_subset_Icc_self ht)]
      exact hline t ht)
  have hhor : (∫ᶜ z in γ, holomorphicOneForm D z)=∫ x in a..θ, D (x:ℂ) := by
    change (∫ᶜ z in Path.segment (a:ℂ) (θ:ℂ), holomorphicOneForm D z)=_
    rw [curveIntegral_segment,← real_affine_complex_integral_eq_intervalIntegral D a θ]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [holomorphicOneForm_apply,AffineMap.lineMap_apply_module',Complex.real_smul]
    ring_nf
  have hi (b c : ℝ) : IntervalIntegrable (fun x : ℝ => D (x:ℂ)) volume b c :=
    (continuous_hillAbelianCosineDifferential_real q hq hr n hn n hn).intervalIntegrable b c
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hi Real.pi a) (hi a θ)
  rw [← hillAbelianCosinePrimitive_real_eq_intervalIntegral q hq hr n hn n a,
    ← hillAbelianCosinePrimitive_real_eq_intervalIntegral q hq hr n hn n θ,
    hillAbelianCosinePrimitive_own_arc_anchor q hq hr n hn θ] at hadd
  refine ⟨h.1.mpr hInt,h.2.trans (hhor.trans ?_)⟩
  linear_combination hadd

end NLS.KdV
