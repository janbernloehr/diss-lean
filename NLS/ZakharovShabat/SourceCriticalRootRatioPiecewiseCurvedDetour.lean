import NLS.ZakharovShabat.SourceCriticalRootRatioHalfPlanePrimitive
import NLS.ZakharovShabat.SourceCriticalRootRatioLowerEndpointDoglegHeight
import NLS.ZakharovShabat.SourceCriticalRootRatioArbitraryHalfPlanePathLimit

/-!
# Exact-zero endpoint detours with regular curved tails

A singular endpoint path may first leave each branch point vertically,
then follow several smooth pieces in an open half-plane. A primitive
on that half-plane telescopes the regular pieces, so their total
integral agrees with the horizontal crossing of a zero-integral dogleg.
-/

noncomputable section
open Set Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An endpoint-to-endpoint path with vertical singular prefixes and
three regular pieces that may have corners at their joins. -/
def sourcePiecewiseGapDetourPath
    {l r a b c d : ℂ} (verticalLeft : Path l a) (left : Path a b)
    (crossing : Path b c) (right : Path d c)
    (verticalRight : Path r d) : Path l r :=
  ((((verticalLeft.trans left).trans crossing).trans right.symm).trans
    verticalRight.symm)

/-- Any three `C¹` upper-half-plane pieces may replace the straight
crossing of a sufficiently short upper dogleg, with exact zero
integral even when the pieces meet at corners. -/
theorem exists_sourceCriticalRootRatio_upperPiecewiseDetour_integrable_and_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let ω := NLS.ComplexAnalysis.holomorphicOneForm
      (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z)
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ Ioo (0:ℝ) ε,
      ∀ {a b : ℂ}
        (left : Path (l+(y:ℂ)*Complex.I) a)
        (crossing : Path a b)
        (right : Path (r+(y:ℂ)*Complex.I) b),
        ContDiffOn ℝ 1 left.extend (Icc 0 1) →
        ContDiffOn ℝ 1 crossing.extend (Icc 0 1) →
        ContDiffOn ℝ 1 right.extend (Icc 0 1) →
        (∀ u : I, 0 < (left u).im) →
        (∀ u : I, 0 < (crossing u).im) →
        (∀ u : I, 0 < (right u).im) →
        let path := sourcePiecewiseGapDetourPath
          (Path.segment l (l+(y:ℂ)*Complex.I)) left crossing right
          (Path.segment r (r+(y:ℂ)*Complex.I))
        CurveIntegrable ω path ∧ (∫ᶜ z in path, ω z) = 0 := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let ω := NLS.ComplexAnalysis.holomorphicOneForm
    (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z)
  obtain ⟨ε₁,hε₁,hvertical⟩ :=
    exists_sourceCriticalRootRatio_upperEndpointSegment_curveIntegrable
      hp hp1 ψ hreal n hopen
  obtain ⟨ε₂,hε₂,hdogleg⟩ :=
    exists_sourceCriticalRootRatio_upperDogleg_curveIntegrable_integral_eq
      hp hp1 ψ hreal n hopen
  obtain ⟨ε₃,hε₃,hzero⟩ :=
    exists_sourceCriticalRootRatio_upperDogleg_curveIntegral_eq_zero
      hp hp1 ψ hreal n hopen
  refine ⟨min ε₁ (min ε₂ ε₃),lt_min hε₁ (lt_min hε₂ hε₃),?_⟩
  intro y hy a b left crossing right hleft hcross hright huLeft huCross huRight
  have hy₁ : y ∈ Ioo (0:ℝ) ε₁ :=
    ⟨hy.1,hy.2.trans_le (min_le_left ε₁ (min ε₂ ε₃))⟩
  have hy₂ : y ∈ Ioo (0:ℝ) ε₂ :=
    ⟨hy.1,hy.2.trans_le ((min_le_right ε₁ (min ε₂ ε₃)).trans
      (min_le_left ε₂ ε₃))⟩
  have hy₃ : y ∈ Ioo (0:ℝ) ε₃ :=
    ⟨hy.1,hy.2.trans_le ((min_le_right ε₁ (min ε₂ ε₃)).trans
      (min_le_right ε₂ ε₃))⟩
  let vL := Path.segment l (l+(y:ℂ)*Complex.I)
  let vR := Path.segment r (r+(y:ℂ)*Complex.I)
  let mid := Path.segment (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I)
  have hvL : CurveIntegrable ω vL := by
    have h := hvertical (-1) (by simp) y hy₁
    rw [sourceCanonicalRootGapPoint_neg_one_eq_left hp hp1 ψ n] at h
    exact h
  have hvR : CurveIntegrable ω vR := by
    have h := hvertical 1 (by simp) y hy₁
    rw [sourceCanonicalRootGapPoint_one_eq_right hp hp1 ψ n] at h
    exact h
  have hlInt : CurveIntegrable ω left :=
    sourceCriticalRootRatio_curveIntegrable_of_smoothPath hp hp1 ψ left
      hleft (by
        rintro z ⟨u,rfl⟩
        exact sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal _
          (ne_of_gt (huLeft u)))
  have hcInt : CurveIntegrable ω crossing :=
    sourceCriticalRootRatio_curveIntegrable_of_smoothPath hp hp1 ψ crossing
      hcross (by
        rintro z ⟨u,rfl⟩
        exact sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal _
          (ne_of_gt (huCross u)))
  have hrInt : CurveIntegrable ω right :=
    sourceCriticalRootRatio_curveIntegrable_of_smoothPath hp hp1 ψ right
      hright (by
        rintro z ⟨u,rfl⟩
        exact sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal _
          (ne_of_gt (huRight u)))
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n
  have huMid (u : I) : 0 < (mid u).im := by
    have hseg : mid u ∈ segment ℝ (l+(y:ℂ)*Complex.I)
        (r+(y:ℂ)*Complex.I) := by
      rw [← Path.range_segment]
      exact ⟨u,rfl⟩
    rw [sourceHorizontalSegment_im_eq l r hl hr y _ hseg]
    exact hy.1
  have hreg := sourceCriticalRootRatio_upperPiecewise_pathIntegral_eq
    hp hp1 ψ hreal left crossing right mid hleft hcross hright
    ((sourceSegmentPath_contDiffOn_two _ _).of_le (by norm_num))
    huLeft huCross huRight huMid
  have hdoglegEq := (hdogleg y hy₂).2
  have hzeroEq := hzero y hy₃
  change CurveIntegrable ω
    ((((vL.trans left).trans crossing).trans right.symm).trans vR.symm) ∧
    (∫ᶜ z in ((((vL.trans left).trans crossing).trans right.symm).trans vR.symm),
      ω z) = 0
  constructor
  · exact (((hvL.trans hlInt).trans hcInt).trans hrInt.symm).trans hvR.symm
  · rw [curveIntegral_trans (((hvL.trans hlInt).trans hcInt).trans hrInt.symm) hvR.symm,
      curveIntegral_trans ((hvL.trans hlInt).trans hcInt) hrInt.symm,
      curveIntegral_trans (hvL.trans hlInt) hcInt,
      curveIntegral_trans hvL hlInt, curveIntegral_symm, curveIntegral_symm]
    have hmidEq := sourceCriticalRootRatio_horizontalSegment_curveIntegral_eq hp hp1 ψ n y
    rw [← hmidEq] at hdoglegEq
    calc
      _ = (∫ᶜ z in vL, ω z) +
          ((∫ᶜ z in left, ω z) + (∫ᶜ z in crossing, ω z) -
            (∫ᶜ z in right, ω z)) - (∫ᶜ z in vR, ω z) := by ring
      _ = (∫ᶜ z in vL, ω z) + (∫ᶜ z in mid, ω z) -
            (∫ᶜ z in vR, ω z) := by rw [hreg]
      _ = 0 := by rw [← hdoglegEq]; exact hzeroEq

/-- Any three `C¹` lower-half-plane pieces may replace the straight
crossing of a sufficiently short lower dogleg, with exact zero
integral even when the pieces meet at corners. -/
theorem exists_sourceCriticalRootRatio_lowerPiecewiseDetour_integrable_and_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let ω := NLS.ComplexAnalysis.holomorphicOneForm
      (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z)
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ Ioo (0:ℝ) ε,
      ∀ {a b : ℂ}
        (left : Path (l+((-y:ℝ):ℂ)*Complex.I) a)
        (crossing : Path a b)
        (right : Path (r+((-y:ℝ):ℂ)*Complex.I) b),
        ContDiffOn ℝ 1 left.extend (Icc 0 1) →
        ContDiffOn ℝ 1 crossing.extend (Icc 0 1) →
        ContDiffOn ℝ 1 right.extend (Icc 0 1) →
        (∀ u : I, (left u).im < 0) →
        (∀ u : I, (crossing u).im < 0) →
        (∀ u : I, (right u).im < 0) →
        let path := sourcePiecewiseGapDetourPath
          (Path.segment l (l+((-y:ℝ):ℂ)*Complex.I)) left crossing right
          (Path.segment r (r+((-y:ℝ):ℂ)*Complex.I))
        CurveIntegrable ω path ∧ (∫ᶜ z in path, ω z) = 0 := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let ω := NLS.ComplexAnalysis.holomorphicOneForm
    (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z)
  obtain ⟨ε₁,hε₁,hvertical⟩ :=
    exists_sourceCriticalRootRatio_lowerEndpointSegment_curveIntegrable
      hp hp1 ψ hreal n hopen
  obtain ⟨ε₂,hε₂,hdogleg⟩ :=
    exists_sourceCriticalRootRatio_lowerDogleg_curveIntegrable_integral_eq
      hp hp1 ψ hreal n hopen
  obtain ⟨ε₃,hε₃,hzero⟩ :=
    exists_sourceCriticalRootRatio_lowerDogleg_curveIntegral_eq_zero
      hp hp1 ψ hreal n hopen
  refine ⟨min ε₁ (min ε₂ ε₃),lt_min hε₁ (lt_min hε₂ hε₃),?_⟩
  intro y hy a b left crossing right hleft hcross hright hlLeft hlCross hlRight
  have hy₁ : y ∈ Ioo (0:ℝ) ε₁ :=
    ⟨hy.1,hy.2.trans_le (min_le_left ε₁ (min ε₂ ε₃))⟩
  have hy₂ : y ∈ Ioo (0:ℝ) ε₂ :=
    ⟨hy.1,hy.2.trans_le ((min_le_right ε₁ (min ε₂ ε₃)).trans
      (min_le_left ε₂ ε₃))⟩
  have hy₃ : y ∈ Ioo (0:ℝ) ε₃ :=
    ⟨hy.1,hy.2.trans_le ((min_le_right ε₁ (min ε₂ ε₃)).trans
      (min_le_right ε₂ ε₃))⟩
  let vL := Path.segment l (l+((-y:ℝ):ℂ)*Complex.I)
  let vR := Path.segment r (r+((-y:ℝ):ℂ)*Complex.I)
  let mid := Path.segment (l+((-y:ℝ):ℂ)*Complex.I) (r+((-y:ℝ):ℂ)*Complex.I)
  have hvL : CurveIntegrable ω vL := by
    have h := hvertical (-1) (by simp) y hy₁
    rw [sourceCanonicalRootGapPoint_neg_one_eq_left hp hp1 ψ n] at h
    exact h
  have hvR : CurveIntegrable ω vR := by
    have h := hvertical 1 (by simp) y hy₁
    rw [sourceCanonicalRootGapPoint_one_eq_right hp hp1 ψ n] at h
    exact h
  have hlInt : CurveIntegrable ω left :=
    sourceCriticalRootRatio_curveIntegrable_of_smoothPath hp hp1 ψ left
      hleft (by
        rintro z ⟨u,rfl⟩
        exact sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal _
          (ne_of_lt (hlLeft u)))
  have hcInt : CurveIntegrable ω crossing :=
    sourceCriticalRootRatio_curveIntegrable_of_smoothPath hp hp1 ψ crossing
      hcross (by
        rintro z ⟨u,rfl⟩
        exact sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal _
          (ne_of_lt (hlCross u)))
  have hrInt : CurveIntegrable ω right :=
    sourceCriticalRootRatio_curveIntegrable_of_smoothPath hp hp1 ψ right
      hright (by
        rintro z ⟨u,rfl⟩
        exact sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal _
          (ne_of_lt (hlRight u)))
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n
  have hlMid (u : I) : (mid u).im < 0 := by
    have hseg : mid u ∈ segment ℝ (l+((-y:ℝ):ℂ)*Complex.I)
        (r+((-y:ℝ):ℂ)*Complex.I) := by
      rw [← Path.range_segment]
      exact ⟨u,rfl⟩
    rw [sourceHorizontalSegment_im_eq l r hl hr (-y) _ hseg]
    exact neg_lt_zero.mpr hy.1
  have hreg := sourceCriticalRootRatio_lowerPiecewise_pathIntegral_eq
    hp hp1 ψ hreal left crossing right mid hleft hcross hright
    ((sourceSegmentPath_contDiffOn_two _ _).of_le (by norm_num))
    hlLeft hlCross hlRight hlMid
  have hdoglegEq := (hdogleg y hy₂).2
  have hzeroEq := hzero y hy₃
  change CurveIntegrable ω
    ((((vL.trans left).trans crossing).trans right.symm).trans vR.symm) ∧
    (∫ᶜ z in ((((vL.trans left).trans crossing).trans right.symm).trans vR.symm),
      ω z) = 0
  constructor
  · exact (((hvL.trans hlInt).trans hcInt).trans hrInt.symm).trans hvR.symm
  · rw [curveIntegral_trans (((hvL.trans hlInt).trans hcInt).trans hrInt.symm) hvR.symm,
      curveIntegral_trans ((hvL.trans hlInt).trans hcInt) hrInt.symm,
      curveIntegral_trans (hvL.trans hlInt) hcInt,
      curveIntegral_trans hvL hlInt, curveIntegral_symm, curveIntegral_symm]
    have hmidEq := sourceCriticalRootRatio_horizontalSegment_curveIntegral_eq hp hp1 ψ n (-y)
    rw [← hmidEq] at hdoglegEq
    calc
      _ = (∫ᶜ z in vL, ω z) +
          ((∫ᶜ z in left, ω z) + (∫ᶜ z in crossing, ω z) -
            (∫ᶜ z in right, ω z)) - (∫ᶜ z in vR, ω z) := by ring
      _ = (∫ᶜ z in vL, ω z) + (∫ᶜ z in mid, ω z) -
            (∫ᶜ z in vR, ω z) := by rw [hreg]
      _ = 0 := by rw [← hdoglegEq]; exact hzeroEq

end NLS.ZakharovShabat
