import NLS.Articles.KdVPseudomeasures.OriginalHillQuarticEnergyContour
import NLS.Articles.KdVPseudomeasures.OriginalHillFiniteGapCubicContour
import NLS.KdV.HillFiniteGapQuarticPhase

/-! On the SAME actual local patch, the normalized quartic contour
has the physical finite-gap energy value and the exact canonical-phase
bracket free-minus12 moment series. Identifying its derivative with the
physical energy derivative along action curves remains separate. -/
noncomputable section
open Set Metric Complex NLS.KdV NLS.Poisson NLS.WeightedCoeff NLS.ZakharovShabat
namespace NLS.Articles.KdVPseudomeasures

theorem hillH1_exists_quarticEnergyContour_eq_physical
    (P : HillProductEquationPatch) {W : Set (CoeffPair 2)}
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (q : RealSignedHilbert (signedStepOrder 0 1))
    (hf : hillIntegerSourceInclusion 1 q ∈ hillRealFiniteGapLocus)
    (hq : hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q) ∈ P.momentSource C) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      P.quarticEnergyContour W 0 R (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q))=
        periodOneKdVHamiltonian (signedOneRealToScalarDomain q) := by
  let Q := hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)
  have hr : IsRealPeriodOneHminusOne Q := (hillIntegerSourceInclusion 1 q).property
  let B := P.parent.parent.miuraBall.actionBall
  have hqB : Q ∈ B.source := (P.parent.subset (P.subset hq.1)).1
  let u : PeriodOneRealL2 := ⟨B.lift Q,B.lift_real Q hqB hr⟩
  have hi := B.image Q hqB
  have hfu := hillMiuraRealSource_finiteGap_of_hillRealFiniteGap (hillIntegerSourceInclusion 1 q) hf u B.shift hi
  obtain ⟨T,hT,hcontour⟩ := hillH1_finiteGap_Miura_weighted_quartic_energy_contour C q u B.shift hfu hi hq.2
  refine ⟨T,hT,fun R hR => ?_⟩
  have he := hcontour R hR 0
  simp only [Int.cast_zero,mul_zero,sub_zero] at he
  change P.weightedQuarticPrimitiveCircle W 0 R Q=_ at he
  rw [HillProductEquationPatch.quarticEnergyContour,he]
  have hc : (2*I/(Real.pi:ℂ))*(-(Real.pi:ℂ)*I/2)=1 := by
    field_simp
    rw [I_sq]
    ring
  rw [← mul_assoc,hc,one_mul]

theorem originalHill_exists_finiteGap_quartic_contour_phase_formula
    (q : RealSignedHilbert (signedStepOrder 0 1))
    (hf : hillIntegerSourceInclusion 1 q ∈ hillRealFiniteGapLocus) :
    ∃ P : HillProductEquationPatch, ∃ W : Set (CoeffPair 2),
      ∃ C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W,
        hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q) ∈ P.momentSource C ∧
        ∃ T : ℝ, 0 < T ∧
          (∀ R : ℝ, T ≤ R → P.quarticEnergyContour W 0 R
            (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q))=
              periodOneKdVHamiltonian (signedOneRealToScalarDomain q)) ∧
          ∀ n : ℕ+, hillHminusCanonicalGapSquare n
              (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)) ≠ 0 →
            ∃ A : HillPhysicalOnIndexPhaseChart P n,
              hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q) ∈ A.source ∧
              ∀ R : ℝ, T ≤ R → sphere (0:ℂ) R ⊆ sourceCanonicalRootDomain (by simp) (by norm_num)
                (P.sourcePsi (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q))) →
                hminusGardnerBracket (P.quarticEnergyContour W 0 R) A.completePhase
                  (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)) =
                    (2*(Real.pi:ℂ)*(n:ℤ))^3-12*P.centeredSecondMomentSeries W n
                      (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)) := by
  obtain ⟨P,W,C,hq,Tc,hTc,hcube⟩ := originalHill_exists_finiteGap_cubic_contour (hillIntegerSourceInclusion 1 q) hf
  obtain ⟨Te,hTe,henergy⟩ := hillH1_exists_quarticEnergyContour_eq_physical P C q hf hq
  let Q := hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)
  have hr : IsRealPeriodOneHminusOne Q := (hillIntegerSourceInclusion 1 q).property
  refine ⟨P,W,C,hq,max Tc Te,lt_of_lt_of_le hTc (le_max_left _ _),?_,?_⟩
  · intro R hR
    exact henergy R ((le_max_right _ _).trans hR)
  · intro n hn
    obtain ⟨A,_,hA⟩ := exists_hillPhysicalOnIndexPhaseChart P n Q
      (P.real_mem_physicalDirichletSource Q hq.1 hr) hr hn
    refine ⟨A,hA,fun R hR hcircle => ?_⟩
    rw [A.quarticEnergyContour_completePhase_Gardner_of_real C 0 R
      (hTc.le.trans ((le_max_left _ _).trans hR)) Q hA hq hr hcircle]
    exact hcube R ((le_max_left _ _).trans hR) hcircle n hn

end NLS.Articles.KdVPseudomeasures
