import NLS.Articles.KdVPseudomeasures.OriginalHillOddMomentCancellation
import NLS.Articles.KdVPseudomeasures.OriginalHillFiniteGapMiura
import NLS.KdV.HillFiniteGapCubicContour

/-! The exact outer cubic contour formula at every original finite-gap
rough source and every open original selected gap. This is a contour
identity; its identification with the physical frequency is still separate. -/
noncomputable section
open Set Metric Complex NLS.KdV NLS.WeightedCoeff NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

theorem originalHill_exists_finiteGap_cubic_contour (q : HillRealMeanZeroSource)
    (hf : q ∈ hillRealFiniteGapLocus) :
    ∃ P : HillProductEquationPatch, ∃ W : Set (CoeffPair 2),
      ∃ C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W,
        hillRealMeanZeroInclusion q ∈ P.momentSource C ∧
        ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
          sphere (0:ℂ) R ⊆ sourceCanonicalRootDomain (by simp) (by norm_num)
            (P.sourcePsi (hillRealMeanZeroInclusion q)) →
          ∀ n : ℕ+, hillHminusCanonicalGapSquare n (hillRealMeanZeroInclusion q) ≠ 0 →
          (2/(I*(Real.pi:ℂ))) *
            (∮ z in C(0,R),
              (sourceFullAbelianPrimitive (by simp) (by norm_num) W 0
                (z,P.sourcePsi (hillRealMeanZeroInclusion q)))^3*
              P.abelianFrequencyDifferential n (z,hillRealMeanZeroInclusion q)) =
            (2*(Real.pi:ℂ)*(n:ℤ))^3-12*P.centeredSecondMomentSeries W n (hillRealMeanZeroInclusion q) := by
  obtain ⟨P,W,C,hq,_,_⟩ := originalHill_exists_frequency_moment_neighborhood q
  have hr : IsRealPeriodOneHminusOne (hillRealMeanZeroInclusion q) := by intro k; exact q.property k
  let B := P.parent.parent.miuraBall.actionBall
  have hqB := (P.parent.subset (P.subset hq.1)).1
  let u : PeriodOneRealL2 := ⟨B.lift (hillRealMeanZeroInclusion q),B.lift_real _ hqB hr⟩
  have hi := B.image (hillRealMeanZeroInclusion q) hqB
  have hfu := hillMiuraRealSource_finiteGap_of_hillRealFiniteGap q hf u B.shift hi
  obtain ⟨T,hT,hformula⟩ := P.exists_finiteGap_cubic_contour_moment_formula C
    (hillRealMeanZeroInclusion q) hq hr hfu
  refine ⟨P,W,C,hq,T,hT,fun R hR hcircle n hn => hformula R hR hcircle n ?_⟩
  intro hzero
  change hillMiuraDiracRight u.val (n:ℤ)-hillMiuraDiracLeft u.val (n:ℤ)=0 at hzero
  have hs := hillHminusCanonicalGapSquare_eq_Miura_of_real (hillRealMeanZeroInclusion q) hr
    u B.shift hi (B.outside _ hqB) n
  apply hn
  rw [hs]
  rw [hzero,zero_mul,zero_pow (by norm_num : (2:ℕ)≠0)]

end NLS.Articles.KdVPseudomeasures
