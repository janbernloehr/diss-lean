import NLS.Articles.KdVPseudomeasures.OriginalHillFrequencyMoments
import NLS.KdV.HillCubicPrimitiveMomentReduction

/-! Every original rough real source admits one complex neighborhood on
which all actual odd Hill moments vanish and the cubic contour has its
exact free term and -12 second-moment coefficient. -/
noncomputable section
open Set Complex NLS.KdV NLS.WeightedCoeff NLS.ZakharovShabat
namespace NLS.Articles.KdVPseudomeasures

theorem originalHill_exists_odd_moment_cancellation (q : HillRealMeanZeroSource) :
    ∃ P : HillProductEquationPatch, ∃ W : Set (CoeffPair 2),
      ∃ C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W,
        hillRealMeanZeroInclusion q ∈ P.momentSource C ∧ IsOpen (P.momentSource C) ∧
        ∀ a ∈ P.momentSource C, ∀ n m : ℕ+,
          (∀ l : ℕ, (∮ z in C((P.centers (m:ℤ):ℂ),P.radii (m:ℤ)),
            (sourceFullAbelianPrimitive (by simp) (by norm_num) W (m:ℤ) (z,P.sourcePsi a))^(2*l+1)*
              P.abelianFrequencyDifferential n (z,a))=0) ∧
          (4/(I*(Real.pi:ℂ))) *
            (∮ z in C((P.centers (m:ℤ):ℂ),P.radii (m:ℤ)),
              (sourceFullAbelianPrimitive (by simp) (by norm_num) W (m:ℤ) (z,P.sourcePsi a)-
                I*(Real.pi:ℂ)*(m:ℤ))^3*P.abelianFrequencyDifferential n (z,a)) =
            (2*(Real.pi:ℂ)*(n:ℤ))^3*(if m=n then 1 else 0)-
              12*(m:ℤ)*P.centeredMoment W n m 1 a := by
  obtain ⟨P,W,C,hq,hopen,_⟩ := originalHill_exists_frequency_moment_neighborhood q
  exact ⟨P,W,C,hq,hopen,fun a ha n m =>
    ⟨fun l => P.odd_centeredMoment_eq_zero C n m l a ha,
      P.normalized_cubic_primitive_contour C n m a ha⟩⟩

end NLS.Articles.KdVPseudomeasures
