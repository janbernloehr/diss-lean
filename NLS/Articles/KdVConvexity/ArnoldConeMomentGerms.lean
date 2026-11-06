import NLS.Articles.KdVConvexity.LocalCubicPairCharts
import NLS.Articles.KdVConvexity.GlobalArnoldSurjectivity
import NLS.Articles.KdVConvexity.GlobalArnoldActionFibers

/-! # Actual source choices and local moment germs over every action point -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Articles.KdVConvexity
open NLS.KdV NLS.Articles.KdVKdV2Frequencies

def baseActionNormalization : BaseActionSpace ≃L[ℂ] Coeff 1 :=
  (WeightedCoeff.weightIsometry baseActionWeight 1).toContinuousLinearEquiv

def cubicContourScale (n : ℕ+) : ℂ := ((8*(n : ℝ)*Real.pi : ℝ) : ℂ)

def normalizedRawActionCoordinate (n : ℕ+) (b : Coeff 1) : ℂ :=
  (baseActionNormalization.symm b).val (actionIndexEquiv.symm n)

structure ArnoldConeSourceFamily (I : PeriodOneHminusOne → BaseActionSpace) where
  potential : Coeff.nonnegativeLocus 1 → PeriodOneHminusOne
  real : ∀ a, IsRealPeriodOneHminusOne (potential a)
  meanZero : ∀ a, (potential a).val 0 = 0
  action : ∀ a, I (potential a) = baseActionNormalization.symm a.val

theorem nonempty_ArnoldConeSourceFamily
    (ΩI : Set PeriodOneHminusOne) (hΩI : {q | IsRealPeriodOneHminusOne q} ⊆ ΩI)
    (I : PeriodOneHminusOne → BaseActionSpace) (hI : AnalyticOnNhd ℂ I ΩI)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n) = hillHminusRealGapContourMoment q hr n 0) :
    Nonempty (ArnoldConeSourceFamily I) := by
  classical
  have hlift (a : Coeff.nonnegativeLocus 1) :
      ∃ q : PeriodOneHminusOne, IsRealPeriodOneHminusOne q ∧ q.val 0 = 0 ∧
        I q = baseActionNormalization.symm a.val := by
    apply exists_source_of_nonnegative_Arnold_actions ΩI hΩI I hI hrec
    apply (WeightedCoeff.mem_nonnegativeLocus_iff baseActionWeight 1 _).mpr
    change baseActionNormalization (baseActionNormalization.symm a.val) ∈ Coeff.nonnegativeLocus 1
    rw [baseActionNormalization.apply_symm_apply]
    exact a.property
  choose q hqr hqm hqI using hlift
  exact ⟨⟨q,hqr,hqm,hqI⟩⟩

def ArnoldConeSourceFamily.scaledCubicMoment {I : PeriodOneHminusOne → BaseActionSpace}
    (S : ArnoldConeSourceFamily I) (n : ℕ+) (a : Coeff.nonnegativeLocus 1) : ℂ :=
  cubicContourScale n*hillHminusRealGapCubicContourMoment (S.potential a) (S.real a) n

theorem ArnoldConeSourceFamily.localCubicGerms
    (D : GlobalRoughAbelianForwardData)
    (ΩI : Set PeriodOneHminusOne) (hΩI : {q | IsRealPeriodOneHminusOne q} ⊆ ΩI)
    (I : PeriodOneHminusOne → BaseActionSpace) (hI : AnalyticOnNhd ℂ I ΩI)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n) = hillHminusRealGapContourMoment q hr n 0)
    (S : ArnoldConeSourceFamily I) (a : Coeff.nonnegativeLocus 1) :
    ∃ z : Coeff 2 × Coeff 2, ∃ U : Set (Coeff 2 × Coeff 2),
    ∃ f : ℕ+ → (Coeff 2 × Coeff 2) → ℂ,
      z ∈ Coeff.realPairLocus 2 ∧ quadraticActionsExponent (q := 1) z = a.val ∧
      IsOpen U ∧ z ∈ U ∧ (∀ n, AnalyticOnNhd ℂ (f n) U) ∧
      (∀ n u, u ∈ U → ∀ hr : u ∈ Coeff.realPairLocus 2,
        f n u = S.scaledCubicMoment n
          ⟨quadraticActionsExponent u,Coeff.quadraticActions_mem_nonnegativeLocus u hr⟩) ∧
      ∃ s : Finset ℕ+, ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ U, ∀ n ∉ s,
        ‖f n u‖ ≤ C*‖normalizedRawActionCoordinate n (quadraticActionsExponent u)‖^2 := by
  obtain ⟨z0,hzr,hza,U,Q,M,hU,hzU,_hQ,_hQ0,hM,hd,s,C,hC,hb⟩ :=
    exists_local_cubic_pair_chart D ΩI hΩI I hI hrec (S.potential a) (S.real a) (S.meanZero a)
  have hzact : quadraticActionsExponent (q := 1) z0 = a.val := by
    have hh : baseActionNormalization (normalizedCoordinateActions z0) = a.val := by
      rw [hza,S.action a,baseActionNormalization.apply_symm_apply]
    have hw : baseActionNormalization (normalizedCoordinateActions z0) = quadraticActionsExponent (q := 1) z0 :=
      WeightedCoeff.weight_actionsFromNormalizedCoordinates baseActionWeight z0
    exact hw.symm.trans hh
  let f : ℕ+ → (Coeff 2 × Coeff 2) → ℂ := fun n u => cubicContourScale n*M n u
  refine ⟨z0,U,f,hzr,hzact,hU,hzU,fun n => analyticOnNhd_const.mul (hM n),?_,s,C,hC,?_⟩
  · intro n u hu hur
    obtain ⟨hQu,hQm,hQI,hrecM⟩ := hd u hu hur
    let b : Coeff.nonnegativeLocus 1 :=
      ⟨quadraticActionsExponent u,Coeff.quadraticActions_mem_nonnegativeLocus u hur⟩
    have heI : I (Q u) = I (S.potential b) := hQI.trans (S.action b).symm
    have heD := hillHminusDiscriminant_eq_of_global_Arnold_eq I hrec
      (Q u) (S.potential b) hQu (S.real b) hQm (S.meanZero b) heI
    have heM := (hillHminusRealGapContourMoments_eq_of_discriminant_eq
      (Q u) (S.potential b) hQu (S.real b) heD n).2
    change cubicContourScale n*M n u = cubicContourScale n*
      hillHminusRealGapCubicContourMoment (S.potential b) (S.real b) n
    rw [hrecM n,heM]
  · intro u hu n hn
    exact hb u hu n hn

end NLS.Articles.KdVConvexity
