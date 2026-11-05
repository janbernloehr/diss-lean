import NLS.SequenceSpaces.PeriodOneMiuraConjugation
import NLS.ComplexAnalysis.ConjugateAnalytic

/-! # Holomorphic signed completion of positive weighted coordinates -/
noncomputable section
open scoped ComplexConjugate
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.WeightedCoeff

def signedHolomorphicCompletion (w : Weight) (Y : Coeff 2 → WeightedCoeff w 2) (u : Coeff 2) : WeightedCoeff w 2 :=
  (weightIsometry w 2).symm ((weightIsometry w 2) (Y u)+Coeff.reflection
    (star ((weightIsometry w 2) (Y (periodOneL2Conjugation u)))))

theorem signedHolomorphicCompletion_apply (w : Weight) (hw : ∀ j, w (-j) = w j)
    (Y : Coeff 2 → WeightedCoeff w 2) (u : Coeff 2) (j : ℤ) :
    (signedHolomorphicCompletion w Y u).val j = (Y u).val j +
      conj ((Y (periodOneL2Conjugation u)).val (-j)) := by
  change ((w j : ℂ)*(Y u).val j+conj ((w (-j) : ℂ)*(Y (periodOneL2Conjugation u)).val (-j)))/(w j : ℂ) = _
  rw [hw,map_mul,Complex.conj_ofReal]
  field_simp [w.complex_ne_zero]

theorem signedHolomorphicCompletion_analytic_bound (w : Weight) (Y : Coeff 2 → WeightedCoeff w 2)
    (η K : ℝ)
    (hYa : AnalyticOnNhd ℂ Y (ball (0 : Coeff 2) η)) (hY0 : Y 0 = 0)
    (hb : ∀ u ∈ ball (0 : Coeff 2) η, ‖Y u‖ ≤ K*(‖u‖+‖u‖^2)) :
    AnalyticOnNhd ℂ (signedHolomorphicCompletion w Y) (ball (0 : Coeff 2) η) ∧
      signedHolomorphicCompletion w Y 0 = 0 ∧
      ∀ u ∈ ball (0 : Coeff 2) η, ‖signedHolomorphicCompletion w Y u‖ ≤ 2*K*(‖u‖+‖u‖^2) := by
  let G := fun u => (weightIsometry w 2) (Y u)
  let L := (Coeff.reflection (p := 2)).toContinuousLinearEquiv.toContinuousLinearMap
  have hJ (u : Coeff 2) (hu : u ∈ ball 0 η) : periodOneL2Conjugation u ∈ ball (0 : Coeff 2) η := by
    rwa [mem_ball_zero_iff,norm_periodOneL2Conjugation,← mem_ball_zero_iff]
  have hGa : AnalyticOnNhd ℂ G (ball (0 : Coeff 2) η) := by
    intro u hu
    exact (((weightIsometry w 2).toContinuousLinearEquiv.toContinuousLinearMap).analyticAt _).comp (hYa u hu)
  refine ⟨?_,?_,?_⟩
  · intro u hu
    have hs := analyticAt_star_star (hGa (periodOneL2Conjugation u) (hJ u hu))
    simp only [periodOneL2Conjugation,star_star] at hs
    have hn := (L.analyticAt _).comp (f := (star ∘ G ∘ star) ∘ Coeff.reflection)
      (hs.comp (f := Coeff.reflection) (L.analyticAt u))
    exact (((weightIsometry w 2).symm.toContinuousLinearEquiv.toContinuousLinearMap).analyticAt _).comp
      ((hGa u hu).add hn)
  · have hJ0 : periodOneL2Conjugation 0 = 0 := by ext j; simp
    simp only [signedHolomorphicCompletion,hY0,hJ0,map_zero,star_zero,add_zero]
  · intro u hu
    change ‖(weightIsometry w 2).symm (G u+Coeff.reflection (star (G (periodOneL2Conjugation u))))‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    apply (norm_add_le _ _).trans
    rw [Coeff.reflection.norm_map,norm_star]
    change ‖Y u‖+‖Y (periodOneL2Conjugation u)‖ ≤ _
    have h := add_le_add (hb u hu) (hb _ (hJ u hu))
    rw [norm_periodOneL2Conjugation] at h
    exact h.trans_eq (by ring)

end NLS.WeightedCoeff
