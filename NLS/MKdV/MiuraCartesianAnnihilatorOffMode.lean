import NLS.MKdV.MiuraCartesianAnnihilatorModes

/-! # Off-mode cancellation without assuming cross-mode canonical brackets -/
noncomputable section
open Set Complex NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraCartesianJacobian_Gardner_observable_eval (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m n : ℕ) (hn : 1 ≤ n)
    (P : (ℂ × ℂ) →L[ℂ] ℂ) :
    miuraPositiveCartesianEval n (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)
      (l2GardnerDirection (miuraCartesianObservable m P) (scalarInclusion a))) =
      (l2GardnerBracket (miuraCartesianX n) (miuraCartesianObservable m P) (scalarInclusion a),
       l2GardnerBracket (miuraCartesianY n) (miuraCartesianObservable m P) (scalarInclusion a)) := by
  have har : ∀ j, scalarInclusion a j = conj (scalarInclusion a (-j)) := by
    intro j
    simpa only [scalarInclusion_apply] using ha j
  rw [miuraCartesianJacobian_eval _ har n hn]
  exact (l2GardnerBracket_pair (miuraL2CartesianCoordinates n) _ _
    (analyticAt_miuraL2CartesianCoordinates _ har n hn).differentiableAt).symm

theorem miuraCartesianJacobian_Gardner_observable_mean (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℕ) (hm : 1 ≤ m)
    (P : (ℂ × ℂ) →L[ℂ] ℂ) :
    (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)
      (l2GardnerDirection (miuraCartesianObservable m P) (scalarInclusion a))).2 = 0 := by
  have har : ∀ j, scalarInclusion a j = conj (scalarInclusion a (-j)) := by
    intro j
    simpa only [scalarInclusion_apply] using ha j
  rw [miuraCartesianJacobian_mean _ har,l2GardnerDirection,
    l2SpatialDerivative_apply _ (miuraCartesianObservable_Gardner_memlp a ha m hm P)]
  simp

theorem miuraAction_CartesianObservable_bracket_of_ne (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : m ≠ n) (P : (ℂ × ℂ) →L[ℂ] ℂ) :
    l2GardnerBracket (miuraL2Action n) (miuraCartesianObservable m P) (scalarInclusion a) = 0 := by
  have hother : l2GardnerBracket (miuraCartesianObservable m P) (miuraL2Action n) (scalarInclusion a) = 0 := by
    rw [l2GardnerBracket,fderiv_miuraCartesianObservable a ha m hm P]
    change P ((fderiv ℂ (miuraL2CartesianCoordinates m) (scalarInclusion a))
      (l2GardnerDirection (miuraL2Action n) (scalarInclusion a))) = 0
    rw [fderiv_miuraCartesian_apply_Gardner_action a ha m n hm hn,if_neg hmn,map_zero]
  have h := l2GardnerBracket_antisymm_of_memlp (miuraL2Action n) (miuraCartesianObservable m P)
    (scalarInclusion a) (miuraActionGardner_memlp a ha n hn)
    (miuraCartesianObservable_Gardner_memlp a ha m hm P)
  rwa [hother,neg_zero] at h

theorem miuraCartesian_annihilator_off_mode (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : m ≠ n) (P : (ℂ × ℂ) →L[ℂ] ℂ)
    (L : MiuraPositiveCartesianTarget →L[ℂ] ℂ)
    (hL : L.comp (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)) = 0) :
    L (miuraCartesianInsert n (miuraPositiveCartesianEval n
      (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)
        (l2GardnerDirection (miuraCartesianObservable m P) (scalarInclusion a))))) = 0 := by
  rw [miuraCartesianCotangent_insert L n hn]
  by_cases hzero : miuraMKdVAction a ha n = 0
  · obtain ⟨hx,hy⟩ := miuraCartesian_annihilator_closed_coefficients a ha n hn hzero L hL
    rw [hx,hy,zero_mul,zero_mul,add_zero]
  · let x := miuraCartesianX n (scalarInclusion a)
    let y := miuraCartesianY n (scalarInclusion a)
    let z := miuraPositiveCartesianEval n (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)
      (l2GardnerDirection (miuraCartesianObservable m P) (scalarInclusion a)))
    let α := miuraCartesianCotangentX L n
    let β := miuraCartesianCotangentY L n
    have har : ∀ j, scalarInclusion a j = conj (scalarInclusion a (-j)) := by
      intro j
      simpa only [scalarInclusion_apply] using ha j
    have hdot : x*z.1+y*z.2 = 0 := by
      have h := congrArg (fun Q : Coeff 2 →L[ℂ] ℂ => Q
        (l2GardnerDirection (miuraCartesianObservable m P) (scalarInclusion a)))
        (fderiv_miuraL2Action_cartesian_radius (scalarInclusion a) har n hn)
      change l2GardnerBracket (miuraL2Action n) (miuraCartesianObservable m P) (scalarInclusion a) = _ at h
      rw [miuraAction_CartesianObservable_bracket_of_ne a ha m n hm hn hmn P] at h
      change x*z.1+y*z.2 = 0
      dsimp only [z]
      rw [miuraCartesianJacobian_Gardner_observable_eval a ha m n hn P]
      exact h.symm
    have hr : α*y-β*x = 0 := miuraCartesian_annihilator_radial a ha n hn L hL
    have hs : x^2+y^2 ≠ 0 := by
      have h := miuraL2CartesianCoordinates_physical_H1_radius a ha n hn
      change x^2+y^2 = 2*miuraMKdVAction a ha n at h
      rw [h]
      exact mul_ne_zero (by norm_num) hzero
    have hc : (x^2+y^2)*(α*z.1+β*z.2) = 0 := by
      calc
        _ = (α*x+β*y)*(x*z.1+y*z.2)+(α*y-β*x)*(y*z.1-x*z.2) := by ring
        _ = 0 := by rw [hdot,hr]; ring
    exact (mul_eq_zero.mp hc).resolve_left hs

end NLS.MKdV
