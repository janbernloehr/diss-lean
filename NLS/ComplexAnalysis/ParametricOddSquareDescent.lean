import NLS.ComplexAnalysis.OddSquareDescent
import NLS.ComplexAnalysis.EntireEvenSquareDescent
import NLS.ComplexAnalysis.ParametricDividedDifference

/-! # Joint odd square descent on an open parameter domain

The filled quotient by twice the frequency descends analytically in the
energy and Banach parameter, including the ramification point. Only the
parameter neighborhood on which the original family is analytic is used.
-/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem analyticOnNhd_local_even_square_descent
    (F : ℂ × A → ℂ) {U : Set A} (hU : IsOpen U)
    (hF : AnalyticOnNhd ℂ F (univ ×ˢ U))
    (heven : ∀ a ∈ U, ∀ z, F (-z,a) = F (z,a)) :
    AnalyticOnNhd ℂ (fun p : ℂ × A => F (Complex.sqrt p.1,p.2)) (univ ×ˢ U) := by
  intro p hp
  let R : ℝ := ‖p.1‖+1
  have hR : 0 < R := by dsimp [R]; positivity
  let V : Set (ℂ × A) := ball 0 (R^2) ×ˢ U
  have hV : IsOpen V := isOpen_ball.prod hU
  have hpV : p ∈ V := by
    refine ⟨?_,hp.2⟩
    simp only [mem_ball, dist_zero_right]
    dsimp [R]
    nlinarith [norm_nonneg p.1]
  let G : ℂ × (ℂ × A) → ℂ := fun x => F (x.1,x.2.2)
  have hG : AnalyticOnNhd ℂ G (closedBall 0 R ×ˢ V) := by
    intro x hx
    have ha : AnalyticAt ℂ (fun y : ℂ × (ℂ × A) => y.2.2) x :=
      analyticAt_snd.comp (f := fun y : ℂ × (ℂ × A) => y.2) analyticAt_snd
    exact (hF (x.1,x.2.2) ⟨mem_univ _,hx.2.2⟩).comp
      (f := fun y : ℂ × (ℂ × A) => (y.1,y.2.2)) (analyticAt_fst.prod ha)
  have he : ∀ a ∈ V, ∀ z ∈ ball (0 : ℂ) R, G (-z,a) = G (z,a) := by
    intro a ha z _
    exact heven a.2 ha.2 z
  have hb : ∀ a ∈ V, ‖Complex.sqrt a.1‖ < R := by
    intro a ha
    have hnorm : ‖Complex.sqrt a.1‖^2 = ‖a.1‖ := by rw [← norm_pow, sq_sqrt]
    have hball : ‖a.1‖ < R^2 := by
      simpa only [mem_ball, dist_zero_right] using ha.1
    nlinarith [norm_nonneg (Complex.sqrt a.1)]
  have hsq : AnalyticOnNhd ℂ (fun a : ℂ × A => (Complex.sqrt a.1)^2) V := by
    simp only [sq_sqrt]
    exact analyticOnNhd_fst
  exact analyticOnNhd_evenFamily_of_analytic_square G R hR V hV hG he
    (fun a => Complex.sqrt a.1) hb hsq p hpV

theorem analyticOnNhd_parametric_oddSquareDescent
    (F : ℂ × A → ℂ) {U : Set A} (hU : IsOpen U)
    (hF : AnalyticOnNhd ℂ F (univ ×ˢ U))
    (hodd : ∀ a ∈ U, ∀ z, F (-z,a) = -F (z,a)) :
    AnalyticOnNhd ℂ (fun p : ℂ × A => oddSquareDescent (fun z => F (z,p.2)) p.1)
      (univ ×ˢ U) := by
  let G : ℂ × A → ℂ := fun p => dslope (fun z => F (z,p.2)) 0 p.1 / 2
  have hG : AnalyticOnNhd ℂ G (univ ×ˢ U) := by
    have h := analyticOnNhd_parametricMovingDividedDifference F (fun _ => 0) hU hF
      analyticOnNhd_const
    intro p hp
    have he : G =ᶠ[𝓝 p] (fun t => parametricMovingDividedDifference F (fun _ => 0) t / 2) := by
      filter_upwards [(isOpen_univ.prod hU).mem_nhds hp] with t ht
      dsimp [G]
      rw [parametricMovingDividedDifference_eq_dslope F (fun _ => 0) hF
        analyticOnNhd_const t.1 t.2 ht.2]
    exact ((h p hp).div_const).congr he.symm
  have heven : ∀ a ∈ U, ∀ z, G (-z,a) = G (z,a) := by
    intro a ha z
    dsimp [G]
    rw [dslope_zero_even_of_odd _ (hodd a ha)]
  exact analyticOnNhd_local_even_square_descent G hU hG heven

end NLS.ComplexAnalysis
