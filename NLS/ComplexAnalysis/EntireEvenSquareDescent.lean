import NLS.ComplexAnalysis.ParametricEvenSquareDescent
import Mathlib.Analysis.RCLike.Sqrt

/-! # Entire even families descend analytically to the squared coordinate

The root selection need not be continuous. Fixed Cauchy circles give joint
Banach analyticity in the energy and the parameters, including at zero.
-/

noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem complex_sqrt_sq (z : ℂ) : (Complex.sqrt z)^2 = z := by
  have h := Complex.cpow_nat_inv_pow z (Nat.succ_ne_zero 1)
  norm_num at h
  simpa only [Complex.sqrt, one_div] using h

theorem analyticOnNhd_entire_even_square_descent
    {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]
    (F : ℂ × A → ℂ) (hF : AnalyticOnNhd ℂ F univ)
    (heven : ∀ a z, F (-z,a) = F (z,a)) (d : ℂ → ℂ) (hd : ∀ z, (d z)^2 = z) :
    AnalyticOnNhd ℂ (fun p : ℂ × A => F (d p.1,p.2)) univ := by
  intro p _
  let R : ℝ := ‖p.1‖+1
  have hR : 0 < R := by dsimp [R]; positivity
  let V : Set (ℂ × A) := ball 0 (R^2) ×ˢ univ
  have hV : IsOpen V := isOpen_ball.prod isOpen_univ
  have hp : p ∈ V := by
    refine ⟨?_, mem_univ _⟩
    simp only [mem_ball, dist_zero_right]
    dsimp [R]
    nlinarith [norm_nonneg p.1]
  let G : ℂ × (ℂ × A) → ℂ := fun x => F (x.1,x.2.2)
  have hG : AnalyticOnNhd ℂ G univ := by
    intro x _
    have hq : AnalyticAt ℂ (fun y : ℂ × (ℂ × A) => y.2.2) x :=
      analyticAt_snd.comp (f := fun y : ℂ × (ℂ × A) => y.2) analyticAt_snd
    exact (hF (x.1,x.2.2) (mem_univ _)).comp
      (f := fun y : ℂ × (ℂ × A) => (y.1,y.2.2)) (analyticAt_fst.prod hq)
  have he : ∀ a ∈ V, ∀ z ∈ ball (0 : ℂ) R, G (-z,a) = G (z,a) := by
    intro a _ z _
    exact heven a.2 z
  have hb : ∀ a ∈ V, ‖d a.1‖ < R := by
    intro a ha
    have hnorm : ‖d a.1‖^2 = ‖a.1‖ := by rw [← norm_pow, hd]
    have hball : ‖a.1‖ < R^2 := by simpa only [mem_ball, dist_zero_right] using ha.1
    nlinarith [norm_nonneg (d a.1)]
  have hsq : AnalyticOnNhd ℂ (fun a : ℂ × A => (d a.1)^2) V := by
    simp only [hd]
    exact analyticOnNhd_fst
  exact analyticOnNhd_evenFamily_of_analytic_square G R hR V hV
    (hG.mono (subset_univ _)) he (fun a => d a.1) hb hsq p hp

end NLS.ComplexAnalysis
