import NLS.ComplexAnalysis.ParametricEvenSquareDescent
import NLS.ComplexAnalysis.LocalAnalyticSquareRoot

/-! # Analyticity descends through a squared input

If a scalar function becomes analytic after squaring its input, it is
analytic at the squared base point. At zero the Cauchy transform of the
even pullback avoids selecting an analytic square root.
-/
noncomputable section
open Set Metric Filter Topology
namespace NLS.ComplexAnalysis

/-- Analyticity of a square pullback descends even at the ramification point. -/
theorem analyticAt_of_comp_sq (g : ℂ → ℂ) (w : ℂ)
    (h : AnalyticAt ℂ (fun v => g (v^2)) w) : AnalyticAt ℂ g (w^2) := by
  by_cases hw : w = 0
  · subst w
    obtain ⟨R,hR,hball⟩ := nhds_basis_closedBall.mem_iff.mp h.eventually_analyticAt
    let F : ℂ × ℂ → ℂ := fun x => g (x.1^2)
    have hF : AnalyticOnNhd ℂ F (closedBall 0 R ×ˢ (univ : Set ℂ)) := by
      intro x hx
      exact (hball hx.1).comp (f := fun x : ℂ × ℂ => x.1) analyticAt_fst
    have hroot (a : ℂ) : (Complex.sqrt a)^2 = a := by
      have he := Complex.cpow_nat_inv_pow a (Nat.succ_ne_zero 1)
      norm_num at he
      simpa only [Complex.sqrt,one_div] using he
    have ha := analyticOnNhd_evenFamily_of_analytic_square F R hR
      (ball (0 : ℂ) (R^2)) isOpen_ball
      (hF.mono (prod_mono Subset.rfl (subset_univ _)))
      (fun a _ d _ => by simp [F]) Complex.sqrt
      (fun a ha => by
        have he := congrArg norm (hroot a)
        rw [norm_pow] at he
        have hb : ‖a‖ < R^2 := by simpa only [mem_ball,dist_zero_right] using ha
        nlinarith [norm_nonneg (Complex.sqrt a)])
      (by simpa only [hroot] using (analyticOnNhd_id : AnalyticOnNhd ℂ (fun a : ℂ => a) (ball 0 (R^2))))
    have he : (fun a => F (Complex.sqrt a,a)) = g := by
      funext a
      exact congrArg g (hroot a)
    rw [he] at ha
    simpa only [zero_pow (by decide : 2 ≠ 0)] using
      ha 0 (mem_ball_self (sq_pos_of_pos hR))
  · obtain ⟨V,hV,hbase,r,hr,hrbase,hsq⟩ :=
      exists_local_analytic_squareRoot (fun a : ℂ => a) (w^2) w analyticAt_id hw rfl
    have hh : AnalyticAt ℂ (fun v => g (v^2)) (r (w^2)) := by
      simpa only [hrbase] using h
    have hc : AnalyticAt ℂ (fun a => g ((r a)^2)) (w^2) := hh.comp (hr _ hbase)
    apply hc.congr
    filter_upwards [hV.mem_nhds hbase] with a ha
    rw [(hsq a ha).2]

end NLS.ComplexAnalysis
