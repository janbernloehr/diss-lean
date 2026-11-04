import NLS.ComplexAnalysis.AnalyticDiscSquareRoot
import NLS.ComplexAnalysis.ConvexHolomorphicPrimitive
import NLS.ComplexAnalysis.TraceRootPrimitive
import Mathlib.Analysis.Complex.Convex

/-! # Continuing a trace primitive through a regular real boundary point

A nonvanishing discriminant on a real-centered disc has an analytic
root. One upper anchor fixes its sign; the derivative then continues
the actual primitive across the real diameter with its original value.
-/

noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem tendsto_real_upper_vertical (x : ℝ) :
    Tendsto (fun ε : ℝ => (x : ℂ) + (ε : ℂ) * I) (𝓝[>] 0)
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : ContinuousAt (fun ε : ℝ => (x : ℂ) + (ε : ℂ) * I) 0 := by fun_prop
    simpa only [ofReal_zero, zero_mul, add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
      mul_one, mul_zero, zero_add, add_zero] using (show (0 : ℝ) < ε from hε)

theorem real_upper_nhds_neBot (x : ℝ) : NeBot (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) :=
  (tendsto_real_upper_vertical x).neBot

/-- An actual upper-half-plane trace primitive extends holomorphically
across every noncritical real-centered disc, retaining its root, value,
derivative and hyperbolic trace identities. -/
theorem exists_upper_trace_primitive_extension_on_ball
    (D R F : ℂ → ℂ) (x ρ : ℝ) (hρ : 0 < ρ)
    (hD : AnalyticOnNhd ℂ D (ball (x : ℂ) ρ))
    (hne : ∀ z ∈ ball (x : ℂ) ρ, D z ^ 2 - 4 ≠ 0)
    (hR : AnalyticOnNhd ℂ R {z : ℂ | 0 < z.im})
    (hsq : ∀ z : ℂ, 0 < z.im → R z ^ 2 = D z ^ 2 - 4)
    (hF : ∀ z : ℂ, 0 < z.im → HasDerivAt F (deriv D z / R z) z)
    (htrace : ∀ z : ℂ, 0 < z.im → 2 * cosh (F z) = D z ∧ 2 * sinh (F z) = R z) :
    ∃ L G : ℂ → ℂ,
      AnalyticOnNhd ℂ L (ball (x : ℂ) ρ) ∧
      AnalyticOnNhd ℂ G (ball (x : ℂ) ρ) ∧
      (∀ z ∈ ball (x : ℂ) ρ,
        L z ≠ 0 ∧ L z ^ 2 = D z ^ 2 - 4 ∧
          HasDerivAt G (deriv D z / L z) z ∧
            2 * cosh (G z) = D z ∧ 2 * sinh (G z) = L z) ∧
      EqOn L R (ball (x : ℂ) ρ ∩ {z : ℂ | 0 < z.im}) ∧
      EqOn G F (ball (x : ℂ) ρ ∩ {z : ℂ | 0 < z.im}) := by
  let B := ball (x : ℂ) ρ
  let U := B ∩ {z : ℂ | 0 < z.im}
  let a : ℂ := (x : ℂ) + ((ρ / 2 : ℝ) : ℂ) * I
  have haB : a ∈ B := by
    rw [mem_ball, dist_eq_norm]
    simp only [a, add_sub_cancel_left, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (half_pos hρ)]
    linarith
  have haIm : 0 < a.im := by
    simpa only [a, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
      mul_one, mul_zero, add_zero, zero_add] using half_pos hρ
  have haU : a ∈ U := ⟨haB, haIm⟩
  obtain ⟨H, hH, hHsq⟩ := exists_analytic_squareRoot_on_ball
    (fun z => D z ^ 2 - 4) x ρ hρ ((hD.pow 2).sub analyticOnNhd_const) hne
  have hnorm : ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L B ∧
      (∀ z ∈ B, L z ≠ 0 ∧ L z ^ 2 = D z ^ 2 - 4) ∧ L a = R a := by
    have he : H a ^ 2 = R a ^ 2 := (hHsq a haB).2.trans (hsq a haIm).symm
    rcases eq_or_eq_neg_of_sq_eq_sq (H a) (R a) he with he | he
    · exact ⟨H, hH, hHsq, he⟩
    · refine ⟨fun z => -H z, hH.neg, ?_, ?_⟩
      · intro z hz
        exact ⟨neg_ne_zero.mpr (hHsq z hz).1, by simpa only [neg_sq] using (hHsq z hz).2⟩
      · change -H a = R a
        rw [he, neg_neg]
  obtain ⟨L, hL, hLsq, hLa⟩ := hnorm
  have hUopen : IsOpen U := isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
  have hUconv : Convex ℝ U := (convex_ball _ _).inter (convex_halfSpace_im_gt 0)
  have hmatchR : EqOn R L U := hUconv.isPreconnected.eq_of_sq_eq
    (hR.continuousOn.mono (fun _ hz => hz.2)) (hL.continuousOn.mono (fun _ hz => hz.1))
    (fun z hz => by change R z ^ 2 = L z ^ 2; exact (hsq z hz.2).trans (hLsq z hz.1).2.symm)
    (fun {z} hz => (hLsq z hz.1).1) haU hLa.symm
  have hquot : AnalyticOnNhd ℂ (fun z => deriv D z / L z) B :=
    hD.deriv.div hL (fun z hz => (hLsq z hz).1)
  obtain ⟨P, hP⟩ := exists_primitive_on_convex (fun z => deriv D z / L z) B
    (convex_ball _ _) isOpen_ball hquot.differentiableOn
  let G : ℂ → ℂ := fun z => P z - P a + F a
  have hGderiv (z : ℂ) (hz : z ∈ B) : HasDerivAt G (deriv D z / L z) z :=
    ((hP z hz).sub_const _).add_const _
  have hG : AnalyticOnNhd ℂ G B :=
    (show DifferentiableOn ℂ G B from fun z hz =>
      (hGderiv z hz).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_ball
  have hGa : G a = F a := by simp only [G, sub_self, zero_add]
  have hmatchF : EqOn F G U := hUopen.eqOn_of_deriv_eq hUconv.isPreconnected
    (fun z hz => (hF z hz.2).differentiableAt.differentiableWithinAt)
    (hG.differentiableOn.mono (fun _ hz => hz.1))
    (fun z hz => by rw [(hF z hz.2).deriv, (hGderiv z hz.1).deriv, hmatchR hz]) haU hGa.symm
  have hexa : exp (G a) = (D a + L a) / 2 := by
    rw [hGa, ← (htrace a haIm).1, hLa, ← (htrace a haIm).2, ← cosh_add_sinh]
    ring
  have hexp := exp_primitive_of_traceRoot D L G B isOpen_ball (convex_ball _ _).isPreconnected
    hD hL (fun z hz => (hLsq z hz).2) (fun z hz => (hLsq z hz).1) hGderiv a haB hexa
  refine ⟨L, G, hL, hG, ?_, fun z hz => (hmatchR hz).symm, fun z hz => (hmatchF hz).symm⟩
  intro z hz
  have ht := traceRoot_identities_of_exp D L G z (hLsq z hz).2 (hexp z hz)
  exact ⟨(hLsq z hz).1, (hLsq z hz).2, hGderiv z hz, ht.1, ht.2⟩

end NLS.ComplexAnalysis
