import NLS.ComplexAnalysis.EndpointRootCirclePeriod
import NLS.ComplexAnalysis.EntireEvenSquareDescent

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

def centeredQuadraticRoot (s : A → ℂ) (t : ℂ × A) : ℂ :=
  -t.1*sqrt (1-s t.2/t.1^2)

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
theorem centeredQuadraticRoot_sq (s : A → ℂ) (z : ℂ) (p : A) (hz : z ≠ 0) :
    centeredQuadraticRoot s (z,p)^2 = z^2-s p := by
  rw [centeredQuadraticRoot,mul_pow,neg_sq,complex_sqrt_sq]
  field_simp

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
theorem centeredQuadraticRoot_eq_endpointRoot (s : A → ℂ) (z : ℂ) (p : A) (d : ℂ)
    (hz : z ≠ 0) (hd : d^2 = s p) :
    centeredQuadraticRoot s (z,p) = endpointRoot (-d) d z := by
  have hc : ((-d+d)/2 : ℂ) = 0 := by ring
  have hrad : (d-(-d))^2/(4*((-d+d)/2-z)^2) = s p/z^2 := by
    rw [hc,← hd]
    field_simp
    ring
  simp only [hc,zero_sub] at hrad
  simp only [centeredQuadraticRoot,endpointRoot,NLS.ZakharovShabat.normalizedStandardRoot,hrad,hc,zero_sub]

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
theorem centeredQuadraticRoot_ne_zero (s : A → ℂ) (z : ℂ) (p : A) (r : ℝ)
    (hr : 0 < r) (hz : r ≤ ‖z‖) (hs : ‖s p‖ < r^2) : centeredQuadraticRoot s (z,p) ≠ 0 := by
  have hzn : z ≠ 0 := norm_pos_iff.mp (hr.trans_le hz)
  intro he
  have hsq := centeredQuadraticRoot_sq s z p hzn
  rw [he,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
  have hsame : z^2 = s p := (sub_eq_zero.mp hsq.symm)
  have hn : ‖z‖^2 = ‖s p‖ := by rw [← norm_pow,hsame]
  nlinarith [norm_nonneg z]

theorem analyticOnNhd_centeredQuadraticRoot
    (s : A → ℂ) (r R : ℝ) (hr : 0 < r) (V : Set A)
    (hs : AnalyticOnNhd ℂ s V) (hsmall : ∀ p ∈ V, ‖s p‖ < r^2) :
    AnalyticOnNhd ℂ (centeredQuadraticRoot s) ((closedBall (0:ℂ) R \ ball 0 r) ×ˢ V) := by
  intro t ht
  have hz : r ≤ ‖t.1‖ := by
    simpa only [mem_ball,dist_zero_right,not_lt] using ht.1.2
  have hzn : t.1 ≠ 0 := norm_pos_iff.mp (hr.trans_le hz)
  have hratio : ‖s t.2/t.1^2‖ < 1 := by
    rw [norm_div,norm_pow]
    apply (div_lt_one (sq_pos_of_pos (hr.trans_le hz))).mpr
    exact (hsmall t.2 ht.2).trans_le ((sq_le_sq₀ hr.le (norm_nonneg _)).mpr hz)
  have hslit := mem_slitPlane_one_sub_of_norm_lt_one _ hratio
  have hrat : AnalyticAt ℂ (fun u : ℂ × A => 1-s u.2/u.1^2) t :=
    analyticAt_const.sub (((hs t.2 ht.2).comp (f := fun u : ℂ × A => u.2) analyticAt_snd).div
      (analyticAt_fst.pow 2) (pow_ne_zero 2 hzn))
  have hroot : AnalyticAt ℂ Complex.sqrt (1-s t.2/t.1^2) :=
    Complex.differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds hslit)
  exact analyticAt_fst.neg.mul (hroot.comp (f := fun u : ℂ × A => 1-s u.2/u.1^2) hrat)

end NLS.ComplexAnalysis
