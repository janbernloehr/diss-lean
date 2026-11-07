import NLS.Articles.KdVPseudomeasures.SourceDirichletAppendixC4
import NLS.Articles.KdVPseudomeasures.PeriodicProjectionConvergence

/-! Both printed estimates of Lemma C.4, with one constant, one original
Sobolev neighborhood and one common index cutoff. -/
noncomputable section
open Set Metric Complex NLS.KdV
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

theorem sourceLemmaC_4 (r : ℝ) (hr : 1/2 < r) (hr1 : r < 1) :
    ∃ Ct : ℝ, 0 < Ct ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) 2,
      ∀ Nmin : ℕ, ∃ N : ℕ, ∃ U : Set (FourierLebesgueSpace (2:ℝ) (-r) 2),
        Nmin ≤ N ∧ IsOpen U ∧ q ∈ U ∧
        ∀ b ∈ U, IsPeriodicDistribution 1 b.val.toTempered →
          ∀ n : ℕ+, N ≤ (n:ℕ) →
            ‖singularHillLinfRieszProjection (hillSobolevBaseInclusion r hr1.le b)
                  (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
              singularHillLinfRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ ≤
              Ct*(Real.log (n:ℝ))^2/(n:ℝ)^(1-r)*‖b‖ ∧
            ‖singularDirichletLinfRieszProjection (hillSobolevBaseInclusion r hr1.le b)
                  (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
              singularDirichletLinfRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ ≤
              Ct*(Real.log (n:ℝ))^2/(n:ℝ)^(1-r)*‖b‖ := by
  obtain ⟨Cp,hCp,hperiodic⟩ := sourcePeriodicProjection_appendixC4 r hr hr1
  obtain ⟨Cd,hCd,hdirichlet⟩ := sourceDirichletProjection_appendixC4 r hr hr1
  let Ct := max Cp Cd
  have hCt : 0 < Ct := hCp.trans_le (le_max_left _ _)
  refine ⟨Ct,hCt,?_⟩
  intro q Nmin
  obtain ⟨Np,_,hNmin,hp⟩ := hperiodic (‖q‖+1) Nmin
  obtain ⟨Nd,V,_,hV,hqV,hd⟩ := hdirichlet q Nmin
  refine ⟨max Np Nd,V ∩ ball q 1,hNmin.trans (le_max_left _ _),hV.inter isOpen_ball,
    ⟨hqV,mem_ball_self (by norm_num)⟩,?_⟩
  intro b hb hperiod n hn
  have hbnorm : ‖b‖ ≤ ‖q‖+1 := by
    have hdist : ‖b-q‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hb.2
    have ht := norm_add_le (b-q) q
    rw [sub_add_cancel] at ht
    linarith
  have hscale : ∀ C : ℝ, C ≤ Ct →
      C*(Real.log (n:ℝ))^2/(n:ℝ)^(1-r)*‖b‖ ≤
        Ct*(Real.log (n:ℝ))^2/(n:ℝ)^(1-r)*‖b‖ := by
    intro C hC
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC (sq_nonneg _))
        (Real.rpow_nonneg (by positivity) _)) (norm_nonneg b)
  exact ⟨(hp b hbnorm n ((le_max_left _ _).trans hn)).trans (hscale Cp (le_max_left _ _)),
    (hd b hb.1 hperiod n ((le_max_right _ _).trans hn)).trans (hscale Cd (le_max_right _ _))⟩

end NLS.Articles.KdVPseudomeasures
