import NLS.ComplexAnalysis.ParametricCosineMeanSegment
import NLS.ComplexAnalysis.EntireEvenSquareDescent

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

def centeredMeanFree (f : ℂ × A → ℂ) (s : A → ℂ) (t : ℂ × A) : ℂ :=
  f t-parametricCosineMean f (fun _ => 0) (sqrt (s t.2),t.2)/(Real.pi : ℂ)

theorem analyticAt_centeredCosineMean_of_collapse
    (f : ℂ × A → ℂ) (s : A → ℂ) (a : A)
    (hf : AnalyticAt ℂ f (0,a)) (hs : AnalyticAt ℂ s a) (hs0 : s a = 0) :
    AnalyticAt ℂ (fun p => parametricCosineMean f (fun _ => 0) (sqrt (s p),p)) a := by
  let D := {t | AnalyticAt ℂ f t}
  have hsq : AnalyticAt ℂ (fun p => (sqrt (s p))^2) a := by
    simpa only [complex_sqrt_sq] using hs
  apply analyticAt_parametricCosineMean_of_squared_gap_segment f (fun _ => 0) (fun p => sqrt (s p))
    D (isOpen_analyticAt ℂ f) (fun _ ht => ht) a analyticAt_const hsq
  intro θ _
  change AnalyticAt ℂ f (0+sqrt (s a)*(Real.cos θ : ℂ),a)
  simpa only [hs0,sqrt_zero,zero_mul,add_zero] using hf

theorem analyticAt_centeredMeanFree_of_collapse
    (f : ℂ × A → ℂ) (s : A → ℂ) (a : A)
    (hf : AnalyticAt ℂ f (0,a)) (hs : AnalyticAt ℂ s a) (hs0 : s a = 0) :
    AnalyticAt ℂ (centeredMeanFree f s) (0,a) := by
  have hm := analyticAt_centeredCosineMean_of_collapse f s a hf hs hs0
  have hmJ : AnalyticAt ℂ (fun t : ℂ × A => parametricCosineMean f (fun _ => 0) (sqrt (s t.2),t.2)) (0,a) :=
    AnalyticAt.comp (𝕜 := ℂ) (x := ((0 : ℂ),a))
      (g := fun p : A => parametricCosineMean f (fun _ => 0) (sqrt (s p),p))
      (f := fun t : ℂ × A => t.2) hm analyticAt_snd
  exact hf.sub (hmJ.div_const)

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
theorem integral_centeredMeanFree_cosine_eq_zero
    (f : ℂ × A → ℂ) (s : A → ℂ) (p : A)
    (hf : IntervalIntegrable (fun θ : ℝ => f (sqrt (s p)*(Real.cos θ : ℂ),p)) volume 0 Real.pi) :
    (∫ θ in (0 : ℝ)..Real.pi,
      centeredMeanFree f s (sqrt (s p)*(Real.cos θ : ℂ),p)) = 0 := by
  let m := ∫ θ in (0 : ℝ)..Real.pi, f (sqrt (s p)*(Real.cos θ : ℂ),p)
  have he : (fun θ : ℝ => centeredMeanFree f s (sqrt (s p)*(Real.cos θ : ℂ),p)) =
      (fun θ => f (sqrt (s p)*(Real.cos θ : ℂ),p)-m/(Real.pi : ℂ)) := by
    funext θ
    simp only [centeredMeanFree,parametricCosineMean,zero_add,m]
  rw [he,intervalIntegral.integral_sub hf intervalIntegrable_const,intervalIntegral.integral_const,
    sub_zero,Complex.real_smul]
  change m-(Real.pi : ℂ)*(m/(Real.pi : ℂ)) = 0
  field_simp
  ring

end NLS.ComplexAnalysis
