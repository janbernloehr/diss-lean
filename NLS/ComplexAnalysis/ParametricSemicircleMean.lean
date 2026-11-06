import NLS.ComplexAnalysis.LocalEvenSquareFamily
import NLS.ComplexAnalysis.ParametricCosineMeanSegment
import NLS.ComplexAnalysis.SemicircleMean

/-! # Analytic semicircle means through a collapsed gap

The sine-square cosine mean is even in the half-gap. Local square
descent therefore gives analyticity from the analytic midpoint and
squared half-gap, with no regularity assumption on the chosen root.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

def parametricSemicircleMean (g : ℂ × A → ℂ) (t : A → ℂ) (x : ℂ × A) : ℂ :=
  normalizedSemicircleMean (fun s : ℝ => g (t x.2+x.1*(s : ℂ),x.2))

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
theorem parametricSemicircleMean_neg (g : ℂ × A → ℂ) (t : A → ℂ) (d : ℂ) (a : A) :
    parametricSemicircleMean g t (-d,a) = parametricSemicircleMean g t (d,a) := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => (Real.sin θ : ℂ)^2*g (t a+d*(Real.cos θ : ℂ),a)) Real.pi (a := 0) (b := Real.pi)
  simpa only [parametricSemicircleMean,normalizedSemicircleMean,sub_self,sub_zero,Real.cos_pi_sub,
    Real.sin_pi_sub,ofReal_neg,mul_neg,neg_mul] using congrArg (fun v : ℂ => (2/(Real.pi : ℂ))*v) h

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
theorem parametricSemicircleMean_eq_of_sq_eq (g : ℂ × A → ℂ) (t : A → ℂ)
    (d e : ℂ) (a : A) (he : d^2 = e^2) :
    parametricSemicircleMean g t (d,a) = parametricSemicircleMean g t (e,a) := by
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp he with h | h
  · rw [h]
  · rw [h,parametricSemicircleMean_neg]

theorem analyticAt_parametricSemicircleMean
    (g : ℂ × A → ℂ) (t : A → ℂ) (D : Set (ℂ × A)) (hD : IsOpen D)
    (hg : AnalyticOnNhd ℂ g D) (a : A) (d : ℂ) (ht : AnalyticAt ℂ t a)
    (hsegment : ∀ θ ∈ Icc (0 : ℝ) Real.pi, (t a+d*(Real.cos θ : ℂ),a) ∈ D) :
    AnalyticAt ℂ (parametricSemicircleMean g t) (d,a) := by
  let V : Set A := {b | AnalyticAt ℂ t b}
  have hV : IsOpen V := isOpen_analyticAt ℂ t
  let T : ℂ × (ℂ × A) → ℂ × A := fun x => (t x.2.2+x.2.1*Complex.cos x.1,x.2.2)
  let B : Set (ℂ × (ℂ × A)) := univ ×ˢ (univ ×ˢ V)
  have hB : IsOpen B := isOpen_univ.prod (isOpen_univ.prod hV)
  have hT (x : ℂ × (ℂ × A)) (hx : x ∈ B) : AnalyticAt ℂ T x := by
    have ha : AnalyticAt ℂ (fun x : ℂ × (ℂ × A) => x.2.2) x :=
      analyticAt_snd.comp (f := fun x : ℂ × (ℂ × A) => x.2) analyticAt_snd
    have hd : AnalyticAt ℂ (fun x : ℂ × (ℂ × A) => x.2.1) x :=
      analyticAt_fst.comp (f := fun x : ℂ × (ℂ × A) => x.2) analyticAt_snd
    exact (((hx.2.2).comp (f := fun x : ℂ × (ℂ × A) => x.2.2) ha).add
      (hd.mul (Complex.analyticAt_cos.comp (f := fun x : ℂ × (ℂ × A) => x.1) analyticAt_fst))).prod ha
  let E : Set (ℂ × (ℂ × A)) := B ∩ T ⁻¹' D
  have hE : IsOpen E :=
    (show ContinuousOn T B from fun x hx => (hT x hx).continuousAt.continuousWithinAt).isOpen_inter_preimage hB hD
  let F : ℂ × (ℂ × A) → ℂ := fun x => (Complex.sin x.1)^2*g (T x)
  have hF : AnalyticOnNhd ℂ F E := by
    intro x hx
    exact ((Complex.analyticAt_sin.comp (f := fun x : ℂ × (ℂ × A) => x.1) analyticAt_fst).pow 2).mul
      ((hg (T x) hx.2).comp (f := T) (hT x hx.1))
  have hi := analyticAt_intervalIntegral_of_jointAnalytic F hE hF 0 Real.pi (d,a) (by
    intro θ hθ
    refine ⟨⟨mem_univ _,mem_univ _,ht⟩,?_⟩
    change (t a+d*Complex.cos (θ : ℂ),a) ∈ D
    rw [← Complex.ofReal_cos]
    exact hsegment θ (by simpa only [uIcc_of_le Real.pi_pos.le] using hθ))
  change AnalyticAt ℂ (fun x : ℂ × A => (2/(Real.pi : ℂ))*(∫ θ in (0 : ℝ)..Real.pi,
    (Real.sin θ : ℂ)^2*g (t x.2+x.1*(Real.cos θ : ℂ),x.2))) (d,a)
  have hh : AnalyticAt ℂ (fun x : ℂ × A => (2/(Real.pi : ℂ))*(∫ θ in (0 : ℝ)..Real.pi,
      F ((θ : ℂ),x))) (d,a) := analyticAt_const.mul hi
  simpa only [F,T,← Complex.ofReal_cos,← Complex.ofReal_sin] using hh

theorem analyticAt_parametricSemicircleMean_of_analytic_square
    (g : ℂ × A → ℂ) (t d : A → ℂ) (D : Set (ℂ × A)) (hD : IsOpen D)
    (hg : AnalyticOnNhd ℂ g D) (a : A) (ht : AnalyticAt ℂ t a)
    (hsq : AnalyticAt ℂ (fun b => (d b)^2) a)
    (hsegment : ∀ θ ∈ Icc (0 : ℝ) Real.pi, (t a+d a*(Real.cos θ : ℂ),a) ∈ D) :
    AnalyticAt ℂ (fun b => parametricSemicircleMean g t (d b,b)) a :=
  analyticAt_evenFamily_of_analytic_square (parametricSemicircleMean g t) d a
    (analyticAt_parametricSemicircleMean g t D hD hg a (d a) ht hsegment)
    (fun b e => parametricSemicircleMean_neg g t e b) hsq

end NLS.ComplexAnalysis
