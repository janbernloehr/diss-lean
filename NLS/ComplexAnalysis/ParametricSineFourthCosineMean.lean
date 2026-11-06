import NLS.ComplexAnalysis.ParametricEvenSquareDescent
import NLS.ComplexAnalysis.ParametricIntervalIntegralAnalytic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- The sine-fourth weighted cosine mean of a spectral numerator. -/
def parametricSineFourthCosineMean (g : ℂ × A → ℂ) (t : A → ℂ) (x : ℂ × A) : ℂ :=
  ∫ θ in (0:ℝ)..Real.pi, (Real.sin θ : ℂ)^4*g (t x.2+x.1*(Real.cos θ:ℂ),x.2)

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
/-- Exchanging the two endpoints leaves the cosine mean unchanged. -/
theorem parametricSineFourthCosineMean_neg (g : ℂ × A → ℂ) (t : A → ℂ) (d : ℂ) (a : A) :
    parametricSineFourthCosineMean g t (-d,a) = parametricSineFourthCosineMean g t (d,a) := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => (Real.sin θ : ℂ)^4*g (t a+d*(Real.cos θ:ℂ),a)) Real.pi (a := 0) (b := Real.pi)
  simpa only [parametricSineFourthCosineMean,sub_self,sub_zero,Real.cos_pi_sub,Real.sin_pi_sub,ofReal_neg,mul_neg,neg_mul] using h

/-- A jointly analytic spectral numerator has a jointly analytic weighted cosine
mean in an independent complex half-gap and the source parameter. -/
theorem analyticOnNhd_parametricSineFourthCosineMean
    (g : ℂ × A → ℂ) (t : A → ℂ) (D : Set (ℂ × A)) (hD : IsOpen D)
    (hg : AnalyticOnNhd ℂ g D) (V : Set A) (hV : IsOpen V)
    (ht : AnalyticOnNhd ℂ t V) (R : ℝ)
    (hchart : ∀ a ∈ V, ∀ d ∈ ball (0:ℂ) R, ∀ θ ∈ Icc (0:ℝ) Real.pi,
      (t a+d*(Real.cos θ:ℂ),a) ∈ D) :
    AnalyticOnNhd ℂ (parametricSineFourthCosineMean g t) (ball 0 R ×ˢ V) := by
  let T : ℂ × (ℂ × A) → ℂ × A := fun x => (t x.2.2+x.2.1*Complex.cos x.1,x.2.2)
  let B : Set (ℂ × (ℂ × A)) := {x | x.2.2 ∈ V}
  let E : Set (ℂ × (ℂ × A)) := B ∩ T ⁻¹' D
  have hB : IsOpen B := hV.preimage (continuous_snd.comp continuous_snd)
  have hT (x : ℂ × (ℂ × A)) (hx : x ∈ B) : AnalyticAt ℂ T x := by
    have ha : AnalyticAt ℂ (fun x : ℂ × (ℂ × A) => x.2.2) x :=
      analyticAt_snd.comp (f := fun x : ℂ × (ℂ × A) => x.2) analyticAt_snd
    have hd : AnalyticAt ℂ (fun x : ℂ × (ℂ × A) => x.2.1) x :=
      analyticAt_fst.comp (f := fun x : ℂ × (ℂ × A) => x.2) analyticAt_snd
    exact (((ht x.2.2 hx).comp (f := fun x : ℂ × (ℂ × A) => x.2.2) ha).add
      (hd.mul (Complex.analyticAt_cos.comp (f := fun x : ℂ × (ℂ × A) => x.1) analyticAt_fst))).prod ha
  have hE : IsOpen E :=
    (show ContinuousOn T B from fun x hx => (hT x hx).continuousAt.continuousWithinAt).isOpen_inter_preimage hB hD
  let G : ℂ × (ℂ × A) → ℂ := fun x => (Complex.sin x.1)^4*g (T x)
  have hG : AnalyticOnNhd ℂ G E :=
    fun x hx => ((Complex.analyticAt_sin.comp (f := fun x : ℂ × (ℂ × A) => x.1) analyticAt_fst).pow 4).mul
      ((hg (T x) hx.2).comp (f := T) (hT x hx.1))
  have hi := analyticOnNhd_intervalIntegral_of_jointAnalytic G hE hG 0 Real.pi
    (isOpen_ball.prod hV) (by
      intro x hx θ hθ
      refine ⟨hx.2,?_⟩
      change (t x.2+x.1*Complex.cos (θ:ℂ),x.2) ∈ D
      rw [← Complex.ofReal_cos]
      exact hchart x.2 hx.2 x.1 hx.1 θ
        (by simpa only [uIcc_of_le Real.pi_pos.le] using hθ))
  unfold parametricSineFourthCosineMean
  simpa only [G,T,← Complex.ofReal_cos,← Complex.ofReal_sin] using hi

/-- Analytic squared gaps suffice for cosine means near a closed gap.
The half-gap itself may be an arbitrary, even discontinuous root selection. -/
theorem analyticOnNhd_parametricSineFourthCosineMean_of_analytic_square
    (g : ℂ × A → ℂ) (t : A → ℂ) (D : Set (ℂ × A)) (hD : IsOpen D)
    (hg : AnalyticOnNhd ℂ g D) (V : Set A) (hV : IsOpen V)
    (ht : AnalyticOnNhd ℂ t V) (R S : ℝ) (hR : 0 < R) (hRS : R < S)
    (hchart : ∀ a ∈ V, ∀ d ∈ ball (0:ℂ) S, ∀ θ ∈ Icc (0:ℝ) Real.pi,
      (t a+d*(Real.cos θ:ℂ),a) ∈ D)
    (d : A → ℂ) (hd : ∀ a ∈ V, ‖d a‖ < R)
    (hsq : AnalyticOnNhd ℂ (fun a => (d a)^2) V) :
    AnalyticOnNhd ℂ (fun a => parametricSineFourthCosineMean g t (d a,a)) V := by
  apply analyticOnNhd_evenFamily_of_analytic_square (parametricSineFourthCosineMean g t) R hR V hV
    ((analyticOnNhd_parametricSineFourthCosineMean g t D hD hg V hV ht S hchart).mono
      (prod_mono (closedBall_subset_ball hRS) Subset.rfl))
    (fun a _ e _ => parametricSineFourthCosineMean_neg g t e a) d hd hsq

end NLS.ComplexAnalysis
