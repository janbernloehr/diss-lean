import NLS.ComplexAnalysis.ParametricCosineMean
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Regular sine-square means at a collapsed gap -/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- The cosine profile weighted by the square of its sine. -/
def parametricSineSquareMean (g : ℂ × A → ℂ) (t : A → ℂ) (x : ℂ × A) : ℂ :=
  ∫ θ in (0:ℝ)..Real.pi, (Real.sin θ : ℂ)^2 * g (t x.2+x.1*(Real.cos θ:ℂ),x.2)

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
/-- At collapse the weighted mean is pi over two times the central value. -/
theorem parametricSineSquareMean_zero (g : ℂ × A → ℂ) (t : A → ℂ) (a : A) :
    parametricSineSquareMean g t (0,a) = (Real.pi : ℂ)/2*g (t a,a) := by
  simp only [parametricSineSquareMean,zero_mul,add_zero,intervalIntegral.integral_mul_const]
  have he : (∫ θ in (0:ℝ)..Real.pi, (Real.sin θ : ℂ)^2) = (Real.pi : ℂ)/2 := by
    rw [show (fun θ : ℝ => (Real.sin θ : ℂ)^2) = fun θ => (((Real.sin θ)^2 : ℝ) : ℂ) by
      funext θ; simp, intervalIntegral.integral_ofReal]
    simp
  rw [he]

/-- Joint analyticity of the regular numerator gives differentiability of
its weighted mean in an independent half-gap at the collapsed gap. -/
theorem differentiableAt_parametricSineSquareMean_zero
    (g : ℂ × A → ℂ) (t : A → ℂ) (a : A)
    (hg : AnalyticAt ℂ g (t a,a)) (ht : AnalyticAt ℂ t a) :
    DifferentiableAt ℂ (parametricSineSquareMean g t) (0,a) := by
  let D := {x | AnalyticAt ℂ g x}
  let V := {b | AnalyticAt ℂ t b}
  let T : ℂ × (ℂ × A) → ℂ × A := fun x => (t x.2.2+x.2.1*Complex.cos x.1,x.2.2)
  let B : Set (ℂ × (ℂ × A)) := {x | x.2.2 ∈ V}
  let E := B ∩ T ⁻¹' D
  have hB : IsOpen B := (isOpen_analyticAt ℂ t).preimage (continuous_snd.comp continuous_snd)
  have hT (x : ℂ × (ℂ × A)) (hx : x ∈ B) : AnalyticAt ℂ T x := by
    have ha : AnalyticAt ℂ (fun x : ℂ × (ℂ × A) => x.2.2) x :=
      analyticAt_snd.comp (f := fun x : ℂ × (ℂ × A) => x.2) analyticAt_snd
    have hd : AnalyticAt ℂ (fun x : ℂ × (ℂ × A) => x.2.1) x :=
      analyticAt_fst.comp (f := fun x : ℂ × (ℂ × A) => x.2) analyticAt_snd
    exact (((hx).comp (f := fun x : ℂ × (ℂ × A) => x.2.2) ha).add
      (hd.mul (Complex.analyticAt_cos.comp (f := fun x : ℂ × (ℂ × A) => x.1) analyticAt_fst))).prod ha
  have hE : IsOpen E :=
    (show ContinuousOn T B from fun x hx => (hT x hx).continuousAt.continuousWithinAt).isOpen_inter_preimage
      hB (isOpen_analyticAt ℂ g)
  let F : ℂ × (ℂ × A) → ℂ := fun x => Complex.sin x.1 ^ 2 * g (T x)
  have hF : AnalyticOnNhd ℂ F E := by
    intro x hx
    exact (((Complex.analyticAt_sin.comp (f := fun x : ℂ × (ℂ × A) => x.1)
      analyticAt_fst).pow 2).mul ((hx.2).comp (f := T) (hT x hx.1)))
  have hi := (hasFDerivAt_intervalIntegral_of_jointAnalytic F hE hF 0 Real.pi (0,a)
    (by intro θ _; exact ⟨ht,by simpa [T,D] using hg⟩)).differentiableAt
  simpa only [parametricSineSquareMean,F,T,← Complex.ofReal_sin,← Complex.ofReal_cos] using! hi

end NLS.ComplexAnalysis
