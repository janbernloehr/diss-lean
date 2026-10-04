import NLS.ComplexAnalysis.ParametricCosineMean
import NLS.ComplexAnalysis.CompactParameterBounds

/-! # Local analytic cosine means through root collisions

A compact spectral disc supplies one source neighborhood and one contour
radius. Analyticity of the midpoint and squared half-gap is enough; the
individual half-gap may change sign or vanish.
-/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- Local analyticity of the cosine mean from symmetric endpoint data.
No continuity or analyticity of the chosen half-gap is assumed. -/
theorem analyticAt_parametricCosineMean_of_analytic_square
    (g : ℂ × A → ℂ) (t d : A → ℂ) (D : Set (ℂ × A)) (hD : IsOpen D)
    (hg : AnalyticOnNhd ℂ g D) (a : A)
    (ht : AnalyticAt ℂ t a) (hsq : AnalyticAt ℂ (fun b => (d b)^2) a)
    (S : ℝ) (hdS : ‖d a‖ < S)
    (hdisc : ∀ z ∈ closedBall (t a) S, (z,a) ∈ D) :
    AnalyticAt ℂ (fun b => parametricCosineMean g t (d b,b)) a := by
  obtain ⟨R,hdR,hRS⟩ := exists_between hdS
  have hR : 0 < R := (norm_nonneg _).trans_lt hdR
  let q : A → ℂ := fun b => (d b)^2
  let O : Set A := {b | AnalyticAt ℂ t b ∧ AnalyticAt ℂ q b}
  have hO : IsOpen O := (isOpen_analyticAt ℂ t).inter (isOpen_analyticAt ℂ q)
  have haO : a ∈ O := ⟨ht,hsq⟩
  have hq : AnalyticOnNhd ℂ q O := fun _ hb => hb.2
  let V₀ : Set A := O ∩ q ⁻¹' ball 0 (R^2)
  have hV₀ : IsOpen V₀ := hq.continuousOn.isOpen_inter_preimage hO isOpen_ball
  have haV₀ : a ∈ V₀ := by
    refine ⟨haO,?_⟩
    change (d a)^2 ∈ ball (0:ℂ) (R^2)
    rw [mem_ball,dist_zero_right,norm_pow]
    exact (sq_lt_sq₀ (norm_nonneg _) hR.le).mpr hdR
  let T : ℂ × A → ℂ × A := fun x => (t x.2+x.1,x.2)
  let B : Set (ℂ × A) := univ ×ˢ V₀
  have hB : IsOpen B := isOpen_univ.prod hV₀
  have hT (x : ℂ × A) (hx : x ∈ B) : AnalyticAt ℂ T x :=
    (((hx.2.1.1).comp (f := fun x : ℂ × A => x.2) analyticAt_snd).add analyticAt_fst).prod analyticAt_snd
  let E : Set (ℂ × A) := B ∩ T ⁻¹' D
  have hE : IsOpen E :=
    (show ContinuousOn T B from fun x hx => (hT x hx).continuousAt.continuousWithinAt).isOpen_inter_preimage hB hD
  have hslice : closedBall (0:ℂ) S ×ˢ {a} ⊆ E := by
    rintro ⟨z,b⟩ ⟨hz,hb⟩
    have hba : b = a := mem_singleton_iff.mp hb
    subst b
    refine ⟨⟨mem_univ _,haV₀⟩,hdisc (t a+z) ?_⟩
    simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left,sub_zero] using hz
  obtain ⟨K,U,_,hU,hK,haU,hKU⟩ := generalized_tube_lemma
    (isCompact_closedBall (0:ℂ) S) isCompact_singleton hE hslice
  let V : Set A := U ∩ V₀
  have hV : IsOpen V := hU.inter hV₀
  have haV : a ∈ V := ⟨haU (mem_singleton a),haV₀⟩
  have hchart : ∀ b ∈ V, ∀ e ∈ ball (0:ℂ) S, ∀ θ ∈ Icc (0:ℝ) Real.pi,
      (t b+e*(Real.cos θ:ℂ),b) ∈ D := by
    intro b hb e he θ _
    have hcos : ‖(Real.cos θ:ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one θ
    have hz : e*(Real.cos θ:ℂ) ∈ closedBall (0:ℂ) S := by
      simp only [mem_closedBall,dist_zero_right,norm_mul]
      calc
        ‖e‖*‖(Real.cos θ:ℂ)‖ ≤ ‖e‖*1 := mul_le_mul_of_nonneg_left hcos (norm_nonneg _)
        _ ≤ S := by simpa only [mul_one] using (mem_ball_zero_iff.mp he).le
    exact (hKU (show (e*(Real.cos θ:ℂ),b) ∈ K ×ˢ U from ⟨hK hz,hb.1⟩)).2
  apply analyticOnNhd_parametricCosineMean_of_analytic_square g t D hD hg V hV
    (fun b hb => hb.2.1.1) R S hR hRS hchart d _ (fun b hb => hb.2.1.2) a haV
  intro b hb
  have hn : ‖d b‖^2 < R^2 := by
    simpa only [V₀,q,mem_preimage,mem_ball,dist_zero_right,norm_pow] using hb.2.2
  exact (sq_lt_sq₀ (norm_nonneg _) hR.le).mp hn

end NLS.ComplexAnalysis
