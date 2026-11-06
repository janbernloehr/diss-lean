import NLS.ComplexAnalysis.ParametricCosineMeanSegment
import NLS.ComplexAnalysis.ParametricSineSquareCosineMeanLocal

/-! # Analytic sine-squared cosine means on the actual segment

Only regularity along the actual gap segment is required. Analyticity of
the squared half-gap suffices even for discontinuous root selections.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem analyticAt_parametricSineSquareCosineMean_of_analytic_endpoints
    (g : ℂ × A → ℂ) (t d : A → ℂ) (D : Set (ℂ × A)) (hD : IsOpen D)
    (hg : AnalyticOnNhd ℂ g D) (a : A)
    (ht : AnalyticAt ℂ t a) (hd : AnalyticAt ℂ d a)
    (hsegment : ∀ θ ∈ Icc (0 : ℝ) Real.pi, (t a+d a*(Real.cos θ : ℂ),a) ∈ D) :
    AnalyticAt ℂ (fun b => parametricSineSquareCosineMean g t (d b,b)) a := by
  let V : Set A := {b | AnalyticAt ℂ t b ∧ AnalyticAt ℂ d b}
  have hV : IsOpen V := (isOpen_analyticAt ℂ t).inter (isOpen_analyticAt ℂ d)
  let T : ℂ × A → ℂ × A := fun x => (t x.2+d x.2*Complex.cos x.1,x.2)
  let B : Set (ℂ × A) := univ ×ˢ V
  have hB : IsOpen B := isOpen_univ.prod hV
  have hT (x : ℂ × A) (hx : x ∈ B) : AnalyticAt ℂ T x :=
    (((hx.2.1).comp (f := fun x : ℂ × A => x.2) analyticAt_snd).add
      (((hx.2.2).comp (f := fun x : ℂ × A => x.2) analyticAt_snd).mul
        (Complex.analyticAt_cos.comp (f := fun x : ℂ × A => x.1) analyticAt_fst))).prod analyticAt_snd
  let E : Set (ℂ × A) := B ∩ T ⁻¹' D
  have hE : IsOpen E :=
    (show ContinuousOn T B from fun x hx => (hT x hx).continuousAt.continuousWithinAt).isOpen_inter_preimage
      hB hD
  let F : ℂ × A → ℂ := fun x => Complex.sin x.1^2*g (T x)
  have hF : AnalyticOnNhd ℂ F E := fun x hx =>
    ((Complex.analyticAt_sin.comp (f := fun x : ℂ × A => x.1) analyticAt_fst).pow 2).mul
      ((hg (T x) hx.2).comp (f := T) (hT x hx.1))
  have hi := analyticAt_intervalIntegral_of_jointAnalytic F hE hF 0 Real.pi a (by
    intro θ hθ
    refine ⟨⟨mem_univ _,ht,hd⟩,?_⟩
    change (t a+d a*Complex.cos (θ : ℂ),a) ∈ D
    rw [← Complex.ofReal_cos]
    exact hsegment θ (by simpa only [uIcc_of_le Real.pi_pos.le] using hθ))
  simpa only [F,T,parametricSineSquareCosineMean,← Complex.ofReal_cos,
    ← Complex.ofReal_sin] using hi

theorem analyticAt_parametricSineSquareCosineMean_of_squared_gap_segment
    (g : ℂ × A → ℂ) (t d : A → ℂ) (D : Set (ℂ × A)) (hD : IsOpen D)
    (hg : AnalyticOnNhd ℂ g D) (a : A)
    (ht : AnalyticAt ℂ t a) (hsq : AnalyticAt ℂ (fun b => (d b)^2) a)
    (hsegment : ∀ θ ∈ Icc (0 : ℝ) Real.pi, (t a+d a*(Real.cos θ : ℂ),a) ∈ D) :
    AnalyticAt ℂ (fun b => parametricSineSquareCosineMean g t (d b,b)) a := by
  by_cases hzero : d a = 0
  · have hpoint : (t a,a) ∈ D := by
      simpa only [hzero,zero_mul,add_zero] using hsegment 0 ⟨le_rfl,Real.pi_pos.le⟩
    have hslice : IsOpen ((fun z : ℂ => (z,a)) ⁻¹' D) :=
      hD.preimage (continuous_id.prodMk continuous_const)
    obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hslice.mem_nhds hpoint)
    apply analyticAt_parametricSineSquareCosineMean_of_analytic_square g t d D hD hg a ht hsq (ε/2)
      (by simpa only [hzero,norm_zero] using half_pos hε)
    intro z hz
    exact hball (closedBall_subset_ball (half_lt_self hε) hz)
  · obtain ⟨V,hV,haV,r,hr,hra,hsquare⟩ := exists_local_analytic_squareRoot
      (fun b => (d b)^2) a (d a) hsq hzero rfl
    have hmean := analyticAt_parametricSineSquareCosineMean_of_analytic_endpoints g t r D hD hg
      a ht (hr a haV) (fun θ hθ => by rw [hra]; exact hsegment θ hθ)
    apply hmean.congr
    filter_upwards [hV.mem_nhds haV] with b hb
    have he : (d b)^2 = (r b)^2 := (hsquare b hb).2.symm
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp he with he | he
    · rw [he]
    · rw [he,parametricSineSquareCosineMean_neg]

end NLS.ComplexAnalysis
