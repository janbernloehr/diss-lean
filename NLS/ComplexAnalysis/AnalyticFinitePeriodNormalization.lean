import NLS.ComplexAnalysis.AnalyticImplicitBanachRoot

/-! # Constructing analytic finite period normalization

A finite analytic period matrix equal to the identity at a base point
has an actual local analytic inverse family. The implicit function theorem
solves all normalization equations simultaneously, without an inverse
matrix or selected coefficient family as an input.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis
variable {ι E : Type} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem exists_analytic_finite_period_normalization
    (P : E → ι → ι → ℂ) (a : E)
    (hP : ∀ j k, AnalyticAt ℂ (fun q => P q j k) a)
    (hPa : ∀ j k, P a j k = if j = k then 1 else 0) :
    ∃ C : E → ι → ι → ℂ, ∃ V : Set E, IsOpen V ∧ a ∈ V ∧
      AnalyticOnNhd ℂ C V ∧ (∀ n j, C a n j = if n = j then 1 else 0) ∧
      ∀ q ∈ V, ∀ n k, (∑ j, C q n j*P q j k) = if n = k then 1 else 0 := by
  classical
  let I0 : ι → ι → ℂ := fun n j => if n = j then 1 else 0
  let F : ((ι → ι → ℂ) × E) → (ι → ι → ℂ) :=
    fun t n k => (∑ j, t.1 n j*P t.2 j k)-I0 n k
  have hF : AnalyticAt ℂ F (I0,a) := by
    apply AnalyticAt.pi
    intro n
    apply AnalyticAt.pi
    intro k
    apply AnalyticAt.sub _ analyticAt_const
    apply Finset.analyticAt_fun_sum
    intro j _
    have hc : AnalyticAt ℂ (fun t : (ι → ι → ℂ) × E => t.1 n j) (I0,a) := by
      have hfst : AnalyticAt ℂ (fun t : (ι → ι → ℂ) × E => t.1) (I0,a) := analyticAt_fst
      exact analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hfst n) j
    have hp : AnalyticAt ℂ (fun t : (ι → ι → ℂ) × E => P t.2 j k) (I0,a) := by
      simpa only [Function.comp_def] using!
        (hP j k).comp (f := fun t : (ι → ι → ℂ) × E => t.2)
          (analyticAt_snd (p := (I0,a)))
    exact hc.mul hp
  have hsection : (fun c : ι → ι → ℂ => F (c,a)) = (fun c => c-I0) := by
    funext c n k
    simp [F, hPa]
  have hz : F (I0,a) = 0 := by
    change (fun c => F (c,a)) I0 = 0
    rw [hsection]
    exact sub_self _
  have hpartial : (fderiv ℂ F (I0,a)).comp
      (ContinuousLinearMap.inl ℂ (ι → ι → ℂ) E) = ContinuousLinearMap.id ℂ (ι → ι → ℂ) := by
    have hc := hF.differentiableAt.hasFDerivAt.comp
      (f := fun c : ι → ι → ℂ => (c,a)) I0 (hasFDerivAt_prodMk_left I0 a)
    change HasFDerivAt (fun c => F (c,a)) _ I0 at hc
    rw [hsection] at hc
    exact hc.unique ((hasFDerivAt_id I0).sub_const I0)
  have hbij : Function.Bijective ((fderiv ℂ F (I0,a)).comp
      (ContinuousLinearMap.inl ℂ (ι → ι → ℂ) E)) := by
    rw [hpartial]
    exact Function.bijective_id
  obtain ⟨C, hC, hCa, hzero⟩ := exists_analytic_implicitBanachRoot F I0 a hF hz hbij
  obtain ⟨r, hr, han⟩ := hC.exists_ball_analyticOnNhd
  obtain ⟨W, hWsub, hW, haW⟩ := _root_.mem_nhds_iff.mp hzero
  refine ⟨C, W ∩ Metric.ball a r, hW.inter Metric.isOpen_ball,
    ⟨haW, Metric.mem_ball_self hr⟩, han.mono inter_subset_right, ?_, ?_⟩
  · intro n j
    exact congrFun (congrFun hCa n) j
  intro q hq n k
  have he := congrFun (congrFun (hWsub hq.1) n) k
  exact sub_eq_zero.mp he

end NLS.ComplexAnalysis
