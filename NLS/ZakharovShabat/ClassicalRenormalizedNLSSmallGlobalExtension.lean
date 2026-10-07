import NLS.ZakharovShabat.ClassicalRenormalizedNLSLocalExtension

/-! # Global classical renormalized dynamics near zero above p=2

One invariant open source neighborhood supports a physical global group.
Every compact-time map is the analytic, unique continuous extension of
classical finite-gap renormalized NLS on that neighborhood. The theorem
constructs the neighborhood, its source-norm ball, and all spectral data.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The finite-gap extension part of the near-zero global assertion of
Corollary 22.2(ii), with actual classical finite-gap agreement and uniqueness
of the continuous solution-map extension. Agreement for arbitrary smooth
data is still needed for the dissertation’s full solution definition. -/
theorem exists_small_global_classicalRenormalizedNLSExtension
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p) :
    ∃ U : Set (realTypeSourceSubmodule p), IsOpen U ∧ (0 : realTypeSourceSubmodule p) ∈ U ∧
      (∃ r > 0, Metric.ball 0 r ⊆ U) ∧
      ∃ S : realTypeSourceSubmodule p → ℝ → realTypeSourceSubmodule p,
        (∀ φ ∈ U, S φ 0 = φ) ∧
        (∀ φ ∈ U, ∀ time : ℝ, S φ time ∈ U) ∧
        (∀ φ ∈ U, ∀ time r : ℝ, S (S φ r) time = S φ (time+r)) ∧
        ContinuousOn (fun x : ℝ × realTypeSourceSubmodule p => S x.2 x.1) (univ ×ˢ U) ∧
        ∀ T : ℝ, ∃ F : realTypeSourceSubmodule p → C(Icc (-T) T,realTypeSourceSubmodule p),
          AnalyticOnNhd ℝ F U ∧ IsContinuousClassicalRenormalizedNLSExtensionOn hp hp1 T U F ∧
          (∀ φ ∈ U, ∀ time : Icc (-T) T, F φ time = S φ time.val) ∧
          ∀ G : realTypeSourceSubmodule p → C(Icc (-T) T,realTypeSourceSubmodule p),
            IsContinuousClassicalRenormalizedNLSExtensionOn hp hp1 T U G →
              EqOn G F U ∧ AnalyticOnNhd ℝ G U := by
  obtain ⟨W,P,_,_,hP,hr,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas hp hp1
  obtain ⟨V,B,X,t,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  obtain ⟨U,hU,hzero,hball,hvalid,hinv⟩ := A.exists_invariant_small_renormalizedFlow D
  refine ⟨U,hU,hzero,hball,A.hamiltonianRenormalizedImageFlow D,
    fun φ _ => A.hamiltonianRenormalizedImageFlow_zero D φ,
    fun φ hφ time => hinv φ hφ (-time),?_,
    A.continuousOn_hamiltonianRenormalizedImageFlow hs hP hr D U hvalid,?_⟩
  · intro φ hφ time r
    exact A.hamiltonianRenormalizedImageFlow_add hs.toSourcePsiIsolatingComplexExtension D φ time r
      (hvalid φ hφ (-r))
  · intro T
    have hsub : U ⊆ A.renormalizedTrajectoryDomain t T := fun φ hφ time => hvalid φ hφ time.val
    have ha := (A.analytic_hamiltonianRenormalizedImageTrajectoryOn hs hP hr D T).mono hsub
    have he := A.isContinuousClassicalRenormalizedNLSExtensionOn_hamiltonianImageTrajectory
      hs hP hr D h2p T U hsub
    exact ⟨A.hamiltonianRenormalizedImageTrajectoryOn D T,ha,he,
      fun φ hφ time => A.hamiltonianRenormalizedImageTrajectoryOn_apply hs hP hr D T φ (hsub hφ) time,
      fun _ hG => ⟨hG.unique he hU,hG.analytic_of_reference he hU ha⟩⟩

end NLS.ZakharovShabat
