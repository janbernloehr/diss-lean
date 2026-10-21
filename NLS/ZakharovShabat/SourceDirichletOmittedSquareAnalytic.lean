import NLS.ZakharovShabat.SourceGapWeightedEtaAuxiliary
import NLS.ZakharovShabat.CanonicalDeletedProductLp
import NLS.ZakharovShabat.FreeSquaredSineBounds
import NLS.ZakharovShabat.SourceBoundaryDisplacementAnalytic
import NLS.SequenceSpaces.FiniteHeadTailBound
import NLS.SequenceSpaces.LocallyBoundedRealization

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Squared omitted-product normalization at the actual central and tail Dirichlet roots. -/
def sourceDirichletOmittedSquareError (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) : ℂ :=
  (sourceStandardRootOmittedProduct hp hp1 n ψ
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n))^2-1

/-- The complete squared normalization error, with its actual coefficients proved below. -/
def sourceDirichletOmittedSquareRemainder (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) : Coeff p :=
  Coeff.ofFunctionOrZero p (sourceDirichletOmittedSquareError hp hp1 ψ)

namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The original angular charts keep every actual Dirichlet sample in the omitted domain. -/
theorem dirichlet_omitted_sample_data (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
    canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n ∈
      sourceStandardRootOmittedDomain hp hp1 ψ n ∧
    AnalyticAt ℂ (fun χ : CoeffPair p => sourceStandardRootOmittedProduct hp hp1 n χ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet χ n)) ψ := by
  obtain ⟨U,c,T,r,R,z₀,hψU,E,_⟩ := H.angular_original_annulus_chart ψ hψ n
  let μ := fun χ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet χ n
  have hμball := (E.disc_family ψ hψU).dirichlet_mem_ball n
  refine ⟨((E.disc_family ψ hψU).contour_family.2 n).2.2.1 (ball_subset_closedBall hμball),?_⟩
  exact (E.omitted_analytic (μ ψ,ψ) ⟨hμball,hψU⟩).comp
    (f := fun χ : CoeffPair p => (μ χ,χ))
    ((H.original_theta_common_domain.roots_analytic .dirichlet n ψ hψ).prod analyticAt_id)

/-- The entire sampled squared error has locally bounded original lp norm on W. -/
theorem dirichlet_omitted_square_local_bound (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ W ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ ψ ∈ V,
        Memℓp (sourceDirichletOmittedSquareError hp hp1 ψ) p ∧
        ‖sourceDirichletOmittedSquareRemainder hp hp1 ψ‖ ≤ B := by
  classical
  let D := H.original_theta_common_domain
  let d := sourceBoundaryDisplacement hp hp1 .dirichlet
  let f := sourceDirichletOmittedSquareError hp hp1
  have hd : ContinuousAt d φ :=
    (analyticOnNhd_sourceBoundaryDisplacement_of_roots hp hp1 W D.source_open D.roots_analytic
      .dirichlet φ hφ).continuousAt
  have hc (n : ℤ) : AnalyticOnNhd ℂ (fun ψ => f ψ n) W := fun ψ hψ =>
    ((H.dirichlet_omitted_sample_data ψ hψ n).2.pow 2).sub analyticAt_const
  obtain ⟨K,V₀,hV₀,hφV₀,hsmall⟩ := Coeff.exists_local_uniform_small_coordinates hp d φ hd
    (Real.pi/4) (by positivity)
  obtain ⟨U,hU,_,hφU,_,Amax,hAmax,hmajor⟩ :=
    exists_uniform_canonicalDeletedPairError_majorants hp hp1 (periodOnePotential φ)
  obtain ⟨C,hC,hfree⟩ := exists_freeSquaredSine_displacement_bounds (Real.pi/4)
  let S := Coeff.lowFrequencies (K+1)
  let head : CoeffPair p → Coeff p := fun ψ => Coeff.finiteHead S (f ψ)
  have hhead : ContinuousAt head φ := by
    unfold head Coeff.finiteHead
    apply tendsto_finsetSum S
    intro n _
    exact (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p n).continuous.continuousAt.comp
      (hc n φ hφ).continuousAt
  have hdb : ∀ᶠ ψ in 𝓝 φ, ‖d ψ‖ < ‖d φ‖+1 :=
    hd.norm.eventually (gt_mem_nhds (by linarith))
  have hhb : ∀ᶠ ψ in 𝓝 φ, ‖head ψ‖ < ‖head φ‖+1 :=
    hhead.norm.eventually (gt_mem_nhds (by linarith))
  let T := W ∩ ((periodOnePotential (p := p)) ⁻¹' U) ∩ V₀
  have hT : IsOpen T := (D.source_open.inter (hU.preimage (periodOnePotential (p := p)).continuous)).inter hV₀
  have hφT : φ ∈ T := ⟨⟨hφ,hφU⟩,hφV₀⟩
  obtain ⟨V,hVsub,hV,hφV⟩ := _root_.mem_nhds_iff.mp
    (inter_mem (hT.mem_nhds hφT) (inter_mem hdb hhb))
  refine ⟨V,hV,hφV,fun ψ hψ => (hVsub hψ).1.1.1,
    (‖head φ‖+1)+(1+C)*(Amax+‖d φ‖+1),by positivity,?_⟩
  intro ψ hψ
  have hψW := (hVsub hψ).1.1.1
  obtain ⟨A,hA,hvalue,_⟩ := hmajor (periodOnePotential ψ) (hVsub hψ).1.1.2 (periodOnePotential_mem ψ)
  have htail (n : ℤ) (hn : n ∉ S) : ‖f ψ n‖ ≤ (1+C)*(‖A n‖+‖d ψ n‖) := by
    have hnK : K < n.natAbs := by
      dsimp only [S] at hn
      rw [Coeff.mem_lowFrequencies] at hn
      omega
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n
    have hμ : ‖μ-(Real.pi:ℂ)*n‖ ≤ Real.pi/4 := (hsmall ψ (hVsub hψ).1.2 n hnK).le
    have hsq : f ψ n = canonicalDeletedPeriodicProduct hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n μ-1 := by
      exact congrArg (fun z : ℂ => z-1)
        (sourceStandardRootOmittedProduct_sq_eq_canonicalDeletedPeriodicProduct hp hp1 ψ n μ
          (H.dirichlet_omitted_sample_data ψ hψW n).1)
    have he : canonicalDeletedPeriodicProduct hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n μ-1 =
        canonicalDeletedPairError hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n μ+
          ((freeSineQuotient n μ)^2-1) := by
      unfold canonicalDeletedPairError
      ring
    rw [hsq,he]
    have ha := hvalue n μ (by linarith [Real.pi_pos])
    have hf := (hfree n μ hμ).1
    change ‖(freeSineQuotient n μ)^2-1‖ ≤ C*‖d ψ n‖ at hf
    have ht := (norm_add_le _ _).trans (add_le_add ha hf)
    exact ht.trans (by nlinarith [norm_nonneg (A n),norm_nonneg (d ψ n)])
  obtain ⟨hm,hn⟩ := Coeff.memℓp_and_norm_ofFunctionOrZero_le_of_head_tail_bound
    (f ψ) (f ψ) S A (d ψ) (1+C) (by positivity) (fun _ _ => le_rfl) htail
  refine ⟨hm,hn.trans ?_⟩
  change ‖head ψ‖+(1+C)*(‖A‖+‖d ψ‖) ≤ _
  have hdψ := (hVsub hψ).2.1
  have hhψ := (hVsub hψ).2.2
  change ‖d ψ‖ < ‖d φ‖+1 at hdψ
  change ‖head ψ‖ < ‖head φ‖+1 at hhψ
  exact add_le_add hhψ.le (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

/-- The squared normalization error is an actual lp-valued analytic map on the unchanged W. -/
theorem dirichlet_omitted_square_analytic (H : SourceLemma12_12Data hp hp1 W₀ W s) :
    AnalyticOnNhd ℂ (sourceDirichletOmittedSquareRemainder hp hp1) W ∧
      ∀ ψ ∈ W, ∀ n, sourceDirichletOmittedSquareRemainder hp hp1 ψ n =
        sourceDirichletOmittedSquareError hp hp1 ψ n := by
  obtain ⟨hv,ha⟩ := Coeff.analytic_realization_of_local_bounds
    (sourceDirichletOmittedSquareError hp hp1) H.original_theta_common_domain.source_open
    (fun n ψ hψ => ((H.dirichlet_omitted_sample_data ψ hψ n).2.pow 2).sub analyticAt_const)
    (by
      intro φ hφ
      obtain ⟨V,hV,hφV,hVW,B,_,hb⟩ := H.dirichlet_omitted_square_local_bound φ hφ
      refine ⟨V,hV,hφV,hVW,B,?_⟩
      intro ψ hψ
      refine ⟨sourceDirichletOmittedSquareRemainder hp hp1 ψ,?_,(hb ψ hψ).2⟩
      exact Coeff.ofFunctionOrZero_apply_of_mem p _ (hb ψ hψ).1)
  exact ⟨ha,hv⟩

end SourceLemma12_12Data
end NLS.ZakharovShabat
