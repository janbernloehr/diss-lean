import NLS.ZakharovShabat.SourceAngularCanonicalCosinePrimitive
import NLS.ComplexAnalysis.DenseSegmentComplement
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Canonical cosine matching on every regular sheet point

Analytic continuation extends the exterior matching formula throughout
both halves of the convex angle chart. Density of the nonreal angles
then transfers it to every regular prescribed-sheet point, including
interior points of the canonical cut.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourceAngularCanonicalCosineChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {W V : Set (CoeffPair p)}
  {Ω : Set ℂ} {c : ℤ → ℂ} {R : ℤ → ℝ}

/-- The canonical exterior matching holds at every nonreal angle in
the constructed convex chart, without shrinking it source by source. -/
theorem spectral_matching_of_im_ne_zero
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (F : ℂ → ℂ) (A : ℂ)
    (hF : ∀ z ∈ ball (c m) (R m) \ sourcePeriodicSegment hp hp1 ψ m,
      HasDerivAt F (sourceAngularIntegrand n s
        (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) z)
    (hA : Tendsto F (𝓝[ball (c m) (R m) \ sourcePeriodicSegment hp hp1 ψ m]
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)) (𝓝 A))
    (θ : ℂ) (hθ : θ ∈ Ω) (hi : θ.im ≠ 0) :
    F (sourceCanonicalCosinePoint hp hp1 m (θ,ψ))-A =
      cosineRootCoefficient (sourceStandardRoot hp hp1 ψ m)
        (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
        (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m/2) θ *
        sourceAngularCanonicalCosinePrimitive hp hp1 n m s (θ,ψ) := by
  let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let δ := canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m/2
  let T := cosineGapPoint τ δ
  let H : ℂ → ℂ := fun e => sourceAngularCanonicalCosinePrimitive hp hp1 n m s (e,ψ)
  let f : ℂ → ℂ := fun e => F (T e)-A
  let g : ℂ → ℂ := fun e => cosineRootCoefficient (sourceStandardRoot hp hp1 ψ m) τ δ e*H e
  have hl : τ-δ = canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
    dsimp [τ,δ,canonicalPeriodicMidpoint,canonicalPeriodicGap]; ring
  have hr : τ+δ = canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
    dsimp [τ,δ,canonicalPeriodicMidpoint,canonicalPeriodicGap]; ring
  have hδ : δ ≠ 0 := div_ne_zero (D.gap_ne_zero ψ hψ) (by norm_num)
  have hT : AnalyticOnNhd ℂ T univ := fun _ _ =>
    analyticAt_const.add (analyticAt_const.mul Complex.analyticAt_cos)
  have hcut (e : ℂ) (he : e.im ≠ 0) : T e ∉ sourcePeriodicSegment hp hp1 ψ m := by
    change T e ∉ segment ℝ _ _
    rw [← hl,← hr]
    exact cosineGapPoint_not_mem_segment τ δ e hδ he
  have hFa : AnalyticOnNhd ℂ F (ball (c m) (R m) \ sourcePeriodicSegment hp hp1 ψ m) :=
    (show DifferentiableOn ℂ F _ from fun z hz =>
      (hF z hz).differentiableAt.differentiableWithinAt).analyticOnNhd
        (isOpen_ball.sdiff (isClosed_sourcePeriodicSegment hp hp1 ψ m))
  obtain ⟨U,hU,_,hangle,hUΩ,hmatch⟩ := D.spectral_matching ψ hψ n F A hF hA
  have extend (S : Set ℂ) (hS : IsOpen S) (hconv : Convex ℝ S) (hSΩ : S ⊆ Ω)
      (hSim : ∀ e ∈ S, e.im ≠ 0) (b : ℂ) (hbS : b ∈ S) (hbU : b ∈ U) : EqOn f g S := by
    have hf : AnalyticOnNhd ℂ f S := by
      intro e he
      exact ((hFa (T e) ⟨D.cosine_enclosed ψ hψ e (hSΩ he),hcut e (hSim e he)⟩).comp
        (hT e (mem_univ _))).sub analyticAt_const
    have hg : AnalyticOnNhd ℂ g S := by
      intro e he
      have hQ := (sourceStandardRoot_analyticAt hp hp1 ψ m (T e) (hcut e (hSim e he))).comp
        (hT e (mem_univ _))
      have hcoef : AnalyticAt ℂ (cosineRootCoefficient (sourceStandardRoot hp hp1 ψ m) τ δ) e :=
        (analyticAt_const.mul Complex.analyticAt_sin).div hQ
          (sourceStandardRoot_ne_zero_off_segment hp hp1 ψ m (T e) (hcut e (hSim e he)))
      exact hcoef.mul ((D.primitive_analytic n (e,ψ) ⟨hSΩ he,hψ⟩).comp
        (f := fun e : ℂ => (e,ψ)) (analyticAt_id.prod analyticAt_const))
    have heq : f =ᶠ[𝓝 b] g := by
      filter_upwards [hU.mem_nhds hbU,hS.mem_nhds hbS] with e heU heS
      exact hmatch e heU (hSim e heS)
    exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconv.isPreconnected hbS heq
  have hπU := hangle (right_mem_segment ℝ _ _)
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · have hπcl : (Real.pi:ℂ) ∈ closure {e : ℂ | e.im < 0} := by
      rw [Complex.closure_setOfPred_im_lt]; simp
    obtain ⟨b,hbU,hbhalf⟩ := mem_closure_iff.mp hπcl U hU hπU
    exact extend (Ω ∩ {e : ℂ | e.im < 0})
      (D.angle_open.inter (isOpen_lt Complex.continuous_im continuous_const))
      (D.angle_convex.inter (convex_halfSpace_im_lt 0)) inter_subset_left
      (fun e he => he.2.ne) b ⟨hUΩ hbU,hbhalf⟩ hbU ⟨hθ,hneg⟩
  · have hπcl : (Real.pi:ℂ) ∈ closure {e : ℂ | 0 < e.im} := by
      rw [Complex.closure_setOfPred_lt_im]; simp
    obtain ⟨b,hbU,hbhalf⟩ := mem_closure_iff.mp hπcl U hU hπU
    exact extend (Ω ∩ {e : ℂ | 0 < e.im})
      (D.angle_open.inter (isOpen_lt continuous_const Complex.continuous_im))
      (D.angle_convex.inter (convex_halfSpace_im_gt 0)) inter_subset_left
      (fun e he => he.2.ne') b ⟨hUΩ hbU,hbhalf⟩ hbU ⟨hθ,hpos⟩

/-- The full prescribed-sheet primitive equals the canonical joint
cosine primitive times its literal differential coefficient. The
formula includes real angles and points on the selected cut. -/
theorem sheet_matching
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (w : ℂ) (hw : w ≠ 0)
    (F E : ℂ → ℂ) (A : ℂ)
    (hE : SourceAngularSheetPrimitiveData hp hp1 n m s ψ (c m) (R m) w F A E)
    (θ : ℂ) (hθ : θ ∈ Ω)
    (hθsheet : (sourceCanonicalCosinePoint hp hp1 m (θ,ψ),ψ) ∈ sourceAngularRootSheetDomain hp w) :
    E (sourceCanonicalCosinePoint hp hp1 m (θ,ψ)) =
      ((-canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m/2 *
          Complex.sin θ) * (2*I*sourceStandardRootOmittedProduct hp hp1 m ψ
            (sourceCanonicalCosinePoint hp hp1 m (θ,ψ))) /
          sourceAngularRootSheet hp w (sourceCanonicalCosinePoint hp hp1 m (θ,ψ),ψ)) *
        sourceAngularCanonicalCosinePrimitive hp hp1 n m s (θ,ψ) := by
  let T : ℂ → ℂ := fun e => sourceCanonicalCosinePoint hp hp1 m (e,ψ)
  let K : ℂ → ℂ := fun z => 2*I*sourceStandardRootOmittedProduct hp hp1 m ψ z
  let δ := canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m/2
  let f : ℂ → ℂ := fun e => E (T e)
  let g : ℂ → ℂ := fun e => ((-δ*Complex.sin e)*K (T e)/sourceAngularRootSheet hp w (T e,ψ))*
    sourceAngularCanonicalCosinePrimitive hp hp1 n m s (e,ψ)
  let S := Ω ∩ T ⁻¹' sourceAngularRegularSheetDisc hp ψ (c m) (R m) w
  have hT : Continuous T := by
    change Continuous (fun e : ℂ => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m + δ*Complex.cos e)
    exact continuous_const.add (continuous_const.mul Complex.continuous_cos)
  have hS : IsOpen S := D.angle_open.inter
    ((isOpen_sourceAngularRegularSheetDisc hp hp1 ψ (c m) (R m) w).preimage hT)
  have hθS : θ ∈ S := ⟨hθ,D.cosine_enclosed ψ hψ θ hθ,hθsheet⟩
  have hf : ContinuousOn f S := hE.analytic_sheet.continuousOn.comp hT.continuousOn
    (fun _ he => he.2)
  have hg : ContinuousOn g S := by
    have hK : ContinuousOn (fun e => K (T e)) S := by
      have ha : AnalyticOnNhd ℂ K (ball (c m) (R m)) := by
        intro z hz
        exact analyticAt_const.mul ((D.endpoint_data ψ hψ).analytic_omitted z
          (((D.disc_family ψ hψ).contour_family.2 m).2.2.1 (ball_subset_closedBall hz)))
      exact ha.continuousOn.comp hT.continuousOn (fun _ he => he.2.1)
    have hQ : ContinuousOn (fun e => sourceAngularRootSheet hp w (T e,ψ)) S :=
      (analyticOnNhd_sourceAngularRootSheet hp hp1 w).continuousOn.comp
        (hT.prodMk continuous_const).continuousOn (fun _ he => he.2.2)
    have hH : ContinuousOn (fun e => sourceAngularCanonicalCosinePrimitive hp hp1 n m s (e,ψ)) S :=
      (D.primitive_analytic n).continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun _ he => ⟨he.1,hψ⟩)
    exact (((by fun_prop : ContinuousOn (fun e : ℂ => -δ*Complex.sin e) S).mul hK).div hQ
      (fun e he => sourceAngularRootSheet_ne_zero hp w hw (T e,ψ) he.2.2)).mul hH
  have hdense : Dense {e : ℂ | e.im ≠ 0} := by
    have heq : {e : ℂ | e.im ≠ 0} = Complex.im ⁻¹' {(0:ℝ)}ᶜ := by ext e; simp
    rw [heq]
    exact (dense_compl_singleton (0:ℝ)).preimage Complex.isOpenMap_im
  have heq : EqOn f g (S ∩ {e : ℂ | e.im ≠ 0}) := by
    intro e he
    have hcut : T e ∉ sourcePeriodicSegment hp hp1 ψ m := by
      have hl : canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m - δ =
          canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
        dsimp [δ,canonicalPeriodicMidpoint,canonicalPeriodicGap]; ring
      have hr : canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m + δ =
          canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
        dsimp [δ,canonicalPeriodicMidpoint,canonicalPeriodicGap]; ring
      change T e ∉ segment ℝ _ _
      rw [← hl,← hr]
      exact cosineGapPoint_not_mem_segment _ δ e (div_ne_zero (D.gap_ne_zero ψ hψ) (by norm_num)) he.2
    have hQne := sourceStandardRoot_ne_zero_off_segment hp hp1 ψ m (T e) hcut
    have hfullne := sourceAngularRootSheet_ne_zero hp w hw (T e,ψ) he.1.2.2
    have hmatch := D.spectral_matching_of_im_ne_zero ψ hψ n F A hE.hasDerivAt_exterior
      hE.tendsto_left_exterior e he.1.1 he.2
    have hvalue := hE.eqOn_exterior ⟨he.1.2,hcut⟩
    change E (T e) = (sourceCanonicalRoot hp hp1 ψ (T e)/sourceAngularRootSheet hp w (T e,ψ))*(F (T e)-A) at hvalue
    have hcanonical : sourceCanonicalRoot hp hp1 ψ (T e) = K (T e)*sourceStandardRoot hp hp1 ψ m (T e) := by
      rw [sourceCanonicalRoot_eq_omitted hp hp1 m ψ (T e)]
      dsimp only [K]
      ring
    dsimp only [f,g]
    rw [hvalue,hmatch,hcanonical]
    change ((K (T e)*sourceStandardRoot hp hp1 ψ m (T e))/sourceAngularRootSheet hp w (T e,ψ))*
      ((-δ*Complex.sin e)/sourceStandardRoot hp hp1 ψ m (T e)*
        sourceAngularCanonicalCosinePrimitive hp hp1 n m s (e,ψ)) = _
    field_simp [hQne,hfullne]
  simpa only [f,g,T,K,δ,neg_div] using
    continuous_eqOn_of_dense_on_open _ S hdense hS f g hf hg heq hθS

end SourceAngularCanonicalCosineChartData
end NLS.ZakharovShabat
