import NLS.ZakharovShabat.SourceAngularOriginalPrimitives

/-!
# Original-disk angular primitives including collapsed gaps

At a collapsed gap the actual off-diagonal numerator cancels the
selected root. Integrating its removable extension gives a primitive
on the full disk. Its regular-sheet values satisfy the same normalized
primitive interface as an open gap, so later path comparisons need no
noncollapse restriction on beta.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual removable extension has a primitive on the full original disk. -/
theorem angular_collapsed_original_primitive (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m) :
    ∃ F : ℂ → ℂ, ∀ z ∈ ball (P.center:ℂ) P.radius,
      HasDerivAt F (sourceAngularCollapsedIntegrand hp hp1 n m s ψ z) z := by
  apply exists_primitive_on_convex _ _ (convex_ball _ _) isOpen_ball
  exact ((sourceAngularCollapsedIntegrand_analyticOnNhd hp hp1 n m s ψ
    (H.angular_endpoint_data ψ hψ m)).mono
      (fun _ hz => P.closedBall_subset_omittedDomain (ball_subset_closedBall hz))).differentiableOn

/-- Periodic endpoint values agree on every original disk, including a collapsed gap. -/
theorem angular_original_endpoint_primitive (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m) :
    ∃ F : ℂ → ℂ, ∃ A : ℂ,
      (∀ z ∈ ball (P.center:ℂ) P.radius \ sourcePeriodicSegment hp hp1 ψ m,
        HasDerivAt F (sourceAngularIntegrand n s
          (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) z) ∧
      Tendsto F (𝓝[ball (P.center:ℂ) P.radius \ sourcePeriodicSegment hp hp1 ψ m]
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)) (𝓝 A) ∧
      Tendsto F (𝓝[ball (P.center:ℂ) P.radius \ sourcePeriodicSegment hp hp1 ψ m]
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)) (𝓝 A) := by
  by_cases hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m =
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  · obtain ⟨F,hF⟩ := H.angular_collapsed_original_primitive ψ hψ n m P
    have hg : sourcePeriodicGapDisplacement hp hp1 ψ m = 0 := by
      simp only [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap,hgap,sub_self]
    refine ⟨F,F (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m),?_,?_,?_⟩
    · intro z hz
      rw [H.angular_extension.angular_collapsed_integrand_eq_canonical ψ hψ n m hmn hg z (by
        intro k
        by_cases hk : k = m
        · subst k; exact hz.2
        · exact P.closedBall_subset_omittedDomain (ball_subset_closedBall hz.1) k hk)]
      exact hF z hz.1
    · exact (hF _ (P.gap (left_mem_segment ℝ _ _))).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · rw [← hgap]
      exact (hF _ (P.gap (left_mem_segment ℝ _ _))).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · obtain ⟨F,hF⟩ := H.angular_original_primitive ψ hψ n m hmn P
    obtain ⟨A,hA,hB⟩ := exists_sourceAngular_primitive_common_endpoint_limit hp hp1 n m s ψ
      _ _ P.gap P.closedBall_subset_omittedDomain (H.angular_endpoint_data ψ hψ m) hgap F hF
    exact ⟨F,A,hF,hA,hB⟩

/-- The same prescribed-sheet interface is available even when the selected gap collapses. -/
theorem angular_original_sheet_primitive_all_gaps (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m) (w : ℂ) (hw : w ≠ 0) :
    ∃ F : ℂ → ℂ, ∃ A : ℂ, ∃ E : ℂ → ℂ,
      SourceAngularSheetPrimitiveData hp hp1 n m s ψ (P.center:ℂ) P.radius w F A E := by
  by_cases hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m =
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  · obtain ⟨F,A,hF,hA,hB⟩ := H.angular_original_endpoint_primitive ψ hψ n m hmn P
    let Λ := sourceAngularRegularSheetDisc hp ψ (P.center:ℂ) P.radius w
    have hopen : IsOpen Λ := isOpen_sourceAngularRegularSheetDisc hp hp1 ψ _ _ w
    have hcan (z : ℂ) (hz : z ∈ Λ) : z ∈ sourceCanonicalRootDomain hp hp1 ψ := by
      intro k
      by_cases hk : k = m
      · subst k
        have hne := (sourceAngularRootSheet_point_ne_periodic_endpoints hp hp1 ψ m w z hw hz.2).1
        simpa only [sourcePeriodicSegment,← hgap,segment_same,mem_singleton_iff] using hne
      · exact P.closedBall_subset_omittedDomain (ball_subset_closedBall hz.1) k hk
    have hQ : ContinuousOn (sourceCanonicalRoot hp hp1 ψ) Λ :=
      fun z hz => (sourceCanonicalRoot_analyticOnNhd hp hp1 ψ z (hcan z hz)).continuousAt.continuousWithinAt
    have hR : ContinuousOn (fun z : ℂ => sourceAngularRootSheet hp w (z,ψ)) Λ := by
      intro z hz
      exact ((analyticOnNhd_sourceAngularRootSheet hp hp1 w (z,ψ) hz.2).comp (x := z) (f := fun u : ℂ => (u,ψ))
        (analyticAt_id.prod analyticAt_const)).continuousAt.continuousWithinAt
    have hsq (z : ℂ) (hz : z ∈ Λ) :
        sourceCanonicalRoot hp hp1 ψ z ^ 2 = sourceAngularRootSheet hp w (z,ψ) ^ 2 :=
      (sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four hp hp1 ψ z (hcan z hz)).trans
        (sourceAngularRootSheet_sq hp w hw (z,ψ)).symm
    have hne (z : ℂ) (hz : z ∈ Λ) : sourceAngularRootSheet hp w (z,ψ) ≠ 0 :=
      sourceAngularRootSheet_ne_zero hp w hw (z,ψ) hz.2
    have hFd (z : ℂ) (hz : z ∈ Λ) :
        HasDerivAt F (sourcePsiCandidate n (z,(s n ψ:Coeff p))/sourceCanonicalRoot hp hp1 ψ z) z :=
      hF z ⟨hz.1,hcan z hz m⟩
    let E := sourceAngularExteriorPrimitive hp hp1 ψ w F A
    have hEd : ∀ z ∈ Λ, HasDerivAt E
        (sourceAngularIntegrand n s (sourceAngularRootSheet hp w) (z,ψ)) z :=
      rootRatioPrimitive_hasDerivAt _ _ _ F Λ A hopen hQ hR hsq hne hFd
    have hEa : AnalyticOnNhd ℂ E Λ :=
      rootRatioPrimitive_analyticOnNhd _ _ _ F Λ A hopen hQ hR hsq hne hFd
    have hmatch : EqOn E (sourceAngularExteriorPrimitive hp hp1 ψ w F A)
        (Λ \ sourcePeriodicSegment hp hp1 ψ m) := fun _ _ => rfl
    refine ⟨F,A,E,⟨hF,hA,hEa,hEd,?_,?_,hmatch⟩⟩
    · exact sourceAngular_glued_sheet_boundary_zero hp hp1 ψ m _ _ w hw
        P.closedBall_subset_omittedDomain F E A _ hEa.continuousOn hmatch hA
    · exact sourceAngular_glued_sheet_boundary_zero hp hp1 ψ m _ _ w hw
        P.closedBall_subset_omittedDomain F E A _ hEa.continuousOn hmatch hB
  · exact H.angular_original_sheet_primitive ψ hψ n m hmn P hgap w hw

end SourceLemma12_12Data
end NLS.ZakharovShabat
