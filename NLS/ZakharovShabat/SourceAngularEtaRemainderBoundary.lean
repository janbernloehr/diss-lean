import NLS.ZakharovShabat.SourceAngularEtaRemainderPrimitive
import NLS.ZakharovShabat.SourceAngularPrimitiveCommonBoundary
import NLS.ComplexAnalysis.PrimitiveBoundaryPathIntegral

/-!
# Equal endpoint limits of the diagonal eta remainder

The regular remainder numerator is analytic across a noncollapsed
complex gap. A weighted square-root bound gives common limits of its
spectral primitive at both endpoints. The cosine comparison proves
that these limits agree, so the primitive can be normalized to zero
at both endpoints, just as for the off-diagonal angular terms.
-/

noncomputable section
open Set Filter Topology Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A common endpoint bound for the actual diagonal remainder,
derived from its analytic numerator and the selected-root estimate. -/
theorem exists_sourceAngularEtaRemainder_endpoint_weighted_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ n)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
    ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧
      ∀ a ∈ ({l,r} : Set ℂ), ∀ z : ℂ,
        z ∉ sourcePeriodicSegment hp hp1 ψ n →
        ‖a-z‖ ≤ ε →
        ‖sourceAngularEtaRemainderIntegrand hp hp1 n s ψ z *
          (Real.sqrt ((‖r-l‖/2)*‖a-z‖) : ℂ)‖ ≤ M := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let S := sourcePeriodicSegment hp hp1 ψ n
  let g : ℂ → ℂ := fun z => sourceAngularGapNumerator hp hp1 n n s ψ z-Complex.I
  have hS : IsCompact S := by
    change IsCompact (segment ℝ l r)
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  obtain ⟨ε₀,hε₀,hthick⟩ := hS.exists_cthickening_subset_open
    hdata.isOpen_omitted hdata.gap_avoids_other_gaps
  have hg : AnalyticOnNhd ℂ g (sourceStandardRootOmittedDomain hp hp1 ψ n) :=
    (sourceAngularGapNumerator_analyticOnNhd hp hp1 n n s ψ hdata.analytic_omitted).sub analyticOnNhd_const
  obtain ⟨C,hC⟩ := hS.cthickening.exists_bound_of_continuousOn (hg.continuousOn.mono hthick)
  let M := max C 0+1
  have hM : 0 < M := by dsimp [M]; positivity
  let δ := ‖r-l‖/2
  have hδ : 0 < δ := div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hgap.symm)) (by norm_num)
  refine ⟨min ε₀ δ,M,lt_min hε₀ hδ,hM,?_⟩
  intro a ha z hz hnear
  have haS : a ∈ S := by
    simp only [mem_insert_iff,mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _
  have hzK : z ∈ cthickening ε₀ S :=
    Metric.mem_cthickening_of_dist_le z a ε₀ S haS (by
      rw [dist_eq_norm,norm_sub_rev]
      exact hnear.trans (min_le_left _ _))
  have hbound : ‖g z‖ ≤ M :=
    (hC z hzK).trans (by dsimp [M]; linarith [le_max_left C 0])
  have hroot : Real.sqrt (δ*‖a-z‖) ≤ ‖sourceStandardRoot hp hp1 ψ n z‖ :=
    sourceStandardRoot_complexEndpoint_norm_lower_bound hp hp1 ψ n a z ha hz
      (hnear.trans (min_le_right _ _))
  rw [sourceAngularEtaRemainderIntegrand_eq_gapNumerator]
  exact norm_div_mul_real_le_of_weight_le_norm _ _ _ M
    (Real.sqrt_nonneg _) hM.le hbound hroot
    (sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z hz)

/-- Every spectral remainder primitive has one common limit at
each endpoint, for all approaches inside the cut complement. -/
theorem exists_sourceAngularEtaRemainder_primitive_endpoint_limits
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ n)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
    (F : ℂ → ℂ)
    (hF : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ n,
      HasDerivAt F (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ z) z) :
    ∃ A B : ℂ,
      Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ n]
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) (𝓝 A) ∧
      Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ n]
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) (𝓝 B) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let f := sourceAngularEtaRemainderIntegrand hp hp1 n s ψ
  let D := ball c R \ sourcePeriodicSegment hp hp1 ψ n
  obtain ⟨ε,M,hε,hM,hweighted⟩ := exists_sourceAngularEtaRemainder_endpoint_weighted_bound
    hp hp1 n s ψ hdata hgap
  let δ := ‖r-l‖/2
  have hδ : 0 < δ := div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hgap.symm)) (by norm_num)
  have hb (a : ℂ) (ha : a ∈ ({l,r} : Set ℂ)) (z : ℂ) (hz : z ∈ D)
      (hnear : ‖z-a‖ ≤ ε) : ‖f z * (Real.sqrt (δ*‖z-a‖) : ℂ)‖ ≤ M := by
    have h := hweighted a ha z hz.2 (by rwa [norm_sub_rev])
    simpa only [f,δ,l,r,norm_sub_rev] using h
  have hf : ContinuousOn f D :=
    (sourceAngularEtaRemainderIntegrand_analyticOnNhd hp hp1 n s ψ c R hother).continuousOn.mono
      (fun _ hz => ⟨ball_subset_closedBall hz.1,hz.2⟩)
  obtain ⟨A,hA⟩ := exists_primitive_segment_left_boundary_limit f F (ball c R) l r δ M ε
    isOpen_ball (hseg (left_mem_segment ℝ _ _)) hgap hδ hM.le hε hf hF (hb l (by simp))
  obtain ⟨B,hB⟩ := exists_primitive_segment_right_boundary_limit f F (ball c R) l r δ M ε
    isOpen_ball (hseg (right_mem_segment ℝ _ _)) hgap hδ hM.le hε hf hF (hb r (by simp))
  exact ⟨A,B,hA,hB⟩

/-- The two endpoint limits of a single-valued remainder primitive
agree, also when the gap segment is nonreal. -/
theorem exists_sourceAngularEtaRemainder_primitive_common_endpoint_limit
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ n)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
    (F : ℂ → ℂ)
    (hF : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ n,
      HasDerivAt F (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ z) z) :
    ∃ A : ℂ,
      Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ n]
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) (𝓝 A) ∧
      Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ n]
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) (𝓝 A) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let τ := (l+r)/2
  let δ := (r-l)/2
  have hl : τ-δ = l := by dsimp [τ,δ]; ring
  have hr : τ+δ = r := by dsimp [τ,δ]; ring
  have hδ : δ ≠ 0 := div_ne_zero (sub_ne_zero.mpr hgap.symm) (by norm_num)
  obtain ⟨A,B,hA,hB⟩ := exists_sourceAngularEtaRemainder_primitive_endpoint_limits
    hp hp1 n s ψ c R hseg hother hdata hgap F hF
  have hab : A = B := by
    apply primitive_cosine_gap_boundary_values_eq
      (fun z => sourceAngularGapNumerator hp hp1 n n s ψ z-Complex.I)
      (sourceStandardRoot hp hp1 ψ n) F (ball c R) τ δ A B isOpen_ball hδ
    · rw [hl,hr]; exact hseg
    · exact ((sourceAngularGapNumerator_analyticOnNhd hp hp1 n n s ψ hdata.analytic_omitted).sub
        analyticOnNhd_const).mono (fun z hz => hother (ball_subset_closedBall hz))
    · rw [hl,hr]
      intro z hz
      exact (sourceStandardRoot_analyticAt hp hp1 ψ n z hz.2).continuousAt.continuousWithinAt
    · rw [hl,hr]
      intro z hz
      exact sourceStandardRoot_sq_of_not_mem_segment hp hp1 ψ n z hz.2
    · rw [hl,hr]
      intro z hz
      rw [← sourceAngularEtaRemainderIntegrand_eq_gapNumerator]
      exact hF z hz
    · rw [hl,hr]; exact hA
    · rw [hl,hr]; exact hB
  exact ⟨A,hA,hab.symm ▸ hB⟩

/-- The same model/remainder splitting holds for integrable paths
with singular endpoints. Only the primitive's relative boundary
values enter the remainder; no winding or homotopy assumption is needed. -/
theorem sourceAngularEta_pathIntegral_decomposition_of_boundary_values
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (D : Set ℂ) (F : ℂ → ℂ)
    (hF : ∀ z ∈ D, HasDerivAt F (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ z) z)
    {a b A B : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ D)
    (hint : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ))) γ)
    (hmodel : CurveIntegrable (holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ)) γ)
    (hA : Tendsto F (𝓝[D] a) (𝓝 A)) (hB : Tendsto F (𝓝[D] b) (𝓝 B)) :
    sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ =
      (∫ᶜ z in γ, holomorphicOneForm (sourceAngularEtaModelIntegrand hp hp1 n ψ) z) + (B-A) := by
  let f : ℂ → ℂ := fun z => sourceAngularIntegrand n s
    (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)
  let M := sourceAngularEtaModelIntegrand hp hp1 n ψ
  have hω : holomorphicOneForm (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ) =
      holomorphicOneForm f-holomorphicOneForm M := by
    funext z
    exact sub_smul (f z) (M z) (ContinuousLinearMap.id ℂ ℂ)
  have hremInt : CurveIntegrable
      (holomorphicOneForm (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ)) γ := by
    rw [hω]
    exact hint.sub hmodel
  have hrem := curveIntegral_eq_sub_of_primitive_boundary_ends _ F D hF γ hγ hγD hremInt hA hB
  rw [hω,curveIntegral_sub hint hmodel] at hrem
  change (∫ᶜ z in γ, holomorphicOneForm f z) = (∫ᶜ z in γ, holomorphicOneForm M z) + (B-A)
  exact sub_eq_iff_eq_add.mp hrem |>.trans (add_comm _ _)

namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- At every complex source the actual diagonal remainder admits a
spectral primitive normalized to zero at both ends of each open gap. -/
theorem exists_eta_remainder_normalized_endpoint_primitives
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (hdata : ∀ n, SourceAngularEndpointSpectralData hp hp1 ψ n) :
    ∃ c : ℤ → ℂ, ∃ r R : ℤ → ℝ,
      (∀ n, 0 < r n ∧ r n < R n ∧
        sourcePeriodicSegment hp hp1 ψ n ⊆ ball (c n) (r n) ∧
        closedBall (c n) (R n) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) ∧
      ∀ n, canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠
          canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n →
        ∃ F : ℂ → ℂ,
          (∀ z ∈ ball (c n) (R n) \ sourcePeriodicSegment hp hp1 ψ n,
            HasDerivAt F (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ z) z) ∧
          Tendsto F (𝓝[ball (c n) (R n) \ sourcePeriodicSegment hp hp1 ψ n]
            (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) (𝓝 0) ∧
          Tendsto F (𝓝[ball (c n) (R n) \ sourcePeriodicSegment hp hp1 ψ n]
            (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) (𝓝 0) := by
  obtain ⟨c,r,R,hgeom,hprim⟩ := hs.exists_eta_remainder_discComplement_primitives ψ hψ
  refine ⟨c,r,R,hgeom,?_⟩
  intro n hgap
  obtain ⟨G,hG⟩ := hprim n
  obtain ⟨A,hA,hB⟩ := exists_sourceAngularEtaRemainder_primitive_common_endpoint_limit hp hp1 n s ψ
    (c n) (R n) ((hgeom n).2.2.1.trans (ball_subset_ball (hgeom n).2.1.le))
    (hgeom n).2.2.2 (hdata n) hgap G hG
  refine ⟨fun z => G z-A,fun z hz => (hG z hz).sub_const A,?_,?_⟩
  · simpa only [sub_self] using hA.sub (tendsto_const_nhds (x := A))
  · simpa only [sub_self] using hB.sub (tendsto_const_nhds (x := A))

end SourcePsiSquaredGapComplexExtension
end NLS.ZakharovShabat
