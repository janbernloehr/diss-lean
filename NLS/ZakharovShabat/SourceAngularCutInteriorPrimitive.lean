import NLS.ComplexAnalysis.CosinePrimitiveSheetContinuation
import NLS.ZakharovShabat.SourceAngularPrimitiveCommonBoundary
import NLS.ZakharovShabat.SourceDeletedPairOmittedSquare

/-!
# Actual angular primitives at interior points of a periodic cut

Divide the prescribed full root by the literal `2i` times the omitted
standard-root product. Its square is the selected endpoint polynomial,
including on the cut. Cosine continuation then gives an analytic primitive
of the actual angular integrand on the prescribed sheet near the terminal.
The exterior matching formula retains the exact full-root sheet ratio.
-/

noncomputable section
open Set Filter Topology Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Continue the endpoint-normalized actual angular primitive through
an interior cut point on any prescribed regular full-root sheet. -/
theorem exists_sourceAngular_cutInterior_sheet_primitive
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ m)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (F : ℂ → ℂ)
    (hF : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ m,
      HasDerivAt F (sourceAngularIntegrand n s
        (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) z)
    (b : ℂ) (hb : b ∈ sourcePeriodicSegment hp hp1 ψ m)
    (hleft : b ≠ canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (hright : b ≠ canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (w : ℂ) (hw : w ≠ 0) (hbSheet : (b,ψ) ∈ sourceAngularRootSheetDomain hp w) :
    ∃ A : ℂ, ∃ B : Set ℂ, ∃ P : ℂ → ℂ,
      Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ m]
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)) (𝓝 A) ∧
      IsOpen B ∧ b ∈ B ∧ B ⊆ ball c R ∧
      (∀ z ∈ B, (z,ψ) ∈ sourceAngularRootSheetDomain hp w) ∧ AnalyticOnNhd ℂ P B ∧
      (∀ z ∈ B, HasDerivAt P (sourceAngularIntegrand n s (sourceAngularRootSheet hp w) (z,ψ)) z) ∧
      ∀ z ∈ B, z ∉ sourcePeriodicSegment hp hp1 ψ m →
        P z = (sourceCanonicalRoot hp hp1 ψ z/sourceAngularRootSheet hp w (z,ψ))*(F z-A) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let τ := (l+r)/2
  let δ := (r-l)/2
  have hl : τ-δ = l := by dsimp [τ,δ]; ring
  have hr : τ+δ = r := by dsimp [τ,δ]; ring
  have hδ : δ ≠ 0 := div_ne_zero (sub_ne_zero.mpr hgap.symm) (by norm_num)
  let K : ℂ → ℂ := fun z => 2*I*sourceStandardRootOmittedProduct hp hp1 m ψ z
  let Q : ℂ → ℂ := fun z => sourceAngularRootSheet hp w (z,ψ)/K z
  let Λ := ball c R ∩ (fun z : ℂ => (z,ψ)) ⁻¹' sourceAngularRootSheetDomain hp w
  have hΛ : IsOpen Λ := isOpen_ball.inter
    ((isOpen_sourceAngularRootSheetDomain hp hp1 w).preimage (by fun_prop))
  have hKne (z : ℂ) (hz : z ∈ ball c R) : K z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z m (hother (ball_subset_closedBall hz)))
  have hQanalytic : AnalyticOnNhd ℂ Q Λ := by
    intro z hz
    exact ((analyticOnNhd_sourceAngularRootSheet hp hp1 w (z,ψ) hz.2).comp
      (x := z) (f := fun u : ℂ => (u,ψ)) (analyticAt_id.prod analyticAt_const)).div
      (analyticAt_const.mul (hdata.analytic_omitted z (hother (ball_subset_closedBall hz.1))))
      (hKne z hz.1)
  have hQsq (z : ℂ) (hz : z ∈ Λ) : Q z^2 = (τ-δ-z)*(τ+δ-z) := by
    have hzD := hother (ball_subset_closedBall hz.1)
    dsimp only [Q,K]
    rw [div_pow,sourceAngularRootSheet_sq hp w hw,hl,hr]
    dsimp only [sourceAngularRadicand,l,r]
    rw [canonicalDiscriminant_sq_sub_four_eq_pair_mul hp hp1 _ (periodOnePotential_mem ψ) m z,
      ← sourceStandardRootOmittedProduct_sq_eq_canonicalDeletedPeriodicProduct hp hp1 ψ m z hzD]
    have hPne := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z m hzD
    rw [mul_pow,mul_pow,I_sq]
    field_simp
    ring
  obtain ⟨A,hA,_hAr⟩ := exists_sourceAngular_primitive_common_endpoint_limit
    hp hp1 n m s ψ c R hseg hother hdata hgap F hF
  obtain ⟨B,P,hB,hbB,hBsub,hP,hPd,hmatch⟩ := exists_gap_interior_regular_sheet_primitive
    (sourceAngularGapNumerator hp hp1 n m s ψ) (sourceStandardRoot hp hp1 ψ m) F Q
    (ball c R) Λ τ δ A b isOpen_ball hδ (by rw [hl,hr]; exact hseg)
    ((sourceAngularGapNumerator_analyticOnNhd hp hp1 n m s ψ hdata.analytic_omitted).mono
      (fun z hz => hother (ball_subset_closedBall hz)))
    (by
      rw [hl,hr]
      intro z hz
      exact (sourceStandardRoot_analyticAt hp hp1 ψ m z hz.2).continuousAt.continuousWithinAt)
    (by
      rw [hl,hr]
      intro z hz
      exact sourceStandardRoot_sq_of_not_mem_segment hp hp1 ψ m z hz.2)
    (by
      rw [hl,hr]
      intro z hz
      rw [← sourceAngularIntegrand_eq_gapNumerator_div_standardRoot hp hp1 n m s ψ z]
      exact hF z hz)
    (by rw [hl,hr]; exact hA) (by rw [hl,hr]; exact hb)
    (by simpa only [hl] using hleft) (by simpa only [hr] using hright)
    hΛ ⟨hseg hb,hbSheet⟩ hQanalytic hQsq
  refine ⟨A,B,P,hA,hB,hbB,fun z hz => (hBsub hz).1,
    fun z hz => (hBsub hz).2.2,hP,?_,?_⟩
  · intro z hz
    have heq : sourceAngularGapNumerator hp hp1 n m s ψ z/Q z =
        sourceAngularIntegrand n s (sourceAngularRootSheet hp w) (z,ψ) := by
      exact div_div_div_cancel_right₀ (hKne z (hBsub hz).1) _ _
    rw [← heq]
    exact hPd z hz
  · intro z hz hcut
    have hcut' : z ∉ segment ℝ (τ-δ) (τ+δ) := by rw [hl,hr]; exact hcut
    rw [hmatch z hz hcut']
    congr 1
    rw [sourceCanonicalRoot_eq_omitted hp hp1 m ψ z]
    dsimp only [Q,K]
    rw [div_div_eq_mul_div]
    ring

/-- On the interior of its own isolated gap, the actual Dirichlet
anti-discriminant is nonzero. This supplies the prescribed sheet value
without a separate regularity assumption. -/
theorem sourceDirichletAntiDiscriminant_ne_zero_at_gap_interior
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ m)
    (hb : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ sourcePeriodicSegment hp hp1 ψ m)
    (hl : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ≠
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (hr : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) :
    sourceAntiDiscriminantCandidate hp hp1 ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ≠ 0 := by
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  have hrad : sourceAngularRadicand hp (μ,ψ) ≠ 0 := by
    dsimp only [sourceAngularRadicand]
    rw [canonicalDiscriminant_sq_sub_four_eq_pair_mul hp hp1 _ (periodOnePotential_mem ψ) m μ]
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hl.symm)) (sub_ne_zero.mpr hr.symm))
      (canonicalDeletedPeriodicProduct_ne_zero_on_sourceOmittedDomain hp hp1 ψ m μ
        (hdata.gap_avoids_other_gaps hb))
  intro hzero
  apply hrad
  change canonicalDiscriminant hp (periodOnePotential ψ) μ^2-4 = 0
  rw [sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot hp hp1 ψ m,hzero]
  simp

namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual normalized psi family supplies exterior primitives and
their analytic continuations at every interior Dirichlet terminal. The
terminal sheet equals the actual anti-discriminant. No primitive, cosine
coordinate, root sheet, or nonzero terminal value is supplied by callers. -/
theorem exists_angular_dirichlet_cutInterior_primitives
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (hdata : ∀ m, SourceAngularEndpointSpectralData hp hp1 ψ m) :
    ∃ c : ℤ → ℂ, ∃ r R : ℤ → ℝ,
      (∀ m, 0 < r m ∧ r m < R m ∧
        sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) (r m) ∧
        closedBall (c m) (R m) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m) ∧
      ∀ n m, m ≠ n →
        canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
          canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m →
        let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
        let w := sourceAntiDiscriminantCandidate hp hp1 ψ μ
        μ ∈ sourcePeriodicSegment hp hp1 ψ m →
        μ ≠ canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m →
        μ ≠ canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m →
        ∃ F : ℂ → ℂ, ∃ A : ℂ, ∃ B : Set ℂ, ∃ P : ℂ → ℂ,
          (∀ z ∈ ball (c m) (R m) \ sourcePeriodicSegment hp hp1 ψ m,
            HasDerivAt F (sourceAngularIntegrand n s
              (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) z) ∧
          Tendsto F (𝓝[ball (c m) (R m) \ sourcePeriodicSegment hp hp1 ψ m]
            (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)) (𝓝 A) ∧
          IsOpen B ∧ μ ∈ B ∧ B ⊆ ball (c m) (R m) ∧
          (∀ z ∈ B, (z,ψ) ∈ sourceAngularRootSheetDomain hp w) ∧
          sourceAngularRootSheet hp w (μ,ψ) = w ∧ AnalyticOnNhd ℂ P B ∧
          (∀ z ∈ B, HasDerivAt P (sourceAngularIntegrand n s (sourceAngularRootSheet hp w) (z,ψ)) z) ∧
          ∀ z ∈ B, z ∉ sourcePeriodicSegment hp hp1 ψ m →
            P z = (sourceCanonicalRoot hp hp1 ψ z/sourceAngularRootSheet hp w (z,ψ))*(F z-A) := by
  obtain ⟨c,r,R,hgeom,hprim⟩ := hs.exists_angular_discComplement_primitives ψ hψ
  refine ⟨c,r,R,hgeom,?_⟩
  intro n m hmn hgap μ w hμ hl hr
  obtain ⟨F,hF⟩ := hprim n m hmn
  have hw : w ≠ 0 := sourceDirichletAntiDiscriminant_ne_zero_at_gap_interior hp hp1 ψ m
    (hdata m) hμ hl hr
  have hbase := sourceAngularRootSheet_dirichlet_base hp hp1 ψ m hw
  obtain ⟨A,B,P,hA,hB,hμB,hBsub,hBsheet,hP,hPd,hmatch⟩ :=
    exists_sourceAngular_cutInterior_sheet_primitive hp hp1 n m s ψ (c m) (R m)
      ((hgeom m).2.2.1.trans (ball_subset_ball (hgeom m).2.1.le))
      (hgeom m).2.2.2 (hdata m) hgap F hF μ hμ hl hr w hw hbase.1
  exact ⟨F,A,B,P,hF,hA,hB,hμB,hBsub,hBsheet,hbase.2,hP,hPd,hmatch⟩

end SourcePsiSquaredGapComplexExtension

end NLS.ZakharovShabat
