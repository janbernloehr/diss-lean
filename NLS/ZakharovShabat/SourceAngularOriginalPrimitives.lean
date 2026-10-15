import NLS.ZakharovShabat.SourceAngularOriginalDomain
import NLS.ZakharovShabat.SourceAngularEtaRemainderChoiceIndependence

/-!
# Angular primitives on every original isolating disk

The original contour normalization constructs both off-diagonal
primitives and diagonal model-remainder primitives on any supplied
original circle's full cut disk. The two periodic boundary values agree;
normalization and gluing then give the prescribed-sheet data used by the
endpoint path integrals. The source domain and psi maps are unchanged.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A smaller original circle still encloses the selected gap. -/
private theorem exists_inner_original_circle
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {m : ℤ}
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m) :
    ∃ r : ℝ, 0 < r ∧ r < P.radius ∧
      sourcePeriodicSegment hp hp1 ψ m ⊆ ball (P.center:ℂ) r ∧
      ∃ Q : SourceCriticalRootPeriodCircle hp hp1 ψ m,
        Q.center = P.center ∧ Q.radius = r := by
  obtain ⟨r,ρ,hr,hrρ,hρR,hseg⟩ := exists_nested_radii_of_segment_subset_ball
    (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (P.center:ℂ) P.radius P.gap
  have hrR := hrρ.trans hρR
  refine ⟨r,hr,hrR,hseg,⟨P.center,r,hr,hseg,?_⟩,rfl,rfl⟩
  intro k hk z hz
  rcases P.other k hk z hz with hl | hu
  · left; linarith
  · right; linarith

namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Zero original periods give a primitive on the entire original cut disk. -/
theorem angular_original_primitive (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m) :
    ∃ F : ℂ → ℂ, ∀ z ∈ ball (P.center:ℂ) P.radius \ sourcePeriodicSegment hp hp1 ψ m,
      HasDerivAt F (sourceAngularIntegrand n s
        (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)) z := by
  obtain ⟨r,hr,hrR,hseg,Q,hc,hR⟩ := exists_inner_original_circle P
  have hzero : sourcePsiContour hp hp1 n (s n ψ : Coeff p) ψ (P.center:ℂ) r = 0 := by
    simpa only [hc,hR,if_neg hmn] using H.previous.previous.psi.period ψ hψ n m Q
  obtain ⟨G,hG⟩ := sourceAngular_exists_annulus_primitive hp hp1 n m s ψ _ r P.radius
    hr hrR hseg P.closedBall_subset_omittedDomain hzero
  have hclosed : IsClosed (sourcePeriodicSegment hp hp1 ψ m) := by
    apply IsCompact.isClosed
    change IsCompact (segment ℝ _ _)
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hmid := sourcePeriodicMidpoint_mem_segment hp hp1 ψ m
  obtain ⟨F,_,hF⟩ := exists_primitive_on_disc_complement_of_annular_primitive
    _ G (P.center:ℂ) (sourceStandardRootMidpoint hp hp1 ψ m) r P.radius hr.le hrR
    (sourcePeriodicSegment hp hp1 ψ m) hclosed hmid ((convex_segment _ _).starConvex hmid) hseg
    (sourceAngular_discComplement_analyticOnNhd hp hp1 n m s ψ _ _
      P.closedBall_subset_omittedDomain) hG
  exact ⟨F,hF⟩

/-- The normalized diagonal period removes exactly the explicit eta model. -/
theorem eta_original_remainder_primitive (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ n) :
    ∃ F : ℂ → ℂ, ∀ z ∈ ball (P.center:ℂ) P.radius \ sourcePeriodicSegment hp hp1 ψ n,
      HasDerivAt F (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ z) z := by
  obtain ⟨r,hr,hrR,hseg,Q,hc,hR⟩ := exists_inner_original_circle P
  apply sourceAngularEtaRemainder_exists_discComplement_primitive hp hp1 n s ψ _ r P.radius
    hr hrR hseg P.closedBall_subset_omittedDomain
  simpa only [hc,hR,ite_true] using H.previous.previous.psi.period ψ hψ n n Q

/-- Off-diagonal primitive data on any original disk and any regular terminal sheet. -/
theorem angular_original_sheet_primitive (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (w : ℂ) (hw : w ≠ 0) :
    ∃ F : ℂ → ℂ, ∃ A : ℂ, ∃ E : ℂ → ℂ,
      SourceAngularSheetPrimitiveData hp hp1 n m s ψ (P.center:ℂ) P.radius w F A E := by
  obtain ⟨F,hF⟩ := H.angular_original_primitive ψ hψ n m hmn P
  have hd := H.angular_endpoint_data ψ hψ m
  obtain ⟨A,E,hA,hEa,hEd,hEl,hEr,hmatch,_⟩ := exists_sourceAngular_glued_sheet_primitive
    hp hp1 n m s ψ _ _ P.gap P.closedBall_subset_omittedDomain hd hgap F hF w hw
  exact ⟨F,A,E,⟨hF,hA,hEa,hEd,hEl,hEr,hmatch⟩⟩

/-- Diagonal remainder data on any original disk, normalized at both endpoints. -/
theorem eta_original_sheet_primitive (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ n)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
    (w : ℂ) (hw : w ≠ 0) :
    ∃ F E : ℂ → ℂ,
      SourceAngularEtaRemainderSheetPrimitiveData hp hp1 n s ψ (P.center:ℂ) P.radius w F E := by
  obtain ⟨G,hG⟩ := H.eta_original_remainder_primitive ψ hψ n P
  have hd := H.angular_endpoint_data ψ hψ n
  obtain ⟨A,hA,hB⟩ := exists_sourceAngularEtaRemainder_primitive_common_endpoint_limit hp hp1 n s ψ
    _ _ P.gap P.closedBall_subset_omittedDomain hd hgap G hG
  let F : ℂ → ℂ := fun z => G z-A
  have hF : ∀ z ∈ ball (P.center:ℂ) P.radius \ sourcePeriodicSegment hp hp1 ψ n,
      HasDerivAt F (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ z) z :=
    fun z hz => (hG z hz).sub_const A
  have hl : Tendsto F (𝓝[ball (P.center:ℂ) P.radius \ sourcePeriodicSegment hp hp1 ψ n]
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) (𝓝 0) := by
    simpa only [sub_self] using hA.sub (tendsto_const_nhds (x := A))
  have hr : Tendsto F (𝓝[ball (P.center:ℂ) P.radius \ sourcePeriodicSegment hp hp1 ψ n]
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) (𝓝 0) := by
    simpa only [sub_self] using hB.sub (tendsto_const_nhds (x := A))
  obtain ⟨E,hEa,hEd,hEl,hEr,hmatch,_⟩ := exists_sourceAngularEta_glued_remainder_sheet_primitive
    hp hp1 n s ψ _ _ P.gap P.closedBall_subset_omittedDomain hd hgap F hF hl hr w hw
  exact ⟨F,E,⟨hF,hl,hr,hEa,hEd,hEl,hEr,hmatch⟩⟩

end SourceLemma12_12Data
end NLS.ZakharovShabat
