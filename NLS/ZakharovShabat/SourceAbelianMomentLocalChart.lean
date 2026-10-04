import NLS.ZakharovShabat.SourceAbelianMomentCircleAnalytic
import NLS.ZakharovShabat.SourceAbelianMomentLocalVanishing
import NLS.ZakharovShabat.SourceAbelianMomentRealContourComparison

/-! # Simultaneous local charts for all normalized moments

One real-centered source ball and one fixed family of isolating circles
support every numerator index, integration index and moment order.
All four identities of Lemma 20.1 hold on each such ball.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure SourceAbelianMomentLocalChart (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n)
    (φ : realTypeSourceLocus p) where
  radius : ℝ
  radius_pos : 0 < radius
  center : ℤ → ℂ
  contourRadius : ℤ → ℝ
  family : ∀ ψ ∈ ball φ.val radius,
    sourcePsiRealCenteredContourFamily hp hp1 ψ center contourRadius
  charts : ∀ ψ ∈ ball φ.val radius, Nonempty (SourceAbelianSpectralChart hp hp1 W ψ)
  analytic : ∀ (n k : ℤ) (m : ℕ), AnalyticOnNhd ℂ
    (fun ψ => sourceAbelianMomentCircle hp hp1 W n k m (s n ψ : Coeff p) ψ (center k) (contourRadius k))
    (ball φ.val radius)
  zero_order : ∀ ψ ∈ ball φ.val radius, ∀ n k : ℤ,
    sourceAbelianMomentCircle hp hp1 W n k 0 (s n ψ : Coeff p) ψ (center k) (contourRadius k) =
      (2*Real.pi : ℂ)*(if k = n then 1 else 0)
  odd : ∀ ψ ∈ ball φ.val radius, ∀ (n k : ℤ) (l : ℕ),
    sourceAbelianMomentCircle hp hp1 W n k (2*l+1) (s n ψ : Coeff p) ψ (center k) (contourRadius k) = 0
  collapsed : ∀ ψ ∈ ball φ.val radius, ∀ (n k : ℤ),
    canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k = 0 →
    ∀ m : ℕ, sourceAbelianMomentCircle hp hp1 W n k (m+1)
      (s n ψ : Coeff p) ψ (center k) (contourRadius k) = 0

/-- Construct simultaneous moment charts for a specified normalized
psi extension. This also permits retaining the stronger squared-gap
extension used in Lemma 20.3 and Theorem 20.4. -/
theorem SourcePsiNormalizedComplexExtension.exists_moment_localCharts
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (hs : SourcePsiNormalizedComplexExtension hp hp1 V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ : realTypeSourceLocus p, ∃ L : SourceAbelianMomentLocalChart hp hp1 W s φ,
        ball φ.val L.radius ⊆ V := by
  classical
  obtain ⟨W,hW,hrealW,hC⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  obtain ⟨P,hP,_,hrealP,hPdata⟩ := exists_global_sourcePsiContourIntegrand_jointAnalytic hp hp1
  obtain ⟨O,hO,_,hrealO,hOdata⟩ := exists_global_source_analytic_omittedJointProduct hp hp1
  refine ⟨W,hW,hrealW,?_⟩
  intro φ
  obtain ⟨C,hCφ⟩ := hC ⟨φ.val,φ.property⟩
  have hφC : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hCφ]
    exact mem_ball_self C.discs.sourceRadius_pos
  obtain ⟨δ,hδ,hsub⟩ := Metric.isOpen_iff.mp
    (hV.inter (hP.inter (hO.inter isOpen_ball))) φ.val
    ⟨hrealV φ.property,hrealP φ.property,hrealO φ.property,hφC⟩
  let U := ball φ.val δ
  have hUV : U ⊆ V := fun _ h => (hsub h).1
  have hUP : U ⊆ P := fun _ h => (hsub h).2.1
  have hUO : U ⊆ O := fun _ h => (hsub h).2.2.1
  have hUC : U ⊆ ball C.discs.source.val C.discs.sourceRadius := fun _ h => (hsub h).2.2.2
  let R : ℤ → ℝ := fun k => (C.discs.inner k+C.discs.outer k)/2
  have hinner (k : ℤ) : C.discs.inner k ≤ R k := by dsimp [R]; linarith [C.discs.inner_lt k]
  have houter (k : ℤ) : R k < C.discs.outer k := by dsimp [R]; linarith [C.discs.inner_lt k]
  have hR (k : ℤ) : 0 < R k := (C.discs.inner_pos k).trans_le (hinner k)
  have hfamily (ψ : CoeffPair p) (hψ : ψ ∈ U) :
      sourcePsiRealCenteredContourFamily hp hp1 ψ C.discs.center R := by
    refine ⟨C.discs.center_real,fun k => ⟨hR k,?_,?_,?_⟩⟩
    · exact (C.discs.segment_subset ψ (hUC hψ) k).trans (ball_subset_ball (hinner k))
    · exact (closedBall_subset_closedBall (houter k).le).trans (C.discs.avoids_other ψ (hUC hψ) k)
    · exact C.intermediate_circle_root k ψ (hUC hψ) (R k) (hinner k) (houter k)
  have hD : IsOpen (sourcePsiContourJointDomain hp hp1 U) := by
    have he : sourcePsiContourJointDomain hp hp1 U =
        sourcePsiContourJointDomain hp hp1 P ∩
          (fun t : ℂ × (Coeff p × CoeffPair p) => t.2.2) ⁻¹' U := by
      ext t
      constructor
      · intro ht
        exact ⟨⟨hUP ht.1,ht.2⟩,ht.1⟩
      · intro ht
        exact ⟨ht.2,ht.1.2⟩
    rw [he]
    exact (hPdata 0).1.inter (isOpen_ball.preimage (continuous_snd.comp continuous_snd))
  have hF (k : ℤ) : AnalyticOnNhd ℂ (sourceFullAbelianPrimitive hp hp1 W k)
      (sourceCanonicalRootJointDomain hp hp1 U) :=
    (C.full_analytic k).mono (fun _ ht => ⟨hUC ht.1,ht.2⟩)
  have hPsi (n : ℤ) : AnalyticOnNhd ℂ (sourcePsiContourIntegrandJoint hp hp1 n)
      (sourcePsiContourJointDomain hp hp1 U) :=
    (hPdata n).2.mono (fun _ ht => ⟨hUP ht.1,ht.2⟩)
  have han (n k : ℤ) (m : ℕ) : AnalyticOnNhd ℂ
      (fun ψ => sourceAbelianMomentCircle hp hp1 W n k m (s n ψ : Coeff p) ψ (C.discs.center k) (R k)) U := by
    intro ψ hψ
    exact hs.analyticAt_momentCircle W U n k m hD (hF k) (hPsi n) ψ (hUV hψ) hψ
      (C.discs.center k) (R k) (hR k).le ((hfamily ψ hψ).2 k).2.2.2
  have hzero (n k : ℤ) : EqOn
      (fun ψ => sourceAbelianMomentCircle hp hp1 W n k 0 (s n ψ : Coeff p) ψ (C.discs.center k) (R k))
      (fun _ => (2*Real.pi : ℂ)*(if k = n then 1 else 0)) U := by
    have he := eqOn_sourceRealCenteredBalls_of_real_agreement hp φ φ δ δ _ _
      (han n k 0).differentiableOn (differentiableOn_const _) (by
        intro χ hχ
        rw [sourceAbelianMomentCircle_zero,hs.real_agreement n χ]
        rw [sourcePsiGapRoot_contour_orthogonality hp hp1 n χ _ _ (hfamily χ.val hχ.1) k])
    exact fun ψ hψ => he ⟨hψ,hψ⟩
  refine ⟨{
    radius := δ
    radius_pos := hδ
    center := C.discs.center
    contourRadius := R
    family := hfamily
    charts := fun ψ hψ => C.charts ψ (hUC hψ)
    analytic := han
    zero_order := fun ψ hψ n k => hzero n k hψ
    odd := ?_
    collapsed := ?_
  },hUV⟩
  · intro ψ hψ n k l
    exact C.momentCircle_odd_eq_zero n k l (s n ψ : Coeff p) ψ (hUC hψ)
      (sourceStandardRootOmittedProduct_analyticOnNhd_spectral hp hp1 k O (hOdata k).2.1 ψ (hUO hψ))
      (R k) (hinner k) (houter k)
  · intro ψ hψ n k hgap m
    exact C.momentCircle_succ_eq_zero_of_collapsed n k m (s n ψ : Coeff p) ψ (hUC hψ)
      (sourceStandardRootOmittedProduct_analyticOnNhd_spectral hp hp1 k O (hOdata k).2.1 ψ (hUO hψ))
      hgap (R k) (hinner k) (houter k)

/-- Actual primitives and the normalized psi branch admit compatible
local moment data near every real potential, at every finite `p>1`. -/
theorem exists_sourceAbelianMoment_localCharts (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W V : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      IsOpen V ∧ realTypeSourceLocus p ⊆ V ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        SourcePsiNormalizedComplexExtension hp hp1 V s ∧
        ∀ φ : realTypeSourceLocus p, ∃ L : SourceAbelianMomentLocalChart hp hp1 W s φ,
          ball φ.val L.radius ⊆ V := by
  obtain ⟨_,V,_,hV,_,hrealV,_,s,hs⟩ := exists_sourcePsi_lemma12_11 hp hp1
  obtain ⟨W,hW,hrealW,hlocal⟩ := hs.exists_moment_localCharts hV hrealV
  exact ⟨W,V,hW,hrealW,hV,hrealV,s,hs,hlocal⟩

end NLS.ZakharovShabat
