import NLS.ZakharovShabat.SourcePrimitivePowerCircle
import NLS.ZakharovShabat.SourceAbelianMomentLocalChart

/-! # Common source balls for all primitive-power moments

All gap indices and natural orders share one source ball and one family
of fixed isolating circles. No psi extension is needed for these moments.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure SourcePrimitivePowerLocalChart (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (φ : realTypeSourceLocus p) where
  radius : ℝ
  radius_pos : 0 < radius
  center : ℤ → ℂ
  contourRadius : ℤ → ℝ
  family : ∀ ψ ∈ ball φ.val radius,
    sourcePsiRealCenteredContourFamily hp hp1 ψ center contourRadius
  charts : ∀ ψ ∈ ball φ.val radius, Nonempty (SourceAbelianSpectralChart hp hp1 W ψ)
  analytic : ∀ (n : ℤ) (m : ℕ), AnalyticOnNhd ℂ
    (fun ψ => sourcePrimitivePowerCircle hp hp1 W n m ψ (center n) (contourRadius n))
    (ball φ.val radius)
  even : ∀ ψ ∈ ball φ.val radius, ∀ (n : ℤ) (m : ℕ),
    sourcePrimitivePowerCircle hp hp1 W n (2*m) ψ (center n) (contourRadius n) = 0
  collapsed : ∀ ψ ∈ ball φ.val radius, ∀ n : ℤ,
    canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0 →
    ∀ m : ℕ, sourcePrimitivePowerCircle hp hp1 W n m ψ (center n) (contourRadius n) = 0

/-- Actual simultaneous primitive-power charts exist around every real source. -/
theorem exists_sourcePrimitivePower_localCharts (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ : realTypeSourceLocus p, Nonempty (SourcePrimitivePowerLocalChart hp hp1 W φ) := by
  obtain ⟨W,hW,hrealW,hC⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  obtain ⟨G,hG,_,hrealG,hDom,_⟩ := exists_global_source_analytic_canonicalRoot hp hp1
  refine ⟨W,hW,hrealW,?_⟩
  intro φ
  obtain ⟨C,hCφ⟩ := hC ⟨φ.val,φ.property⟩
  have hφC : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hCφ]
    exact mem_ball_self C.discs.sourceRadius_pos
  obtain ⟨δ,hδ,hsub⟩ := Metric.isOpen_iff.mp (hG.inter isOpen_ball) φ.val
    ⟨hrealG φ.property,hφC⟩
  let U := ball φ.val δ
  have hUG : U ⊆ G := fun _ h => (hsub h).1
  have hUC : U ⊆ ball C.discs.source.val C.discs.sourceRadius := fun _ h => (hsub h).2
  let R : ℤ → ℝ := fun n => (C.discs.inner n+C.discs.outer n)/2
  have hinner (n : ℤ) : C.discs.inner n ≤ R n := by dsimp [R]; linarith [C.discs.inner_lt n]
  have houter (n : ℤ) : R n < C.discs.outer n := by dsimp [R]; linarith [C.discs.inner_lt n]
  have hR (n : ℤ) : 0 < R n := (C.discs.inner_pos n).trans_le (hinner n)
  have hfamily (ψ : CoeffPair p) (hψ : ψ ∈ U) :
      sourcePsiRealCenteredContourFamily hp hp1 ψ C.discs.center R := by
    refine ⟨C.discs.center_real,fun n => ⟨hR n,?_,?_,?_⟩⟩
    · exact (C.discs.segment_subset ψ (hUC hψ) n).trans (ball_subset_ball (hinner n))
    · exact (closedBall_subset_closedBall (houter n).le).trans (C.discs.avoids_other ψ (hUC hψ) n)
    · exact C.intermediate_circle_root n ψ (hUC hψ) (R n) (hinner n) (houter n)
  have hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 U) := by
    have he : sourceCanonicalRootJointDomain hp hp1 U =
        sourceCanonicalRootJointDomain hp hp1 G ∩ Prod.snd ⁻¹' U := by
      ext t
      exact ⟨fun ht => ⟨⟨hUG ht.1,ht.2⟩,ht.1⟩,fun ht => ⟨ht.2,ht.1.2⟩⟩
    rw [he]
    exact hDom.inter (isOpen_ball.preimage continuous_snd)
  exact ⟨{
    radius := δ
    radius_pos := hδ
    center := C.discs.center
    contourRadius := R
    family := hfamily
    charts := fun ψ hψ => C.charts ψ (hUC hψ)
    analytic := fun n m => sourcePrimitivePowerCircle_analyticOnNhd hp hp1 W U n m
      isOpen_ball hD ((C.full_analytic n).mono (fun _ ht => ⟨hUC ht.1,ht.2⟩))
      (C.discs.center n) (R n) (hR n).le (fun ψ hψ => (hfamily ψ hψ).2 n |>.2.2.2)
    even := fun ψ hψ n m => C.powerCircle_even_eq_zero n m ψ (hUC hψ) (R n) (hinner n) (houter n)
    collapsed := fun ψ hψ n hgap m => C.powerCircle_eq_zero_of_collapsed n m ψ (hUC hψ)
      hgap (R n) (hinner n) (houter n)
  }⟩

end NLS.ZakharovShabat
