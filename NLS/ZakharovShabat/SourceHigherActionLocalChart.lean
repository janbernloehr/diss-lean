import NLS.ZakharovShabat.SourceHigherActionCircleAnalytic
import NLS.ZakharovShabat.SourcePrimitivePowerLocalChart

/-! # Simultaneous local charts for every higher action

The source ball and isolating circles are chosen before the level. Real
agreement and vanishing at collapsed complex gaps are part of the proved
construction, not additional assumptions on the source.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure SourceHigherActionLocalChart (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceLocus p) where
  radius : ℝ
  radius_pos : 0 < radius
  center : ℤ → ℂ
  contourRadius : ℤ → ℝ
  family : ∀ ψ ∈ ball φ.val radius,
    sourcePsiRealCenteredContourFamily hp hp1 ψ center contourRadius
  analytic : ∀ (n : ℤ) (k : ℕ), AnalyticOnNhd ℂ
    (fun ψ => sourceHigherActionCircle hp hp1 ψ (center n) (contourRadius n) k)
    (ball φ.val radius)
  agrees_real : ∀ ψ : realTypeSourceSubmodule p, ψ.val ∈ ball φ.val radius →
    ∀ (n : ℤ) (k : ℕ), sourceHigherActionCircle hp hp1 ψ.val (center n) (contourRadius n) k =
      (sourceRealHigherAction hp hp1 ψ n k : ℂ)
  collapsed : ∀ ψ ∈ ball φ.val radius, ∀ n : ℤ,
    sourcePeriodicGapDisplacement hp hp1 ψ n = 0 → ∀ k : ℕ,
      sourceHigherActionCircle hp hp1 ψ (center n) (contourRadius n) k = 0

/-- A common analytic chart for all indices and levels exists around every
real source at every finite exponent above one. -/
theorem exists_sourceHigherActionLocalChart (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceLocus p) : Nonempty (SourceHigherActionLocalChart hp hp1 φ) := by
  obtain ⟨W,_,_,hC⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  obtain ⟨C,hCφ⟩ := hC ⟨φ.val,φ.property⟩
  obtain ⟨G,hG,_,hrealG,hD,hq⟩ := exists_global_sourceCriticalRootRatio_jointAnalytic hp hp1
  obtain ⟨E,hE,hrealE,hzero⟩ := exists_global_sourceHigherActionCircle_zero_of_zeroGap hp hp1
  have hφC : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hCφ]
    exact mem_ball_self C.discs.sourceRadius_pos
  obtain ⟨δ,hδ,hsub⟩ := Metric.isOpen_iff.mp ((hG.inter hE).inter isOpen_ball) φ.val
    ⟨⟨hrealG φ.property,hrealE φ.property⟩,hφC⟩
  let U := ball φ.val δ
  have hUG : U ⊆ G := fun _ h => (hsub h).1.1
  have hUE : U ⊆ E := fun _ h => (hsub h).1.2
  have hUC : U ⊆ ball C.discs.source.val C.discs.sourceRadius := fun _ h => (hsub h).2
  let R : ℤ → ℝ := fun n => (C.discs.inner n+C.discs.outer n)/2
  have hi (n : ℤ) : C.discs.inner n ≤ R n := by dsimp [R]; linarith [C.discs.inner_lt n]
  have ho (n : ℤ) : R n < C.discs.outer n := by dsimp [R]; linarith [C.discs.inner_lt n]
  have hR (n : ℤ) : 0 < R n := (C.discs.inner_pos n).trans_le (hi n)
  have hfamily (ψ : CoeffPair p) (hψ : ψ ∈ U) :
      sourcePsiRealCenteredContourFamily hp hp1 ψ C.discs.center R := by
    refine ⟨C.discs.center_real,fun n => ⟨hR n,?_,?_,?_⟩⟩
    · exact (C.discs.segment_subset ψ (hUC hψ) n).trans (ball_subset_ball (hi n))
    · exact (closedBall_subset_closedBall (ho n).le).trans (C.discs.avoids_other ψ (hUC hψ) n)
    · exact C.intermediate_circle_root n ψ (hUC hψ) (R n) (hi n) (ho n)
  exact ⟨{
    radius := δ
    radius_pos := hδ
    center := C.discs.center
    contourRadius := R
    family := hfamily
    analytic := fun n k => sourceHigherActionCircle_analyticOnNhd hp hp1 hD hq isOpen_ball
      _ _ (hR n).le (fun ψ hψ z hz => ⟨hUG hψ,(hfamily ψ hψ).2 n |>.2.2.2 hz⟩) k
    agrees_real := fun ψ hψ n k => C.higherActionCircle_eq_real n k ψ (hUC hψ) _ (hi n) (ho n)
    collapsed := fun ψ hψ n hgap k => hzero ψ (hUE hψ) n hgap _ _ (hR n).le
      ((hfamily ψ hψ).2 n).2.2.1 ((hfamily ψ hψ).2 n).2.2.2 k
  }⟩

end NLS.ZakharovShabat
