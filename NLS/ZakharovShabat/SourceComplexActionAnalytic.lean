import NLS.ZakharovShabat.SourceComplexAction
import NLS.ComplexAnalysis.ParametricCircleIntegralHigher

/-! # Banach analyticity of the actual glued actions

Joint analyticity of the weighted canonical-root quotient passes through
the fixed-circle integral as an actual Banach power series. On each
action chart, that integral is the glued indexed action. One open source
neighborhood of the whole real locus therefore works for every index,
with the indexed action chart domain retained explicitly.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem analyticOnNhd_sourceActionCircle_of_jointAnalytic
    (hp : p ≠ ⊤) (hp1 : 1 < p) {W V : Set (CoeffPair p)}
    (hDopen : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hF : AnalyticOnNhd ℂ (sourceActionIntegrandJoint hp hp1)
      (sourceCanonicalRootJointDomain hp hp1 W))
    (hVopen : IsOpen V) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : ∀ ψ ∈ V, ∀ z ∈ sphere c R,
      (z,ψ) ∈ sourceCanonicalRootJointDomain hp hp1 W) :
    AnalyticOnNhd ℂ (fun ψ : CoeffPair p => sourceActionCircle hp hp1 ψ c R) V := by
  have hraw := analyticOnNhd_circleIntegral_of_jointAnalytic
    (sourceActionIntegrandJoint hp hp1) hDopen hF c R hR hVopen hcircle
  intro ψ hψ
  exact analyticAt_const.mul (hraw ψ hψ)

/-- The original action chart domains are kept, while one common
almost-real neighborhood provides joint analyticity for every index. -/
theorem exists_global_sourceComplexAction_analyticOnNhd
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ n : ℤ, AnalyticOnNhd ℂ (sourceComplexAction hp hp1 n)
        (W ∩ sourceComplexActionDomain hp hp1 n) := by
  obtain ⟨W,hWopen,_,hreal,hDopen,hweighted⟩ :=
    exists_global_sourceActionIntegrand_jointAnalytic hp hp1
  refine ⟨W,hWopen,hreal,?_⟩
  intro n ψ hψ
  obtain ⟨ch,hψch⟩ := hψ.2
  let V := W ∩ ball ch.center ch.radius
  have hVopen : IsOpen V := hWopen.inter isOpen_ball
  have hψV : ψ ∈ V := ⟨hψ.1,hψch⟩
  have hcircle : ∀ χ ∈ V, ∀ z ∈ sphere ch.spectralCenter ch.spectralRadius,
      (z,χ) ∈ sourceCanonicalRootJointDomain hp hp1 W := by
    intro χ hχ z hz
    have hgeom := ch.geometry χ hχ.2
    exact ⟨hχ.1,sourceCanonicalRootDomain_of_enclosingCircle hp hp1 χ n
      ch.spectralCenter ch.spectralRadius hgeom.1 hgeom.2 hz⟩
  have hcircleAnalytic := analyticOnNhd_sourceActionCircle_of_jointAnalytic hp hp1
    hDopen hweighted hVopen ch.spectralCenter ch.spectralRadius ch.spectralRadius_pos.le hcircle
  have hlocal : sourceComplexAction hp hp1 n =ᶠ[𝓝 ψ]
      (fun χ => sourceActionCircle hp hp1 χ ch.spectralCenter ch.spectralRadius) := by
    filter_upwards [hVopen.mem_nhds hψV] with χ hχ
    exact sourceComplexAction_eq_chart hp hp1 n ch χ hχ.2
  exact (hcircleAnalytic ψ hψV).congr hlocal.symm

theorem analyticAt_sourceComplexAction_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    AnalyticAt ℂ (sourceComplexAction hp hp1 n) φ := by
  obtain ⟨W,_,hWreal,hI⟩ := exists_global_sourceComplexAction_analyticOnNhd hp hp1
  exact hI n φ ⟨hWreal hreal,
    realTypeSourceLocus_subset_sourceComplexActionDomain hp hp1 n hreal⟩

end NLS.ZakharovShabat
