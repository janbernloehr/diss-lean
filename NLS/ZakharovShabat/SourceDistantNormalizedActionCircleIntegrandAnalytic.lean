import NLS.ZakharovShabat.SourceDistantCriticalGapQuotientAnalyticNeighborhood
import NLS.ZakharovShabat.SourceDistantCriticalRootRatioJointAnalyticCircles
import NLS.ZakharovShabat.SourceNormalizedActionCircleAnalytic

/-!
# A common analytic domain for distant normalized-action integrands

The symmetric periodic data, critical gap quotient, and deleted
spectral factor are jointly analytic at every point of every distant
free circle over one complex source neighborhood. Rationalization
of the normalized-action kernel preserves this analyticity, including
at complex collapsed gaps.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The normalized contour integrand is jointly analytic when its
source-dependent parameters and deleted factor are analytic at an
exterior spectral point. -/
theorem analyticAt_sourceNormalizedActionCircleIntegrandJoint_of_analyticData
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ)
    (hτ : AnalyticAt ℂ (fun χ : CoeffPair p =>
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential χ)
        (periodOnePotential_mem χ) n) ψ)
    (hq : AnalyticAt ℂ (fun χ : CoeffPair p =>
      (sourcePeriodicGapDisplacement hp hp1 χ n)^2) ψ)
    (hB : AnalyticAt ℂ (fun χ : CoeffPair p =>
      canonicalCriticalGapQuotient hp hp1 (periodOnePotential χ)
        (periodOnePotential_mem χ) n) ψ)
    (hE : AnalyticAt ℂ (fun t : ℂ × CoeffPair p =>
      sourceCriticalRootRatioExtension hp hp1 n t.2 t.1) (z,ψ)) :
    AnalyticAt ℂ (sourceNormalizedActionCircleIntegrandJoint hp hp1 n) (z,ψ) := by
  let τ (χ : CoeffPair p) := canonicalPeriodicMidpoint hp hp1
    (periodOnePotential χ) (periodOnePotential_mem χ) n
  let q (χ : CoeffPair p) := (sourcePeriodicGapDisplacement hp hp1 χ n)^2
  let B (χ : CoeffPair p) := canonicalCriticalGapQuotient hp hp1
    (periodOnePotential χ) (periodOnePotential_mem χ) n
  let W (t : ℂ × CoeffPair p) := sourceStandardRoot hp hp1 t.2 n t.1
  let E (t : ℂ × CoeffPair p) :=
    sourceCriticalRootRatioExtension hp hp1 n t.2 t.1
  have hrootfun (χ : CoeffPair p) (w : ℂ) :
      sourceStandardRoot hp hp1 χ n w = normalizedStandardRoot (τ χ) (q χ) w := by
    simp only [sourceStandardRoot,τ,q,sourcePeriodicGapDisplacement_apply]
  have hτj : AnalyticAt ℂ (fun t : ℂ × CoeffPair p => τ t.2) (z,ψ) :=
    hτ.comp (analyticAt_snd (p := (z,ψ)))
  have hqj : AnalyticAt ℂ (fun t : ℂ × CoeffPair p => q t.2) (z,ψ) :=
    hq.comp (analyticAt_snd (p := (z,ψ)))
  have hBj : AnalyticAt ℂ (fun t : ℂ × CoeffPair p => B t.2) (z,ψ) :=
    hB.comp (analyticAt_snd (p := (z,ψ)))
  have hW : AnalyticAt ℂ W (z,ψ) :=
    sourceStandardRoot_joint_analyticAt_of_symmetric hp hp1 ψ n z hτ
      (by simpa only [q,sourcePeriodicGapDisplacement_apply] using hq) (hz n)
  have hWne : W (z,ψ) ≠ 0 :=
    sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z (hz n)
  have hτne : τ ψ ≠ z := by
    intro he
    exact (hz n) (he.symm ▸ sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)
  have hplus : τ ψ-z+W (z,ψ) ≠ 0 := by
    rw [show W (z,ψ) = normalizedStandardRoot (τ ψ) (q ψ) z from
      hrootfun ψ z]
    exact normalizedStandardRoot_add_ne_zero (τ ψ) (q ψ) z hτne
  have hd : AnalyticAt ℂ
      (fun t : ℂ × CoeffPair p => τ t.2-t.1) (z,ψ) :=
    hτj.sub analyticAt_fst
  have hsum : AnalyticAt ℂ
      (fun t : ℂ × CoeffPair p => 4*(τ t.2-t.1+W t)) (z,ψ) :=
    analyticAt_const.mul (hd.add hW)
  have hsumne : (4:ℂ)*(τ ψ-z+W (z,ψ)) ≠ 0 :=
    mul_ne_zero (by norm_num) hplus
  have hK : AnalyticAt ℂ (fun t : ℂ × CoeffPair p =>
      ((τ t.2-t.1)/(4*(τ t.2-t.1+W t)) +
        2*(τ t.2-t.1)*B t.2 + q t.2*(B t.2)^2)/W t) (z,ψ) :=
    (((hd.div hsum hsumne).add
      ((analyticAt_const.mul hd).mul hBj)).add
        (hqj.mul (hBj.pow 2))).div hW hWne
  have hfun : sourceNormalizedActionCircleIntegrandJoint hp hp1 n =
      (fun t : ℂ × CoeffPair p =>
        ((τ t.2-t.1)/(4*(τ t.2-t.1+W t)) +
          2*(τ t.2-t.1)*B t.2 + q t.2*(B t.2)^2)/W t * E t) := by
    funext t
    simp only [sourceNormalizedActionCircleIntegrandJoint,
      normalizedActionCircleKernel,τ,q,B,W,E,
      sourceStandardRoot,sourcePeriodicGapDisplacement_apply]
  rw [hfun]
  exact hK.mul hE

/-- One source neighborhood and one cutoff make the full rationalized
normalized-action integrand jointly analytic on every distant free
circle, including at collapsed complex gaps. -/
theorem exists_local_source_distantNormalizedActionCircleIntegrand_jointAnalytic
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ n : ℤ, K < n.natAbs →
        ∀ z ∈ sphere ((Real.pi:ℂ)*n) (Real.pi/8),
          AnalyticAt ℂ (sourceNormalizedActionCircleIntegrandJoint hp hp1 n)
            (z,ψ) := by
  obtain ⟨Kb,Vb,hVbopen,hφVb,hB⟩ :=
    exists_local_source_distantCriticalGapQuotient_analytic hp hp1 φ hreal
  obtain ⟨Ke,Ve,hVeopen,hφVe,hE⟩ :=
    exists_local_source_distantCriticalRootRatio_jointAnalytic_onFreeCircles
      hp hp1 φ hreal
  obtain ⟨Kg,Vg,hVgopen,hφVg,hgeom⟩ :=
    exists_local_sourceNormalizedAction_uniform_tail_circle_data
      hp hp1 φ hreal
  obtain ⟨W,hWopen,_,hrealW,hdata⟩ :=
    exists_global_source_analytic_midpoint_squaredGap hp hp1
  let K := max (max Kb Ke) Kg
  let V : Set (CoeffPair p) := ((Vb ∩ Ve) ∩ Vg) ∩ W
  have hVopen : IsOpen V :=
    ((hVbopen.inter hVeopen).inter hVgopen).inter hWopen
  have hφV : φ ∈ V := ⟨⟨⟨hφVb,hφVe⟩,hφVg⟩,hrealW hreal⟩
  refine ⟨K,V,hVopen,hφV,?_⟩
  intro ψ hψ n hn z hz
  have hKb : Kb < n.natAbs :=
    lt_of_le_of_lt (le_max_left _ _) (lt_of_le_of_lt (le_max_left _ _) hn)
  have hKe : Ke < n.natAbs :=
    lt_of_le_of_lt (le_max_right _ _) (lt_of_le_of_lt (le_max_left _ _) hn)
  have hKg : Kg ≤ n.natAbs := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hn)
  obtain ⟨hseg,hother,_,_,_⟩ := hgeom ψ hψ.1.2 n hKg
  have hzdom : z ∈ sourceCanonicalRootDomain hp hp1 ψ :=
    sourceCanonicalRootDomain_of_enclosingCircle hp hp1 ψ n
      ((Real.pi:ℂ)*n) (Real.pi/8) hseg hother hz
  have hτ := (hdata ψ hψ.2 n).1
  have hq : AnalyticAt ℂ (fun χ : CoeffPair p =>
      (sourcePeriodicGapDisplacement hp hp1 χ n)^2) ψ := by
    simpa only [sourcePeriodicGapDisplacement_apply] using
      (hdata ψ hψ.2 n).2
  exact analyticAt_sourceNormalizedActionCircleIntegrandJoint_of_analyticData
    hp hp1 n ψ z hzdom hτ hq
      (hB ψ hψ.1.1.1 n hKb) (hE ψ hψ.1.1.2 n hKe z hz)

end NLS.ZakharovShabat
