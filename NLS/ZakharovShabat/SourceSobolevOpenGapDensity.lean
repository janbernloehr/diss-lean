import NLS.ZakharovShabat.SourceSection20SobolevDomain
import NLS.ComplexAnalysis.RealAnalyticDenseNonzero

/-! # Opening a selected gap in the real H1 topology

The analytic squared gap is not identically zero on the real H1 source
space. Its nonzero locus is therefore dense in that topology, which permits
perturbations preserving open physical H1 norm constraints.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The selected gap is open on this part of the actual real H1 source space. -/
def sourceSobolevOpenGapRealLocus (n : ℤ) : Set realTypeSobolevSourceLocus :=
  {a | canonicalPeriodicGap (by simp) (by norm_num)
    (periodOnePotential (sobolevSourceInclusion a.val)) (periodOnePotential_mem _) n ≠ 0}

/-- Opening a selected gap is dense in the H1 topology itself. -/
theorem dense_sourceSobolevOpenGapRealLocus (n : ℤ) : Dense (sourceSobolevOpenGapRealLocus n) := by
  let S : Submodule ℝ (ScalarDomain 2 × ScalarDomain 2) :=
    (realTypeSourceSubmodule 2).comap (sobolevSourceInclusion.restrictScalars ℝ).toLinearMap
  let F : S → ℂ := fun a => (canonicalPeriodicGap (by simp) (by norm_num)
    (periodOnePotential (sobolevSourceInclusion a.val)) (periodOnePotential_mem _) n)^2
  obtain ⟨W,_,_,hreal,hMG⟩ := exists_global_source_analytic_midpoint_squaredGap (by simp : (2:ℝ≥0∞) ≠ ⊤) (by norm_num)
  have hF : AnalyticOnNhd ℝ F univ := by
    intro a _
    exact (((hMG (sobolevSourceInclusion a.val) (hreal a.property) n).2.comp
      (sobolevSourceInclusion.analyticAt a.val)).restrictScalars (𝕜 := ℝ)).comp (S.subtypeL.analyticAt a)
  obtain ⟨a,ha⟩ := exists_realSobolev_open_gap n
  let b : S := ⟨a.val,a.property⟩
  have hb : F b ≠ 0 := pow_ne_zero 2 ha
  have hd := NLS.ComplexAnalysis.dense_ne_zero_of_real_analytic F hF b hb
  change Dense {a : S | canonicalPeriodicGap (by simp) (by norm_num)
    (periodOnePotential (sobolevSourceInclusion a.val)) (periodOnePotential_mem _) n ≠ 0}
  apply hd.mono
  intro a ha hz
  exact ha (by dsimp only [F]; rw [hz]; norm_num)

end NLS.ZakharovShabat
