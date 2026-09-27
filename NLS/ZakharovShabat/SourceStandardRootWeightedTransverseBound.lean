import NLS.ZakharovShabat.SourceStandardRootWeightedOuterArcLimit
import NLS.ZakharovShabat.SourceCriticalRootRatioTransverseBound

/-!
# Uniform transverse bound for a weighted inverse standard root

An analytic numerator is bounded on a compact thickening of the
selected gap. The transverse lower bound for the standard root then
shows that the cosine Jacobian cancels the endpoint singularity
uniformly on short vertical approaches from either side.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A locally analytic numerator divided by the selected standard
root has a uniform cosine-weighted bound along short vertical
approaches to an open real gap. -/
theorem exists_sourceStandardRoot_weighted_transverse_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (g : ℂ → ℂ) (U : Set ℂ) (hUopen : IsOpen U)
    (hgapU : standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n) ⊆ U)
    (hg : AnalyticOnNhd ℂ g U) :
    let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re
    let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re
    ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧
      cthickening ε (standardRootGapSegment
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n)) ⊆ U ∧
      ∀ t ∈ Icc (-1 : ℝ) 1, ∀ y : ℝ, y ≠ 0 → |y| ≤ ε →
        let z := sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I
        ‖(g z / sourceStandardRoot hp hp1 ψ n z) *
          ((((b-a)/2 * Real.sqrt (1-t^2)):ℝ):ℂ)‖ ≤ M := by
  let S := standardRootGapSegment
    (sourceStandardRootMidpoint hp hp1 ψ n)
    (sourceStandardRootHalfGap hp hp1 ψ n)
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  have hS : IsCompact S := standardRootGapSegment_compact _ _
  obtain ⟨ε,hε,hthick⟩ := hS.exists_cthickening_subset_open hUopen hgapU
  have hK : IsCompact (cthickening ε S) := hS.cthickening
  have hGcont : ContinuousOn g (cthickening ε S) := by
    intro z hz
    exact ((hg z (hthick hz)).continuousAt).continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hGcont
  let M := max C 0 + 1
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨ε,M,hε,hM,hthick,?_⟩
  intro t ht y hy hyε
  let q := sourceCanonicalRootGapPoint hp hp1 ψ n t
  let z := q + (y:ℂ)*I
  let w : ℝ := (b-a)/2 * Real.sqrt (1-t^2)
  have hqS : q ∈ S := ⟨t,ht,rfl⟩
  have hdist : dist z q = |y| := by
    calc
      dist z q = ‖(y:ℂ)*I‖ := by
        rw [dist_eq_norm]
        congr 1
        dsimp [z]
        ring
      _ = |y| := by simp
  have hzK : z ∈ cthickening ε S :=
    Metric.mem_cthickening_of_dist_le z q ε S hqS
      (by simpa [hdist] using hyε)
  have hG : ‖g z‖ ≤ M :=
    (hC z hzK).trans (by dsimp [M]; linarith [le_max_left C 0])
  have hqim : q.im = 0 := by
    change (sourceCanonicalRootGapPoint hp hp1 ψ n t).im = 0
    rw [sourceCanonicalRootGapPoint_eq_ofReal_realGapAffinePoint
      hp hp1 ψ hreal n t]
    simp
  have hzim : z.im = y := by simp [z,hqim]
  have hnot : z ∉ sourcePeriodicSegment hp hp1 ψ n := by
    intro hmem
    have him := sourcePeriodicSegment_im_eq_zero_of_realType
      hp hp1 ψ hreal n z hmem
    exact hy (by linarith)
  have hw : 0 ≤ w := by
    dsimp [w]
    have hd : 0 ≤ (b-a)/2 := by
      dsimp [a,b]
      exact (div_pos (sub_pos.mpr hopen) (by norm_num)).le
    exact mul_nonneg hd (Real.sqrt_nonneg _)
  have hroot : w ≤ ‖sourceStandardRoot hp hp1 ψ n z‖ :=
    sourceStandardRoot_transverse_norm_lower_bound
      hp hp1 ψ hreal n hopen t y ht hy
  have hB : sourceStandardRoot hp hp1 ψ n z ≠ 0 :=
    sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z hnot
  exact norm_div_mul_real_le_of_weight_le_norm
    (g z) (sourceStandardRoot hp hp1 ψ n z) w M hw hM.le
    hG hroot hB

end NLS.ZakharovShabat
