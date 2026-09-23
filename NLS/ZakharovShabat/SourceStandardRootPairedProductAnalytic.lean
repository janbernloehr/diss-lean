import NLS.ZakharovShabat.SourceStandardRootPairedProduct
import NLS.ZakharovShabat.SourceStandardRootJointAnalytic

/-!
# Analytic finite cutoffs of the paired standard-root product

Every finite cutoff is holomorphic off the noncentral periodic gaps. On
the connected almost-real source domain, the same cutoffs are jointly
analytic in the spectral parameter and source coefficients. These are the
analytic approximants for the locally uniform limit in Lemma 10.5.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The natural finite cutoff of the omitted-zero paired product. -/
def sourceStandardRootPairedPartialProduct (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (z : ℂ) (N : ℕ) : ℂ :=
  ∏ j ∈ Finset.range N, sourceStandardRootPairedFactor hp hp1 ψ z j

/-- Each finite cutoff tends pointwise to the paired infinite product. -/
theorem tendsto_sourceStandardRootPairedPartialProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) :
    Filter.Tendsto (fun N : ℕ => sourceStandardRootPairedPartialProduct hp hp1 ψ z N)
      Filter.atTop (nhds (sourceStandardRootPairedProduct hp hp1 ψ z)) := by
  simpa only [sourceStandardRootPairedPartialProduct] using
    tendsto_sourceStandardRootPairedProduct hp hp1 ψ z

/-- A paired factor is analytic at every point away from its two gaps. -/
theorem sourceStandardRootPairedFactor_analyticAt
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceStandardRootPairedDomain hp hp1 ψ) (j : ℕ) :
    AnalyticAt ℂ (fun w => sourceStandardRootPairedFactor hp hp1 ψ w j) z := by
  let k : ℤ := (j+1 : ℕ)
  have hk : k ≠ 0 := by dsimp [k]; omega
  have hpos := sourceStandardRoot_analyticAt hp hp1 ψ k z (hz k hk)
  have hneg := sourceStandardRoot_analyticAt hp hp1 ψ (-k) z
    (hz (-k) (neg_ne_zero.mpr hk))
  change AnalyticAt ℂ
    (fun w => (sourceStandardRoot hp hp1 ψ k w / ((Real.pi : ℂ)*k)) *
      (sourceStandardRoot hp hp1 ψ (-k) w / (-((Real.pi : ℂ)*k)))) z
  exact hpos.div_const.mul hneg.div_const

/-- The factor continuity needed for uniform product convergence on
compact subsets of the gap complement. -/
theorem sourceStandardRootPairedFactor_continuousOn
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (K : Set ℂ) (hK : K ⊆ sourceStandardRootPairedDomain hp hp1 ψ)
    (j : ℕ) :
    ContinuousOn (fun w => sourceStandardRootPairedFactor hp hp1 ψ w j) K := by
  intro z hz
  exact (sourceStandardRootPairedFactor_analyticAt hp hp1 ψ z (hK hz) j).continuousAt.continuousWithinAt

/-- Every finite paired cutoff is analytic on the omitted-zero domain. -/
theorem sourceStandardRootPairedPartialProduct_analyticAt
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceStandardRootPairedDomain hp hp1 ψ) (N : ℕ) :
    AnalyticAt ℂ (fun w => sourceStandardRootPairedPartialProduct hp hp1 ψ w N) z := by
  exact (Finset.range N).analyticAt_fun_prod
    (fun j _ => sourceStandardRootPairedFactor_analyticAt hp hp1 ψ z hz j)

/-- Joint analyticity of a paired factor follows from that of its two
indexed standard roots. -/
theorem sourceStandardRootPairedFactor_joint_analyticAt
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceStandardRootPairedDomain hp hp1 ψ)
    (hroot : ∀ n : ℤ, z ∉ sourcePeriodicSegment hp hp1 ψ n →
      AnalyticAt ℂ (fun t : ℂ × CoeffPair p =>
        sourceStandardRoot hp hp1 t.2 n t.1) (z,ψ)) (j : ℕ) :
    AnalyticAt ℂ (fun t : ℂ × CoeffPair p =>
      sourceStandardRootPairedFactor hp hp1 t.2 t.1 j) (z,ψ) := by
  let k : ℤ := (j+1 : ℕ)
  have hk : k ≠ 0 := by dsimp [k]; omega
  have hpos := hroot k (hz k hk)
  have hneg := hroot (-k) (hz (-k) (neg_ne_zero.mpr hk))
  change AnalyticAt ℂ
    (fun t : ℂ × CoeffPair p =>
      (sourceStandardRoot hp hp1 t.2 k t.1 / ((Real.pi : ℂ)*k)) *
      (sourceStandardRoot hp hp1 t.2 (-k) t.1 / (-((Real.pi : ℂ)*k)))) (z,ψ)
  exact hpos.div_const.mul hneg.div_const

/-- One connected source domain supports jointly analytic finite paired
cutoffs at every point away from the moving noncentral gaps. -/
theorem exists_global_source_analytic_pairedPartialProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ ψ ∈ W, ∀ z ∈ sourceStandardRootPairedDomain hp hp1 ψ, ∀ N : ℕ,
        AnalyticAt ℂ (fun t : ℂ × CoeffPair p =>
          sourceStandardRootPairedPartialProduct hp hp1 t.2 t.1 N) (z,ψ) := by
  obtain ⟨W, hWopen, hWconnected, hR, hA⟩ :=
    exists_global_source_analytic_standardRoot hp hp1
  refine ⟨W, hWopen, hWconnected, hR, ?_⟩
  intro ψ hψ z hz N
  exact (Finset.range N).analyticAt_fun_prod (fun j _ =>
    sourceStandardRootPairedFactor_joint_analyticAt hp hp1 ψ z hz
      (hA ψ hψ · z ·) j)

end NLS.ZakharovShabat
