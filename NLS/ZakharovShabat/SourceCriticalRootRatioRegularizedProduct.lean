import NLS.ZakharovShabat.SourceEquation2_15
import NLS.ZakharovShabat.SourceOpenGapComplement

/-!
# One product filling every collapsed critical-root factor

Replace a collapsed-gap factor by one before taking the full product.
The resulting single function agrees with the actual quotient off all
gaps, and with the omitted analytic product throughout the omitted domain
of every collapsed index. Infinitely many collapsed gaps are allowed.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Fill a collapsed factor by its analytic value one, even at the common endpoint. -/
def sourceCriticalRootRegularizedFactor (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (z : ℂ) (m : ℤ) : ℂ :=
  if canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m = 0 then 1
  else (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z)/
    sourceStandardRoot hp hp1 ψ m z

/-- A single normalized product continuing the critical-root quotient through all collapsed gaps. -/
def sourceCriticalRootRatioContinued (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  -Complex.I*(∏' m : ℤ, sourceCriticalRootRegularizedFactor hp hp1 ψ z m)

/-- Filling collapsed factors preserves absolute convergence of the individual errors. -/
theorem summable_norm_sourceCriticalRootRegularizedFactor_sub_one
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) :
    Summable (fun m : ℤ => ‖sourceCriticalRootRegularizedFactor hp hp1 ψ z m-1‖) := by
  apply (summable_norm_sourceCriticalRootRatio_factor_sub_one hp hp1 ψ z).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro m
  unfold sourceCriticalRootRegularizedFactor
  split
  · simp only [sub_self,norm_zero]; exact norm_nonneg _
  · exact le_rfl

/-- The continued product is an unconditional product, not merely a totalized tprod expression. -/
theorem multipliable_sourceCriticalRootRegularizedFactor
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) :
    Multipliable (sourceCriticalRootRegularizedFactor hp hp1 ψ z) := by
  convert multipliable_one_add_of_summable
    (summable_norm_sourceCriticalRootRegularizedFactor_sub_one hp hp1 ψ z) using 1
  ext m
  ring

/-- Away from its selected gap, a filled factor agrees with the actual critical factor. -/
theorem SourceLemma10_10Data.regularizedFactor_eq
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)} (h : SourceLemma10_10Data hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (z : ℂ) (m : ℤ)
    (hz : z ∉ sourcePeriodicSegment hp hp1 ψ m) :
    sourceCriticalRootRegularizedFactor hp hp1 ψ z m =
      (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z)/
        sourceStandardRoot hp hp1 ψ m z := by
  unfold sourceCriticalRootRegularizedFactor
  split
  · rename_i hg
    have hc := h.critical_eq_midpoint_of_gap_zero ψ hψ m
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hg)
    have hw := sourceStandardRoot_ne_zero_off_segment hp hp1 ψ m z hz
    rw [sourceStandardRoot_of_zeroGap hp hp1 ψ m z hg] at hw
    rw [hc,sourceStandardRoot_of_zeroGap hp hp1 ψ m z hg,div_self hw]
  · rfl

/-- On the original cut complement the single continued function equals the actual quotient. -/
theorem SourceEquation2_15Data.continued_eq_quotient
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)} (h : SourceEquation2_15Data hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    sourceCriticalRootRatioContinued hp hp1 ψ z = sourceCriticalRootRatioJoint hp hp1 (z,ψ) := by
  rw [sourceCriticalRootRatioContinued]
  have he := funext (fun m => h.previous.regularizedFactor_eq ψ hψ z m (hz m))
  rw [he]
  exact (sourceCriticalRootRatio_product hp hp1 ψ z hz).symm

/-- Filling all collapsed factors agrees with the selected omitted product on its whole domain. -/
theorem SourceEquation2_15Data.continued_eq_extension
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)} (h : SourceEquation2_15Data hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0)
    (z : ℂ) (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    sourceCriticalRootRatioContinued hp hp1 ψ z = sourceCriticalRootRatioExtension hp hp1 n ψ z := by
  let a := canonicalCriticalDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  have he : sourceCriticalRootRegularizedFactor hp hp1 ψ z =
      sourceSingleRootQuotientFactor hp hp1 ψ a z n := by
    funext m
    by_cases hm : m = n
    · subst m
      simp only [sourceCriticalRootRegularizedFactor,hg,
        sourceSingleRootQuotientFactor,ite_true]
    · rw [h.previous.regularizedFactor_eq ψ hψ z m (hz m hm)]
      simp only [sourceSingleRootQuotientFactor,if_neg hm,a,
        displacedRoots_canonicalCriticalDisplacement]
  unfold sourceCriticalRootRatioContinued sourceCriticalRootRatioExtension
  rw [he,(hasProd_sourceSingleRootQuotientFactor hp hp1 ψ a z n hz).tprod_eq]

/-- At zero source the extension is -i on the entire plane, including every collapsed endpoint. -/
theorem sourceCriticalRootRatioContinued_zero_source (hp : p ≠ ⊤) (hp1 : 1 < p) (z : ℂ) :
    sourceCriticalRootRatioContinued hp hp1 (0 : CoeffPair p) z = -Complex.I := by
  have hg (m : ℤ) : canonicalPeriodicGap hp hp1
      (periodOnePotential (0 : CoeffPair p)) (periodOnePotential_mem 0) m = 0 := by
    simpa only [map_zero] using canonicalPeriodicGap_zero (p := p) hp hp1 m
  simp only [sourceCriticalRootRatioContinued,sourceCriticalRootRegularizedFactor,hg,
    ite_true,tprod_one,mul_one]

end NLS.ZakharovShabat
