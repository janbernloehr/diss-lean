import NLS.ZakharovShabat.SourceSingleRootRelativeComparison
import NLS.ZakharovShabat.SourcePsiCriticalRootComparison
import NLS.ZakharovShabat.SourceQuotientClosedDiscs

/-! # Relative product estimates on actual critical-root discs

The separation constant is supplied by the spectral isolating discs.
The estimates hold on their closures, hence on the comparison contours
and on the full gap segments, including collapsed gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Quantitative relative-product estimate for the literal factors in equation (38). -/
def SourcePsiCriticalRelativeEstimate (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n k : ℤ) (a : DeletedCoeff p n) (ψ : CoeffPair p) (z : ℂ) (c : ℝ) : Prop :=
  let a' := sourcePsiFillDeletedRoot n a (sourceCriticalRoot hp hp1 ψ n)
  let b := canonicalCriticalDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let S := ∑' m, ‖sourceRootRelativePerturbation k a' b z m‖
  Summable (fun m => ‖sourceRootRelativePerturbation k a' b z m‖) ∧
    S ≤ c*‖a'-b‖*‖Coeff.puncturedLattice p.conjExponent
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖ ∧
    ‖sourcePsiCriticalFilledQuotient hp hp1 n k a ψ z-
        sourceCriticalDeletedQuotient hp hp1 k ψ z‖ ≤
      ‖sourceCriticalDeletedQuotient hp hp1 k ψ z‖*Real.exp S*S

/-- Actual critical roots satisfy the reciprocal-row separation on every closed disc. -/
theorem SourceIsolatingNeighborhoods.critical_relative_separation
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (k : ℤ) (z : ℂ) (hz : z ∈ closure (D k)) :
    ∀ m : ℤ, m ≠ k → c⁻¹*|((m-k : ℤ) : ℝ)| ≤ ‖sourceCriticalRoot hp hp1 ψ m-z‖ := by
  intro m hm
  have hc : sourceCriticalRoot hp hp1 ψ m ∈ D m :=
    hD.cluster ψ hψ m (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have hd := hD.closedDisc_separation k m hm.symm z hz _ hc
  simpa only [dist_eq_norm,norm_sub_rev,Int.cast_sub,abs_sub_comm] using hd

/-- Comparison with the actual critical deleted product, on original closed discs. -/
theorem SourceIsolatingNeighborhoods.norm_quotient_sub_critical_le
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (k : ℤ) (a : Coeff p)
    (z : ℂ) (hz : z ∈ closure (D k)) :
    let b := canonicalCriticalDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
    let S := ∑' m, ‖sourceRootRelativePerturbation k a b z m‖
    Summable (fun m => ‖sourceRootRelativePerturbation k a b z m‖) ∧
      S ≤ c*‖a-b‖*‖Coeff.puncturedLattice p.conjExponent
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖ ∧
      ‖sourceSingleRootQuotientJointProduct hp hp1 k (z,(a,ψ))-
          sourceCriticalDeletedQuotient hp hp1 k ψ z‖ ≤
        ‖sourceCriticalDeletedQuotient hp hp1 k ψ z‖*Real.exp S*S := by
  dsimp only
  let b := canonicalCriticalDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  have hc : 0 < c := zero_lt_one.trans_le hD.one_le
  have hsep : ∀ m : ℤ, m ≠ k → c⁻¹*|((m-k : ℤ) : ℝ)| ≤ ‖displacedRoots b m-z‖ := by
    simpa only [b,displacedRoots_canonicalCriticalDisplacement,sourceCriticalRoot] using
      hD.critical_relative_separation ψ hψ k z hz
  obtain ⟨hs,hb⟩ := summable_sourceRootRelativePerturbation hp hp1 k a b z c⁻¹ (inv_pos.mpr hc) hsep
  refine ⟨hs,by simpa only [inv_inv] using hb,?_⟩
  exact norm_sourceSingleRootQuotient_sub_le_relative hp hp1 ψ k a b z
    (hD.closedDisc_subset_omittedDomain ψ hψ k hz) c⁻¹ (inv_pos.mpr hc) hsep

/-- The two products in equation (38) satisfy the actual relative-root estimate. -/
theorem SourceIsolatingNeighborhoods.norm_psiFilledQuotient_sub_critical_le
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n k : ℤ) (a : DeletedCoeff p n)
    (z : ℂ) (hz : z ∈ closure (D k)) :
    let a' := sourcePsiFillDeletedRoot n a (sourceCriticalRoot hp hp1 ψ n)
    let b := canonicalCriticalDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
    let S := ∑' m, ‖sourceRootRelativePerturbation k a' b z m‖
    Summable (fun m => ‖sourceRootRelativePerturbation k a' b z m‖) ∧
      S ≤ c*‖a'-b‖*‖Coeff.puncturedLattice p.conjExponent
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖ ∧
      ‖sourcePsiCriticalFilledQuotient hp hp1 n k a ψ z-
          sourceCriticalDeletedQuotient hp hp1 k ψ z‖ ≤
        ‖sourceCriticalDeletedQuotient hp hp1 k ψ z‖*Real.exp S*S :=
  hD.norm_quotient_sub_critical_le ψ hψ k
    (sourcePsiFillDeletedRoot n a (sourceCriticalRoot hp hp1 ψ n)) z hz

end NLS.ZakharovShabat
