import NLS.ZakharovShabat.SourcePsiOriginalOmega
import NLS.ZakharovShabat.SourcePsiDoubleOmittedProduct
import NLS.ZakharovShabat.SourcePsiDeletedProductNonzero
import NLS.ZakharovShabat.SourcePsiRealGapQuotient
import NLS.ZakharovShabat.SourceCriticalRootGapNeighborhood

/-!
# Regularity and nonvanishing of the literal zeta on original disks

On the full placement domain the unused numerator root is separated
from the closed selected disk. The quotient representation therefore
holds on an open neighborhood, which proves analyticity of the literal
product. Other placed roots are absent from the selected gap, giving
nonvanishing there even when that gap is collapsed.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceCorollary10_6Data.originalZeta_analyticOnNhd
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceCorollary10_6Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n m : ℤ) (hmn : m ≠ n)
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (d r : ℝ) (hr : 0 < r) (he : D m = ball (d:ℂ) r) :
    AnalyticOnNhd ℂ (sourcePsiZeta hp hp1 n m a ψ) (closedBall (d:ℂ) r) := by
  let U := sourceStandardRootOmittedDomain hp hp1 ψ m ∩ {z | z ≠ displacedRoots a n}
  have hU : IsOpen U := (isOpen_sourceStandardRootOmittedDomain_of_realType hp hp1 ψ hreal m).inter
    (isOpen_ne_fun continuous_id continuous_const)
  have hreg : AnalyticOnNhd ℂ (sourcePsiGapRegularFactor hp hp1 n m a ψ) U := by
    intro z hz
    exact (analyticAt_const.mul (H.spectral ψ hψW a m z hz.1)).div
      (analyticAt_const.sub analyticAt_id) (sub_ne_zero.mpr hz.2.symm)
  have hzeta : AnalyticOnNhd ℂ (sourcePsiZeta hp hp1 n m a ψ) U := by
    apply hreg.congr hU
    intro z hz
    exact sourcePsiGapRegularFactor_eq_zeta hp hp1 n m hmn a ψ z hz.1 hz.2
  apply hzeta.mono
  intro z hz
  exact ⟨(hD.periodCircle ψ hψV m d r hr he).closedBall_subset_omittedDomain hz,
    hD.originalRootPlacement_avoids_closedBall a ha m n hmn.symm d r hr he z hz⟩

theorem SourceIsolatingNeighborhoods.originalZeta_ne_zero_on_gap
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψV : ψ ∈ V) (n m : ℤ) (hmn : m ≠ n)
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (z : ℂ) (hz : z ∈ sourcePeriodicSegment hp hp1 ψ m) :
    sourcePsiZeta hp hp1 n m a ψ z ≠ 0 := by
  have hzD := hD.gap ψ hψV m hz
  have hother (k : ℤ) (hkm : k ≠ m) : z ≠ displacedRoots a k := by
    intro he
    exact Set.disjoint_left.mp (hD.disjoint m k hkm.symm) hzD (he ▸ ha k)
  have hdom : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m := by
    intro k hkm hzk
    exact Set.disjoint_left.mp (hD.disjoint m k hkm.symm) hzD (hD.gap ψ hψV k hzk)
  rw [← sourcePsiGapRegularFactor_eq_zeta hp hp1 n m hmn a ψ z hdom (hother n hmn.symm)]
  exact div_ne_zero (mul_ne_zero Complex.I_ne_zero
    (sourceSingleRootQuotientJointProduct_ne_zero_of_off_other hp hp1 m z a ψ hother hdom))
    (sub_ne_zero.mpr (hother n hmn.symm).symm)

theorem SourceIsolatingNeighborhoods.originalZeta_rotated_real_on_gap
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψV : ψ ∈ V) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ) (hmn : m ≠ n) (a : Coeff p)
    (ha : a ∈ sourcePsiOriginalRootPlacement D) (haReal : ∀ k : ℤ, (a k).im = 0)
    (z : ℂ) (hz : z ∈ sourcePeriodicSegment hp hp1 ψ m) :
    ((-I)*(((n-m:ℤ):ℂ)*sourcePsiZeta hp hp1 n m a ψ z)).im = 0 := by
  obtain ⟨d,r,hr,he⟩ := hD.discs m
  let P := hD.periodCircle ψ hψV m d r hr he
  have hzcl := ball_subset_closedBall (P.gap hz)
  have hdom := P.closedBall_subset_omittedDomain hzcl
  have hsep := hD.originalRootPlacement_avoids_closedBall a ha m n hmn.symm d r hr he z hzcl
  rw [← sourcePsiGapRegularFactor_eq_zeta hp hp1 n m hmn a ψ z hdom hsep]
  have hzReal : (z.re:ℂ) = z := by
    apply Complex.ext
    · rfl
    · simpa using (sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 ψ hreal m z hz).symm
  have hroots (k : ℤ) : (displacedRoots a k).im = 0 := by simp [displacedRoots,haReal]
  have hf := sourcePsiGapRegularFactor_weighted_re_eq_zero_of_real_roots hp hp1 ψ hreal a hroots
    n m z.re (hzReal ▸ hdom)
  rw [hzReal] at hf
  rw [Complex.mul_im, show (-I).re = 0 by simp, show (-I).im = -1 by simp, hf]
  ring

end NLS.ZakharovShabat
