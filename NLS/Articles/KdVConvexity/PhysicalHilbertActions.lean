import NLS.Articles.KdVConvexity.HilbertActionUnreindex
import NLS.KdV.HillRawActionSequence
import NLS.KdV.HillWeightedNativeSource
import NLS.KdV.HillH1LinearActionEnergy

/-! # The actual physical raw actions in the original positive-index ell2 space -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVConvexity
open NLS.KdV

def physicalHilbertActions (w : SpectralWeight) (q : RealHillWeightedPotential w) : ActionSpace :=
  actionUnreindex (Coeff.exponentInclusion (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hillRawActionSequence w q))

theorem physicalHilbertActions_apply (w : SpectralWeight) (q : RealHillWeightedPotential w) (n : ℕ+) :
    physicalHilbertActions w q n = (hillPeriodOneAction w q.val q.property n : ℂ) := by
  rw [physicalHilbertActions,actionUnreindex_apply,Coeff.exponentInclusion_apply,
    hillRawActionSequence_apply,actionIndexEquiv_nat_index]

theorem continuous_physicalHilbertActions (w : SpectralWeight) : Continuous (physicalHilbertActions w) :=
  actionUnreindex.continuous.comp
    ((Coeff.exponentInclusion (by norm_num : (1 : ℝ≥0∞) ≤ 2)).continuous.comp
      (continuous_hillRawActionSequence w))

theorem physicalHilbertActions_mem_positiveQuadrant
    (w : SpectralWeight) (q : RealHillWeightedPotential w) : physicalHilbertActions w q ∈ positiveQuadrant := by
  intro n
  rw [physicalHilbertActions_apply]
  exact ⟨ofReal_im _,hillPeriodOneAction_nonneg w q.val q.property n n.pos⟩

theorem physicalHilbertActions_intrinsic_Arnold
    (w : SpectralWeight) (q : RealHillWeightedPotential w) (n : ℕ+) :
    physicalHilbertActions w q n = hillHminusRealGapContourMoment (hillWeightedNativeHminusSource w q.val)
      (hillWeightedNativeHminusSource_real w q) n 0 := by
  rw [physicalHilbertActions_apply]
  exact (hillWeightedNative_ArnoldAction w q n).symm

theorem baseActionInclusion_physicalHilbertActions
    (I : PeriodOneHminusOne → BaseActionSpace)
    (hI : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n) = hillHminusRealGapContourMoment q hr n 0)
    (w : SpectralWeight) (q : RealHillWeightedPotential w) :
    baseActionInclusion (physicalHilbertActions w q) = I (hillWeightedNativeHminusSource w q.val) := by
  apply Subtype.ext
  funext k
  rw [baseActionInclusion_apply,physicalHilbertActions_intrinsic_Arnold]
  simpa only [Equiv.symm_apply_apply] using
    (hI _ (hillWeightedNativeHminusSource_real w q) (actionIndexEquiv k)).symm

theorem linear_physicalHilbertActions_nat
    (q : RealHillWeightedPotential hillH1SpectralWeight) (k : ℕ) :
    ((8*((Equiv.pnatEquivNat.symm k : ℕ+) : ℝ)^3*Real.pi^3 : ℝ) : ℂ)*
      physicalHilbertActions hillH1SpectralWeight q (Equiv.pnatEquivNat.symm k) =
    ((8*Real.pi^3*(k+1 : ℕ)^3*hillPeriodOneAction hillH1SpectralWeight q.val q.property (k+1) : ℝ) : ℂ) := by
  rw [physicalHilbertActions_apply]
  change ((8*((k+1 : ℕ) : ℝ)^3*Real.pi^3 : ℝ) : ℂ)*
    (hillPeriodOneAction hillH1SpectralWeight q.val q.property (k+1) : ℂ) = _
  push_cast
  ring

theorem hillH1LinearActionEnergy_eq_physicalHilbertActions
    (q : RealHillWeightedPotential hillH1SpectralWeight) :
    hillH1LinearActionEnergy q = ∑' n : ℕ+,
      ((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ)*physicalHilbertActions hillH1SpectralWeight q n := by
  rw [hillH1LinearActionEnergy_eq_tsum]
  have he := Equiv.pnatEquivNat.symm.tsum_eq
    (fun n : ℕ+ => ((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ)*physicalHilbertActions hillH1SpectralWeight q n)
  simpa only [linear_physicalHilbertActions_nat] using he

theorem summable_norm_linear_physicalHilbertActions_H1
    (q : RealHillWeightedPotential hillH1SpectralWeight) :
    Summable (fun n : ℕ+ => ‖((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ)*physicalHilbertActions hillH1SpectralWeight q n‖) := by
  have hs := summable_norm_hillH1LinearActionTerms q
  apply Equiv.pnatEquivNat.symm.summable_iff.mp
  simpa only [Function.comp_def,linear_physicalHilbertActions_nat] using hs

end NLS.Articles.KdVConvexity
