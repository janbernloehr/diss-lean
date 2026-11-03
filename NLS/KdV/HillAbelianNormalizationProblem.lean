import NLS.KdV.HillAbelianCandidatePeriods
import NLS.KdV.HillEnergyRootIdentification

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillAbelianPsiCandidate_congr_omitted
    (σ τ : ℕ → ℝ) (n : ℕ) (h : ∀ k : ℕ, k+1 ≠ n → σ k = τ k) :
    hillAbelianPsiCandidate σ n = hillAbelianPsiCandidate τ n := by
  funext z
  unfold hillAbelianPsiCandidate hillAbelianNumeratorProduct
  congr 1
  congr 1
  funext k
  unfold hillAbelianNumeratorFactor
  split_ifs with hk
  · rfl
  · rw [hillGapRootEnergyFactor,hillGapRootEnergyFactor,h k hk]

theorem hillAbelianCandidatePeriod_congr_omitted
    (σ τ : ℕ → ℝ) (n k : ℕ) (h : ∀ j : ℕ, j+1 ≠ n → σ j = τ j) :
    hillAbelianCandidatePeriod q hq hr σ n k =
      hillAbelianCandidatePeriod q hq hr τ n k := by
  unfold hillAbelianCandidatePeriod
  rw [hillAbelianPsiCandidate_congr_omitted σ τ n h]

def hillAbelianNormalizedRoots (n : ℕ) : Set (hillGapRootBox q hq hr) :=
  {σ | ∀ k : ℕ, 1 ≤ k → hillAbelianCandidatePeriod q hq hr σ.val n k =
    if k = n then 1 else 0}

theorem isClosed_hillAbelianNormalizedRoots (n : ℕ) :
    IsClosed (hillAbelianNormalizedRoots q hq hr n) := by
  simp only [hillAbelianNormalizedRoots,ofPred_forall]
  exact isClosed_iInter (fun k => isClosed_iInter (fun hk =>
    isClosed_eq (continuous_hillAbelianCandidatePeriod q hq hr n k hk) continuous_const))

theorem isCompact_hillAbelianNormalizedRoots (n : ℕ) :
    IsCompact (hillAbelianNormalizedRoots q hq hr n) := by
  let : CompactSpace (hillGapRootBox q hq hr) :=
    isCompact_iff_compactSpace.mp (isCompact_hillGapRootBox q hq hr)
  exact (isClosed_hillAbelianNormalizedRoots q hq hr n).isCompact

theorem hillAbelianCandidatePeriod_eq_physical_cut
    (σ : ℕ → ℝ) (n k : ℕ) (hk : 1 ≤ k) :
    hillAbelianCandidatePeriod q hq hr σ n k =
      (2*(Real.pi : ℂ))⁻¹ * ∮ z in C((hillRealGapCenter q hq hr k : ℂ),
        hillRealGapHalfLength q hq hr k + hillRealGapCollar q hq hr k),
      hillAbelianPsiCandidate σ n z / hillL2RealCutRoot (SpectralWeight.one.toCoeff q) z := by
  obtain ⟨hd,hη,_⟩ := hillRealGapContour_geometry q hq hr k hk
  have hR := add_nonneg hd hη.le
  unfold hillAbelianCandidatePeriod
  congr 1
  apply circleIntegral.integral_congr hR
  intro z hz
  dsimp only []
  rw [hillEnergyCanonicalRootProduct_eq_realCutRoot q hq hr
    (hillRealGapContour_sphere_subset q hq hr k hk hz)]

end NLS.KdV
