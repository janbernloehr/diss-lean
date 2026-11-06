import NLS.KdV.HillGlobalDifferentialUniqueness
import NLS.KdV.HillAbelianPhysicalRootSequence
import NLS.KdV.HillIntrinsicNormalizedGapPeriodGerm

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillAbelianNormalizedComplexPsi_eq_selected_of_physical_roots
    (ε D : ℝ) (hc : HillComplexPeriodControl h0q h0r ε D)
    (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ ε) (n : ℕ) (hn : 1 ≤ n) (a : Coeff 2)
    (ha : star a = a)
    (hgap : ∀ k : ℕ, 1 ≤ k → k ≠ n → hillAbelianHilbertRootEnergy a k ∈
      segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ))
    (hperiods : ∀ k : ℕ, 1 ≤ k → k ≠ n →
      hillAbelianComplexPeriod 0 h0q h0r n k (a,SpectralWeight.one.toCoeff q) = 0) :
    hillAbelianNormalizedComplexPsi h0q h0r n (a,SpectralWeight.one.toCoeff q) =
      hillAbelianSelectedGlobalPsi q hq hr n hn := by
  let roots := hillAbelianPhysicalRootSequence q hq hr n a
  have hroots : roots ∈ hillGapRootBox q hq hr :=
    hillAbelianPhysicalRootSequence_mem_gapRootBox q hq hr n a hgap
  have hψ (E : ℂ) : hillAbelianPsiCandidate roots n E = hillAbelianHilbertPsi n (E,a) :=
    hillAbelianPsiCandidate_physicalRootSequence_eq q hq hr n a ha E
  have hperiod (k : ℕ) (hk : 1 ≤ k) : hillAbelianCandidatePeriod q hq hr roots n k =
      hillAbelianComplexPeriod 0 h0q h0r n k (a,SpectralWeight.one.toCoeff q) := by
    rw [hillAbelianComplexPeriod_eq_intrinsic_physical h0q h0r ε D hc q hq hr hp n k hk a]
    unfold hillAbelianCandidatePeriod
    simp_rw [hψ]
  have he := hillAbelian_normalized_candidate_eq_selected q hq hr roots hroots n hn
    (fun k hk hkn => by rw [hperiod k hk]; exact hperiods k hk hkn)
  rw [hperiod n hn] at he
  change (fun E => hillAbelianHilbertPsi n (E,a)/
    hillAbelianComplexPeriod 0 h0q h0r n n (a,SpectralWeight.one.toCoeff q)) = _
  simpa only [hψ] using he

end NLS.KdV
