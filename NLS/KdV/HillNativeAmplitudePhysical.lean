import NLS.KdV.HillNativeAmplitudePrefactor

/-! # One common physical neighborhood for all native amplitude factors -/
noncomputable section
open Set Metric Complex
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillNativeAbelianAmplitudePrefactor_all_physical_matching :
    ∃ η : ℝ, 0 < η ∧ ∀ q : RealPeriodOneHillPotential, ∀ u : Coeff 2,
      SpectralWeight.one.toCoeff q.val = Coeff.periodDouble u → ‖u‖ < η → ∀ k : ℕ+,
      hillNativeAbelianAmplitudePrefactor h0q h0r k u =
        hillAbelianAmplitudePrefactor q.val q.property.1 q.property.2 (k : ℕ) := by
  obtain ⟨η,hη,hphysical⟩ := exists_hillNativeActionGapRatio_all_physical_matching h0q h0r
  exact ⟨η,hη,fun q u hcoeff hu k => hillNativeAbelianAmplitudePrefactor_eq_of_ratio h0q h0r k q u
    (hphysical q u hcoeff hu k)⟩

end NLS.KdV
