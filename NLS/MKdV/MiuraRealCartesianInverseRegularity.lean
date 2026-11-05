import NLS.MKdV.MiuraRealSobolevCartesianCompatibility
import NLS.ComplexAnalysis.AnalyticInverseRegularityTransfer

/-! # Native Sobolev regularity of the unique small physical L² inverse

The native inverse charts agree with the actual original L² map under
bounded coefficient-preserving inclusions. L² properness and zero-fiber
rigidity therefore make the native small inverse the only physical L²
preimage, so higher regularity follows from native target regularity.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.MKdV

/-- For each integer s>=0, a full open native real target neighborhood
has an analytic H^s inverse, and every physical L² preimage is exactly
that inverse's original coefficient inclusion. -/
theorem exists_miuraPhysicalCartesian_small_inverse_Sobolev_regularity (s : ℕ) :
    ∃ V : Set (MiuraRealSobolevCartesianTarget s), IsOpen V ∧ (0 : MiuraRealSobolevCartesianTarget s) ∈ V ∧
      ∃ G : MiuraRealSobolevCartesianTarget s → MiuraRealSobolevSource s,
        AnalyticOnNhd ℝ G V ∧ G 0 = 0 ∧ ∀ z ∈ V,
          miuraPhysicalSobolevCartesianMap s (G z) = z ∧
          ∀ a : Coeff.physicalRealSubmodule 2,
            miuraPhysicalCartesianMap a = miuraPhysicalSobolevL2CartesianInclusion s z ↔
              a = miuraPhysicalSobolevL2SourceInclusion s (G z) := by
  obtain ⟨U,V,_,hV,_,h0V,_,_,G,_,hGA,hG0,_,hG⟩ := exists_miuraPhysicalSobolevCartesian_localInverse_at_zero s
  obtain ⟨W,hW,h0W,huniq⟩ := exists_miuraPhysicalCartesian_global_unique_small_data
  obtain ⟨T,hT,h0T,hGT,hpre⟩ := @NLS.ComplexAnalysis.exists_analytic_inverse_regularity_neighborhood
    (Coeff.physicalRealSubmodule 2) MiuraRealCartesianTarget (MiuraRealSobolevSource s) (MiuraRealSobolevCartesianTarget s)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    miuraPhysicalCartesianMap (miuraPhysicalSobolevCartesianMap s)
    (miuraPhysicalSobolevL2SourceInclusion s) (miuraPhysicalSobolevL2CartesianInclusion s)
    (miuraPhysicalSobolevL2CartesianInclusion s).continuous (map_zero _) (miuraPhysicalSobolevCartesianMap_L2 s)
    V hV h0V G hGA (fun z hz => (hG z hz).2) W hW h0W huniq
  exact ⟨T,hT,h0T,G,hGT,hG0,hpre⟩

end NLS.MKdV
