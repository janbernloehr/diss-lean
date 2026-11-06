import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianNativeGerms
import NLS.Articles.KdVKdV2Frequencies.ActualRoughFourierDifferential

/-! # Exact origin and Fourier differential for the SAME global map

Every original physical local extension agrees with the global signed
map on an actual complex neighborhood of zero. Consequently the origin
and its full mean-zero rough Fourier derivative belong to this map.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV
namespace GlobalRoughAbelianForwardData

theorem signed_eqOn_original_extension (D : GlobalRoughAbelianForwardData)
    (η : ℝ) (hη : 0 < η)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (hZa : AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η))
    (hphys : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val ∈ ball (0 : PeriodOneHminusOne) η → ∀ j : ℤ,
      (Z (hillPhysicalHminusEmbedding p).val).val j =
        hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ η ∧ ball (0 : PeriodOneHminusOne) ρ ⊆ D.domain ∧
      EqOn D.signed Z (ball (0 : PeriodOneHminusOne) ρ) := by
  let q0 : PeriodOneRealHminusOne := ⟨0,by intro j; simp⟩
  let ρ := min η (D.chart q0).data.radius
  have hρ : 0 < ρ := lt_min hη (D.chart q0).data.radius_pos
  have hsub : ball (0 : PeriodOneHminusOne) ρ ⊆ D.domain :=
    (ball_subset_ball (min_le_right _ _)).trans (D.chart_subset_domain q0)
  have hηsub : ball (0 : PeriodOneHminusOne) ρ ⊆ ball (0 : PeriodOneHminusOne) η :=
    ball_subset_ball (min_le_left _ _)
  refine ⟨ρ,hρ,min_le_left _ _,hsub,?_⟩
  apply eqOn_weighted_rough_ball_of_physical_eq _ ρ hρ D.signed Z
    (D.signed_analytic.mono hsub) (hZa.mono hηsub)
  intro p hp
  apply Subtype.ext
  funext j
  exact (D.signed_physical p j).trans (hphys p (hηsub hp) j).symm

theorem signed_at_origin (D : GlobalRoughAbelianForwardData) : D.signed 0 = 0 := by
  obtain ⟨η,_C,Z,hη,_hC,hZa,hZ0,_hZb,_hZr,hphys,_hZF⟩ :=
    exists_hillHminus_native_fourier_abelian_map
  obtain ⟨ρ,hρ,_hle,_hsub,he⟩ := D.signed_eqOn_original_extension η hη Z hZa hphys
  exact (he (mem_ball_self hρ)).trans hZ0

/-- The literal paper differential (2 |j| pi)^(-1/2), for every
mean-zero rough direction and every signed output coefficient. -/
theorem signed_fourier_differential (D : GlobalRoughAbelianForwardData)
    (h : PeriodOneHminusOne) (hm : h.val 0 = 0) (j : ℤ) :
    ((fderiv ℂ D.signed 0) h).val j =
      (Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹*h.val j := by
  let q0 : PeriodOneRealHminusOne := ⟨0,by intro k; simp⟩
  exact actual_rough_abelian_fourier_differential (D.chart q0).data.radius
    (D.chart q0).data.radius_pos D.signed
    (D.signed_analytic.mono (D.chart_subset_domain q0))
    (fun p _ k => D.signed_physical p k) h hm j

end GlobalRoughAbelianForwardData
end NLS.Articles.KdVKdV2Frequencies
