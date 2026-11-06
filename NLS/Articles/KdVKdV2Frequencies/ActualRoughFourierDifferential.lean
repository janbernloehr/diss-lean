import NLS.Articles.KdVKdV2Frequencies.NativeRoughFourierAbelianMap
import NLS.KdV.HillRoughPhysicalUniqueness

/-! # The Fourier differential of ANY given actual rough Abelian map

Original physical recovery identifies the whole complex germ with the
verified Fourier map. Thus all derivatives belong to the supplied map;
an independent existential choice is never substituted for its inverse.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

theorem actual_rough_abelian_fourier_differential
    (η : ℝ) (hη : 0<η)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (hZa : AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η))
    (hphys : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ j : ℤ,
      (Z (hillPhysicalHminusEmbedding p).val).val j=
        hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j) :
    ∀ h : PeriodOneHminusOne, h.val 0=0 → ∀ j : ℤ,
      ((fderiv ℂ Z 0) h).val j=(Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹*h.val j := by
  obtain ⟨δ,C,Y,hδ,_hC,hYa,_hY0,_hYb,_hYr,hYphys,hYF⟩ := exists_hillHminus_native_fourier_abelian_map
  let ρ := min η δ
  have hρ : 0<ρ := lt_min hη hδ
  have hηsub : ball (0 : PeriodOneHminusOne) ρ⊆ball (0 : PeriodOneHminusOne) η :=
    ball_subset_ball (min_le_left _ _)
  have hδsub : ball (0 : PeriodOneHminusOne) ρ⊆ball (0 : PeriodOneHminusOne) δ :=
    ball_subset_ball (min_le_right _ _)
  have he : EqOn Z Y (ball (0 : PeriodOneHminusOne) ρ) := by
    apply eqOn_weighted_rough_ball_of_physical_eq _ ρ hρ Z Y (hZa.mono hηsub) (hYa.mono hδsub)
    intro p hp
    apply Subtype.ext
    funext j
    exact (hphys p (hηsub hp) j).trans (hYphys p (hδsub hp) j).symm
  have hevent : Z =ᶠ[𝓝 (0 : PeriodOneHminusOne)] Y :=
    Filter.eventuallyEq_of_mem (ball_mem_nhds _ hρ) he
  have hd : fderiv ℂ Z 0=fderiv ℂ Y 0 := hevent.fderiv_eq
  intro h hh j
  rw [hd]
  exact hYF h hh j

end NLS.Articles.KdVKdV2Frequencies
