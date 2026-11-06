import NLS.Articles.KdVKdV2Frequencies.NativeRoughSobolevSignedAbelian
import NLS.KdV.HillRoughPhysicalUniqueness

/-! # Stronger Sobolev germs of ANY SAME actual signed rough map

Original physical recovery uniquely identifies the full complex rough
map. The constructed stronger signed germs therefore restrict the GIVEN
actual map, preserving any inverse and canonical identities it already has.
One common rough radius precedes every order and eligible real source.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

private theorem restrict_actual_germ
    {E P F Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup P] [NormedSpace ℂ P]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : E →L[ℂ] P) (I : F → Y) (A B : P → Y)
    (V : Set P) (hV : IsOpen V) (heq : EqOn A B V)
    (q : E) (hqV : L q∈V) (U : Set E) (hU : IsOpen U) (hqU : q∈U)
    (C : ℝ) (g : E → F) (hC : 0≤C) (hga : AnalyticOnNhd ℂ g U)
    (hdata : ∀ p∈U, ‖g p‖≤C ∧ I (g p)=A (L p)) :
    ∃ W : Set E, IsOpen W ∧ q∈W ∧ ∃ C : ℝ, ∃ g : E → F,
      0≤C ∧ AnalyticOnNhd ℂ g W ∧ ∀ p∈W, L p∈V ∧ ‖g p‖≤C ∧ I (g p)=B (L p) := by
  let W := U∩L ⁻¹' V
  refine ⟨W,hU.inter (hV.preimage L.continuous),⟨hqU,hqV⟩,C,g,hC,hga.mono inter_subset_left,?_⟩
  intro p hp
  exact ⟨hp.2,(hdata p hp.1).1,((hdata p hp.1).2).trans (heq hp.2)⟩

/-- The GIVEN actual signed rough map has all stronger complex native
Sobolev germs on ONE smaller rough ball, before ALL orders and sources.
The map itself is not replaced by another existential coordinate family. -/
theorem exists_hillHminus_actual_signed_sobolev_restrictions
    (η : ℝ) (hη : 0<η)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (hZa : AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η))
    (hZphys : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ j : ℤ,
        (Z (hillPhysicalHminusEmbedding p).val).val j=
          hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j) :
    ∃ ρ : ℝ, 0<ρ ∧ ρ≤η ∧
      ∀ t : ℝ, ∀ ht : 0≤t, ∀ q : WeightedCoeff (Weight.sobolev (t-1)) 2,
        IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht q) →
        periodOneSobolevImageInclusion t ht q∈ball (0 : PeriodOneHminusOne) ρ →
        ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
          ∃ C : ℝ, ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev (t-1/2)) 2,
            0≤C ∧ AnalyticOnNhd ℂ g V ∧ ∀ p∈V,
              periodOneSobolevImageInclusion t ht p∈ball (0 : PeriodOneHminusOne) ρ ∧ ‖g p‖≤C ∧
              WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) (g p)=
                Z (periodOneSobolevImageInclusion t ht p) := by
  obtain ⟨r,Y,hr,hYa,_hY0,hYphys,_hYreal,hstrong⟩ := exists_hillHminus_actual_all_sobolev_signed_abelian
  let ρ := min η r
  have hρ : 0<ρ := lt_min hη hr
  have hsubZ : ball (0 : PeriodOneHminusOne) ρ⊆ball (0 : PeriodOneHminusOne) η :=
    ball_subset_ball (min_le_left _ _)
  have hsubY : ball (0 : PeriodOneHminusOne) ρ⊆ball (0 : PeriodOneHminusOne) r :=
    ball_subset_ball (min_le_right _ _)
  have hEq : EqOn Y Z (ball (0 : PeriodOneHminusOne) ρ) := by
    apply eqOn_weighted_rough_ball_of_physical_eq (Weight.sobolev (-1/2)) ρ hρ Y Z
      (hYa.mono hsubY) (hZa.mono hsubZ)
    intro p hp
    apply Subtype.ext
    funext j
    exact (hYphys p (hsubY hp) j).trans (hZphys p (hsubZ hp) j).symm
  refine ⟨ρ,hρ,min_le_left _ _,?_⟩
  intro t ht q hreal hq
  obtain ⟨U,hU,hqU,C,g,hC,hga,hdata⟩ := hstrong t ht q hreal (hsubY hq)
  exact restrict_actual_germ (periodOneSobolevImageInclusion t ht)
    (WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2)) Y Z
    (ball (0 : PeriodOneHminusOne) ρ) isOpen_ball hEq q hq U hU hqU C g hC hga
    (fun p hp => (hdata p hp).2)

end NLS.Articles.KdVKdV2Frequencies
