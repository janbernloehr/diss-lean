import NLS.Articles.KdVKdV2Frequencies.ActualPositiveAbelianFourier
import NLS.Articles.KdVKdV2Frequencies.NativeRoughAbelianPacket
import NLS.KdV.HillAbelianSignedPhysicalRecovery
import NLS.KdV.HillRoughPhysicalUniqueness
import NLS.SequenceSpaces.SobolevSignedRealCompactGerm

/-! # The actual full signed Fourier principal of the SAME supplied map -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

/-- Both actual conjugate source principals, with exact target transport. -/
def actualSignedFourierPrincipal (D : RoughAbelianFourierData) (e : ℤ → Bool)
    (t : ℝ) (ht : 0≤t) (p : WeightedCoeff (Weight.sobolev (t-1)) 2) :
    WeightedCoeff (Weight.sobolev (t-1)) 2 →L[ℂ] WeightedCoeff (Weight.sobolev (t-1/2)) 2 :=
  WeightedCoeff.nativeSignedPrincipal (Weight.sobolev (t-1)) (Weight.sobolev (t-1/2))
    (Weight.sobolev_neg (t-1)) (actualPositiveFourierPrincipal D e t ht p)
    (actualPositiveFourierPrincipal D e t ht
      (WeightedCoeff.conjugateReflection (Weight.sobolev (t-1)) (Weight.sobolev_neg (t-1)) p))

/-- A genuine full complex native germ, including EXACTLY to the GIVEN
weak map, with its full Fourier compact remainder at every real point. -/
def SignedAbelianFourierGermAt (ρ : ℝ)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (D : RoughAbelianFourierData) (e : ℤ → Bool) (t : ℝ) (ht : 0≤t)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2) : Prop :=
  ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
    (∀ p∈V, WeightedCoeff.conjugateReflection (Weight.sobolev (t-1)) (Weight.sobolev_neg (t-1)) p∈V) ∧
    ∃ C : ℝ, ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev (t-1/2)) 2,
      0≤C ∧ AnalyticOnNhd ℂ g V ∧ ∀ p∈V,
        periodOneSobolevImageInclusion t ht p∈ball (0 : PeriodOneHminusOne) ρ ∧ ‖g p‖≤C ∧
        WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) (g p)=
          Z (periodOneSobolevImageInclusion t ht p) ∧
        (IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht p) →
          IsCompactOperator (fderiv ℂ g p-actualSignedFourierPrincipal D e t ht p))

/-- ONE full actual chart, root witness, uniformly nonzero full positive
symbol, reciprocal and physical signs precede ALL orders and real bases. -/
def HasSignedAbelianFourierGerms (η : ℝ)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2) : Prop :=
  ∃ ρ : ℝ, 0<ρ ∧ ρ≤η ∧ ∃ D : RoughAbelianFourierData, ρ≤D.radius ∧ ∃ e : ℤ → Bool,
    ∀ t : ℝ, ∀ ht : 0≤t, ∀ q : WeightedCoeff (Weight.sobolev (t-1)) 2,
      IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht q) →
      periodOneSobolevImageInclusion t ht q∈ball (0 : PeriodOneHminusOne) ρ →
      SignedAbelianFourierGermAt ρ Z D e t ht q

private theorem signed_fourier_germ_of_positive
    (ρ : ℝ) (Y : PeriodOneHminusOne → Coeff 2)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (hTZ : EqOn (WeightedCoeff.signedTargetLift (Weight.sobolev (-1)) (Weight.sobolev (-1/2)) Y)
      Z (ball (0 : PeriodOneHminusOne) ρ))
    (D : RoughAbelianFourierData) (e : ℤ → Bool) (t : ℝ) (ht : 0≤t)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hqr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht q))
    (hpos : PositiveAbelianFourierGermAt ρ D e Y t ht q) :
    SignedAbelianFourierGermAt ρ Z D e t ht q := by
  obtain ⟨U,hU,hqU,M,H,hM,hHa,hdata⟩ := hpos
  obtain ⟨V,hV,hqV,_hVU,hJ,C,g,hC,hga,hd⟩ := exists_sobolev_signedTargetLift_real_compact_germ
    t ht Y ρ q hqr U hU hqU M hM H hHa
    (fun p hp => ⟨(hdata p hp).1,(hdata p hp).2.1,(hdata p hp).2.2.1⟩)
    (actualPositiveFourierPrincipal D e t ht) (fun p hp => (hdata p hp).2.2.2)
  refine ⟨V,hV,hqV,hJ,C,g,hC,hga,?_⟩
  intro p hp
  exact ⟨(hd p hp).1,(hd p hp).2.1,
    ((hd p hp).2.2.1).trans (hTZ (hd p hp).1),(hd p hp).2.2.2⟩

/-- ANY GIVEN actual signed physical coordinate map has the full actual
Fourier principal plus compact, with native complex germs in ALL orders.
ONE smaller rough ball and retained actual spectral data precede them. -/
theorem exists_actual_signed_abelian_fourier_germs
    (η : ℝ) (hη : 0<η)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (hZa : AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η))
    (hZphys : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ j : ℤ,
      (Z (hillPhysicalHminusEmbedding p).val).val j=
        hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j) :
    HasSignedAbelianFourierGerms η Z := by
  obtain ⟨D⟩ := nonempty_roughAbelianFourierData
  obtain ⟨r,_CY,Y,hr,_hCY,hYa,_hY0,hYb,hYphys⟩ := exists_hillHminus_native_normalized_abelian_packet
  let r0 := min η r
  have hr0 : 0<r0 := lt_min hη hr
  have hsub0Y : ball (0 : PeriodOneHminusOne) r0⊆ball (0 : PeriodOneHminusOne) r :=
    ball_subset_ball (min_le_right _ _)
  obtain ⟨ρ,hρ,hρ0,hρD,e,_heq,hstrong⟩ := exists_actual_positive_abelian_fourier_germs
    D r0 hr0 Y (hYa.mono hsub0Y) (fun p hp => (hYb p (hsub0Y hp)).2)
    (fun p hp n => hYphys p (hsub0Y hp) n)
  have hρη : ρ≤η := hρ0.trans (min_le_left _ _)
  have hsubZ : ball (0 : PeriodOneHminusOne) ρ⊆ball (0 : PeriodOneHminusOne) η :=
    ball_subset_ball hρη
  have hsubY : ball (0 : PeriodOneHminusOne) ρ⊆ball (0 : PeriodOneHminusOne) r :=
    ball_subset_ball (hρ0.trans (min_le_right _ _))
  let T := WeightedCoeff.signedTargetLift (Weight.sobolev (-1)) (Weight.sobolev (-1/2)) Y
  have hTa : AnalyticOnNhd ℂ T (ball (0 : PeriodOneHminusOne) ρ) := by
    intro p hp
    apply WeightedCoeff.analyticOnNhd_signedTargetLift (Weight.sobolev (-1)) (Weight.sobolev (-1/2))
      (Weight.sobolev_neg (-1)) Y (ball (0 : PeriodOneHminusOne) r) hYa p
    refine ⟨hsubY hp,?_⟩
    simpa only [mem_preimage,mem_ball_zero_iff,WeightedCoeff.norm_conjugateReflection] using hsubY hp
  have hTZ : EqOn T Z (ball (0 : PeriodOneHminusOne) ρ) := by
    apply eqOn_weighted_rough_ball_of_physical_eq _ ρ hρ T Z hTa (hZa.mono hsubZ)
    intro p hp
    apply Subtype.ext
    funext j
    exact (hillAbelian_signedTargetLift_physical r Y (fun q hq => (hYb q hq).2) hYphys p (hsubY hp) j).trans
      (hZphys p (hsubZ hp) j).symm
  exact ⟨ρ,hρ,hρη,D,hρD,e,fun t ht q hqr hq =>
    signed_fourier_germ_of_positive ρ Y Z hTZ D e t ht q hqr (hstrong t ht q hqr hq)⟩

end NLS.Articles.KdVKdV2Frequencies
