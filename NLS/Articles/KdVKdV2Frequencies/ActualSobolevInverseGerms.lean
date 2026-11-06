import NLS.Articles.KdVKdV2Frequencies.ActualRoughFourierDifferential
import NLS.Articles.KdVKdV2Frequencies.ActualSignedSobolevRestriction
import NLS.KdV.HillSobolevAbelianInverse

/-! # All stronger analytic germs of ANY SAME actual rough inverse at zero

Original physical recovery fixes the Fourier differential and all native
complex forward restrictions. The analytic inverse theorem and actual
weak uniqueness then prove strong analyticity of the supplied inverse.
The strong neighborhoods may depend on the Sobolev order.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

private theorem reindex_native_restriction
    (a b s : ℝ) (hs : -1≤s) (ha : a=s) (hb : b=s+1/2)
    (ha0 : -1≤a)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (V : Set (WeightedCoeff (Weight.sobolev a) 2)) (hV : IsOpen V)
    (h0V : (0 : WeightedCoeff (Weight.sobolev a) 2)∈V)
    (g : WeightedCoeff (Weight.sobolev a) 2 → WeightedCoeff (Weight.sobolev b) 2)
    (hga : AnalyticOnNhd ℂ g V)
    (he : ∀ p∈V, ∀ j : ℤ, (g p).val j=(Z (WeightedCoeff.sobolevInclusion ha0 p)).val j) :
    ∃ V' : Set (WeightedCoeff (Weight.sobolev s) 2), IsOpen V' ∧ 0∈V' ∧
      ∃ g' : WeightedCoeff (Weight.sobolev s) 2 → WeightedCoeff (Weight.sobolev (s+1/2)) 2,
        AnalyticOnNhd ℂ g' V' ∧ ∀ p∈V', ∀ j : ℤ,
          (g' p).val j=(Z (WeightedCoeff.sobolevInclusion hs p)).val j := by
  subst a
  subst b
  exact ⟨V,hV,h0V,g,hga,he⟩

/-- Native complex analytic inverse germs at zero in the exact isometric
mean-zero h^(s+1/2) chart, with literal source/target inclusions. -/
def HasAllSobolevInverseGerms
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (W : Set (DeletedCoeff 2 0)) (R : DeletedCoeff 2 0 → PeriodOneHminusOne) : Prop :=
    ∀ s : ℝ, ∀ hs : -1≤s,
      ∃ T : Set (DeletedCoeff 2 0), IsOpen T ∧ 0∈T ∧
        ∃ G : DeletedCoeff 2 0 → WeightedCoeff (Weight.sobolev s) 2,
          AnalyticOnNhd ℂ G T ∧ G 0=0 ∧ ∀ b∈T,
            WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ)≤s+1/2) b∈W ∧
            WeightedCoeff.sobolevInclusion hs (G b)=
              R (WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ)≤s+1/2) b) ∧
            (G b).val 0=0 ∧
            Z (WeightedCoeff.sobolevInclusion hs (G b))=
              WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤s+1/2)
                (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (s+1/2)) b)

/-- Every given actual physical rough inverse has native complex analytic
H^s-valued germs on the mean-zero h^(s+1/2) target chart, ALL s>=-1.
The SAME Z,R are used throughout, on actual complex neighborhoods. -/
theorem exists_actual_rough_inverse_all_sobolev_germs
    (η : ℝ) (hη : 0<η)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (hZa : AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η)) (hZ0 : Z 0=0)
    (hphys : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ j : ℤ,
      (Z (hillPhysicalHminusEmbedding p).val).val j=
        hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j)
    (W : Set (DeletedCoeff 2 0)) (hW : IsOpen W) (h0W : (0 : DeletedCoeff 2 0)∈W)
    (R : DeletedCoeff 2 0 → PeriodOneHminusOne) (hRc : ContinuousOn R W) (hR0 : R 0=0)
    (hRdata : ∀ b∈W, (R b).val 0=0 ∧
      Z (R b)=WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b) :
    ∀ s : ℝ, ∀ hs : -1≤s,
      ∃ T : Set (DeletedCoeff 2 0), IsOpen T ∧ 0∈T ∧
        ∃ G : DeletedCoeff 2 0 → WeightedCoeff (Weight.sobolev s) 2,
          AnalyticOnNhd ℂ G T ∧ G 0=0 ∧ ∀ b∈T,
            WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ)≤s+1/2) b∈W ∧
            WeightedCoeff.sobolevInclusion hs (G b)=
              R (WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ)≤s+1/2) b) ∧
            (G b).val 0=0 ∧
            Z (WeightedCoeff.sobolevInclusion hs (G b))=
              WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤s+1/2)
                (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (s+1/2)) b) := by
  have hFourier := actual_rough_abelian_fourier_differential η hη Z hZa hphys
  obtain ⟨ρ,hρ,_hρη,hforward⟩ := exists_hillHminus_actual_signed_sobolev_restrictions η hη Z hZa hphys
  intro s hs
  have hreal : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion (s+1) (by linarith) 0) := by
    intro j
    simp only [map_zero,WeightedCoeff.zero_val,map_zero]
  have hmem : periodOneSobolevImageInclusion (s+1) (by linarith) 0∈ball (0 : PeriodOneHminusOne) ρ := by
    rw [map_zero]
    exact mem_ball_self hρ
  obtain ⟨U,hU,h0U,_C,f,_hC,hfa,hdata⟩ := hforward (s+1) (by linarith) 0 hreal hmem
  have hraw : ∀ p∈U, ∀ j : ℤ, (f p).val j=
      (Z (WeightedCoeff.sobolevInclusion (by linarith : -1≤s+1-1) p)).val j := by
    intro p hp j
    have H := congrArg (fun z => z.val j) (hdata p hp).2.2
    simpa only [periodOneSobolevImageInclusion,WeightedCoeff.sobolevInclusion_apply] using H
  obtain ⟨V,hV,h0V,g,hga,hge⟩ := reindex_native_restriction
    (s+1-1) (s+1-1/2) s hs (by ring) (by ring) (by linarith) Z U hU h0U f hfa hraw
  have hcomm : ∀ p∈V, WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤s+1/2) (g p)=
      Z (WeightedCoeff.sobolevInclusion hs p) := by
    intro p hp
    apply Subtype.ext
    funext j
    simpa only [WeightedCoeff.sobolevInclusion_apply] using hge p hp j
  obtain ⟨T,hT,h0T,G,hGa,hG0,hGdata⟩ := exists_sobolev_abelian_inverse_of_actual_restriction
    η hη Z hZa hZ0 hFourier W hW h0W R hRc hR0 hRdata s hs V hV h0V g hga hcomm
  refine ⟨T,hT,h0T,G,hGa,hG0,?_⟩
  intro b hb
  obtain ⟨hbW,hinc,_hGV,hm,_hstrongright⟩ := hGdata b hb
  refine ⟨hbW,hinc,hm,?_⟩
  rw [hinc,(hRdata _ hbW).2]
  exact WeightedCoeff.meanZeroSobolevInclusion_lift _ b

end NLS.Articles.KdVKdV2Frequencies
