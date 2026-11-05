import NLS.Articles.KdVKdV2Frequencies.NativeRoughFourierAbelianMap
import NLS.KdV.HillHminusAbelianDerivative
import NLS.ComplexAnalysis.AnalyticOpenInverse

/-! # An actual local analytic inverse at the H-minus-one endpoint

Both mean-zero spaces use their exact weight isometries. The source lift
is H-minus-one, the target lift is H-minus-one-half, and both inverse
identities are identities of the actual signed physical Abelian extension.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

theorem exists_hillHminus_native_meanZero_abelian_inverse :
    ∃ η : ℝ, ∃ Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2,
      ∃ U V : Set (DeletedCoeff 2 0), ∃ G : DeletedCoeff 2 0 → DeletedCoeff 2 0,
      0 < η ∧ AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η) ∧ Z 0=0 ∧
      (∀ q∈ball (0 : PeriodOneHminusOne) η, (Z q).val 0=0) ∧
      (∀ q∈ball (0 : PeriodOneHminusOne) η, IsRealPeriodOneHminusOne q →
        ∀ j : ℤ, (Z q).val (-j)=conj ((Z q).val j)) ∧
      (∀ p : RealPeriodOneHillPotential,
        (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ j : ℤ,
        (Z (hillPhysicalHminusEmbedding p).val).val j=
          hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j) ∧
      IsOpen U ∧ IsOpen V ∧ 0∈U ∧ 0∈V ∧ U⊆ball (0 : DeletedCoeff 2 0) η ∧
      let F := WeightedCoeff.meanZeroWeightedMap (Weight.sobolev (-1/2))
        (fun u => Z ((WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2).symm u))
      F '' U=V ∧ Set.BijOn F U V ∧ AnalyticOnNhd ℂ F U ∧ AnalyticOnNhd ℂ G V ∧
      (∀ a∈U, G (F a)=a ∧
        WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) (F a)=
          Z (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) a)) ∧
      ∀ b∈V, G b∈U ∧ Z (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) (G b))=
        WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b := by
  obtain ⟨η,_C,Z,hη,_hC,hZa,hZ0,hZb,hZr,hZp,hFourier⟩ := exists_hillHminus_native_fourier_abelian_map
  let v := Weight.sobolev (-1)
  let w := Weight.sobolev (-1/2)
  let J := (WeightedCoeff.weightIsometry v 2).symm
  let Y : Coeff 2 → WeightedCoeff w 2 := fun u => Z (J u)
  let F := WeightedCoeff.meanZeroWeightedMap w Y
  have hYa : AnalyticOnNhd ℂ Y (ball (0 : Coeff 2) η) := by
    intro u hu
    have hmem : J u∈ball (0 : PeriodOneHminusOne) η := by
      simpa only [mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hu
    exact (hZa _ hmem).comp (f := J) (J.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt u)
  have hFa : AnalyticOnNhd ℂ F (ball (0 : DeletedCoeff 2 0) η) :=
    WeightedCoeff.analyticOnNhd_meanZeroWeightedMap w Y η hYa
  have hF0 : F 0=0 := by
    change WeightedCoeff.meanZeroWeightedProjectionCLM w (Z (J 0))=0
    rw [map_zero,hZ0,map_zero]
  have hunit := isUnit_fderiv_meanZeroHminusAbelianMap Z
    (hZa 0 (mem_ball_self hη)).differentiableAt hFourier
  obtain ⟨U,V,hU,hV,h0U,h0V,hsub,himage,hbij,G,hFaU,hGa,hleft,hright⟩ :=
    NLS.ComplexAnalysis.exists_analytic_inverse_open_sets isOpen_ball hFa (mem_ball_self hη) hunit
  have hsource (a : DeletedCoeff 2 0) (ha : a∈U) :
      WeightedCoeff.meanZeroWeightedLiftCLM v a∈ball (0 : PeriodOneHminusOne) η := by
    simpa only [mem_ball_zero_iff,WeightedCoeff.meanZeroWeightedLift_norm] using hsub ha
  have hlift (a : DeletedCoeff 2 0) (ha : a∈U) :
      WeightedCoeff.meanZeroWeightedLiftCLM w (F a)=Z (WeightedCoeff.meanZeroWeightedLiftCLM v a) :=
    WeightedCoeff.meanZeroWeightedLift_projection w _ ((hZb _ (hsource a ha)).2)
  refine ⟨η,Z,U,V,G,hη,hZa,hZ0,(fun q hq => (hZb q hq).2),hZr,hZp,hU,hV,h0U,
    by simpa only [hF0] using h0V,hsub,himage,hbij,hFaU,hGa,?_,?_⟩
  · intro a ha
    exact ⟨hleft a ha,hlift a ha⟩
  · intro b hb
    obtain ⟨hGb,he⟩ := hright b hb
    exact ⟨hGb,(hlift (G b) hGb).symm.trans (by rw [he])⟩

end NLS.Articles.KdVKdV2Frequencies
