import NLS.Articles.KdVKdV2Frequencies.NativeRoughRealAbelianInverse
import NLS.KdV.HillRoughAbelianGardner
import NLS.KdV.HillBirkhoffAbelianNormalization

/-! # One actual canonical rough Abelian chart and its real local inverse

The same native chart has the full original Gardner matrix at every complex
mean-zero H-minus-one source in its ball, admits a two-sided analytic real
local inverse at zero, and agrees with the fixed GLOBAL original L2
Birkhoff map wherever a physical L2 source belongs to the rough ball.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

theorem exists_hillHminus_native_canonical_real_abelian_inverse :
    ∃ η : ℝ, ∃ Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2,
      ∃ U V : Set (DeletedCoeff 2 0), ∃ G : DeletedCoeff 2 0 → DeletedCoeff 2 0,
      0 < η ∧ AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η) ∧ Z 0=0 ∧
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
      (∀ b∈V, G b∈U ∧ Z (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) (G b))=
        WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b) ∧
      (∀ b∈V, deletedL2Conjugation b=b → deletedL2Conjugation (G b)=G b) ∧
      (∀ b∈V, deletedL2Conjugation b=b → ∃ q : PeriodOneRealHminusOne,
        q.val.val 0=0 ∧ q.val∈ball (0 : PeriodOneHminusOne) η ∧
          WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1)) q.val=G b ∧
          Z q.val=WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b) ∧
      (∀ q∈ball (0 : PeriodOneHminusOne) η, q.val 0=0 →
        ∀ (σ τ : Bool) (n m : ℕ+),
          NLS.Poisson.hminusGardnerBracket (hillRoughSignedAbelianComponent Z σ n)
            (hillRoughSignedAbelianComponent Z τ m) q=hillOriginalComplexGardnerMatrixEntry σ τ n m/2) ∧
      ∀ q : hillRealMeanZeroSourceSubmodule,
        hillOriginalHminusSource q.val.val∈ball (0 : PeriodOneHminusOne) η → ∀ n : ℕ+,
          (Z (hillOriginalHminusSource q.val.val)).val (n : ℤ)=hillOriginalBirkhoffAbelianCoordinate q n := by
  obtain ⟨η,Z,U,V,G,hη,hZa,hZ0,hZp,hU,hV,h0U,h0V,hsub,himage,hbij,hFa,hGa,hleft,hright,hGr,hGreal⟩ :=
    exists_hillHminus_native_real_abelian_inverse
  refine ⟨η,Z,U,V,G,hη,hZa,hZ0,hZp,hU,hV,h0U,h0V,hsub,himage,hbij,hFa,hGa,hleft,hright,hGr,hGreal,?_,?_⟩
  · intro q hq hmean σ τ n m
    exact hillRoughAbelian_Gardner_matrix_on_complex_ball Z η hη hZa hZp q hq hmean σ τ n m
  · intro q hq n
    exact hillBirkhoffAbelian_rough_map_agreement Z (ball (0 : PeriodOneHminusOne) η) hZp q hq n

end NLS.Articles.KdVKdV2Frequencies
