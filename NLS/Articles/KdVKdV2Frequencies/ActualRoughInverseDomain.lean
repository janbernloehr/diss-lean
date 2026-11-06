import NLS.Articles.KdVKdV2Frequencies.ActualWeakJacobianNeighborhood
import NLS.ComplexAnalysis.CommonInverseDomain

/-! # ONE actual common rough inverse domain before all native orders -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

/-- The GIVEN actual rough R is a left inverse on ONE common normalized
rough source ball inside an actual weak injectivity domain. The choice
precedes every stronger order and eligible real base. -/
theorem exists_actual_common_rough_inverse_domain
    (η : ℝ) (hη : 0<η)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (hZa : AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η)) (hZ0 : Z 0=0)
    (hphys : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ j : ℤ,
      (Z (hillPhysicalHminusEmbedding p).val).val j=
        hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j)
    (W : Set (DeletedCoeff 2 0)) (hW : IsOpen W) (h0W : (0 : DeletedCoeff 2 0)∈W)
    (R : DeletedCoeff 2 0 → PeriodOneHminusOne) (hRc : ContinuousOn R W) (hR0 : R 0=0)
    (hRdata : ∀ b∈W, (R b).val 0=0 ∧ Z (R b)=WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b) :
    ∃ δ : ℝ, ∃ U : Set (DeletedCoeff 2 0), 0<δ ∧ δ≤η ∧ IsOpen U ∧ 0∈U ∧
      U⊆ball (0 : DeletedCoeff 2 0) η ∧ InjOn (weakMeanZeroAbelianMap Z) U ∧
      ∀ a∈ball (0 : DeletedCoeff 2 0) δ, a∈U ∧ weakMeanZeroAbelianMap Z a∈W ∧
        WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1)) (R (weakMeanZeroAbelianMap Z a))∈U ∧
        R (weakMeanZeroAbelianMap Z a)=WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) a := by
  let L := WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))
  let P := WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1))
  let Q := WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))
  let F := weakMeanZeroAbelianMap Z
  let R0 := fun b => P (R b)
  have hFa : AnalyticOnNhd ℂ F (ball (0 : DeletedCoeff 2 0) η) := by
    intro a ha
    have hLa : L a∈ball (0 : PeriodOneHminusOne) η := by
      simpa only [L,mem_ball_zero_iff,WeightedCoeff.meanZeroWeightedLift_norm] using ha
    exact (Q.analyticAt _).comp ((hZa (L a) hLa).comp (L.analyticAt a))
  have hF0 : F 0=0 := by simp only [F,weakMeanZeroAbelianMap,map_zero,hZ0]
  have hu : IsUnit (fderiv ℂ F 0) := by
    change IsUnit (fderiv ℂ (WeightedCoeff.meanZeroWeightedMap (Weight.sobolev (-1/2))
      (fun u => Z ((WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2).symm u))) 0)
    exact isUnit_fderiv_meanZeroHminusAbelianMap Z (hZa 0 (mem_ball_self hη)).differentiableAt
      (actual_rough_abelian_fourier_differential η hη Z hZa hphys)
  obtain ⟨U,_B,hU,_hB,h0U,_hF0B,hUη,_himage,hbij,_G,_hFa,_hGa,_hl,_hr⟩ :=
    NLS.ComplexAnalysis.exists_analytic_inverse_open_sets isOpen_ball hFa (mem_ball_self hη) hu
  have hRc0 : ContinuousOn R0 W := P.continuous.comp_continuousOn hRc
  have hR00 : R0 0=0 := by simp only [R0,hR0,map_zero]
  have hsolve (b : DeletedCoeff 2 0) (hb : b∈W) : F (R0 b)=b := by
    change Q (Z (L (P (R b))))=b
    rw [WeightedCoeff.meanZeroWeightedLift_projection _ _ (hRdata b hb).1,(hRdata b hb).2]
    exact WeightedCoeff.meanZeroWeightedProjection_lift _ b
  obtain ⟨A,hA,h0A,hAU,hAd⟩ := NLS.ComplexAnalysis.exists_common_leftInverse_domain
    F U hU h0U (hFa.mono hUη).continuousOn hF0 hbij.injOn W hW h0W R0 hRc0 hR00 hsolve
  obtain ⟨ε,hε,hεA⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds h0A)
  let δ := min η ε
  have hδ : 0<δ := lt_min hη hε
  have hδA : ball (0 : DeletedCoeff 2 0) δ⊆A :=
    fun _ ha => hεA (ball_subset_ball (min_le_right _ _) ha)
  refine ⟨δ,U,hδ,min_le_left _ _,hU,h0U,hUη,hbij.injOn,?_⟩
  intro a ha
  have hd := hAd a (hδA ha)
  refine ⟨hAU (hδA ha),hd.1,hd.2.1,?_⟩
  have hx := congrArg L hd.2.2
  change L (P (R (F a)))=L a at hx
  rw [WeightedCoeff.meanZeroWeightedLift_projection _ _ (hRdata _ hd.1).1] at hx
  exact hx

end NLS.Articles.KdVKdV2Frequencies
