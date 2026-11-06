import NLS.Articles.KdVKdV2Frequencies.NativeRoughCanonicalAbelianInverse
import NLS.Articles.KdVKdV2Frequencies.RoughAbelianClosedGaps
import NLS.KdV.HillHminusFiniteGapSobolev
import NLS.KdV.HillRoughPhysicalL2Reconstruction
import NLS.KdV.HillBirkhoffAbelianMass

/-! # Actual finite-support targets have regular physical preimages

Every real finite-support target in one open negative-half neighborhood
has a genuine real mean-zero rough preimage with ALL nonnegative Sobolev
orders. L2 membership of the preimage is derived, never assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

open NLS.KdV

theorem exists_hillHminus_native_finite_support_regular_preimages :
    ∃ η : ℝ, ∃ Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2,
      ∃ W : Set (DeletedCoeff 2 0), ∃ R : DeletedCoeff 2 0 → PeriodOneHminusOne,
      0<η ∧ AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η) ∧ Z 0=0 ∧
      (∀ p : RealPeriodOneHillPotential,
        (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ j : ℤ,
        (Z (hillPhysicalHminusEmbedding p).val).val j=
          hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j) ∧
      IsOpen W ∧ 0∈W ∧ AnalyticOnNhd ℂ R W ∧ R 0=0 ∧
      (∀ b∈W, (R b).val 0=0 ∧ R b∈ball (0 : PeriodOneHminusOne) η ∧
        Z (R b)=WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b) ∧
      (∀ b∈W, deletedL2Conjugation b=b → IsRealPeriodOneHminusOne (R b)) ∧
      ∀ b∈W, deletedL2Conjugation b=b →
        (Function.support b.val).Finite → ∃ q : PeriodOneRealHminusOne,
          q.val=R b ∧ q.val.val 0=0 ∧ q.val∈ball (0 : PeriodOneHminusOne) η ∧
          Z q.val=WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b ∧
          ∀ s : ℝ, 0≤s → Memℓp (fun n => (Weight.sobolev s n : ℂ)*q.val.val n) 2 := by
  obtain ⟨η,Z,U,V,G,hη,hZa,hZ0,hZp,hU,hV,h0U,h0V,_hsub,_himage,_hbij,_hFa,hGa,hleft,hright,_hGr,hGreal,_hcanon,_hfixed⟩ :=
    exists_hillHminus_native_canonical_real_abelian_inverse
  obtain ⟨ρ,hρ,hρη,hrecover⟩ := exists_hillHminus_rough_abelian_closed_gap_recovery η hη Z hZa hZp
  have hG0 : G 0=0 := by
    have hh := (hleft 0 h0U).1
    simpa only [WeightedCoeff.meanZeroWeightedMap,Submodule.coe_zero,map_zero,hZ0] using hh
  let W := V∩G ⁻¹' ball (0 : DeletedCoeff 2 0) ρ
  have hW : IsOpen W := hGa.continuousOn.isOpen_inter_preimage hV isOpen_ball
  have h0W : 0∈W := ⟨h0V,by change G 0∈ball (0 : DeletedCoeff 2 0) ρ; rw [hG0]; exact mem_ball_self hρ⟩
  let R : DeletedCoeff 2 0 → PeriodOneHminusOne :=
    fun b => WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) (G b)
  have hRa : AnalyticOnNhd ℂ R W := fun b hb =>
    ((WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))).analyticAt _).comp (hGa b hb.1)
  have hR0 : R 0=0 := by
    change WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) (G 0)=0
    rw [hG0,map_zero]
  have hRdata (b : DeletedCoeff 2 0) (hb : b∈W) :
      (R b).val 0=0 ∧ R b∈ball (0 : PeriodOneHminusOne) η ∧
        Z (R b)=WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b := by
    have hRb : R b∈ball (0 : PeriodOneHminusOne) ρ := by
      rw [mem_ball_zero_iff]
      change ‖WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) (G b)‖<ρ
      rw [WeightedCoeff.meanZeroWeightedLift_norm]
      exact mem_ball_zero_iff.mp hb.2
    refine ⟨?_,ball_subset_ball hρη hRb,(hright b hb.1).2⟩
    change (G b).val 0/(Weight.sobolev (-1) 0 : ℂ)=0
    have hmean : (G b).val 0=0 := (G b).property
    rw [hmean,zero_div]
  have hRreal (b : DeletedCoeff 2 0) (hb : b∈W) (hbr : deletedL2Conjugation b=b) :
      IsRealPeriodOneHminusOne (R b) := by
    obtain ⟨q,hqm,_,hqproj,_⟩ := hGreal b hb.1 hbr
    have hh : R b=q.val := by
      change WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) (G b)=q.val
      rw [←hqproj,WeightedCoeff.meanZeroWeightedLift_projection _ _ hqm]
    rw [hh]
    exact q.property
  refine ⟨η,Z,W,R,hη,hZa,hZ0,hZp,hW,h0W,hRa,hR0,hRdata,hRreal,?_⟩
  intro b hb hbr hbf
  obtain ⟨q,hqm,hqball,hqproj,hqZ⟩ := hGreal b hb.1 hbr
  have hqlift : q.val=WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) (G b) := by
    rw [←hqproj]
    exact (WeightedCoeff.meanZeroWeightedLift_projection _ q.val hqm).symm
  have hqρ : q.val∈ball (0 : PeriodOneHminusOne) ρ := by
    rw [mem_ball_zero_iff,hqlift,WeightedCoeff.meanZeroWeightedLift_norm]
    exact mem_ball_zero_iff.mp hb.2
  classical
  let S := hbf.toFinset
  let N := S.sup Int.natAbs+1
  have hN : 1≤N := by dsimp only [N];omega
  have htail (n : ℕ) (hn : N≤n) : (Z q.val).val (n : ℤ)=0 := by
    have hbzero : b.val (n : ℤ)=0 := by
      by_contra hne
      have hmem : (n : ℤ)∈S := hbf.mem_toFinset.mpr hne
      have hh := Finset.le_sup (f := Int.natAbs) hmem
      simp only [Int.natAbs_natCast] at hh
      dsimp only [N] at hn
      omega
    rw [hqZ]
    change b.val (n : ℤ)/(Weight.sobolev (-1/2) (n : ℤ) : ℂ)=0
    rw [hbzero,zero_div]
  have hclosed (n : ℕ) (hn : N≤n) :
      hillHminusRealLabels q.val q.property (2*n)=hillHminusRealLabels q.val q.property (2*n-1) := by
    exact (hrecover q.val hqρ q.property hqm ⟨n,by omega⟩).mp (htail n hn)
  refine ⟨q,hqlift,hqm,hqball,hqZ,?_⟩
  intro s hs
  exact hillHminus_real_finiteGap_mem_sobolev q.val q.property N hN hclosed s hs

/-- The regular rough inverse is literally an ORIGINAL physical real L2
source. Its fixed global Birkhoff coordinates equal the prescribed target,
and its physical L2 mass has the exact original action normalization. -/
theorem exists_hillHminus_native_finite_support_physical_preimages :
    ∃ η : ℝ, ∃ Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2,
      ∃ W : Set (DeletedCoeff 2 0), ∃ R : DeletedCoeff 2 0 → PeriodOneHminusOne,
      0<η ∧ AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η) ∧ Z 0=0 ∧
      (∀ p : RealPeriodOneHillPotential,
        (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ j : ℤ,
        (Z (hillPhysicalHminusEmbedding p).val).val j=
          hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j) ∧
      IsOpen W ∧ 0∈W ∧ AnalyticOnNhd ℂ R W ∧ R 0=0 ∧
      (∀ b∈W, (R b).val 0=0 ∧ R b∈ball (0 : PeriodOneHminusOne) η ∧
        Z (R b)=WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b) ∧
      (∀ b∈W, deletedL2Conjugation b=b → IsRealPeriodOneHminusOne (R b)) ∧
      ∀ b∈W, deletedL2Conjugation b=b →
        (Function.support b.val).Finite → ∃ q : PeriodOneRealHminusOne,
          ∃ p : hillRealMeanZeroSourceSubmodule,
          q.val=R b ∧ q.val.val 0=0 ∧ q.val∈ball (0 : PeriodOneHminusOne) η ∧
          hillOriginalHminusSource p.val.val=q.val ∧
          Z q.val=WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b ∧
          (∀ s : ℝ, 0≤s → Memℓp (fun n => (Weight.sobolev s n : ℂ)*q.val.val n) 2) ∧
          (∀ n : ℕ+, hillOriginalBirkhoffAbelianCoordinate p n=
            (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b).val (n : ℤ)) ∧
          ‖p‖^2=∑' k : ℕ, (4*Real.pi*(k+1 : ℕ))*
            ‖(WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b).val ((k+1 : ℕ) : ℤ)‖^2 := by
  obtain ⟨η,Z,W,R,hη,hZa,hZ0,hZp,hW,h0W,hRa,hR0,hRdata,hRreal,hpre⟩ := exists_hillHminus_native_finite_support_regular_preimages
  refine ⟨η,Z,W,R,hη,hZa,hZ0,hZp,hW,h0W,hRa,hR0,hRdata,hRreal,?_⟩
  intro b hb hbr hbf
  obtain ⟨q,hqR,hqm,hqball,hqZ,hqS⟩ := hpre b hb hbr hbf
  have hL2 : Memℓp q.val.val 2 := by
    simpa only [Weight.sobolev_zero_apply,ofReal_one,one_mul] using hqS 0 le_rfl
  obtain ⟨p,hpq⟩ := exists_original_physical_meanZero_of_real_hminus_l2 q.val q.property hqm hL2
  have hpball : hillOriginalHminusSource p.val.val∈ball (0 : PeriodOneHminusOne) η := by
    rw [hpq]
    exact hqball
  have hcoord (n : ℕ+) : hillOriginalBirkhoffAbelianCoordinate p n=
      (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b).val (n : ℤ) := by
    have hh := hillBirkhoffAbelian_rough_map_agreement Z (ball (0 : PeriodOneHminusOne) η) hZp p hpball n
    rw [hpq,hqZ] at hh
    exact hh.symm
  refine ⟨q,p,hqR,hqm,hqball,hpq,hqZ,hqS,hcoord,?_⟩
  rw [norm_sq_hillOriginalBirkhoffAbelianCoordinates]
  apply tsum_congr
  intro k
  exact congrArg (fun z : ℂ => (4*Real.pi*(k+1 : ℕ))*‖z‖^2)
    (hcoord (⟨k+1,by omega⟩ : ℕ+))

end NLS.Articles.KdVKdV2Frequencies
