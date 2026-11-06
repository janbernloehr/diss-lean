import NLS.Articles.KdVKdV2Frequencies.NativeRoughFiniteSupportPreimages
import NLS.Articles.KdVKdV2Frequencies.SignedMassTruncationBounds
import NLS.SequenceSpaces.DeletedSymmetricTruncation
import NLS.KdV.HillPhysicalL2RoughClosure
import NLS.KdV.HillBirkhoffAbelianSummability

/-! # The actual rough inverse has the exact physical L2 endpoint

Finite-support physical preimages and their genuine Parseval mass bound
identify every real half-regular target with an ORIGINAL physical L2 source.
Conversely, original physical L2 membership forces native half regularity.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

private theorem halfRegularity_of_original_abelian_match
    (w : Weight) (a : SignedCoordinates w 2) (p : hillRealMeanZeroSourceSubmodule)
    (he : ∀ n : ℕ+, hillOriginalBirkhoffAbelianCoordinate p n=a.val.val (n : ℤ)) :
    HasHalfRegularity a := by
  have h := summable_hillOriginalBirkhoffAbelian_mass p
  have hs : Summable (fun k : ℕ => kdvMassTerm a (k+1)) := by
    apply (h.mul_left (1/2 : ℝ)).congr
    intro k
    unfold kdvMassTerm
    have hn : ‖hillOriginalBirkhoffAbelianCoordinate p (⟨k+1,by omega⟩ : ℕ+)‖^2=
        ‖a.val.val ((k+1 : ℕ) : ℤ)‖^2 :=
      congrArg (fun z : ℂ => ‖z‖^2) (he (⟨k+1,by omega⟩ : ℕ+))
    rw [hn]
    ring
  exact (hasHalfRegularity_iff_summable_kdvMassTerm a).mpr ((summable_nat_add_iff 1).mp hs)

private theorem memlp_rough_inverse_of_halfRegularity
    (w : Weight) (hw : ∀ j, w (-j)=w j)
    (W : Set (DeletedCoeff 2 0)) (hW : IsOpen W)
    (R : DeletedCoeff 2 0 → PeriodOneHminusOne) (hR : ContinuousOn R W)
    (hfinite : ∀ b∈W, deletedL2Conjugation b=b → (Function.support b.val).Finite →
      ∃ p : hillRealMeanZeroSourceSubmodule, hillOriginalHminusSource p.val.val=R b ∧
        ‖p‖^2=∑' k : ℕ, (4*Real.pi*(k+1 : ℕ))*
          ‖(WeightedCoeff.meanZeroWeightedLiftCLM w b).val ((k+1 : ℕ) : ℤ)‖^2)
    (a : SignedCoordinates w 2) (ha : HasHalfRegularity a)
    (hab : WeightedCoeff.meanZeroWeightedProjectionCLM w a.val∈W) :
    Memℓp (R (WeightedCoeff.meanZeroWeightedProjectionCLM w a.val)).val 2 := by
  classical
  let b := WeightedCoeff.meanZeroWeightedProjectionCLM w a.val
  have hb : deletedL2Conjugation b=b := meanZeroWeightedProjection_real w hw a.val a.property.2
  have hlift : WeightedCoeff.meanZeroWeightedLiftCLM w b=a.val :=
    WeightedCoeff.meanZeroWeightedLift_projection w a.val a.property.1
  have htrunc (N : ℕ) : WeightedCoeff.meanZeroWeightedLiftCLM w (deletedSymmetricTruncate N b)=
      (signedTruncate w N a).val := by
    rw [meanZeroWeightedLift_deletedSymmetricTruncate,hlift]
    rfl
  have hnear : ∀ᶠ N : ℕ in atTop, deletedSymmetricTruncate N b∈W :=
    (tendsto_deletedSymmetricTruncate b).eventually (hW.mem_nhds hab)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hnear
  let j (m : ℕ) := N₀+m
  have hexists (m : ℕ) : ∃ p : hillRealMeanZeroSourceSubmodule,
      hillOriginalHminusSource p.val.val=R (deletedSymmetricTruncate (j m) b) ∧
        ‖p‖^2=2*kdvFiniteMass (signedTruncate w (j m) a) := by
    obtain ⟨p,hp,hmass⟩ := hfinite (deletedSymmetricTruncate (j m) b)
      (hN₀ (j m) (by dsimp only [j];omega))
      (deletedSymmetricTruncate_real (j m) b hb) (deletedSymmetricTruncate_finiteSupport (j m) b)
    refine ⟨p,hp,?_⟩
    rw [hmass,htrunc]
    exact (two_kdvFiniteMass_eq_shifted_norm_sum _ (hasHalfRegularity_signedTruncate w (j m) a)).symm
  choose p hpsource hpmass using hexists
  let P (m : ℕ) : RealPeriodOneHillPotential := ⟨(p m).val.val,(p m).val.property⟩
  let C := Real.sqrt (2*kdvFiniteMass a)
  have hmass0 : 0≤kdvFiniteMass a := tsum_nonneg (fun n => kdvMassTerm_nonneg a n)
  have hnorm (m : ℕ) : ‖p m‖≤C := by
    have hle : ‖p m‖^2≤2*kdvFiniteMass a := by
      rw [hpmass]
      exact mul_le_mul_of_nonneg_left (kdvFiniteMass_signedTruncate_le w (j m) a ha) (by norm_num)
    have hC := Real.sq_sqrt (by positivity : 0≤2*kdvFiniteMass a)
    have hC0 := Real.sqrt_nonneg (2*kdvFiniteMass a)
    dsimp only [C]
    nlinarith [norm_nonneg (p m)]
  have hbound : Bornology.IsBounded (range (fun m => (P m).val)) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨C,?_⟩
    rintro _ ⟨m,rfl⟩
    change ‖p m‖≤C
    exact hnorm m
  have hj : Tendsto j atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro n
    filter_upwards [eventually_ge_atTop n] with m hm
    dsimp only [j]
    omega
  have hbconv := (tendsto_deletedSymmetricTruncate b).comp hj
  have hlim := ((hR.continuousAt (hW.mem_nhds hab)).tendsto).comp hbconv
  have hPlim : Tendsto (fun m => hillOriginalHminusSource (P m).val) atTop (𝓝 (R b)) := by
    simpa only [P,hpsource,Function.comp_def,b] using hlim
  exact memlp_of_bounded_original_hminus_limit (R b) P hbound hPlim

/-- ONE actual analytic rough inverse has the exact native physical L2
endpoint for EVERY real target in its neighborhood, not only finite targets. -/
theorem exists_hillHminus_native_L2_endpoint_inverse :
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
      ∀ a : SignedCoordinates (Weight.sobolev (-1/2)) 2,
        let b := WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2)) a.val
        b∈W → (Memℓp (R b).val 2 ↔ HasHalfRegularity a) ∧
          (HasHalfRegularity a → ∃ p : hillRealMeanZeroSourceSubmodule,
            hillOriginalHminusSource p.val.val=R b ∧
            (∀ n : ℕ+, hillOriginalBirkhoffAbelianCoordinate p n=a.val.val (n : ℤ)) ∧
            ‖p‖^2=2*kdvFiniteMass a) := by
  obtain ⟨η,Z,W,R,hη,hZa,hZ0,hZp,hW,h0W,hRa,hR0,hRdata,hRreal,hpre⟩ :=
    exists_hillHminus_native_finite_support_physical_preimages
  have hfinite (b : DeletedCoeff 2 0) (hb : b∈W) (hbr : deletedL2Conjugation b=b)
      (hbf : (Function.support b.val).Finite) :
      ∃ p : hillRealMeanZeroSourceSubmodule, hillOriginalHminusSource p.val.val=R b ∧
        ‖p‖^2=∑' k : ℕ, (4*Real.pi*(k+1 : ℕ))*
          ‖(WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b).val ((k+1 : ℕ) : ℤ)‖^2 := by
    obtain ⟨q,p,hqR,_,_,hp,_,_,_,hmass⟩ := hpre b hb hbr hbf
    exact ⟨p,hp.trans hqR,hmass⟩
  have hphysical (a : SignedCoordinates (Weight.sobolev (-1/2)) 2)
      (hb : WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2)) a.val∈W)
      (hL2 : Memℓp (R (WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2)) a.val)).val 2) :
      ∃ p : hillRealMeanZeroSourceSubmodule,
        hillOriginalHminusSource p.val.val=R (WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2)) a.val) ∧
        ∀ n : ℕ+, hillOriginalBirkhoffAbelianCoordinate p n=a.val.val (n : ℤ) := by
    have hbr := meanZeroWeightedProjection_real (Weight.sobolev (-1/2)) (Weight.sobolev_neg (-1/2)) a.val a.property.2
    have hd := hRdata _ hb
    obtain ⟨p,hp⟩ := exists_original_physical_meanZero_of_real_hminus_l2 _ (hRreal _ hb hbr) hd.1 hL2
    have hpball : hillOriginalHminusSource p.val.val∈ball (0 : PeriodOneHminusOne) η := by
      rw [hp]
      exact hd.2.1
    refine ⟨p,hp,?_⟩
    intro n
    have hh := hillBirkhoffAbelian_rough_map_agreement Z (ball (0 : PeriodOneHminusOne) η) hZp p hpball n
    rw [hp,hd.2.2,WeightedCoeff.meanZeroWeightedLift_projection _ _ a.property.1] at hh
    exact hh.symm
  refine ⟨η,Z,W,R,hη,hZa,hZ0,hZp,hW,h0W,hRa,hR0,hRdata,hRreal,?_⟩
  intro a b hb
  have hL2 (ha : HasHalfRegularity a) : Memℓp (R b).val 2 :=
    memlp_rough_inverse_of_halfRegularity (Weight.sobolev (-1/2)) (Weight.sobolev_neg (-1/2))
      W hW R hRa.continuousOn hfinite a ha hb
  refine ⟨⟨?_,hL2⟩,?_⟩
  · intro hl
    obtain ⟨p,_,hcoord⟩ := hphysical a hb hl
    exact halfRegularity_of_original_abelian_match _ a p hcoord
  · intro ha
    obtain ⟨p,hp,hcoord⟩ := hphysical a hb (hL2 ha)
    refine ⟨p,hp,hcoord,?_⟩
    rw [norm_sq_hillOriginalBirkhoffAbelianCoordinates,two_kdvFiniteMass_eq_shifted_norm_sum a ha]
    apply tsum_congr
    intro k
    exact congrArg (fun z : ℂ => (4*Real.pi*(k+1 : ℕ))*‖z‖^2)
      (hcoord (⟨k+1,by omega⟩ : ℕ+))

/-- The endpoint criterion for EVERY real target in the actual inverse
neighborhood, expressed directly on its literal weighted lift. -/
theorem exists_hillHminus_native_real_target_L2_endpoint_inverse :
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
        (Memℓp (R b).val 2 ↔ Memℓp (fun j => (Weight.sobolev (1/2) j : ℂ)*
          (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b).val j) 2) ∧
        (Memℓp (fun j => (Weight.sobolev (1/2) j : ℂ)*
          (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b).val j) 2 →
          ∃ p : hillRealMeanZeroSourceSubmodule, hillOriginalHminusSource p.val.val=R b ∧
            (∀ n : ℕ+, hillOriginalBirkhoffAbelianCoordinate p n=
              (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b).val (n : ℤ)) ∧
            ‖p‖^2=∑' k : ℕ, (4*Real.pi*(k+1 : ℕ))*
              ‖(WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b).val ((k+1 : ℕ) : ℤ)‖^2) := by
  obtain ⟨η,Z,W,R,hη,hZa,hZ0,hZp,hW,h0W,hRa,hR0,hRdata,hRreal,hendpoint⟩ :=
    exists_hillHminus_native_L2_endpoint_inverse
  refine ⟨η,Z,W,R,hη,hZa,hZ0,hZp,hW,h0W,hRa,hR0,hRdata,hRreal,?_⟩
  intro b hb hbr
  let a : SignedCoordinates (Weight.sobolev (-1/2)) 2 :=
    ⟨WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b,
      meanZeroWeightedLift_real _ (Weight.sobolev_neg (-1/2)) b hbr⟩
  have hh := hendpoint a (by simpa only [a,WeightedCoeff.meanZeroWeightedProjection_lift] using hb)
  have he : Memℓp (R b).val 2 ↔ Memℓp (fun j => (Weight.sobolev (1/2) j : ℂ)*
      (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b).val j) 2 := by
    simpa only [a,HasHalfRegularity,WeightedCoeff.meanZeroWeightedProjection_lift] using hh.1
  refine ⟨he,?_⟩
  intro ha
  obtain ⟨p,hp,hcoord,hmass⟩ := hh.2 (show HasHalfRegularity a from ha)
  refine ⟨p,?_,hcoord,?_⟩
  · simpa only [a,WeightedCoeff.meanZeroWeightedProjection_lift] using hp
  · exact hmass.trans (two_kdvFiniteMass_eq_shifted_norm_sum a ha)

end NLS.Articles.KdVKdV2Frequencies
