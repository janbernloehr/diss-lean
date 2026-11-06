import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianRealInverse
import NLS.Articles.KdVKdV2Frequencies.NativeAbelianInverseRecovery
import NLS.ComplexAnalysis.RealAnalyticInverseChart
import NLS.ComplexAnalysis.LocalRightInverseMatchingAt

/-! # ONE rough inverse chart before ALL native Sobolev orders

At every real mean-zero rough base, choose one actual two-sided analytic
inverse chart, preserving the physical real form. Every eligible native
inverse chart agrees with that SAME rough inverse on an open complex
target neighborhood. No global surjectivity is assumed or concluded.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV
namespace GlobalRoughAbelianForwardData

theorem exists_real_weak_analytic_inverse_at (D : GlobalRoughAbelianForwardData)
    (a : DeletedCoeff 2 0)
    (hr : IsRealPeriodOneHminusOne (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) a)) :
    ∃ P : OpenPartialHomeomorph (DeletedCoeff 2 0) (DeletedCoeff 2 0),
      (P : DeletedCoeff 2 0 → DeletedCoeff 2 0) = D.meanZeroForward ∧
      a ∈ P.source ∧ P.source ⊆ D.meanZeroDomain ∧
      AnalyticOnNhd ℂ D.meanZeroForward P.source ∧ AnalyticOnNhd ℂ P.symm P.target ∧
      (∀ z ∈ P.target, deletedL2Conjugation z = z → deletedL2Conjugation (P.symm z) = P.symm z) ∧
      ∀ z ∈ P.target, D.signed (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) (P.symm z)) =
        WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) z := by
  have ha : a ∈ D.meanZeroDomain := D.real_mem_domain _ hr
  obtain ⟨P,hP,haP,hsub,hPa,hPia,hreal⟩ := NLS.ComplexAnalysis.exists_real_analytic_openPartialHomeomorph
    D.meanZeroDomain_open D.meanZeroForward_analytic ha (D.isUnit_fderiv_meanZeroForward a hr)
    deletedL2Conjugation isometry_deletedL2Conjugation
    ((WeightedCoeff.meanZeroWeightedLift_real_iff _ (Weight.sobolev_neg (-1)) a).mp hr)
    (fun b _ => D.meanZeroForward_conjugation b)
  refine ⟨P,hP,haP,hsub,hPa,hPia,hreal,?_⟩
  intro z hz
  have he := WeightedCoeff.meanZeroWeightedLift_projection (Weight.sobolev (-1/2))
    (D.signed (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) (P.symm z)))
    (D.signed_zero _ (hsub (P.map_target hz)))
  change WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2))
    (D.meanZeroForward (P.symm z)) = _ at he
  rw [←hP,P.right_inv hz] at he
  exact he.symm

/-- Full actual strong chart, exact native right recovery, and agreement
with the GIVEN weak inverse on an OPEN complex target neighborhood. -/
def NativeInverseMatchesWeakChartAt (D : GlobalRoughAbelianForwardData)
    (P0 : OpenPartialHomeomorph (DeletedCoeff 2 0) (DeletedCoeff 2 0))
    (t : ℝ) (ht : 0 ≤ t) (a : DeletedCoeff 2 0) : Prop :=
  ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧
    WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a ∈ V ∧
    ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev (t-1/2)) 2,
      AnalyticOnNhd ℂ g V ∧
      (∀ p ∈ V, periodOneSobolevImageInclusion t ht p ∈ D.domain ∧
        WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ) ≤ t-1/2) (g p) =
          D.signed (periodOneSobolevImageInclusion t ht p) ∧ (g p).val 0 = 0) ∧
      ∃ P : OpenPartialHomeomorph (DeletedCoeff 2 0) (DeletedCoeff 2 0),
        (P : DeletedCoeff 2 0 → DeletedCoeff 2 0) = nativeMeanZeroAbelianMap t g ∧
        a ∈ P.source ∧ P.source ⊆ (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1))) ⁻¹' V ∧
        AnalyticOnNhd ℂ (nativeMeanZeroAbelianMap t g) P.source ∧ AnalyticOnNhd ℂ P.symm P.target ∧
        ∃ T : Set (DeletedCoeff 2 0), IsOpen T ∧ P a ∈ T ∧ T ⊆ P.target ∧
          ∀ z ∈ T,
            WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ) ≤ t-1/2) z ∈ P0.target ∧
            WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1 : ℝ) ≤ t-1) (P.symm z) =
              P0.symm (WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ) ≤ t-1/2) z) ∧
            periodOneSobolevImageInclusion t ht
              (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) (P.symm z)) =
                WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))
                  (P0.symm (WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ) ≤ t-1/2) z)) ∧
            g (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) (P.symm z)) =
              WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1/2)) z ∧
            D.signed (periodOneSobolevImageInclusion t ht
              (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) (P.symm z))) =
                WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ) ≤ t-1/2)
                  (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1/2)) z)

theorem native_inverse_matches_weak_chart (D : GlobalRoughAbelianForwardData)
    (P0 : OpenPartialHomeomorph (DeletedCoeff 2 0) (DeletedCoeff 2 0))
    (hP0 : (P0 : DeletedCoeff 2 0 → DeletedCoeff 2 0) = D.meanZeroForward)
    (hP0ia : AnalyticOnNhd ℂ P0.symm P0.target)
    (t : ℝ) (ht : 0 ≤ t) (a : DeletedCoeff 2 0)
    (hr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht
      (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a)))
    (ha : WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1 : ℝ) ≤ t-1) a ∈ P0.source) :
    D.NativeInverseMatchesWeakChartAt P0 t ht a := by
  obtain ⟨V,hV,haV,g,hga,hcomm,P,hP,haP,hPV,hFa,hPia,_hleft,hraw⟩ :=
    D.exists_native_analytic_inverse_at t ht a hr
  let J := WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1 : ℝ) ≤ t-1)
  let I := WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ) ≤ t-1/2)
  have hcenter : I (P a) = D.meanZeroForward (J a) := by
    rw [hP]
    exact nativeMeanZeroAbelianMap_commuting t ht D.signed g a (hcomm _ haV).2.1
  have hsolve (z : DeletedCoeff 2 0) (hz : z ∈ P.target) :
      D.meanZeroForward (J (P.symm z)) = I z := by
    have he := nativeMeanZeroAbelianMap_commuting t ht D.signed g (P.symm z)
      (hcomm _ (hPV (P.map_target hz))).2.1
    rw [←hP,P.right_inv hz] at he
    exact he.symm
  obtain ⟨T,hT,hbase,hTP,_hPiaT,hmatch⟩ := NLS.ComplexAnalysis.exists_local_rightInverse_matching_at
    J I D.meanZeroForward P0.source P0.open_source (by rw [←hP0]; exact P0.injOn)
    P0.target P0.open_target P0.symm hP0ia.continuousOn
    (fun z hz => by rw [←hP0]; exact P0.right_inv hz)
    P.target P.open_target P.symm hPia hsolve (P a) (P.map_source haP)
    (by rw [hcenter,←hP0]; exact P0.map_source ha)
    (by rw [P.left_inv haP]; exact ha)
    (by rw [hcenter,←hP0,P0.left_inv ha]; exact ha)
  refine ⟨V,hV,haV,g,hga,hcomm,P,hP,haP,hPV,hFa,hPia,T,hT,hbase,hTP,?_⟩
  intro z hz
  have hs := congrArg (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))) (hmatch z hz).2
  rw [WeightedCoeff.meanZeroSobolevInclusion_lift] at hs
  exact ⟨(hmatch z hz).1,(hmatch z hz).2,hs,(hraw z (hTP hz)).1,(hraw z (hTP hz)).2⟩

/-- ONE real-preserving rough inverse is chosen before ALL orders and
ALL eligible real native bases in its source. Every such native inverse
agrees with THIS SAME inverse on an actual open complex target set. -/
theorem exists_one_weak_inverse_all_native_matching (D : GlobalRoughAbelianForwardData)
    (a0 : DeletedCoeff 2 0)
    (hr0 : IsRealPeriodOneHminusOne (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) a0)) :
    ∃ P0 : OpenPartialHomeomorph (DeletedCoeff 2 0) (DeletedCoeff 2 0),
      (P0 : DeletedCoeff 2 0 → DeletedCoeff 2 0) = D.meanZeroForward ∧
      a0 ∈ P0.source ∧ P0.source ⊆ D.meanZeroDomain ∧
      AnalyticOnNhd ℂ D.meanZeroForward P0.source ∧ AnalyticOnNhd ℂ P0.symm P0.target ∧
      (∀ z ∈ P0.target, deletedL2Conjugation z = z → deletedL2Conjugation (P0.symm z) = P0.symm z) ∧
      (∀ z ∈ P0.target, D.signed (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) (P0.symm z)) =
        WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) z) ∧
      ∀ (t : ℝ) (ht : 0 ≤ t) (a : DeletedCoeff 2 0),
        IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht
          (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a)) →
        WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1 : ℝ) ≤ t-1) a ∈ P0.source →
        D.NativeInverseMatchesWeakChartAt P0 t ht a := by
  obtain ⟨P0,hP0,ha0,hsub,hFa,hP0ia,hreal,hraw⟩ := D.exists_real_weak_analytic_inverse_at a0 hr0
  exact ⟨P0,hP0,ha0,hsub,hFa,hP0ia,hreal,hraw,
    fun t ht a hr ha => D.native_inverse_matches_weak_chart P0 hP0 hP0ia t ht a hr ha⟩

/-- A matched chart yields a genuine native analytic germ of the SAME
rough inverse, with its exact base value, full source/target coefficients
and physical reality. No initial regularity of a rough inverse is assumed. -/
theorem NativeInverseMatchesWeakChartAt.exists_strong_inverse_germ
    {D : GlobalRoughAbelianForwardData}
    {P0 : OpenPartialHomeomorph (DeletedCoeff 2 0) (DeletedCoeff 2 0)}
    {t : ℝ} {ht : 0 ≤ t} {a : DeletedCoeff 2 0}
    (h : D.NativeInverseMatchesWeakChartAt P0 t ht a)
    (hreal : ∀ z ∈ P0.target, deletedL2Conjugation z = z → deletedL2Conjugation (P0.symm z) = P0.symm z) :
    ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧
      ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev (t-1/2)) 2,
        AnalyticOnNhd ℂ g V ∧
        ∃ T : Set (DeletedCoeff 2 0), IsOpen T ∧ nativeMeanZeroAbelianMap t g a ∈ T ∧
          ∃ G : DeletedCoeff 2 0 → WeightedCoeff (Weight.sobolev (t-1)) 2,
            AnalyticOnNhd ℂ G T ∧
            G (nativeMeanZeroAbelianMap t g a) = WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a ∧
            ∀ z ∈ T,
              WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ) ≤ t-1/2) z ∈ P0.target ∧
              G z ∈ V ∧ (G z).val 0 = 0 ∧
              periodOneSobolevImageInclusion t ht (G z) =
                WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))
                  (P0.symm (WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ) ≤ t-1/2) z)) ∧
              g (G z) = WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1/2)) z ∧
              (deletedL2Conjugation z = z → ∀ j : ℤ, (G z).val (-j) = conj ((G z).val j)) := by
  obtain ⟨V,hV,_haV,g,hga,_hcomm,P,hP,haP,hPV,_hFa,hPia,T,hT,hbase,hTP,hmatch⟩ := h
  let L := WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1))
  let I := WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ) ≤ t-1/2)
  let G := fun z => L (P.symm z)
  refine ⟨V,hV,g,hga,T,hT,?_,G,?_,?_,?_⟩
  · rw [←hP]; exact hbase
  · intro z hz
    exact (L.analyticAt _).comp (hPia z (hTP hz))
  · change L (P.symm (nativeMeanZeroAbelianMap t g a)) = L a
    rw [←hP,P.left_inv haP]
  · intro z hz
    obtain ⟨hIz,_hnorm,hs,hg,_hraw⟩ := hmatch z hz
    refine ⟨hIz,hPV (P.map_target (hTP hz)),WeightedCoeff.meanZeroWeightedLift_zero _ _,hs,hg,?_⟩
    intro hJz
    have hzreal := (WeightedCoeff.meanZeroWeightedLift_real_iff
      (Weight.sobolev (t-1/2)) (Weight.sobolev_neg (t-1/2)) z).mpr hJz
    have hIzreal : deletedL2Conjugation (I z) = I z := by
      apply (WeightedCoeff.meanZeroWeightedLift_real_iff
        (Weight.sobolev (-1/2)) (Weight.sobolev_neg (-1/2)) (I z)).mp
      have hL := WeightedCoeff.meanZeroSobolevInclusion_lift
        (by linarith : (-1/2 : ℝ) ≤ t-1/2) z
      have he (j : ℤ) : (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) (I z)).val j =
          (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1/2)) z).val j :=
        (congrArg (fun b : WeightedCoeff (Weight.sobolev (-1/2)) 2 => b.val j) hL).trans
          (WeightedCoeff.sobolevInclusion_apply _ _ j)
      intro j
      exact (he (-j)).trans ((hzreal j).trans (congrArg conj (he j).symm))
    have hsource := (WeightedCoeff.meanZeroWeightedLift_real_iff
      (Weight.sobolev (-1)) (Weight.sobolev_neg (-1)) (P0.symm (I z))).mpr (hreal _ hIz hIzreal)
    intro j
    have he := hsource j
    rw [←hs] at he
    simpa only [periodOneSobolevImageInclusion_apply] using he

end GlobalRoughAbelianForwardData
end NLS.Articles.KdVKdV2Frequencies
