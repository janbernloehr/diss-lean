import NLS.MKdV.MiuraThetaActionDirection
import NLS.MKdV.MiuraNativeActionMeanDifferential
import NLS.MKdV.MiuraNativePhysicalActionRays
import NLS.ComplexAnalysis.RealAnalyticDenseNonzero

/-! # The original own-angle domain is dense in every positive native Sobolev order -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraSobolevActionSequence_eq_physical (m : ℕ) (hm : 1 ≤ m)
    (a : MiuraRealSobolevSource m) (n : ℕ) (hn : 1 ≤ n) :
    (miuraSobolevActionSequence m a.val).val (n : ℤ) =
      miuraMKdVAction (hierarchySobolevToScalarDomain m hm a.val)
        (by intro j; simpa only [hierarchySobolevToScalarDomain_apply] using a.property j) n := by
  obtain ⟨U,_,ha,_,hcoord⟩ := exists_local_miuraSobolevActionSequence_analytic m a.val a.property
  rw [hcoord a.val ha n (by omega),miuraSobolevActionSource_eq_L2_diagonal,
    ← scalarInclusion_hierarchySobolevToScalarDomain m hm a.val]
  exact miuraL2Action_eq_physical _ _ n hn

theorem miuraSobolevActionSequence_ne_zero_implies_gap_ne_zero (m : ℕ) (hm : 1 ≤ m)
    (a : MiuraRealSobolevSource m) (n : ℕ) (hn : 1 ≤ n)
    (hact : (miuraSobolevActionSequence m a.val).val (n : ℤ) ≠ 0) :
    canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (miuraSobolevActionSource m a.val)) (periodOnePotential_mem _) n ≠ 0 := by
  let b := hierarchySobolevToScalarDomain m hm a.val
  have hb : ∀ j, b.val j = conj (b.val (-j)) := by
    intro j
    simpa only [b,hierarchySobolevToScalarDomain_apply] using a.property j
  have hsource : miuraSobolevActionSource m a.val = sobolevSourceInclusion (b,b) := by
    rw [miuraSobolevActionSource_eq_L2_diagonal,← scalarInclusion_hierarchySobolevToScalarDomain m hm a.val,
      scalarL2Diagonal_scalarInclusion]
  rw [miuraSobolevActionSequence_eq_physical m hm a n hn] at hact
  intro hg
  rw [hsource] at hg
  change miuraNLSRight b n-miuraNLSLeft b n = 0 at hg
  have hi := (miuraNLSAction_zero_iff_endpoints b hb n).mpr (sub_eq_zero.mp hg).symm
  exact hact ((miuraMKdVAction_nonnegative_and_zero_iff b hb n hn).2.2.mpr hi)

theorem dense_miuraHigherSobolev_open_angle (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (hn : 1 ≤ n) :
    Dense {a : MiuraRealSobolevSource m | canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (miuraSobolevActionSource m a.val)) (periodOnePotential_mem _) n ≠ 0} := by
  let F : MiuraRealSobolevSource m → ℂ := fun a => (miuraSobolevActionSequence m a.val).val (n : ℤ)
  have hF : AnalyticOnNhd ℝ F univ := by
    intro a _
    have h := ((WeightedCoeff.evalCLM (miuraSpectralActionWeight m) 1 (n : ℤ)).analyticAt _).comp
      (analyticAt_miuraSobolevActionSequence m a)
    exact (h.restrictScalars (𝕜 := ℝ)).comp ((MiuraRealSobolevSource m).subtypeL.analyticAt a)
  obtain ⟨b,hb⟩ := exists_native_profile_on_positive_action_ray m hm 0 n (by omega) 1 (by norm_num)
  have hbase := miuraSobolevActionSequence_nonnegative m 0 n
  have hcoef := congrArg (fun z : MiuraNativeActionMeanTarget m => z.1.val (n : ℤ)) hb
  change (miuraSobolevActionSequence m b.val).val (n : ℤ) =
    (miuraSobolevActionSequence m (0 : MiuraRealSobolevSource m).val).val (n : ℤ)+(1 : ℂ)*
      (WeightedCoeff.single (p := 1) (miuraSpectralActionWeight m) (n : ℤ) 1).val (n : ℤ) at hcoef
  simp only [WeightedCoeff.single_val,Pi.single_eq_same,one_mul] at hcoef
  have hbF : F b ≠ 0 := by
    intro hz
    change (miuraSobolevActionSequence m b.val).val (n : ℤ) = 0 at hz
    rw [hz] at hcoef
    have hr := congrArg Complex.re hcoef
    simp only [Complex.zero_re,Complex.add_re,Complex.one_re] at hr
    linarith [hbase.2]
  exact (NLS.ComplexAnalysis.dense_ne_zero_of_real_analytic F hF b hbF).mono
    (fun a ha => miuraSobolevActionSequence_ne_zero_implies_gap_ne_zero m hm a n hn ha)

end NLS.MKdV
