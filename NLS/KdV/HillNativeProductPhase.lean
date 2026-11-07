import NLS.KdV.HillNativeGardnerCoordinates
import NLS.KdV.HillCompletePhaseCotangent
import NLS.ComplexAnalysis.ProductPhaseCotangents

/-! The actual signed native coordinate cotangents from their exact
action product and complete intrinsic phase ratio. All identities use
full complex source germs and retain the original sqrt-two convention. -/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillHminusNativeCoordinates_ne_zero_of_real_open_gap (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (hg : hillHminusCanonicalGapSquare n q ≠ 0) :
    hillHminusNativeCoordinate (n:ℤ) q ≠ 0 ∧ hillHminusNativeCoordinate (-(n:ℤ)) q ≠ 0 := by
  have hi : hillHminusCanonicalAction n q ≠ 0 :=
    fun hz => hg ((hillHminusCanonicalAction_eq_zero_iff_gapSquare_of_real q hr n).mp hz)
  have hp := hillHminusNativeComplexMap_action_identity q (real_mem_hillHminusActionAngleNativeDomain q hr) n
  exact mul_ne_zero_iff.mp (hp.symm ▸ hi)

theorem eventually_hillHminusNativeCoordinate_product_action (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) :
    (fun p => hillHminusNativeCoordinate (n:ℤ) p*hillHminusNativeCoordinate (-(n:ℤ)) p) =ᶠ[𝓝 q]
      hillHminusCanonicalAction n := by
  filter_upwards [isOpen_hillHminusActionAngleNativeDomain.mem_nhds
    (real_mem_hillHminusActionAngleNativeDomain q hr)] with p hp
  exact hillHminusNativeComplexMap_action_identity p hp n

theorem eventually_hillHminusNativeCoordinate_ratio_phaseSquare (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (hg : hillHminusCanonicalGapSquare n q ≠ 0) :
    (fun p => hillHminusNativeCoordinate (-(n:ℤ)) p/hillHminusNativeCoordinate (n:ℤ) p) =ᶠ[𝓝 q]
      hillHminusCompletePhaseSquare n := by
  have hAmp : hillHminusCanonicalActionAmplitude n q ≠ 0 := by
    intro he
    have hp := (hillHminusCanonicalActionAmplitude_real_positive n q hr).2
    rw [he] at hp
    exact (lt_irrefl 0) hp
  have hA := (analyticOnNhd_hillHminusCanonicalActionAmplitude n q
    (real_mem_hillHminusActionAmplitudeDomain q hr)).continuousAt.eventually_ne hAmp
  have hs : (Real.sqrt 2:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))
  filter_upwards [hA,isOpen_hillHminusActionAngleNativeDomain.mem_nhds
    (real_mem_hillHminusActionAngleNativeDomain q hr),(isOpen_hillHminusCompletePhaseDomain n).mem_nhds
      (show q ∈ hillHminusCompletePhaseDomain n from ⟨real_mem_hillHminusOffIndexAnalyticDomain q hr,hg⟩)] with p hAp hp hphase
  have hm := (hillHminusAbelianCartesian_ne_zero_on_completePhaseDomain n p hphase).2
  dsimp only [hillHminusNativeCoordinate]
  rw [hillHminusNativeComplexMap_positive p hp n,hillHminusNativeComplexMap_negative p hp n,
    hillHminusActionAngleFactorPlus,hillHminusActionAngleFactorMinus,hillHminusCompletePhaseSquare]
  field_simp [hAp,hm,hs]

theorem fderiv_hillHminusNativeCoordinates_from_action_phase (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (hg : hillHminusCanonicalGapSquare n q ≠ 0) :
    fderiv ℂ (hillHminusNativeCoordinate (n:ℤ)) q = hillHminusNativeCoordinate (n:ℤ) q •
      ((2*hillHminusCanonicalAction n q)⁻¹ • fderiv ℂ (hillHminusCanonicalAction n) q-
        I • hillHminusCompletePhaseCotangent n q) ∧
    fderiv ℂ (hillHminusNativeCoordinate (-(n:ℤ))) q = hillHminusNativeCoordinate (-(n:ℤ)) q •
      ((2*hillHminusCanonicalAction n q)⁻¹ • fderiv ℂ (hillHminusCanonicalAction n) q+
        I • hillHminusCompletePhaseCotangent n q) := by
  have hq := real_mem_hillHminusActionAngleNativeDomain q hr
  have hn := hillHminusNativeCoordinates_ne_zero_of_real_open_gap n q hr hg
  have h := fderiv_from_product_phase_ratio (hillHminusNativeCoordinate (n:ℤ))
    (hillHminusNativeCoordinate (-(n:ℤ))) q
    (analyticOnNhd_hillHminusNativeCoordinate _ q hq).differentiableAt
    (analyticOnNhd_hillHminusNativeCoordinate _ q hq).differentiableAt hn.1 hn.2
  have hp := eventually_hillHminusNativeCoordinate_product_action n q hr
  have hR := eventually_hillHminusNativeCoordinate_ratio_phaseSquare n q hr hg
  rw [hp.fderiv_eq,hR.fderiv_eq,hp.eq_of_nhds,hR.eq_of_nhds] at h
  exact h

end NLS.KdV
