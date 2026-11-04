import NLS.Articles.KdVPseudomeasures.OriginalHillCartesianSpectralEstimate
import NLS.KdV.HillActionAngleNativeNorm

/-! The ACTUAL Cartesian sequences define a FULL Banach-analytic native
H-minus-one map into the literal positive-index minus-half weighted Hilbert pair,
using the literal positive-index zero extension. The real form and
exact action normalization are retained. Gardner canonicality, other
regularities and the Birkhoff bijection remain separate obligations. -/
noncomputable section
open Set Complex NLS.KdV
open scoped Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_native_Cartesian_map_common_domain :
    IsOpen hillHminusActionAngleNativeDomain ∧ IsConnected hillHminusActionAngleNativeDomain ∧
      hillHminusActionAngleNativeDomain ⊆ hillHminusActionAngleEnergyDomain ∧
      (∀ q : OriginalHminusOnePotential,
        originalPeriodOneCoefficients q ∈ hillHminusActionAngleNativeDomain) ∧
      AnalyticOnNhd ℂ hillHminusNativeCartesianMap hillHminusActionAngleNativeDomain :=
  ⟨isOpen_hillHminusActionAngleNativeDomain,isConnected_hillHminusActionAngleNativeDomain,
    hillHminusActionAngleNativeDomain_subset,
    (fun q => real_mem_hillHminusActionAngleNativeDomain _ (originalPeriodOneCoefficients_real q)),
    analyticOnNhd_hillHminusNativeCartesianMap⟩

theorem original_Hill_native_Cartesian_map_positive_coordinates (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) (n : ℕ+) :
    (hillHminusNativeCartesianMap q).fst.val ((n:ℕ):ℤ) = hillHminusActionAngleX n q ∧
      (hillHminusNativeCartesianMap q).snd.val ((n:ℕ):ℤ) = hillHminusActionAngleY n q :=
  hillHminusNativeCartesianMap_positive q hq n

theorem original_Hill_native_Cartesian_map_real (q : OriginalHminusOnePotential) (k : ℤ) :
    ((hillHminusNativeCartesianMap (originalPeriodOneCoefficients q)).fst.val k).im = 0 ∧
      ((hillHminusNativeCartesianMap (originalPeriodOneCoefficients q)).snd.val k).im = 0 :=
  hillHminusNativeCartesianMap_real _ (originalPeriodOneCoefficients_real q) k

theorem original_Hill_native_Cartesian_map_action_identity (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) (n : ℕ+) :
    ((hillHminusNativeCartesianMap q).fst.val ((n:ℕ):ℤ))^2+
      ((hillHminusNativeCartesianMap q).snd.val ((n:ℕ):ℤ))^2 = 2*hillHminusCanonicalAction n q :=
  hillHminusNativeCartesianMap_action_identity q hq n

theorem original_Hill_native_Cartesian_map_locally_bounded :
    ∀ q ∈ hillHminusActionAngleNativeDomain, ∃ U : Set PeriodOneHminusOne,
      IsOpen U ∧ q ∈ U ∧ U ⊆ hillHminusActionAngleNativeDomain ∧
      ∃ C : ℝ, 0 < C ∧ ∀ a ∈ U, ‖hillHminusNativeCartesianMap a‖ ≤ C :=
  exists_locally_uniform_hillHminusNativeCartesianMap_norm_bound


theorem original_Hill_native_Cartesian_map_exact_norm (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) :
    ‖hillHminusNativeCartesianMap q‖^2 = ∑' n : ℕ+,
      (‖hillHminusActionAngleX n q‖^2+‖hillHminusActionAngleY n q‖^2)/(n:ℝ) :=
  hillHminusNativeCartesianMap_norm_sq q hq

end NLS.Articles.KdVPseudomeasures
