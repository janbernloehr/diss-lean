import NLS.KdV.PhysicalFrequencyParameterization
import NLS.KdV.PhysicalOffDiagonalFrequency
import NLS.KdV.MiuraCanonicalRootReflection
import NLS.KdV.HillHminusMiuraActionMatching
import NLS.ZakharovShabat.SourceDiagonalCancellationFractionalBound

/-! The ACTUAL corrected physical diagonal contribution has a
fractional bound with two original gap factors, on full complex native
neighborhoods. Its counterterm is calibrated to the literal original +6I. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem PhysicalMiuraFrequencyChart.diagonal_cancellation_identity
    (B : PhysicalMiuraFrequencyChart) (n : ℕ+) (a : PeriodOneHminusOne) :
    let ψ := hillMiuraDiagonal (B.psi.miura.lift a)
    B.correction n a+12*sourceComplexHigherAction (by norm_num) (by norm_num) (n:ℤ) 1 ψ-
      B.offDiagonalCorrection n a=
        -12*(n:ℂ)*(B.atlas.moment (n:ℤ) (n:ℤ) 2 ψ-B.atlas.moment (n:ℤ) (-(n:ℤ)) 2 ψ)+
          12*sourceComplexHigherAction (by norm_num) (by norm_num) (n:ℤ) 1 ψ := by
  dsimp only [PhysicalMiuraFrequencyChart.correction,PhysicalMiuraFrequencyChart.offDiagonalCorrection]
  ring

theorem PhysicalMiuraFrequencyChart.original_counterterm_eq_raw_action
    (B : PhysicalMiuraFrequencyChart) (p : RealPeriodOneHillPotential)
    (hp : hillOriginalHminusSource p.val∈B.domain) (n : ℕ+) :
    6*(hillRealGapIntegral p.val p.property.1 p.property.2 (n:ℕ) 0 : ℂ)=
      12*sourceComplexHigherAction (by norm_num) (by norm_num) (n:ℤ) 1
        (hillMiuraDiagonal (B.psi.miura.lift (hillOriginalHminusSource p.val))) := by
  rw [B.psi.original_action_eq_twice_weighted_Dirac p (B.domain_subset hp) B.real_lift
    (B.outside_shift _ (B.domain_subset hp).1) B.shift B.energyShift_eq n]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {t : ℝ} {ht : 0≤t} {J : E →L[ℂ] PeriodOneHminusOne}

def PhysicalFrequencyParameterization.HasFractionalDiagonalCancellationBounds
    (A : PhysicalFrequencyParameterization E t ht J) (u : ℝ) (q : E) : Prop :=
  ∃ T : Set E, IsOpen T ∧ q∈T ∧ T⊆A.domain ∧ ∃ K : ℕ, ∃ M : ℝ, 0≤M ∧
    ∀ a∈T, ∀ n : ℕ+, K≤(n:ℤ).natAbs →
      let ψ := hillMiuraDiagonal (A.physical.psi.miura.lift (J a))
      (Weight.sobolev (u-1) (n:ℤ)*‖A.physical.correction n (J a)+
        12*sourceComplexHigherAction (by norm_num) (by norm_num) (n:ℤ) 1 ψ-
          A.physical.offDiagonalCorrection n (J a)‖≤
            ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ (n:ℤ)‖^2*M) ∧
      ∀ p : RealPeriodOneHillPotential, J a=hillOriginalHminusSource p.val →
        Weight.sobolev (u-1) (n:ℤ)*‖A.physical.correction n (J a)+
          6*(hillRealGapIntegral p.val p.property.1 p.property.2 (n:ℕ) 0 : ℂ)-
            A.physical.offDiagonalCorrection n (J a)‖≤
              ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ (n:ℤ)‖^2*M

theorem PhysicalFrequencyParameterization.exists_fractional_diagonal_cancellation_bounds
    (A : PhysicalFrequencyParameterization E t ht J)
    (u : ℝ) (hu0 : 0≤u) (hu1 : u≤1) (hut : u≤t)
    (q : E) (hq : q∈A.domain) (hqr : IsRealPeriodOneHminusOne (J q)) :
    A.HasFractionalDiagonalCancellationBounds u q := by
  let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht)
  let φ : realTypeSourceSubmodule 2 := ⟨A.normalizedSource q,A.real_source q hq hqr⟩
  obtain ⟨D,_hD⟩ := A.physical.atlas.exists_errorDomain
    A.estimates.angular_extension.toSourcePsiNormalizedComplexExtension
    A.physical.psi.family.domain_open A.physical.psi.family.real_subset
  obtain ⟨S,hS,hφS,_hSD,K,M,hM,hbound⟩ :=
    D.exists_local_sobolev_diagonal_cancellation_bound
      (sourceHigherActionAtlas (by norm_num) (by norm_num)) A.estimates.angular_extension
      A.physical.psi.family.domain_open A.physical.psi.family.real_subset t ht u hu0 hu1 hut φ
  obtain ⟨T,hT,hqT,hTA,hTS,_hTB⟩ := exists_open_common_pullback_domain A.domain A.domain_open q hq
    A.normalizedSource A.analytic_source.continuousOn S hS hφS
    J J.continuous A.physical.domain A.physical.domain_open (A.domain_subset hq)
  refine ⟨T,hT,hqT,hTA,K,M,hM,?_⟩
  intro a ha n hn
  have hreflect : sourcePeriodicGapDisplacement (by norm_num) (by norm_num)
      (L (A.normalizedSource a)) (-(n:ℤ))=
        sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L (A.normalizedSource a)) (n:ℤ) := by
    rw [A.source_identity a (hTA ha)]
    simpa only [sourcePeriodicGapDisplacement_apply] using
      (sourcePeriodicReflection_hillMiuraDiagonal (A.physical.psi.miura.lift (J a))).gap_neg (n:ℤ)
  have hb := hbound (A.normalizedSource a) (hTS a ha) n hn hreflect
  rw [A.source_identity a (hTA ha)] at hb
  have hraw : Weight.sobolev (u-1) (n:ℤ)*‖A.physical.correction n (J a)+
      12*sourceComplexHigherAction (by norm_num) (by norm_num) (n:ℤ) 1
        (hillMiuraDiagonal (A.physical.psi.miura.lift (J a)))-A.physical.offDiagonalCorrection n (J a)‖≤
          ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num)
            (hillMiuraDiagonal (A.physical.psi.miura.lift (J a))) (n:ℤ)‖^2*M := by
    rw [A.physical.diagonal_cancellation_identity]
    exact hb
  refine ⟨hraw,?_⟩
  intro p hp
  have hpB : hillOriginalHminusSource p.val∈A.physical.domain := by
    rw [← hp]
    exact A.domain_subset (hTA ha)
  have hI := A.physical.original_counterterm_eq_raw_action p hpB n
  rw [← hp] at hI
  rw [hI]
  exact hraw

end NLS.KdV
