import NLS.KdV.PhysicalFrequencyParameterization
import NLS.ZakharovShabat.SourceDiagonalMomentFractionalBound

/-! The actual physical diagonal moments retain two gap factors in
the original parameter norm, on one full complex neighborhood. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {t : ℝ} {ht : 0≤t} {J : E →L[ℂ] PeriodOneHminusOne}

def PhysicalFrequencyParameterization.HasFractionalDiagonalMomentBounds
    (A : PhysicalFrequencyParameterization E t ht J) (u : ℝ) (q : E) : Prop :=
  ∃ T : Set E, IsOpen T ∧ q∈T ∧ T⊆A.domain ∧ ∃ K : ℕ, ∃ M : ℝ, 0≤M ∧
    ∀ a∈T, ∀ k : ℤ, K≤k.natAbs →
      let ψ := hillMiuraDiagonal (A.physical.psi.miura.lift (J a))
      Weight.sobolev u k*‖A.physical.atlas.moment k k 2 ψ-
        (Real.pi:ℂ)*(sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ k)^2/4‖≤
          ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ k‖^2*M

theorem PhysicalFrequencyParameterization.exists_fractional_diagonal_moment_bounds
    (A : PhysicalFrequencyParameterization E t ht J)
    (u : ℝ) (hu0 : 0≤u) (hu1 : u≤1) (hut : u≤t)
    (q : E) (hq : q∈A.domain) (hqr : IsRealPeriodOneHminusOne (J q)) :
    A.HasFractionalDiagonalMomentBounds u q := by
  let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht)
  let φ : realTypeSourceSubmodule 2 := ⟨A.normalizedSource q,A.real_source q hq hqr⟩
  have hφV : L φ.val∈A.physical.psi.family.domain := A.physical.psi.family.real_subset
    (normalizedWeightedSource_realType (sourceSobolevSpectralWeight t ht) φ.val φ.property)
  obtain ⟨D,_hD⟩ := A.physical.atlas.exists_errorDomain
    A.estimates.angular_extension.toSourcePsiNormalizedComplexExtension
    A.physical.psi.family.domain_open A.physical.psi.family.real_subset
  obtain ⟨S,hS,hφS,_hSD,K,M,hM,hbound⟩ :=
    D.exists_local_sobolev_diagonal_moment_bound A.estimates.angular_extension
      t ht u hu0 hu1 hut φ hφV
  obtain ⟨T,hT,hqT,hTA,hTS,_hTB⟩ := exists_open_common_pullback_domain A.domain A.domain_open q hq
    A.normalizedSource A.analytic_source.continuousOn S hS hφS
    J J.continuous A.physical.domain A.physical.domain_open (A.domain_subset hq)
  refine ⟨T,hT,hqT,hTA,K,M,hM,?_⟩
  intro a ha k hk
  have hb := hbound (A.normalizedSource a) (hTS a ha) k hk
  rw [A.source_identity a (hTA ha)] at hb
  exact hb

end NLS.KdV
