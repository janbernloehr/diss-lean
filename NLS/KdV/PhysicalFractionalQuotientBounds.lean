import NLS.KdV.PhysicalFrequencyParameterization
import NLS.ZakharovShabat.SourcePsiFractionalQuotientDecay
import NLS.ZakharovShabat.SourceCriticalFractionalQuotientDecay

/-! Simultaneous fractional bounds for BOTH actual normalization
quotients of one physical frequency chart, in its parameter Banach norm. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {t : ℝ} {ht : 0≤t} {J : E →L[ℂ] PeriodOneHminusOne}

def PhysicalFrequencyParameterization.HasFractionalQuotientBounds
    (A : PhysicalFrequencyParameterization E t ht J) (u : ℝ) (q : E) : Prop :=
  let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht)
  ∃ T : Set E, IsOpen T ∧ q∈T ∧ T⊆A.domain ∧ ∃ K : ℕ, ∃ M : ℝ, 0≤M ∧
    ∀ a∈T, ∀ k : ℤ, K≤k.natAbs → ∀ z∈refinedResonantDisk k,
      (Weight.sobolev u k*‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) k
        (z,(canonicalCriticalDisplacement (by norm_num) (by norm_num)
          (periodOnePotential (L (A.normalizedSource a))) (periodOnePotential_mem _),L (A.normalizedSource a)))-1‖≤M) ∧
      ∀ n : ℤ, Weight.sobolev u k*‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) k
        (z,(sourcePsiFillDeletedRoot n (A.physical.psi.family.roots n (L (A.normalizedSource a)))
          (sourceStandardRootMidpoint (by norm_num) (by norm_num) (L (A.normalizedSource a)) n),
          L (A.normalizedSource a)))-1‖≤M

theorem PhysicalFrequencyParameterization.exists_fractional_quotient_bounds
    (A : PhysicalFrequencyParameterization E t ht J)
    (u : ℝ) (hu0 : 0≤u) (hu1 : u≤1) (hu2t : u≤2*t)
    (q : E) (hq : q∈A.domain) (hqr : IsRealPeriodOneHminusOne (J q)) :
    A.HasFractionalQuotientBounds u q := by
  let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht)
  let φ : realTypeSourceSubmodule 2 := ⟨A.normalizedSource q,A.real_source q hq hqr⟩
  have hφV : L φ.val∈A.physical.psi.family.domain := A.physical.psi.family.real_subset
    (normalizedWeightedSource_realType (sourceSobolevSpectralWeight t ht) φ.val φ.property)
  obtain ⟨Nc,εc,_hεc,Tc,hTc,hφc,Kc,hNKc,Mc,hMc,hc⟩ :=
    exists_local_sobolev_critical_quotient_decay t ht u hu0 hu1 hu2t φ
  obtain ⟨Ns,εs,_hεs,Ts,hTs,hφs,_hTsV,Ks,hNKs,Ms,_hMs,hs⟩ :=
    A.estimates.angular_extension.exists_local_sobolev_filled_quotient_decay t ht u hu0 hu1 hu2t φ hφV
  have hqS : A.normalizedSource q∈Tc∩Ts := ⟨hφc,hφs⟩
  obtain ⟨T,hT,hqT,hTA,hTS,_hTB⟩ := exists_open_common_pullback_domain A.domain A.domain_open q hq
    A.normalizedSource A.analytic_source.continuousOn (Tc∩Ts) (hTc.inter hTs) hqS
    J J.continuous A.physical.domain A.physical.domain_open (A.domain_subset hq)
  refine ⟨T,hT,hqT,hTA,max Kc Ks,max Mc Ms,le_trans hMc (le_max_left _ _),?_⟩
  intro a ha k hk z hz
  have hkc : Kc≤k.natAbs := (le_max_left _ _).trans hk
  have hks : Ks≤k.natAbs := (le_max_right _ _).trans hk
  have hzc : z∈sourceIsolatingDisc (by norm_num) (by norm_num) (L φ.val) Nc εc k := by
    simpa only [sourceIsolatingDisc,if_neg (by omega : ¬k.natAbs≤Nc)] using hz
  have hzs : z∈sourceIsolatingDisc (by norm_num) (by norm_num) (L φ.val) Ns εs k := by
    simpa only [sourceIsolatingDisc,if_neg (by omega : ¬k.natAbs≤Ns)] using hz
  exact ⟨(hc (A.normalizedSource a) (hTS a ha).1 k hkc z hzc).trans (le_max_left _ _),
    fun n => (hs (A.normalizedSource a) (hTS a ha).2 n k hks z hzs).trans (le_max_right _ _)⟩

end NLS.KdV
