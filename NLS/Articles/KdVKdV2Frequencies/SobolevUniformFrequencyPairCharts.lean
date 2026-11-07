import NLS.KdV.PhysicalUniformFrequencyPairPullback
import NLS.Articles.KdVKdV2Frequencies.SobolevSharpFrequencyPairCharts

/-! Actual full-frequency pair germs with one uniform complex tail
neighborhood at every real normalized Sobolev pair, including zero actions. -/
noncomputable section
open Set Complex NLS.KdV NLS.ZakharovShabat NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

structure SobolevUniformFrequencyPairChart (D : GlobalRoughAbelianForwardData) (t : ℝ) where
  domain : Set (Coeff 2 × Coeff 2)
  domain_open : IsOpen domain
  roughPotential : (Coeff 2 × Coeff 2) → PeriodOneHminusOne
  rough_zero : ∀ z∈domain, (roughPotential z).val 0=0
  rough_real : ∀ z∈domain, z∈Coeff.realPairLocus 2 → IsRealPeriodOneHminusOne (roughPotential z)
  rough_signed : ∀ z∈domain, z∈Coeff.realPairLocus 2 → ∀ j : ℤ,
    (D.signed (roughPotential z)).val j=(signedPairToDeleted actionIndexEquiv z).val j/(Weight.sobolev (t-1/2) j : ℂ)
  physical : PhysicalMiuraFrequencyChart
  rough_mem : ∀ z∈domain, roughPotential z∈physical.domain
  correction : ℕ+ → (Coeff 2 × Coeff 2) → ℂ
  analytic_correction : ∀ n, AnalyticOnNhd ℂ (correction n) domain
  actual_correction : ∀ n, ∀ z∈domain, correction n z=physical.correction n (roughPotential z)+
    12*sourceComplexHigherAction (by norm_num) (by norm_num) (n:ℤ) 1
      (hillMiuraDiagonal (physical.psi.miura.lift (roughPotential z)))
  uniform_tail : ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ z∈domain, ∀ n : ℕ+, K≤(n:ℤ).natAbs →
    Weight.sobolev (3*t-1) (n:ℤ)*‖correction n z‖≤ε

theorem exists_sobolevUniformFrequencyPairChart
    (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0<t) (ht1 : t<2/3)
    (z₀ : Coeff 2 × Coeff 2) (hzr : z₀∈Coeff.realPairLocus 2) :
    ∃ P : SobolevUniformFrequencyPairChart D t, z₀∈P.domain := by
  obtain ⟨U,hU,hzU,Q,hQ,hmean,hmatch⟩ := exists_hillNative_pair_inverse D actionIndexEquiv t ht.le z₀ hzr
  let J := periodOneSobolevImageInclusion t ht.le
  have hreal (z : Coeff 2 × Coeff 2) (hz : z∈U) (hzreal : z∈Coeff.realPairLocus 2) :
      IsRealPeriodOneHminusOne (J (Q z)) := by
    rw [hmatch z hz hzreal]
    exact nativeRealPairInverse_real D actionIndexEquiv t ht.le z hzreal
  obtain ⟨A,hqA⟩ := exists_physicalNativeFrequencyParameterization t ht.le (Q z₀) (hreal z₀ hzU hzr)
  obtain ⟨T,f,hT,hzT,hTU,hTB,hfa,hphysical,hb⟩ :=
    A.exists_uniform_pair_frequency_pullback ht ht1 Q U hU hQ z₀ hzU hqA (hreal z₀ hzU hzr)
  refine ⟨{
    domain := T
    domain_open := hT
    roughPotential := fun z => J (Q z)
    rough_zero := ?_
    rough_real := fun z hz => hreal z (hTU hz)
    rough_signed := ?_
    physical := A.physical
    rough_mem := hTB
    correction := f
    analytic_correction := hfa
    actual_correction := hphysical
    uniform_tail := hb
  },hzT⟩
  · intro z hz
    rw [periodOneSobolevImageInclusion_apply]
    exact hmean z (hTU hz)
  · intro z hz hzreal j
    rw [hmatch z (hTU hz) hzreal]
    exact nativeRealPairInverse_signed_apply D actionIndexEquiv t ht.le z hzreal j

end NLS.Articles.KdVKdV2Frequencies
