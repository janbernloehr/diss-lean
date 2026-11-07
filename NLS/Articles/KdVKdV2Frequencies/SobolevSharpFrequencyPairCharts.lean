import NLS.KdV.PhysicalFrequencyPairPullback
import NLS.KdV.PhysicalNativeFrequencyParameterization
import NLS.KdV.HillNativePairInverse
import NLS.Articles.KdVKdV2Frequencies.RawPairArnoldActions

/-! Actual full-frequency germs in normalized Sobolev pairs at EVERY
real base. The target Sobolev order may be any lower order up to 2/3. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV NLS.ZakharovShabat NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

structure SobolevSharpFrequencyPairChart (D : GlobalRoughAbelianForwardData) (t θ : ℝ) where
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
  cutoff : ℕ
  bound : ℝ
  bound_nonneg : 0≤bound
  frequency_bound : ∀ z∈domain, ∀ n : ℕ+, cutoff≤(n:ℤ).natAbs →
    Weight.sobolev (3*θ-1) (n:ℤ)*‖correction n z‖≤bound
  pointwise_tail : θ<2/3 → ∀ z∈domain,
    Tendsto (fun n : ℕ => Weight.sobolev (3*θ-1) ((n+1:ℕ):ℤ)*‖correction ⟨n+1,by omega⟩ z‖) atTop (𝓝 0)

theorem exists_sobolevSharpFrequencyPairChart
    (D : GlobalRoughAbelianForwardData) (t θ : ℝ) (ht : 0≤t) (hθ : 0≤θ) (hθ1 : θ≤2/3) (hθt : θ≤t)
    (z₀ : Coeff 2 × Coeff 2) (hzr : z₀∈Coeff.realPairLocus 2) :
    ∃ P : SobolevSharpFrequencyPairChart D t θ, z₀∈P.domain := by
  obtain ⟨U,hU,hzU,Q,hQ,hmean,hmatch⟩ := exists_hillNative_pair_inverse D actionIndexEquiv t ht z₀ hzr
  let Jt := periodOneSobolevImageInclusion t ht
  let I : WeightedCoeff (Weight.sobolev (t-1)) 2 →L[ℂ] WeightedCoeff (Weight.sobolev (θ-1)) 2 :=
    WeightedCoeff.sobolevInclusion (by linarith)
  have hJ (a : WeightedCoeff (Weight.sobolev (t-1)) 2) :
      periodOneSobolevImageInclusion θ hθ (I a)=Jt a := by
    apply Subtype.ext
    funext n
    simp only [periodOneSobolevImageInclusion_apply,I,Jt,WeightedCoeff.sobolevInclusion_apply]
  have hreal (z : Coeff 2 × Coeff 2) (hz : z∈U) (hzreal : z∈Coeff.realPairLocus 2) :
      IsRealPeriodOneHminusOne (Jt (Q z)) := by
    rw [hmatch z hz hzreal]
    exact nativeRealPairInverse_real D actionIndexEquiv t ht z hzreal
  have hqr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion θ hθ (I (Q z₀))) := by
    rw [hJ]
    exact hreal z₀ hzU hzr
  obtain ⟨A,hqA⟩ := exists_physicalNativeFrequencyParameterization θ hθ (I (Q z₀)) hqr
  have hsharp := A.exists_sharp_frequency_decay hθ1 (I (Q z₀)) hqA hqr
  obtain ⟨B,T,f,hT,hzT,hTU,hTB,hfa,hphysical,K,M,hM,hb,hd⟩ :=
    A.exists_pair_frequency_pullback I Q Jt hJ U hU hQ z₀ hzU hqA hqr hsharp
  refine ⟨{
    domain := T
    domain_open := hT
    roughPotential := fun z => Jt (Q z)
    rough_zero := ?_
    rough_real := fun z hz => hreal z (hTU hz)
    rough_signed := ?_
    physical := B
    rough_mem := hTB
    correction := f
    analytic_correction := hfa
    actual_correction := hphysical
    cutoff := K
    bound := M
    bound_nonneg := hM
    frequency_bound := hb
    pointwise_tail := hd
  },hzT⟩
  · intro z hz
    rw [periodOneSobolevImageInclusion_apply]
    exact hmean z (hTU hz)
  · intro z hz hzreal j
    rw [hmatch z (hTU hz) hzreal]
    exact nativeRealPairInverse_signed_apply D actionIndexEquiv t ht z hzreal j

end NLS.Articles.KdVKdV2Frequencies
