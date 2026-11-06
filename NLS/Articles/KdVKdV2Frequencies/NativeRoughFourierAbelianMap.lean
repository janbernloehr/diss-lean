import NLS.Articles.KdVKdV2Frequencies.NativeRoughSignedAbelianCoordinates
import NLS.Articles.KdVKdV2Frequencies.FreeFourierDifferential
import NLS.KdV.HillUnitRealSourceJetUniqueness
import NLS.SequenceSpaces.PeriodOneHminusOneMeanZeroDensity

/-! # The actual signed rough Abelian map has its Fourier derivative

Original physical real germs identify the literal L2 pullback derivative.
Mean-zero L2 density then determines the full continuous rough derivative,
with the original sqrt(action) normalization at every signed output slot.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

private theorem rough_fourier_derivative
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (η : ℝ) (hη : 0<η) (hZa : AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η))
    (hp : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ j : ℤ,
      (Z (hillPhysicalHminusEmbedding p).val).val j=
        hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j)
    (h : PeriodOneHminusOne) (hmean : h.val 0=0) (j : ℤ) :
    ((fderiv ℂ Z 0) h).val j=(Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹*h.val j := by
  let w := Weight.sobolev (-1/2)
  let ev := WeightedCoeff.evalCLM w 2 j
  let C : Coeff 2 → ℂ := fun u => ev (Z (periodOneL2Inclusion u))
  obtain ⟨W,hWa,_hW0,hWd,hWp⟩ := exists_hillPhysicalAbelianMap_scalar_fourier_differential j
  have hZ0 := (hZa 0 (mem_ball_self hη)).differentiableAt
  have hZL : HasFDerivAt Z (fderiv ℂ Z 0) (periodOneL2Inclusion 0) := by
    simpa only [map_zero] using hZ0.hasFDerivAt
  have hCd : HasFDerivAt C (ev.comp ((fderiv ℂ Z 0).comp periodOneL2Inclusion)) 0 :=
    ev.hasFDerivAt.comp 0 (hZL.comp 0 periodOneL2Inclusion.hasFDerivAt)
  let p0 : RealHillWeightedPotential SpectralWeight.one := ⟨0,by intro k; simp⟩
  let S : RealHillWeightedPotential SpectralWeight.one → PeriodOneHminusOne :=
    fun p => periodOneL2Inclusion (SpectralWeight.one.doubleIndex.toCoeff p.val)
  have ht : Tendsto S (𝓝 p0) (𝓝 (0 : PeriodOneHminusOne)) := by
    simpa only [S,p0,Function.comp_def,map_zero] using
      (periodOneL2Inclusion.continuous.comp (SpectralWeight.one.doubleIndex.toCoeff.continuous.comp
        continuous_subtype_val)).tendsto p0
  have he : ∀ᶠ p : RealHillWeightedPotential SpectralWeight.one in 𝓝 p0,
      C (SpectralWeight.one.doubleIndex.toCoeff p.val)=W (SpectralWeight.one.doubleIndex.toCoeff p.val) := by
    filter_upwards [ht.eventually (ball_mem_nhds (0 : PeriodOneHminusOne) hη),hWp] with p hpball hWp
    let q := hillRealWeightedEmbedding SpectralWeight.one p
    have hEmb : (hillPhysicalHminusEmbedding q).val=S p := by
      change periodOneL2Inclusion (Fourier.paritySample 0 (SpectralWeight.one.toCoeff q.val))=_
      rw [hillRealWeightedEmbedding_toCoeff,hillUnitSample_periodDouble]
    have hmatch := hp q (hEmb.symm ▸ hpball) j
    rw [hEmb,hillUnitUnembed_realWeightedEmbedding] at hmatch
    change (Z (S p)).val j=W (SpectralWeight.one.doubleIndex.toCoeff p.val)
    rw [hWp]
    exact hmatch.trans (by rw [hillPhysicalAbelianMap,hillAbelianCoordinateSequence_apply])
  have hD := fderiv_eq_of_eventuallyEq_unit_realPotentials C W hCd.differentiableAt hWa.differentiableAt he
  rw [hCd.fderiv] at hD
  let L : PeriodOneHminusOne →L[ℂ] ℂ := ev.comp (fderiv ℂ Z 0)
  let M : PeriodOneHminusOne →L[ℂ] ℂ :=
    (Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹ • WeightedCoeff.evalCLM (Weight.sobolev (-1)) 2 j
  have hL2 (u : Coeff 2) (hu : u 0=0) : L (periodOneL2Inclusion u)=M (periodOneL2Inclusion u) := by
    have hh := congrArg (fun A : Coeff 2 →L[ℂ] ℂ => A u) hD
    change ((fderiv ℂ Z 0) (periodOneL2Inclusion u)).val j=(fderiv ℂ W 0) u at hh
    simpa only [L,M,ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul,ev,
      WeightedCoeff.evalCLM_apply,periodOneL2Inclusion_apply] using hh.trans (hWd u hu)
  exact continuousLinearMap_eq_on_meanZero_of_periodOneL2Inclusion L M hL2 h hmean

theorem exists_hillHminus_native_fourier_abelian_map :
    ∃ η C : ℝ, ∃ Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2,
      0 < η ∧ 0 < C ∧ AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η) ∧ Z 0=0 ∧
      (∀ q∈ball (0 : PeriodOneHminusOne) η, ‖Z q‖≤C*‖q‖ ∧ (Z q).val 0=0) ∧
      (∀ q∈ball (0 : PeriodOneHminusOne) η, IsRealPeriodOneHminusOne q →
        ∀ j : ℤ, (Z q).val (-j)=conj ((Z q).val j)) ∧
      (∀ p : RealPeriodOneHillPotential,
        (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ j : ℤ,
        (Z (hillPhysicalHminusEmbedding p).val).val j=
          hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j) ∧
      ∀ h : PeriodOneHminusOne, h.val 0=0 → ∀ j : ℤ,
        ((fderiv ℂ Z 0) h).val j=(Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹*h.val j := by
  obtain ⟨η,C,Z,hη,hC,hZa,hZ0,hZb,hZr,hZp⟩ := exists_hillHminus_native_signed_abelian_coordinates
  exact ⟨η,C,Z,hη,hC,hZa,hZ0,hZb,hZr,hZp,rough_fourier_derivative Z η hη hZa hZp⟩

end NLS.Articles.KdVKdV2Frequencies
