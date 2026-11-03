import NLS.KdV.UnitHillFreeIsomorphism
import NLS.SequenceSpaces.WeightedSingle
import NLS.SequenceSpaces.WeightedFiniteCoefficients
import NLS.FunctionalAnalysis.DenseHyperplaneImage

/-! # Dense full-dual images with the endpoint trace removed

High unit-frequency modes have trace one while their H-minus-one mass images
vanish in norm. Thus removing the Dirichlet trace does not remove any part
of the closure of the full dual image.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ZakharovShabat

/-- The unchanged unit Fourier sequence in the full unit-period H-minus-one space. -/
def unitHillMass : ScalarDomain 2 →L[ℂ] PeriodOneHminusOne :=
  WeightedCoeff.sobolevInclusion (by norm_num : (-1:ℝ) ≤ 1)

@[simp] theorem unitHillMass_coefficient (f : ScalarDomain 2) (n : ℤ) :
    (unitHillMass f).val n = f.val n :=
  WeightedCoeff.sobolevInclusion_apply _ f n

/-- The actual unconjugated mass form on the full unit-period H1 space. -/
def unitHillMassDual : ScalarDomain 2 →L[ℂ] (ScalarDomain 2 →L[ℂ] ℂ) :=
  (WeightedCoeff.sobolevDualityIsometry (p := 2) (q := 2) 1 (by norm_num)).toContinuousLinearEquiv.toContinuousLinearMap.comp unitHillMass

/-- All full H-minus-one data are norm approximable by actual H1 mass images. -/
theorem denseRange_unitHillMass : DenseRange unitHillMass := by
  apply (WeightedCoeff.denseRange_ofFinsupp (Weight.sobolev (-1)) 2 (by norm_num)).mono
  rintro _ ⟨a, rfl⟩
  refine ⟨WeightedCoeff.ofFinsupp (Weight.sobolev 1) 2 a, Subtype.ext ?_⟩
  funext n
  exact unitHillMass_coefficient _ n

/-- The full unit-period H1 dual is the norm closure of the actual mass forms. -/
theorem denseRange_unitHillMassDual : DenseRange unitHillMassDual :=
  (WeightedCoeff.sobolevDualityIsometry (p := 2) (q := 2) 1 (by norm_num)).surjective.denseRange.comp
    denseRange_unitHillMass
    (WeightedCoeff.sobolevDualityIsometry (p := 2) (q := 2) 1 (by norm_num)).continuous

/-- Unit-amplitude high modes disappear in H-minus-one despite their fixed endpoint trace. -/
theorem tendsto_unitHillMass_scalarMode :
    Tendsto (fun n : ℕ => unitHillMass (scalarMode (n:ℤ) 1)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have he (n : ℕ) : unitHillMass (scalarMode (n:ℤ) 1) =
      WeightedCoeff.single (p := 2) (Weight.sobolev (-1)) (n:ℤ) 1 := by
    apply Subtype.ext
    funext k
    simp only [unitHillMass_coefficient, scalarMode_apply, WeightedCoeff.single_val,
      Pi.single_apply]
  have hn (n : ℕ) : ‖unitHillMass (scalarMode (n:ℤ) 1)‖ = (1+(n:ℝ))⁻¹ := by
    rw [he, WeightedCoeff.norm_single]
    simp [Weight.sobolev_apply, Real.rpow_neg_one]
  simp only [hn]
  exact tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_left atTop 1 tendsto_natCast_atTop_atTop)

/-- Every full-dual datum is still approximable after imposing the actual zero trace. -/
theorem denseRange_unitHillMassDual_on_Dirichlet :
    DenseRange (unitHillMassDual.comp unitDirichletSubspace.subtypeL) := by
  apply NLS.FunctionalAnalysis.denseRange_restrict_ker_of_vanishing_trace
    unitHillMassDual unitDirichletTrace denseRange_unitHillMassDual
      (fun n => scalarMode (n:ℤ) 1) (fun n => unitDirichletTrace_scalarMode (n:ℤ) 1)
  let B : PeriodOneHminusOne →L[ℂ] (ScalarDomain 2 →L[ℂ] ℂ) :=
    (WeightedCoeff.sobolevDualityIsometry (p := 2) (q := 2) 1 (by norm_num)).toContinuousLinearEquiv.toContinuousLinearMap
  have ht := (B.continuous.tendsto 0).comp tendsto_unitHillMass_scalarMode
  simpa only [map_zero, Function.comp_def, unitHillMassDual, ContinuousLinearMap.comp_apply, B] using ht

end NLS.KdV
