import NLS.SequenceSpaces.SobolevSignedCompletion
import NLS.KdV.HillAbelianCoordinateSequence
import NLS.KdV.HillHminusPhysicalDirichletLabels
import NLS.KdV.HillHminusOriginalSourceAdapter

/-! # Full original physical recovery of a signed analytic completion

ANY actual normalized positive rough coordinate map with physical recovery
and nonpositive zeros gives the SAME full original signed coordinates.
The literal half-order weight, negative reflection and central zero are
retained, including at low and collapsed physical gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

/-- Actual normalized positive recovery gives full original signed
physical recovery, with no physical L2 source-norm restriction. -/
theorem hillAbelian_signedTargetLift_physical
    (η : ℝ) (P : PeriodOneHminusOne → Coeff 2)
    (hzero : ∀ q∈ball (0 : PeriodOneHminusOne) η, ∀ j : ℤ, j≤0 → P q j=0)
    (hphys : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ n : ℕ+,
      P (hillPhysicalHminusEmbedding p).val (n : ℤ)=
        hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos/
          (Real.sqrt (1+(n : ℝ)) : ℂ))
    (p : RealPeriodOneHillPotential)
    (hp : (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η) (j : ℤ) :
    (WeightedCoeff.signedTargetLift (Weight.sobolev (-1)) (Weight.sobolev (-1/2)) P
      (hillPhysicalHminusEmbedding p).val).val j=
        hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j := by
  let v := Weight.sobolev (-1)
  let w := Weight.sobolev (-1/2)
  let Y := fun q => (WeightedCoeff.weightIsometry w 2).symm (P q)
  let q := (hillPhysicalHminusEmbedding p).val
  have hJ : WeightedCoeff.conjugateReflection v (Weight.sobolev_neg (-1)) q=q :=
    (periodOneHminusConjugation_fixed_iff q).mpr (hillPhysicalHminusEmbedding p).property
  have hnonpos (k : ℤ) (hk : k≤0) : (Y q).val k=0 := by
    change P q k/(w k : ℂ)=0
    rw [hzero q hp k hk,zero_div]
  have hpositive (n : ℕ+) : (Y q).val (n : ℤ)=
      hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos := by
    change P q (n : ℤ)/(w (n : ℤ) : ℂ)=_
    have hw : (w (n : ℤ) : ℂ)=(Real.sqrt (1+(n : ℝ)) : ℂ)⁻¹ := by
      simp only [w,Weight.sobolev_neg_half_apply,Int.cast_natCast,
        abs_of_nonneg (show (0 : ℝ)≤(n : ℝ) by positivity),ofReal_inv]
    rw [hphys p hp n,hw,div_inv_eq_mul]
    exact div_mul_cancel₀ _ (ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne')
  have hnat (n : ℕ) : (Y q).val (n : ℤ)=
      hillAbelianPositiveCoefficient SpectralWeight.one (hillUnitRealSourceUnembed p) n := by
    by_cases hn : 1≤n
    · let k : ℕ+ := ⟨n,by omega⟩
      have hh := hpositive k
      change (Y q).val (n : ℤ)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn at hh
      rw [hillAbelianPositiveCoefficient,dif_pos hn]
      have he := congrArg (fun a : RealPeriodOneHillPotential =>
        hillDirichletAbelianCoordinate a.val a.property.1 a.property.2 n hn)
        (hillRealWeightedEmbedding_unitUnembed p)
      exact hh.trans he.symm
    · have hn0 : n=0 := by omega
      subst n
      simpa only [Nat.cast_zero,hillAbelianPositiveCoefficient_zero] using hnonpos 0 le_rfl
  rw [WeightedCoeff.signedTargetLift_eq_weightedSourceSignedCompletion,
    WeightedCoeff.weightedSourceSignedCompletion_apply v w (Weight.sobolev_neg (-1)) (Weight.sobolev_neg (-1/2))]
  change (Y q).val j+conj ((Y (WeightedCoeff.conjugateReflection v (Weight.sobolev_neg (-1)) q)).val (-j))=_
  rw [hJ]
  by_cases hj : 0≤j
  · rw [hnonpos (-j) (by omega),map_zero,add_zero,hillAbelianRawCoordinateSequence,if_pos hj]
    have hn : ((j.natAbs : ℕ) : ℤ)=j := by rw [Int.natCast_natAbs,abs_of_nonneg hj]
    rw [←hn]
    exact hnat _
  · rw [hnonpos j (by omega),zero_add,hillAbelianRawCoordinateSequence,if_neg hj]
    congr 1
    have hn : ((j.natAbs : ℕ) : ℤ)=-j := by rw [Int.natCast_natAbs,abs_of_nonpos (by omega : j≤0)]
    rw [←hn]
    exact hnat _

end NLS.KdV
