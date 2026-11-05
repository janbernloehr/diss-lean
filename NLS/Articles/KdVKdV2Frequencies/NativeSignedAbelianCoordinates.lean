import NLS.Articles.KdVKdV2Frequencies.NativePositiveAbelianCoordinates
import NLS.SequenceSpaces.SignedHolomorphicCompletion

/-! # A native holomorphic extension of the actual signed weighted Abelian sequence -/
noncomputable section
open scoped ComplexConjugate
open Set Metric Complex
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

private theorem physical_unit_conjugation_fixed (p : RealHillWeightedPotential SpectralWeight.one) :
    periodOneL2Conjugation (SpectralWeight.one.doubleIndex.toCoeff p.val) =
      SpectralWeight.one.doubleIndex.toCoeff p.val := by
  let q := hillRealWeightedEmbedding SpectralWeight.one p
  let u := SpectralWeight.one.doubleIndex.toCoeff p.val
  have hcoeff : SpectralWeight.one.toCoeff q.val = Coeff.periodDouble u := by
    dsimp only [q,hillRealWeightedEmbedding,u]
    rw [toCoeff_hillPeriodOneUnitPotential,toCoeff_hillPeriodOnePotential]
  ext j
  change periodOneL2Conjugation u j = u j
  rw [periodOneL2Conjugation_apply]
  have h := q.property.2 (2*j)
  rw [hcoeff,show -(2*j) = 2*(-j) by ring,Coeff.periodDouble_even,Coeff.periodDouble_even] at h
  rw [h,conj_conj]

private theorem target_weight_even (j : ℤ) :
    hillAbelianTargetWeight SpectralWeight.one (-j) = hillAbelianTargetWeight SpectralWeight.one j := by
  rw [hillAbelianTargetWeight_one_sqrt,hillAbelianTargetWeight_one_sqrt,Int.cast_neg,abs_neg]

theorem exists_hillPhysical_native_signed_abelian_coordinates :
    ∃ η : ℝ, ∃ Z : Coeff 2 → WeightedCoeff (hillAbelianTargetWeight SpectralWeight.one) 2, ∃ K : ℝ,
      0 < η ∧ 0 < K ∧ AnalyticOnNhd ℂ Z (ball (0 : Coeff 2) η) ∧ Z 0 = 0 ∧
      (∀ u ∈ ball (0 : Coeff 2) η, ‖Z u‖ ≤ K*(‖u‖+‖u‖^2) ∧ (Z u).val 0 = 0) ∧
      ∀ p : RealHillWeightedPotential SpectralWeight.one,
        SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η →
        ∀ j : ℤ, (Z (SpectralWeight.one.doubleIndex.toCoeff p.val)).val j =
          hillAbelianRawCoordinateSequence SpectralWeight.one p j := by
  obtain ⟨η,Y,K,hη,hK,hYa,hY0,hYb,hphysical⟩ := exists_hillPhysical_native_positive_abelian_coordinates
  let Z := WeightedCoeff.signedHolomorphicCompletion (hillAbelianTargetWeight SpectralWeight.one) Y
  obtain ⟨hZa,hZ0,hZb⟩ := WeightedCoeff.signedHolomorphicCompletion_analytic_bound
    (hillAbelianTargetWeight SpectralWeight.one) Y η K hYa hY0 (fun u hu => (hYb u hu).1)
  have hcoord (u : Coeff 2) (j : ℤ) : (Z u).val j =
      (Y u).val j+conj ((Y (periodOneL2Conjugation u)).val (-j)) :=
    WeightedCoeff.signedHolomorphicCompletion_apply _ target_weight_even Y u j
  refine ⟨η,Z,2*K,hη,by positivity,hZa,hZ0,?_,?_⟩
  · intro u hu
    refine ⟨hZb u hu,?_⟩
    have hJu : periodOneL2Conjugation u ∈ ball (0 : Coeff 2) η := by
      rwa [mem_ball_zero_iff,norm_periodOneL2Conjugation,← mem_ball_zero_iff]
    rw [hcoord,(hYb u hu).2 0 le_rfl,neg_zero,(hYb _ hJu).2 0 le_rfl,map_zero,zero_add]
  · intro p hp j
    let u := SpectralWeight.one.doubleIndex.toCoeff p.val
    have hJu : periodOneL2Conjugation u = u := physical_unit_conjugation_fixed p
    have hzero : (Y u).val 0 = 0 := (hYb u hp).2 0 le_rfl
    have hnat (n : ℕ) : (Y u).val (n : ℤ) = hillAbelianPositiveCoefficient SpectralWeight.one p n := by
      by_cases hn : 1 ≤ n
      · let k : ℕ+ := ⟨n,by omega⟩
        have he := hphysical p hp k
        change (Y u).val (n : ℤ) = hillDirichletAbelianCoordinate
          (hillRealWeightedEmbedding SpectralWeight.one p).val
          (hillRealWeightedEmbedding SpectralWeight.one p).property.1
          (hillRealWeightedEmbedding SpectralWeight.one p).property.2 n hn at he
        simpa only [hillAbelianPositiveCoefficient,dif_pos hn] using he
      · have hn0 : n = 0 := by omega
        subst n
        simpa only [Nat.cast_zero,hillAbelianPositiveCoefficient_zero] using hzero
    rw [hcoord,hJu]
    by_cases hj : 0 ≤ j
    · have hn : (Y u).val (-j) = 0 := (hYb u hp).2 (-j) (by omega)
      rw [hn,map_zero,add_zero,hillAbelianRawCoordinateSequence,if_pos hj]
      have he : ((j.natAbs : ℕ) : ℤ) = j := by rw [Int.natCast_natAbs,abs_of_nonneg hj]
      rw [← he]
      exact hnat _
    · have hz : (Y u).val j = 0 := (hYb u hp).2 j (by omega)
      rw [hz,zero_add,hillAbelianRawCoordinateSequence,if_neg hj]
      congr 1
      have he : ((j.natAbs : ℕ) : ℤ) = -j := by rw [Int.natCast_natAbs,abs_of_nonpos (by omega : j ≤ 0)]
      rw [← he]
      exact hnat _

end NLS.Articles.KdVKdV2Frequencies
