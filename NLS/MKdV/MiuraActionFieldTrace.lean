import NLS.MKdV.MiuraGardnerTransfer
import NLS.ZakharovShabat.SourceSobolevMomentumActionSum
import NLS.ZakharovShabat.SourceSection20Original

/-! # The physical scalar translation field as an action trace

Pairing positive and negative source modes, with the actual diagonal
Gardner transfer, proves an unconditional L² expansion of ∂x u in the
physical action fields. No independent mKdV Birkhoff chart is assumed.
-/
noncomputable section
open Set Filter Topology NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

/-- The actual positive physical Gardner action fields recover the spatial derivative in L². -/
theorem hasSum_miuraGardnerDirections_spatialDerivative (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    HasSum (fun n : ℕ => (2*(Real.pi : ℂ)*(n+1)) •
      l2GardnerDirection (miuraL2Action (n+1)) (scalarInclusion a)) (periodOneDerivative a) := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num)
  obtain ⟨V₀,V,X,u,E,Wa,A,C,U,Q⟩ := sourceSection20_original
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num)
  let b : realTypeSobolevSourceLocus := ⟨(a,a),(realDiagonalH1Source a ha).property⟩
  let f : ℤ → CoeffPair 2 := fun n => (2*(Real.pi : ℂ)*n) •
    sourceHamiltonianVector le_rfl (sourceComplexAction (by simp) (by norm_num) n)
      (sobolevSourceInclusion (a,a))
  have hS : HasSum f (sourceSobolevSpatialDerivative (a,a)) :=
    D.hasSum_actionHamiltonian_spatialDerivative E.previous.original_theta_common_domain
      Q.toSourceFullAbelianDifferentialData A b
  have hz : f 0 = 0 := by simp only [f,Int.cast_zero,mul_zero,zero_smul]
  have hN := hS.nat_add_neg
  rw [hz,add_zero] at hN
  have hshift : HasSum (fun n : ℕ => f (n+1)+f (-(n+1)))
      (sourceSobolevSpatialDerivative (a,a)) := by
    have h := (hasSum_nat_add_iff' 1).mpr hN
    simpa only [Finset.sum_range_one,Nat.cast_zero,neg_zero,hz,zero_add,sub_zero,Nat.cast_add,Nat.cast_one] using h
  have hmode (n : ℕ) : f (n+1)+f (-(n+1)) =
      scalarL2Diagonal ((2*(Real.pi : ℂ)*(n+1)) •
        l2GardnerDirection (miuraL2Action (n+1)) (scalarInclusion a)) := by
    have hindex : (n : ℤ)+1 = ((n+1 : ℕ) : ℤ) := by omega
    rw [hindex]
    dsimp only [f,sourceHamiltonianVector]
    rw [Int.cast_neg,mul_neg,neg_smul,← sub_eq_add_neg,← smul_sub,← map_sub,
      miuraActionDifference_direction a ha (n+1) (by omega),map_smul]
    norm_cast
  let L := (ContinuousLinearMap.fst ℂ (Coeff 2) (Coeff 2)).comp
    (CoeffPair.toMax 2).toContinuousLinearMap
  have h := L.hasSum hshift
  change HasSum (fun n : ℕ => (f (n+1)+f (-(n+1))).fst) (periodOneDerivative a) at h
  simpa only [hmode,scalarL2Diagonal_fst] using h

/-- Every actual scalar L² cotangent may be applied to the convergent physical field trace. -/
theorem hasSum_miuraGardnerDirections_cotangent (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (L : Coeff 2 →L[ℂ] ℂ) :
    HasSum (fun n : ℕ => (2*(Real.pi : ℂ)*(n+1))*
      L (l2GardnerDirection (miuraL2Action (n+1)) (scalarInclusion a))) (L (periodOneDerivative a)) := by
  simpa only [map_smul,smul_eq_mul] using
    L.hasSum (hasSum_miuraGardnerDirections_spatialDerivative a ha)

end NLS.MKdV
