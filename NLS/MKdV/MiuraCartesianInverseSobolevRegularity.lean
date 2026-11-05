import NLS.MKdV.MiuraJointFiberSobolevRegularity
import NLS.ZakharovShabat.SourceDiagonalActionRootInverse
import NLS.SequenceSpaces.EvenActionPositiveRegularity

/-! # Global Sobolev regularity from actual Cartesian data

A bounded inverse spectral symbol recovers positive NLS coordinates with
exactly the source weight. Even diagonal NLS actions recover the negative
modes, and the checked NLS Sobolev characterization recovers the source.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

/-- Every positive NLS coordinate has the source Sobolev weight whenever
the actual Cartesian map has the corresponding native half-order weight. -/
theorem miuraNLS_positive_weighted_mem_of_Cartesian_data (s : ℕ) (a : MiuraRealL2)
    (z : MiuraPositiveSobolevTarget s)
    (hz : miuraPositiveCartesianMap a.val = miuraPositiveSobolevL2CartesianInclusion s z) :
    Memℓp (fun n : ℤ => if 0 < n then (Weight.sobolev (s : ℝ) n : ℂ)*
      (sourceBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi (scalarL2Diagonal a.val)).1 n else 0) 2 ∧
    Memℓp (fun n : ℤ => if 0 < n then (Weight.sobolev (s : ℝ) n : ℂ)*
      (sourceBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi (scalarL2Diagonal a.val)).2 n else 0) 2 := by
  let φ : realDiagonalSourceLocus 2 := ⟨scalarL2Diagonal a.val,scalarL2Diagonal_realDiagonal a.val a.property⟩
  let q := sourceDiagonalActionRootInverseSequence φ.val
  let x := Coeff.multiplier q (WeightedCoeff.weightIsometry (miuraCartesianWeight s) 2 z.1.1.val)
  let y := -(Coeff.multiplier q (WeightedCoeff.weightIsometry (miuraCartesianWeight s) 2 z.1.2.val))
  have hcoords (n : ℤ) :
      x n = (if 0 < n then (Weight.sobolev (s : ℝ) n : ℂ)*
        (sourceBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi φ.val).1 n else 0) ∧
      y n = (if 0 < n then (Weight.sobolev (s : ℝ) n : ℂ)*
        (sourceBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi φ.val).2 n else 0) := by
    by_cases hn : 0 < n
    · have hc := miuraPositiveCartesianMap_positive a.val a.property n.toNat (by omega)
      rw [Int.toNat_of_nonneg hn.le] at hc
      rw [hz,miuraPositiveSobolevL2CartesianInclusion_eval] at hc
      have hi : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.le
      have hcx := congrArg Prod.fst hc
      have hcy := congrArg Prod.snd hc
      change z.1.1.val.val n = _ at hcx
      change z.1.2.val.val n = _ at hcy
      dsimp only [miuraL2CartesianCoordinates] at hcx hcy
      rw [hi] at hcx hcy
      have hq := sourceDiagonalActionRootInverseSequence_mul φ n hn
      constructor
      · change q n*((miuraCartesianWeight s n : ℂ)*z.1.1.val.val n) = _
        rw [if_pos hn,hcx,miuraCartesianWeight_factor]
        push_cast
        calc
          _ = (Weight.sobolev (s : ℝ) n : ℂ)*(q n*((Weight.sobolev (1/2) n : ℂ)*
            sourceDiagonalActionRoot (by simp) (by norm_num) n φ.val))*
              (sourceBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi φ.val).1 n := by ring
          _ = _ := by rw [hq]; ring
      · change -(q n*((miuraCartesianWeight s n : ℂ)*z.1.2.val.val n)) = _
        rw [if_pos hn,hcy,miuraCartesianWeight_factor]
        push_cast
        calc
          _ = (Weight.sobolev (s : ℝ) n : ℂ)*(q n*((Weight.sobolev (1/2) n : ℂ)*
            sourceDiagonalActionRoot (by simp) (by norm_num) n φ.val))*
              (sourceBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi φ.val).2 n := by ring
          _ = _ := by rw [hq]; ring
    · have hq : q n = 0 := by
        simp only [q,sourceDiagonalActionRootInverseSequence_apply,if_neg hn]
      constructor
      · change q n*((miuraCartesianWeight s n : ℂ)*z.1.1.val.val n) = _
        rw [hq,zero_mul,if_neg hn]
      · change -(q n*((miuraCartesianWeight s n : ℂ)*z.1.2.val.val n)) = _
        rw [hq,zero_mul,neg_zero,if_neg hn]
  have hx : (x : ℤ → ℂ) = _ := funext (fun n => (hcoords n).1)
  have hy : (y : ℤ → ℂ) = _ := funext (fun n => (hcoords n).2)
  exact ⟨hx ▸ lp.memℓp x,hy ▸ lp.memℓp y⟩

/-- Native Cartesian target regularity forces both original NLS coordinate
sequences to have exactly the source Sobolev weight, on the full signed index. -/
theorem miuraNLS_real_weighted_mem_of_Cartesian_data (s : ℕ) (a : MiuraRealL2)
    (z : MiuraPositiveSobolevTarget s)
    (hz : miuraPositiveCartesianMap a.val = miuraPositiveSobolevL2CartesianInclusion s z) :
    let φ : realTypeSourceSubmodule 2 :=
      ⟨scalarL2Diagonal a.val,(scalarL2Diagonal_realDiagonal a.val a.property).1⟩
    Memℓp (fun n : ℤ => Weight.sobolev (s : ℝ) n*
      (sourceRealBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi φ).1 n) 2 ∧
    Memℓp (fun n : ℤ => Weight.sobolev (s : ℝ) n*
      (sourceRealBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi φ).2 n) 2 := by
  let φ : realTypeSourceSubmodule 2 :=
    ⟨scalarL2Diagonal a.val,(scalarL2Diagonal_realDiagonal a.val a.property).1⟩
  let v := sourceRealBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi φ
  obtain ⟨hx,hy⟩ := miuraNLS_positive_weighted_mem_of_Cartesian_data s a z hz
  have hpos : Memℓp (fun n => if 0 < n then Weight.sobolev (s : ℝ) n*v.1 n else 0) 2 ∧
      Memℓp (fun n => if 0 < n then Weight.sobolev (s : ℝ) n*v.2 n else 0) 2 := by
    constructor
    · apply hx.norm.mono
      intro n
      by_cases hn : 0 < n
      · simp only [if_pos hn]
        change ‖Weight.sobolev (s : ℝ) n*
          ((sourceBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi φ.val).1 n).re‖ ≤ _
        simpa only [Real.norm_eq_abs,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using
          Complex.abs_re_le_norm ((Weight.sobolev (s : ℝ) n : ℂ)*
            (sourceBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi φ.val).1 n)
      · simp only [if_neg hn,norm_zero,le_refl]
    · apply hy.norm.mono
      intro n
      by_cases hn : 0 < n
      · simp only [if_pos hn]
        change ‖Weight.sobolev (s : ℝ) n*
          ((sourceBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi φ.val).2 n).re‖ ≤ _
        simpa only [Real.norm_eq_abs,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using
          Complex.abs_re_le_norm ((Weight.sobolev (s : ℝ) n : ℂ)*
            (sourceBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi φ.val).2 n)
      · simp only [if_neg hn,norm_zero,le_refl]
  have heven (n : ℤ) : RealCoeff.pairAction v (-n) = RealCoeff.pairAction v n := by
    rw [miuraActionFlowFamily.data.real_pairAction_eq,miuraActionFlowFamily.data.real_pairAction_eq]
    have he := sourceComplexAction_even_of_diagonal (by simp) (by norm_num) φ (by ext j; rw [scalarL2Diagonal_fst,scalarL2Diagonal_snd]) n
    rw [sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) (-n) φ.val φ.property,
      sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) n φ.val φ.property] at he
    exact congrArg Complex.re he
  exact RealCoeff.weighted_mem_of_positive_of_even_action (by simp) (Weight.sobolev (s : ℝ))
    (by intro n; simp) v heven hpos.1 hpos.2

/-- Global source regularity, with no smallness or action-fiber premise. -/
theorem miuraSobolev_mem_of_Cartesian_data (s : ℕ) (a : MiuraRealL2)
    (z : MiuraPositiveSobolevTarget s)
    (hz : miuraPositiveCartesianMap a.val = miuraPositiveSobolevL2CartesianInclusion s z) :
    Memℓp (fun n : ℤ => (Weight.sobolev (s : ℝ) n : ℂ)*a.val n) 2 := by
  let φ : realTypeSourceSubmodule 2 :=
    ⟨scalarL2Diagonal a.val,(scalarL2Diagonal_realDiagonal a.val a.property).1⟩
  have hc := miuraNLS_real_weighted_mem_of_Cartesian_data s a z hz
  have hs := (miuraActionFlowFamily.data.source_sobolev_mem_iff_real_map_mem
    φ (s : ℝ) (Nat.cast_nonneg s)).mpr hc
  simpa only [φ,scalarL2Diagonal_fst] using hs.1

/-- Every physical L2 preimage of native order-s Cartesian data is the
coefficient-preserving inclusion of an actual physical H^s profile. -/
theorem exists_miuraSobolev_representative_of_Cartesian_data (s : ℕ) (a : MiuraRealL2)
    (z : MiuraRealSobolevCartesianTarget s)
    (hz : miuraPhysicalCartesianMap a = miuraPhysicalSobolevL2CartesianInclusion s z) :
    ∃ A : MiuraRealSobolevSource s, miuraPhysicalSobolevL2SourceInclusion s A = a := by
  have he := congrArg Subtype.val hz
  rw [miuraPhysicalCartesianMap_inclusion] at he
  exact exists_miuraSobolev_representative_of_mem s a (miuraSobolev_mem_of_Cartesian_data s a z.val he)

/-- The exact inverse image of the native Sobolev target is the native
Sobolev source, as subsets of the original L2 spaces. -/
theorem miuraPhysicalCartesian_preimage_Sobolev_range (s : ℕ) :
    miuraPhysicalCartesianMap ⁻¹' Set.range (miuraPhysicalSobolevL2CartesianInclusion s) =
      Set.range (miuraPhysicalSobolevL2SourceInclusion s) := by
  ext a
  constructor
  · rintro ⟨z,hz⟩
    exact exists_miuraSobolev_representative_of_Cartesian_data s a z hz.symm
  · rintro ⟨A,rfl⟩
    exact ⟨miuraPhysicalSobolevCartesianMap s A,miuraPhysicalSobolevCartesianMap_L2 s A⟩

end NLS.MKdV
