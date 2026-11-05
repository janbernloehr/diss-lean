import NLS.MKdV.MiuraCartesianPhaseSaturation
import NLS.MKdV.MiuraRealSobolevCartesianCompatibility
import NLS.ZakharovShabat.SourceActionSobolevEquivalence
import NLS.SequenceSpaces.PhysicalRealWeightedLift

/-! # All Sobolev regularities are constant on joint action fibers -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

/-- Equal original NLS actions force identical nonnegative real Sobolev
regularity of physical scalar profiles, globally in original L2. -/
theorem miuraSobolev_mem_iff_of_NLS_actions_eq (a b : MiuraRealL2)
    (hI : miuraOriginalNLSActionSequence a.val = miuraOriginalNLSActionSequence b.val)
    (t : ℝ) (ht : 0 ≤ t) :
    Memℓp (fun n : ℤ => (Weight.sobolev t n : ℂ)*a.val n) 2 ↔
      Memℓp (fun n : ℤ => (Weight.sobolev t n : ℂ)*b.val n) 2 := by
  let φ : realTypeSourceSubmodule 2 :=
    ⟨scalarL2Diagonal a.val,(scalarL2Diagonal_realDiagonal a.val a.property).1⟩
  let ψ : realTypeSourceSubmodule 2 :=
    ⟨scalarL2Diagonal b.val,(scalarL2Diagonal_realDiagonal b.val b.property).1⟩
  have ha (n : ℤ) : (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re =
      (sourceRealAction (by simp) (by norm_num) ψ.val ψ.property n).re := by
    have h := congrArg (fun z : Coeff 1 => (z n).re) hI
    rw [miuraOriginalNLSActionSequence_apply a.val (real_mem_miuraOriginalNLSActionDomain a.val a.property),
      miuraOriginalNLSActionSequence_apply b.val (real_mem_miuraOriginalNLSActionDomain b.val b.property)] at h
    rw [sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) n φ.val φ.property,
      sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) n ψ.val ψ.property] at h
    exact h
  have h := miuraActionFlowFamily.data.source_sobolev_mem_iff_of_actions_eq φ ψ ha t ht
  simpa only [φ,ψ,scalarL2Diagonal_fst,scalarL2Diagonal_snd,and_self] using h

/-- Coefficient equality identifies a native physical representative in original L2. -/
theorem miuraPhysicalSobolevL2SourceInclusion_eq_of_coefficients (s : ℕ)
    (B : MiuraRealSobolevSource s) (b : MiuraRealL2)
    (hB : ∀ n : ℤ, B.val.val n = b.val n) : miuraPhysicalSobolevL2SourceInclusion s B = b := by
  apply Subtype.ext
  ext n
  exact (miuraPhysicalSobolevL2SourceInclusion_apply s B n).trans (hB n)

/-- A physical original-L2 profile with the native weight has a
coefficient-preserving physical H^s representative. -/
theorem exists_miuraSobolev_representative_of_mem (s : ℕ) (b : MiuraRealL2)
    (hb : Memℓp (fun n : ℤ => (Weight.sobolev (s : ℝ) n : ℂ)*b.val n) 2) :
    ∃ B : MiuraRealSobolevSource s, miuraPhysicalSobolevL2SourceInclusion s B = b := by
  obtain ⟨B,hB⟩ := WeightedCoeff.exists_physicalReal_weighted_coefficients (Weight.sobolev (s : ℝ)) 2 b hb
  exact ⟨B,miuraPhysicalSobolevL2SourceInclusion_eq_of_coefficients s B b hB⟩

/-- Every point of a joint action fiber of an H^s profile has a genuine
native H^s representative with exactly the same original coefficients. -/
theorem exists_miuraJointFiber_Sobolev_representative (s : ℕ) (a : MiuraRealSobolevSource s)
    (b : MiuraRealL2)
    (hI : miuraOriginalNLSActionSequence b.val =
      miuraOriginalNLSActionSequence (miuraPhysicalSobolevL2SourceInclusion s a).val) :
    ∃ B : MiuraRealSobolevSource s, miuraPhysicalSobolevL2SourceInclusion s B = b := by
  have ha0 : Memℓp (fun n : ℤ => (Weight.sobolev (s : ℝ) n : ℂ)*a.val.val n) 2 := a.val.property
  have ha : Memℓp (fun n : ℤ => (Weight.sobolev (s : ℝ) n : ℂ)*
      (miuraPhysicalSobolevL2SourceInclusion s a).val n) 2 := by
    simpa only [miuraPhysicalSobolevL2SourceInclusion_apply] using ha0
  have hb := (miuraSobolev_mem_iff_of_NLS_actions_eq b
    (miuraPhysicalSobolevL2SourceInclusion s a) hI (s : ℝ) (Nat.cast_nonneg s)).mpr ha
  exact exists_miuraSobolev_representative_of_mem s b hb

end NLS.MKdV
