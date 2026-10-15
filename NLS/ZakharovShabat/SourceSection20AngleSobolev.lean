import NLS.ZakharovShabat.SourceSection20MomentumBracket
import NLS.ZakharovShabat.SourceSobolevAngleVector

/-! # The original Section 20 angle vector on real H¹ sources

The proved momentum normalization supplies the complex germ needed for
H¹ recovery. The same explicit analytic vector retains the original
Fourier coefficients, is unique, and agrees with the finite-gap tangent.
No Sobolev tangent or constant-bracket premise is supplied by the caller.
-/
noncomputable section
open Set Filter Topology Complex NLS.Poisson
namespace NLS.ZakharovShabat.SourceSection20Data
variable {W₀ W V Wa B U : Set (CoeffPair 2)}
  {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
  (Q : SourceSection20Data D A B U)
include Q

/-- The explicit H¹ vector preserves exactly the original Hamiltonian coefficients. -/
theorem sobolevThetaVector_inclusion (a : realTypeSobolevSourceLocus) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a.val)) (periodOnePotential_mem _) n ≠ 0) :
    sobolevSourceInclusion (sourceSobolevThetaVector n s a.val) =
      sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n s
        (sobolevSourceInclusion a.val) :=
  D.previous.original_theta_common_domain.sobolevThetaVector_inclusion_of_momentum_germ n a.val
    (D.previous.original_theta_common_domain.real_subset a.property) hn
    (2*(Real.pi : ℂ)*n) (Q.sobolev_momentum_bracket_complex_germ a n hn)

/-- The constructed H¹ lift is unique among all vectors with the original coefficients. -/
theorem existsUnique_sobolevThetaVector (a : realTypeSobolevSourceLocus) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a.val)) (periodOnePotential_mem _) n ≠ 0) :
    ∃! v : ScalarDomain 2 × ScalarDomain 2, sobolevSourceInclusion v =
      sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n s
        (sobolevSourceInclusion a.val) :=
  ⟨sourceSobolevThetaVector n s a.val,Q.sobolevThetaVector_inclusion a n hn,
    fun _v hv => sobolevSourceInclusion_injective (hv.trans (Q.sobolevThetaVector_inclusion a n hn).symm)⟩

/-- The H¹ lift preserves the actual conjugate-pair real form. -/
theorem sobolevThetaVector_realType (a : realTypeSobolevSourceLocus) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a.val)) (periodOnePotential_mem _) n ≠ 0) :
    IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion (sourceSobolevThetaVector n s a.val))) := by
  rw [Q.sobolevThetaVector_inclusion a n hn]
  exact D.previous.original_theta_common_domain.thetaHamiltonian_realType le_rfl n
    ⟨sobolevSourceInclusion a.val,a.property⟩ hn

/-- The actual H¹ direction decreases the selected action at unit speed. -/
theorem sobolevThetaVector_action (a : realTypeSobolevSourceLocus) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a.val)) (periodOnePotential_mem _) n ≠ 0) (k : ℤ) :
    fderiv ℂ (sourceComplexAction (by simp) (by norm_num) k) (sobolevSourceInclusion a.val)
      (sobolevSourceInclusion (sourceSobolevThetaVector n s a.val)) = -(if n = k then 1 else 0) := by
  rw [Q.sobolevThetaVector_inclusion a n hn,sourceAngularThetaHamiltonianVector,
    apply_sourceHamiltonianDirection,sourceBivector_antisymm]
  exact congrArg Neg.neg (D.previous.original_theta_common_domain.thetaAction_eq_kronecker
    le_rfl n k ⟨sobolevSourceInclusion a.val,a.property⟩ hn)

/-- An open selected gap gives a nonzero H¹ angle vector. -/
theorem sobolevThetaVector_ne_zero (a : realTypeSobolevSourceLocus) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a.val)) (periodOnePotential_mem _) n ≠ 0) :
    sourceSobolevThetaVector n s a.val ≠ 0 := by
  intro hz
  have he := Q.sobolevThetaVector_action a n hn n
  simp only [hz,map_zero,ite_true] at he
  norm_num at he

/-- The analytic recovery agrees with the earlier actual finite-gap H¹ tangent. -/
theorem sobolevThetaVector_eq_finiteGap
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n ≠ 0) :
    sourceSobolevThetaVector n s (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf) =
      D.complex.finiteGapThetaSobolevVector D.previous.original_theta_common_domain φ hf n hn := by
  let a := sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf
  have hi : sobolevSourceInclusion a = φ.val := sobolevSourceInclusion_sourceFiniteGapSobolevPair φ hf
  let b : realTypeSobolevSourceLocus := ⟨a,by rw [hi]; exact φ.property⟩
  have hb := Q.sobolevThetaVector_inclusion b n (by simpa only [b,hi] using hn)
  apply sobolevSourceInclusion_injective
  rw [D.complex.finiteGapThetaSobolevVector_inclusion]
  simpa only [b,hi] using hb

/-- The recovered vector is analytic on the H¹ preimage of the original open-gap domain. -/
theorem analyticOnNhd_sobolevThetaVector (n : ℤ) :
    AnalyticOnNhd ℂ (sourceSobolevThetaVector n s)
      {a : ScalarDomain 2 × ScalarDomain 2 | sobolevSourceInclusion a ∈ U ∧
        canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (sobolevSourceInclusion a))
          (periodOnePotential_mem _) n ≠ 0} := by
  intro a ha
  exact analyticAt_sourceSobolevThetaVector D.previous.original_theta_common_domain n a
    (D.complex.source_subset (Q.original_subset ha.1)) ha.2

/-- Every real open-gap source has a complex H¹ neighborhood on which the
analytic recovery is the actual original angle vector. -/
theorem sobolevThetaVector_inclusion_complex_germ (a : realTypeSobolevSourceLocus) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a.val)) (periodOnePotential_mem _) n ≠ 0) :
    (fun b => sobolevSourceInclusion (sourceSobolevThetaVector n s b)) =ᶠ[𝓝 a.val]
      (fun b => sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n s
        (sobolevSourceInclusion b)) := by
  obtain ⟨T,hT,hreal,hsub,he⟩ := Q.exists_sobolev_momentum_domain n
  filter_upwards [hT.mem_nhds (hreal a hn)] with b hb
  apply D.previous.original_theta_common_domain.sobolevThetaVector_inclusion_of_momentum_germ n b
    (D.complex.source_subset (Q.original_subset (hsub hb).1)) (hsub hb).2 (2*(Real.pi : ℂ)*n)
  filter_upwards [hT.mem_nhds hb] with c hc
  exact he c hc

/-- The constructed real H¹ angle vector has the differentiated cotangent's exact spatial derivative. -/
theorem sobolevThetaVector_spatial (a : realTypeSobolevSourceLocus) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a.val)) (periodOnePotential_mem _) n ≠ 0) :
    sourceSobolevSpatialDerivative (sourceSobolevThetaVector n s a.val) =
      sourceHamiltonianDirection le_rfl
        (fderiv ℂ (sourceAngularThetaDifferential (by simp) (by norm_num) n s)
          (sobolevSourceInclusion a.val) (sourceSobolevSpatialDerivative a.val)) :=
  D.previous.original_theta_common_domain.sobolevThetaVector_spatial_of_momentum_germ n a.val
    (D.previous.original_theta_common_domain.real_subset a.property) hn
    (2*(Real.pi : ℂ)*n) (Q.sobolev_momentum_bracket_complex_germ a n hn)

/-- The actual H¹ angle vector does not depend on a choice of original auxiliary family. -/
theorem sobolevThetaVector_independent
    {W₀' W' V' Wa' B' U' : Set (CoeffPair 2)}
    {s' : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {D' : SourceSection17OriginalData (by simp) (by norm_num) W₀' W' V' s'}
    {A' : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa' s'}
    (Q' : SourceSection20Data D' A' B' U') (a : realTypeSobolevSourceLocus) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a.val)) (periodOnePotential_mem _) n ≠ 0) :
    sourceSobolevThetaVector n s a.val = sourceSobolevThetaVector n s' a.val := by
  apply sobolevSourceInclusion_injective
  rw [Q.sobolevThetaVector_inclusion a n hn,Q'.sobolevThetaVector_inclusion a n hn]
  exact (D.complex.hilbertActionReductionVector_eq_thetaHamiltonian
    D.previous.original_theta_common_domain n ⟨sobolevSourceInclusion a.val,a.property⟩ hn).symm.trans
    (D.complex.hilbertActionReductionVector_eq_thetaHamiltonian
      D'.previous.original_theta_common_domain n ⟨sobolevSourceInclusion a.val,a.property⟩ hn)

end NLS.ZakharovShabat.SourceSection20Data
