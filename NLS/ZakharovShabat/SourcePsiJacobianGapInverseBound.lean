import NLS.ZakharovShabat.SourcePsiJacobianGapUniformLimit
import NLS.ZakharovShabat.SourcePsiJacobianGapOperator

/-!
# A common inverse bound for every finite psi Jacobian

Uniform norm convergence on the gap product compares all distant
Jacobians to the uniformly invertible limit. Each remaining index has
a continuous invertible family on the compact gap product. Together
these give one inverse bound for every index and every gap-root vector
at the fixed real-type potential, including the original deleted blocks.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourcePsiGapJacobianEquiv
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hfamily : sourcePsiRealCenteredContourFamily hp hp1 φ c R)
    (n : ℤ) (a : sourcePeriodicGapRootSet hp hp1 φ) : Coeff p ≃L[ℂ] Coeff p :=
  ContinuousLinearEquiv.ofBijective
    (sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a.val) φ)
    (LinearMap.ker_eq_bot.mpr
      (sourcePsiFullRootJacobian_bijective_on_gapProduct hp hp1 φ hφ c R hfamily n a).1)
    (LinearMap.range_eq_top.mpr
      (sourcePsiFullRootJacobian_bijective_on_gapProduct hp hp1 φ hφ c R hfamily n a).2)

def sourcePsiGapJacobianInverse
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hfamily : sourcePsiRealCenteredContourFamily hp hp1 φ c R)
    (n : ℤ) (a : sourcePeriodicGapRootSet hp hp1 φ) : Coeff p →L[ℂ] Coeff p :=
  (sourcePsiGapJacobianEquiv hp hp1 φ hφ c R hfamily n a).symm.toContinuousLinearMap

theorem sourcePsiFullRootJacobian_comp_gapInverse
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hfamily : sourcePsiRealCenteredContourFamily hp hp1 φ c R)
    (n : ℤ) (a : sourcePeriodicGapRootSet hp hp1 φ) :
    (sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a.val) φ).comp
      (sourcePsiGapJacobianInverse hp hp1 φ hφ c R hfamily n a) =
        ContinuousLinearMap.id ℂ (Coeff p) := by
  apply ContinuousLinearMap.ext
  intro x
  exact (sourcePsiGapJacobianEquiv hp hp1 φ hφ c R hfamily n a).apply_symm_apply x

theorem sourcePsiGapJacobianInverse_comp_fullRootJacobian
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hfamily : sourcePsiRealCenteredContourFamily hp hp1 φ c R)
    (n : ℤ) (a : sourcePeriodicGapRootSet hp hp1 φ) :
    (sourcePsiGapJacobianInverse hp hp1 φ hφ c R hfamily n a).comp
      (sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a.val) φ) =
        ContinuousLinearMap.id ℂ (Coeff p) := by
  apply ContinuousLinearMap.ext
  intro x
  exact (sourcePsiGapJacobianEquiv hp hp1 φ hφ c R hfamily n a).symm_apply_apply x

/-- One constant bounds all full Jacobian inverses at every signed
deleted index and every full gap-contained root vector. -/
theorem exists_uniform_sourcePsiGapJacobianInverse_norm
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hfamily : sourcePsiRealCenteredContourFamily hp hp1 φ c R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℤ, ∀ a : sourcePeriodicGapRootSet hp hp1 φ,
      ‖sourcePsiGapJacobianInverse hp hp1 φ hφ c R hfamily n a‖ ≤ M := by
  classical
  obtain ⟨Mstar,hMstar,hstar⟩ := exists_uniform_sourcePsiGapLimitInverse_norm hp hp1 φ hφ
  let ε : ℝ := 1/(2*(Mstar+1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨K,hK⟩ := exists_threshold_sourcePsiFullRootJacobian_gapUniform_small hp hp1 φ hφ c R hfamily ε hε
  have htail (n : ℤ) (hn : K ≤ n.natAbs) (a : sourcePeriodicGapRootSet hp hp1 φ) :
      ‖sourcePsiGapJacobianInverse hp hp1 φ hφ c R hfamily n a‖ ≤ 2*Mstar := by
    have hdiff : ‖sourcePsiGapLimitOperator hp hp1 φ hφ a -
        sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a.val) φ‖ ≤ ε := by
      simpa only [norm_sub_rev] using le_of_lt (hK n hn a)
    have hnear : ‖sourcePsiGapLimitInverse hp hp1 φ hφ a‖ *
        ‖sourcePsiGapLimitOperator hp hp1 φ hφ a -
          sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a.val) φ‖ ≤ (1/2:ℝ) := by
      calc
        _ ≤ Mstar*ε := mul_le_mul (hstar a) hdiff (norm_nonneg _) hMstar
        _ ≤ (Mstar+1)*ε := by gcongr; linarith
        _ = 1/2 := by
          dsimp [ε]
          have hne : Mstar+1 ≠ 0 := by positivity
          field_simp [hne]
    have hbound := NLS.inverse_norm_le_two_mul_of_near
      (sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a.val) φ)
      (sourcePsiGapLimitOperator hp hp1 φ hφ a)
      (sourcePsiGapJacobianInverse hp hp1 φ hφ c R hfamily n a)
      (sourcePsiGapLimitInverse hp hp1 φ hφ a)
      (sourcePsiFullRootJacobian_comp_gapInverse hp hp1 φ hφ c R hfamily n a)
      (sourcePsiGapLimitInverse_comp_operator hp hp1 φ hφ a) hnear
    exact hbound.trans (mul_le_mul_of_nonneg_left (hstar a) (by norm_num))
  have hhead (n : ℤ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ a : sourcePeriodicGapRootSet hp hp1 φ,
      ‖sourcePsiGapJacobianInverse hp hp1 φ hφ c R hfamily n a‖ ≤ B := by
    exact NLS.exists_uniform_inverse_norm_on_compact
      (sourcePeriodicGapRootSet hp hp1 φ) (isCompact_sourcePeriodicGapRootSet hp hp1 φ)
      (fun a => sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a.val) φ)
      (sourcePsiGapJacobianInverse hp hp1 φ hφ c R hfamily n)
      ((continuous_sourcePsiFullRootJacobian_on_realCentered_family hp hp1 φ hφ c R hfamily n).comp
        continuous_subtype_val)
      (sourcePsiFullRootJacobian_comp_gapInverse hp hp1 φ hφ c R hfamily n)
      (sourcePsiGapJacobianInverse_comp_fullRootJacobian hp hp1 φ hφ c R hfamily n)
  choose B hB0 hB using hhead
  let s : Finset ℤ := Finset.Icc (-(K:ℤ)) (K:ℤ)
  let H : ℝ := ∑ n ∈ s, B n
  refine ⟨max H (2*Mstar),le_max_of_le_right (by positivity),?_⟩
  intro n a
  by_cases hn : K ≤ n.natAbs
  · exact (htail n hn a).trans (le_max_right _ _)
  · have hnabs : |n| ≤ (K:ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hn))
    have hns : n ∈ s := by simpa only [s,Finset.mem_Icc] using abs_le.mp hnabs
    have hnH : B n ≤ H := Finset.single_le_sum (fun k _ => hB0 k) hns
    exact (hB n a).trans (hnH.trans (le_max_left _ _))

/-- The same common bound controls genuine two-sided inverses of
the original deleted Jacobian blocks, uniformly in roots and index. -/
theorem exists_uniform_sourcePsiSelectedRootJacobian_gapInverse_norm
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hfamily : sourcePsiRealCenteredContourFamily hp hp1 φ c R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℤ, ∀ a : sourcePeriodicGapRootSet hp hp1 φ,
      ∃ S : DeletedCoeff p n →L[ℂ] DeletedCoeff p n,
        (sourcePsiSelectedRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a.val) φ).comp S =
          ContinuousLinearMap.id ℂ (DeletedCoeff p n) ∧
        S.comp (sourcePsiSelectedRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a.val) φ) =
          ContinuousLinearMap.id ℂ (DeletedCoeff p n) ∧ ‖S‖ ≤ M := by
  obtain ⟨M,hM,hbound⟩ := exists_uniform_sourcePsiGapJacobianInverse_norm hp hp1 φ hφ c R hfamily
  refine ⟨M,hM,?_⟩
  intro n a
  let Q := sourcePsiSelectedRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a.val) φ
  have hbij := (sourcePsiFullRootJacobian_bijective_iff hp hp1 n c R (Coeff.deleteCoordinateTo n a.val) φ).mp
    (sourcePsiFullRootJacobian_bijective_on_gapProduct hp hp1 φ hφ c R hfamily n a)
  let e := ContinuousLinearEquiv.ofBijective Q (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  let S := e.symm.toContinuousLinearMap
  have hQS : Q.comp S = ContinuousLinearMap.id ℂ (DeletedCoeff p n) := by
    apply ContinuousLinearMap.ext
    intro x
    exact e.apply_symm_apply x
  have hSQ : S.comp Q = ContinuousLinearMap.id ℂ (DeletedCoeff p n) := by
    apply ContinuousLinearMap.ext
    intro x
    exact e.symm_apply_apply x
  have heq : Coeff.deletedOperatorExtension n (1/2:ℂ) S =
      sourcePsiGapJacobianInverse hp hp1 φ hφ c R hfamily n a := by
    apply ContinuousLinearMap.ext
    intro x
    apply (sourcePsiFullRootJacobian_bijective_on_gapProduct hp hp1 φ hφ c R hfamily n a).1
    have hleft := congrArg (fun A : Coeff p →L[ℂ] Coeff p => A x)
      (Coeff.deletedJacobianExtension_inverse_comp n Q S hQS)
    have hright := congrArg (fun A : Coeff p →L[ℂ] Coeff p => A x)
      (sourcePsiFullRootJacobian_comp_gapInverse hp hp1 φ hφ c R hfamily n a)
    exact hleft.trans hright.symm
  refine ⟨S,hQS,hSQ,?_⟩
  calc
    ‖S‖ ≤ ‖Coeff.deletedOperatorExtension n (1/2:ℂ) S‖ := Coeff.norm_deletedOperator_le_norm_extension n _ S
    _ ≤ M := by rw [heq]; exact hbound n a

end NLS.ZakharovShabat
