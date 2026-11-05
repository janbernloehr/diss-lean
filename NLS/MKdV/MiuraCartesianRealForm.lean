import NLS.MKdV.MiuraPositiveCartesianProperness
import NLS.SequenceSpaces.PhysicalRealUnweightedProjection

/-! # The physical real Cartesian target and its free Fourier equivalence -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

instance miuraPositiveHalfNormedSpaceReal : NormedSpace ℝ MiuraPositiveHalf :=
  NormedSpace.restrictScalars ℝ ℂ MiuraPositiveHalf

def miuraCartesianRealSubmodule : Submodule ℝ MiuraPositiveCartesianTarget where
  carrier := {z | (∀ n, (z.1.1.val.val n).im = 0 ∧ (z.1.2.val.val n).im = 0) ∧ z.2.im = 0}
  zero_mem' := by exact ⟨fun _ => ⟨rfl,rfl⟩,rfl⟩
  add_mem' := by
    rintro a b ⟨ha,ha0⟩ ⟨hb,hb0⟩
    exact ⟨fun n => ⟨by change (a.1.1.val.val n+b.1.1.val.val n).im = 0; simp [ha n,hb n],
      by change (a.1.2.val.val n+b.1.2.val.val n).im = 0; simp [ha n,hb n]⟩,
      by change (a.2+b.2).im = 0; simp [ha0,hb0]⟩
  smul_mem' := by
    rintro r a ⟨ha,ha0⟩
    exact ⟨fun n => ⟨by change ((r : ℂ)*a.1.1.val.val n).im = 0; simp [Complex.mul_im,(ha n).1],
      by change ((r : ℂ)*a.1.2.val.val n).im = 0; simp [Complex.mul_im,(ha n).2]⟩,
      by change ((r : ℂ)*a.2).im = 0; simp [Complex.mul_im,ha0]⟩

abbrev MiuraRealCartesianTarget := ↥miuraCartesianRealSubmodule

instance miuraRealCartesianTargetNormedSpace : NormedSpace ℝ MiuraRealCartesianTarget :=
  miuraCartesianRealSubmodule.normedSpace

theorem isClosed_miuraCartesianRealSubmodule :
    IsClosed (miuraCartesianRealSubmodule : Set MiuraPositiveCartesianTarget) := by
  have hx (n : ℤ) : Continuous (fun z : MiuraPositiveCartesianTarget => (z.1.1.val.val n).im) :=
    Complex.continuous_im.comp (continuous_fst.comp (miuraPositiveCartesianEval n).continuous)
  have hy (n : ℤ) : Continuous (fun z : MiuraPositiveCartesianTarget => (z.1.2.val.val n).im) :=
    Complex.continuous_im.comp (continuous_snd.comp (miuraPositiveCartesianEval n).continuous)
  have he : (miuraCartesianRealSubmodule : Set MiuraPositiveCartesianTarget) =
      (⋂ n : ℤ, {z | (z.1.1.val.val n).im = 0 ∧ (z.1.2.val.val n).im = 0}) ∩ {z | z.2.im = 0} := by
    ext z
    simp only [mem_inter_iff,mem_iInter,mem_ofPred_eq]
    rfl
  rw [he]
  exact (isClosed_iInter (fun n => (isClosed_eq (hx n) continuous_const).inter
    (isClosed_eq (hy n) continuous_const))).inter
      (isClosed_eq (Complex.continuous_im.comp continuous_snd) continuous_const)

instance miuraRealCartesianTargetComplete : CompleteSpace MiuraRealCartesianTarget :=
  isClosed_miuraCartesianRealSubmodule.completeSpace_coe

private theorem conj_eq_of_im_zero {z : ℂ} (h : z.im = 0) : conj z = z := by
  apply Complex.ext <;> simp [h]

private theorem im_zero_of_conj_eq {z : ℂ} (h : conj z = z) : z.im = 0 := by
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  linarith

theorem miuraCartesianFreeJacobian_physicalReal (a : Coeff.physicalRealSubmodule 2) :
    miuraCartesianFreeJacobian a.val ∈ miuraCartesianRealSubmodule := by
  constructor
  · intro n
    by_cases hn : 0 < n
    · have he := miuraCartesianFreeJacobian_signed n hn a.val
      have hx := congrArg Prod.fst he
      have hy := congrArg Prod.snd he
      change (miuraCartesianFreeJacobian a.val).1.1.val.val n = _ at hx
      change (miuraCartesianFreeJacobian a.val).1.2.val.val n = _ at hy
      rw [hx,hy,sourceDiagonalActionRoot_zero (by simp) (by norm_num) n hn]
      have hneg : conj (a.val (-n)) = a.val n := (a.property n).symm
      have hpos : conj (a.val n) = a.val (-n) := by simpa using (a.property (-n)).symm
      constructor <;> apply im_zero_of_conj_eq
      · simp only [map_mul,map_div₀,map_neg,map_add,Complex.conj_ofReal,hneg,hpos]
        ring
      · simp only [map_mul,map_div₀,map_neg,map_sub,Complex.conj_ofReal,Complex.conj_I,hneg,hpos]
        ring
    · have hx := (miuraCartesianFreeJacobian a.val).1.1.property n (by omega)
      have hy := (miuraCartesianFreeJacobian a.val).1.2.property n (by omega)
      exact ⟨by rw [hx]; rfl,by rw [hy]; rfl⟩
  · rw [miuraCartesianFreeJacobian_mean]
    apply im_zero_of_conj_eq
    simpa using (a.property 0).symm

theorem miuraFreeInverseSymbol_conj (n : ℤ) : conj (miuraFreeInverseSymbol n) = miuraFreeInverseSymbol n := by
  let φ : realDiagonalSourceLocus 2 := ⟨0,⟨by intro j; simp,by rfl⟩⟩
  have he := sourceDiagonalActionRootInverseSequence_apply φ n
  change miuraFreeInverseSymbol n = _ at he
  rw [he]
  split_ifs with hn
  · rw [sourceDiagonalActionRoot_zero (by simp) (by norm_num) n hn]
    simp
  · simp

theorem miuraCartesianFreeInverse_physicalReal (z : MiuraRealCartesianTarget) :
    miuraCartesianFreeInverse z.val ∈ Coeff.physicalRealSubmodule 2 := by
  have hp (n : ℤ) (hn : 0 < n) :
      miuraCartesianFreeInverse z.val n = conj (miuraCartesianFreeInverse z.val (-n)) := by
    rw [miuraCartesianFreeInverse_positive _ n hn,miuraCartesianFreeInverse_negative _ n hn]
    simp only [map_div₀,map_mul,map_sub,map_neg,Complex.conj_I,Complex.conj_ofReal,
      miuraFreeInverseSymbol_conj,conj_eq_of_im_zero (z.property.1 n).1,
      conj_eq_of_im_zero (z.property.1 n).2]
    ring
  intro n
  by_cases hz : n = 0
  · subst n
    simp only [neg_zero,miuraCartesianFreeInverse_mean]
    exact (conj_eq_of_im_zero z.property.2).symm
  · by_cases hn : 0 < n
    · exact hp n hn
    · have he := congrArg conj (hp (-n) (by omega))
      simpa only [neg_neg,Complex.conj_conj] using he.symm

def miuraCartesianRealProjection : MiuraPositiveCartesianTarget →L[ℝ] MiuraRealCartesianTarget :=
  ((miuraCartesianFreeJacobian.restrictScalars ℝ).comp
    ((Coeff.physicalRealSubmodule 2).subtypeL.comp
      ((Coeff.physicalRealPart 2).comp (miuraCartesianFreeInverse.restrictScalars ℝ)))).codRestrict
    miuraCartesianRealSubmodule (fun _ => miuraCartesianFreeJacobian_physicalReal _)

theorem miuraCartesianRealProjection_real (z : MiuraRealCartesianTarget) :
    miuraCartesianRealProjection z.val = z := by
  apply Subtype.ext
  change miuraCartesianFreeJacobian ((Coeff.physicalRealPart 2 (miuraCartesianFreeInverse z.val)).val) = z.val
  have hr := Coeff.physicalRealPart_real 2 ⟨miuraCartesianFreeInverse z.val,miuraCartesianFreeInverse_physicalReal z⟩
  rw [hr]
  exact miuraCartesianFreeJacobian_inverse z.val

end NLS.MKdV
