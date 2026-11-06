import NLS.SequenceSpaces.PositiveReindex
import NLS.SequenceSpaces.DeletedRealConjugation
import NLS.SequenceSpaces.RealFormIdentity

/-! # Normalized complex Hilbert pairs for the real deleted signed target -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS

def signedPairToCoeff (e : ℤ ≃ ℕ+) : (Coeff 2 × Coeff 2) →L[ℂ] Coeff 2 :=
  (Real.sqrt 2 : ℂ)⁻¹ •
    (((positiveReindexIsometry e).toContinuousLinearMap.comp
      (ContinuousLinearMap.fst ℂ (Coeff 2) (Coeff 2)-I • ContinuousLinearMap.snd ℂ (Coeff 2) (Coeff 2)))+
      (Coeff.reflection (p := 2)).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((positiveReindexIsometry e).toContinuousLinearMap.comp
          (ContinuousLinearMap.fst ℂ (Coeff 2) (Coeff 2)+I • ContinuousLinearMap.snd ℂ (Coeff 2) (Coeff 2))))

theorem signedPairToCoeff_apply (e : ℤ ≃ ℕ+) (z : Coeff 2 × Coeff 2) (j : ℤ) :
    signedPairToCoeff e z j = (Real.sqrt 2 : ℂ)⁻¹*
      (positiveReindexFunction e (z.1-I • z.2) j+
        positiveReindexFunction e (z.1+I • z.2) (-j)) := rfl

theorem signedPairToCoeff_zero (e : ℤ ≃ ℕ+) (z : Coeff 2 × Coeff 2) :
    signedPairToCoeff e z 0 = 0 := by
  simp [signedPairToCoeff_apply,positiveReindexFunction]

def signedPairToDeleted (e : ℤ ≃ ℕ+) : (Coeff 2 × Coeff 2) →L[ℂ] DeletedCoeff 2 0 :=
  (signedPairToCoeff e).codRestrict _ (signedPairToCoeff_zero e)

theorem signedPairToDeleted_positive (e : ℤ ≃ ℕ+) (z : Coeff 2 × Coeff 2) (k : ℤ) :
    (signedPairToDeleted e z).val (positiveIndexInjection e k) =
      (z.1 k-I*z.2 k)/(Real.sqrt 2 : ℂ) := by
  have hp : (0 : ℤ) < positiveIndexInjection e k := by
    dsimp only [positiveIndexInjection]; exact_mod_cast (e k).pos
  change signedPairToCoeff e z (positiveIndexInjection e k) = _
  rw [signedPairToCoeff_apply,positiveReindexFunction_index]
  simp only [positiveReindexFunction,dif_neg (by omega : ¬0 < -positiveIndexInjection e k),
    lp.coeFn_sub,Pi.sub_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,add_zero]
  exact (div_eq_inv_mul _ _).symm

theorem signedPairToDeleted_negative (e : ℤ ≃ ℕ+) (z : Coeff 2 × Coeff 2) (k : ℤ) :
    (signedPairToDeleted e z).val (-positiveIndexInjection e k) =
      (z.1 k+I*z.2 k)/(Real.sqrt 2 : ℂ) := by
  have hp : (0 : ℤ) < positiveIndexInjection e k := by
    dsimp only [positiveIndexInjection]; exact_mod_cast (e k).pos
  change signedPairToCoeff e z (-positiveIndexInjection e k) = _
  rw [signedPairToCoeff_apply,neg_neg,positiveReindexFunction_index]
  simp only [positiveReindexFunction,dif_neg (by omega : ¬0 < -positiveIndexInjection e k),
    lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,zero_add]
  exact (div_eq_inv_mul _ _).symm

def deletedToSignedPair (e : ℤ ≃ ℕ+) : DeletedCoeff 2 0 →L[ℂ] (Coeff 2 × Coeff 2) :=
  let V := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).ker.subtypeL
  let C := (positiveReindexPullCLM e).comp V
  let D := (positiveReindexPullCLM e).comp ((Coeff.reflection (p := 2)).toContinuousLinearEquiv.toContinuousLinearMap.comp V)
  (((Real.sqrt 2 : ℂ)⁻¹ • (C+D)).prod ((I/(Real.sqrt 2 : ℂ)) • (C-D)))

theorem deletedToSignedPair_apply (e : ℤ ≃ ℕ+) (b : DeletedCoeff 2 0) (k : ℤ) :
    (deletedToSignedPair e b).1 k =
      (b.val (positiveIndexInjection e k)+b.val (-positiveIndexInjection e k))/(Real.sqrt 2 : ℂ) ∧
    (deletedToSignedPair e b).2 k =
      I*(b.val (positiveIndexInjection e k)-b.val (-positiveIndexInjection e k))/(Real.sqrt 2 : ℂ) := by
  constructor
  · change (Real.sqrt 2 : ℂ)⁻¹*
      (b.val (positiveIndexInjection e k)+b.val (-positiveIndexInjection e k)) = _
    exact (div_eq_inv_mul _ _).symm
  · change (I/(Real.sqrt 2 : ℂ))*
      (b.val (positiveIndexInjection e k)-b.val (-positiveIndexInjection e k)) = _
    ring

theorem signedPairToDeleted_apply_inverse (e : ℤ ≃ ℕ+) (b : DeletedCoeff 2 0) :
    signedPairToDeleted e (deletedToSignedPair e b) = b := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  apply Subtype.ext
  ext j
  by_cases hj : j = 0
  · subst j
    exact (signedPairToDeleted e _).property.trans b.property.symm
  · have hi : ∃ k, j = positiveIndexInjection e k ∨ j = -positiveIndexInjection e k := by
      by_cases hp : 0 < j
      · refine ⟨e.symm ⟨j.toNat,by omega⟩,Or.inl ?_⟩
        change j = ((e (e.symm ⟨j.toNat,by omega⟩) : ℕ) : ℤ)
        have he := e.apply_symm_apply (⟨j.toNat,by omega⟩ : ℕ+)
        exact ((congrArg (fun n : ℕ+ => ((n : ℕ) : ℤ)) he).trans (Int.toNat_of_nonneg hp.le)).symm
      · refine ⟨e.symm ⟨(-j).toNat,by omega⟩,Or.inr ?_⟩
        change j = -((e (e.symm ⟨(-j).toNat,by omega⟩) : ℕ) : ℤ)
        have he := e.apply_symm_apply (⟨(-j).toNat,by omega⟩ : ℕ+)
        have hh := (congrArg (fun n : ℕ+ => ((n : ℕ) : ℤ)) he).trans
          (Int.toNat_of_nonneg (by omega : 0 ≤ -j))
        omega
    obtain ⟨k,hk|hk⟩ := hi
    · subst j
      rw [signedPairToDeleted_positive,(deletedToSignedPair_apply e b k).1,
        (deletedToSignedPair_apply e b k).2]
      field_simp [hne]
      simp only [I_sq]
      linear_combination -(b.val (positiveIndexInjection e k))*hs
    · subst j
      rw [signedPairToDeleted_negative,(deletedToSignedPair_apply e b k).1,
        (deletedToSignedPair_apply e b k).2]
      field_simp [hne]
      simp only [I_sq]
      linear_combination -(b.val (-positiveIndexInjection e k))*hs

theorem signedPairToDeleted_real (e : ℤ ≃ ℕ+) (z : Coeff 2 × Coeff 2)
    (hz : z ∈ Coeff.realPairLocus 2) :
    deletedL2Conjugation (signedPairToDeleted e z) = signedPairToDeleted e z := by
  have hx (k : ℤ) : conj (z.1 k) = z.1 k := Complex.conj_eq_iff_im.mpr (hz.1 k)
  have hy (k : ℤ) : conj (z.2 k) = z.2 k := Complex.conj_eq_iff_im.mpr (hz.2 k)
  have hP (j : ℤ) : conj (positiveReindexFunction e (z.1-I • z.2) j) =
      positiveReindexFunction e (z.1+I • z.2) j := by
    unfold positiveReindexFunction
    split_ifs
    · simp only [lp.coeFn_sub,Pi.sub_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
        map_sub,map_mul,hx,hy,Complex.conj_I,lp.coeFn_add,Pi.add_apply]
      ring
    · exact map_zero _
  have hP' (j : ℤ) : conj (positiveReindexFunction e (z.1+I • z.2) j) =
      positiveReindexFunction e (z.1-I • z.2) j := by
    have h := congrArg conj (hP j)
    simpa only [conj_conj] using h.symm
  apply (deletedL2Conjugation_fixed_iff _).mpr
  apply (periodOneL2Conjugation_fixed_iff _).mpr
  intro j
  change signedPairToCoeff e z (-j) = conj (signedPairToCoeff e z j)
  rw [signedPairToCoeff_apply,signedPairToCoeff_apply,neg_neg,map_mul,map_add,
    Complex.conj_inv,Complex.conj_ofReal,hP,hP']
  ring

theorem deletedToSignedPair_real (e : ℤ ≃ ℕ+) (b : DeletedCoeff 2 0)
    (hb : deletedL2Conjugation b = b) : deletedToSignedPair e b ∈ Coeff.realPairLocus 2 := by
  have hr := (periodOneL2Conjugation_fixed_iff b.val).mp ((deletedL2Conjugation_fixed_iff b).mp hb)
  constructor
  · intro k
    rw [(deletedToSignedPair_apply e b k).1,hr (positiveIndexInjection e k)]
    simp [Complex.div_im]
  · intro k
    rw [(deletedToSignedPair_apply e b k).2,hr (positiveIndexInjection e k)]
    simp [Complex.div_im,Complex.mul_im,Complex.mul_re]

theorem norm_signedPairToDeleted_positive_sq (e : ℤ ≃ ℕ+) (z : Coeff 2 × Coeff 2)
    (hz : z ∈ Coeff.realPairLocus 2) (k : ℤ) :
    ‖(signedPairToDeleted e z).val (positiveIndexInjection e k)‖^2 =
      ((z.1 k).re^2+(z.2 k).re^2)/2 := by
  rw [signedPairToDeleted_positive,norm_div,div_pow,norm_real,Real.norm_eq_abs,sq_abs,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),Complex.sq_norm,Complex.normSq_apply]
  simp only [sub_re,sub_im,mul_re,mul_im,I_re,I_im,zero_mul,one_mul,
    hz.1 k,hz.2 k,sub_zero,zero_sub]
  ring

end NLS
