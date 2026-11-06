import NLS.MKdV.MiuraJointFiberNLSCoordinates

/-! # Physical actions and the squared mean on a full original NLS action fiber -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraRealL2_isospectral_of_NLS_actions_eq (a b : MiuraRealL2)
    (hI : miuraOriginalNLSActionSequence a.val = miuraOriginalNLSActionSequence b.val) :
    miuraRealDiagonalL2Source b ∈ sourceIsospectralSet (by simp) (miuraRealDiagonalL2Source a) := by
  rw [sourceIsospectralSet_eq_actionLevelSet_all_exponents (by simp) (by norm_num)]
  exact fun k => (miuraNLS_action_re_eq_of_sequence_eq a b hI k).symm

/-- The whole native physical action sequence is fixed by all original
NLS actions, globally on physical original L2. -/
theorem miuraL2ActionSequence_eq_of_NLS_actions_eq (a b : MiuraRealL2)
    (hI : miuraOriginalNLSActionSequence a.val = miuraOriginalNLSActionSequence b.val) :
    miuraL2ActionSequence a.val = miuraL2ActionSequence b.val := by
  let φ : realDiagonalSourceLocus 2 := ⟨scalarL2Diagonal a.val,scalarL2Diagonal_realDiagonal a.val a.property⟩
  let ψ : realDiagonalSourceLocus 2 := ⟨scalarL2Diagonal b.val,scalarL2Diagonal_realDiagonal b.val b.property⟩
  obtain ⟨U,_,hreal,_,hcoord⟩ := exists_miuraL2ActionSequence_domain
  apply Subtype.ext
  funext n
  by_cases hn : 0 < n
  · have hi : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.le
    have hnat : 1 ≤ n.toNat := by omega
    rw [← hi,hcoord _ (hreal a.property) n.toNat hnat,hcoord _ (hreal b.property) n.toNat hnat]
    unfold miuraL2Action
    exact congrArg (fun r : ℂ => (1/2 : ℂ)*r)
      (sourceDiagonalLaurentAction_eq_of_isospectral (by simp) (by norm_num) φ ψ
        (miuraRealL2_isospectral_of_NLS_actions_eq a b hI) n.toNat 0 (by omega)).symm
  · rw [miuraL2ActionSequence_nonpositive a.val n hn,miuraL2ActionSequence_nonpositive b.val n hn]

/-- Equal original NLS actions fix the actual squared signed mean on the
entire physical real L2 diagonal. No sign branch is selected. -/
theorem miuraMean_square_eq_of_NLS_actions_eq (a b : MiuraRealL2)
    (hI : miuraOriginalNLSActionSequence a.val = miuraOriginalNLSActionSequence b.val) :
    (b.val 0)^2 = (a.val 0)^2 := by
  have hD := (mem_sourceIsospectralSet_iff_discriminant_eq (by simp) (by norm_num)
    (miuraRealDiagonalL2Source a) (miuraRealDiagonalL2Source b)).mp
      (miuraRealL2_isospectral_of_NLS_actions_eq a b hI)
  have h := congrArg (fun f : ℂ → ℂ => f 0) hD
  change canonicalDiscriminant (by simp) (periodOnePotential (scalarL2Diagonal b.val)) 0 =
    canonicalDiscriminant (by simp) (periodOnePotential (scalarL2Diagonal a.val)) 0 at h
  rw [canonicalDiscriminant_scalarL2_zero,canonicalDiscriminant_scalarL2_zero] at h
  have har : a.val 0 = ((a.val 0).re : ℂ) := by
    apply Complex.ext
    · rfl
    · have he := congrArg Complex.im (a.property 0)
      simp only [neg_zero,Complex.conj_im,Complex.ofReal_im] at *
      linarith
  have hbr : b.val 0 = ((b.val 0).re : ℂ) := by
    apply Complex.ext
    · rfl
    · have he := congrArg Complex.im (b.property 0)
      simp only [neg_zero,Complex.conj_im,Complex.ofReal_im] at *
      linarith
  have hc := mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h
  rw [har,hbr] at hc
  have hreal : Real.cosh (b.val 0).re = Real.cosh (a.val 0).re := by
    simpa only [← Complex.ofReal_cosh,Complex.ofReal_re] using congrArg Complex.re hc
  have habs : |(b.val 0).re| = |(a.val 0).re| := by
    have he := congrArg Real.arcosh
      (show Real.cosh |(b.val 0).re| = Real.cosh |(a.val 0).re| by simpa only [Real.cosh_abs] using hreal)
    simpa only [Real.arcosh_cosh (abs_nonneg _)] using he
  have hsq : (b.val 0).re^2 = (a.val 0).re^2 := by
    have he := congrArg (fun r : ℝ => r^2) habs
    change |(b.val 0).re|^2 = |(a.val 0).re|^2 at he
    simpa only [sq_abs] using he
  rw [har,hbr,← Complex.ofReal_pow,← Complex.ofReal_pow,hsq]

theorem miuraMean_zero_of_NLS_actions_eq (a b : MiuraRealL2) (hm : a.val 0 = 0)
    (hI : miuraOriginalNLSActionSequence a.val = miuraOriginalNLSActionSequence b.val) : b.val 0 = 0 := by
  have h := miuraMean_square_eq_of_NLS_actions_eq a b hI
  rw [hm,zero_pow (by norm_num : 2 ≠ 0)] at h
  exact sq_eq_zero_iff.mp h

/-- At zero mean, the joint fiber is exactly the full physical diagonal
fiber of the entire original signed NLS action sequence. -/
theorem miuraJointActionFiber_eq_NLSActionFiber_of_mean_zero (a : MiuraRealL2) (hm : a.val 0 = 0) :
    miuraJointActionFiber a = {b | miuraOriginalNLSActionSequence b.val = miuraOriginalNLSActionSequence a.val} := by
  ext b
  constructor
  · exact fun hb => hb.2
  · intro hb
    refine ⟨?_,hb⟩
    apply Prod.ext
    · exact miuraL2ActionSequence_eq_of_NLS_actions_eq b a hb
    · exact (miuraMean_zero_of_NLS_actions_eq a b hm hb.symm).trans hm.symm

end NLS.MKdV
