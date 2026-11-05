import NLS.MKdV.MiuraFiniteActionProjection

/-! # Reality of the actual finite physical action projection and its derivative

The functions agree with the independent physical real actions on every
real H1 input. Differentiating their imaginary part along real H1 lines
proves that their actual complex derivatives preserve the real form.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem finiteActionCoordinates_real_values (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (S : Finset (MiuraOpenActionIndex a ha))
    (b : ScalarDomain 2) (hb : ∀ j, b.val j = conj (b.val (-j))) (i : Option S) :
    (miuraFiniteActionCoordinates a ha S b i).im = 0 := by
  cases i with
  | none =>
    have h := congrArg Complex.im (hb 0)
    simp only [neg_zero,Complex.conj_im] at h
    change (b.val 0).im = 0
    linarith
  | some n =>
    change (miuraL2Action n.val.val (scalarInclusion b)).im = 0
    rw [miuraL2Action_eq_physical b hb n.val.val n.val.property.1]
    exact (miuraMKdVAction_nonnegative_and_zero_iff b hb n.val.val n.val.property.1).2.1

theorem finiteActionRows_real_variations (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (S : Finset (MiuraOpenActionIndex a ha))
    (h : ScalarDomain 2) (hh : ∀ j, h.val j = conj (h.val (-j))) (i : Option S) :
    (miuraFiniteActionRows a ha S i h).im = 0 := by
  let γ : ℝ → ScalarDomain 2 := fun t => a+(t : ℂ) • h
  have hγ (t : ℝ) (j : ℤ) : (γ t).val j = conj ((γ t).val (-j)) := by
    change a.val j+(t : ℂ)*h.val j = conj (a.val (-j)+(t : ℂ)*h.val (-j))
    rw [map_add,map_mul,Complex.conj_ofReal,ha j,hh j]
  have hdγ : HasDerivAt γ h 0 := by
    have hc : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) 0 := by
      simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one] using
        (show HasDerivAt (fun t : ℝ => Complex.ofRealCLM t) (Complex.ofRealCLM 1) 0 from Complex.ofRealCLM.hasDerivAt)
    simpa only [one_smul] using hc.smul_const h |>.const_add a
  have hdF := ((ContinuousLinearMap.proj i : (Option S → ℂ) →L[ℂ] ℂ).hasFDerivAt.comp a
    (hasFDerivAt_miuraFiniteActionCoordinates a ha S)).restrictScalars ℝ
  have hdFγ : HasFDerivAt (fun b => miuraFiniteActionCoordinates a ha S b i)
      ((miuraFiniteActionRows a ha S i).restrictScalars ℝ) (γ 0) := by
    simpa only [γ,Complex.ofReal_zero,zero_smul,add_zero] using! hdF
  have hd := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 (hdFγ.comp_hasDerivAt 0 hdγ))
  change HasDerivAt (fun t => (miuraFiniteActionCoordinates a ha S (γ t) i).im)
    (miuraFiniteActionRows a ha S i h).im 0 at hd
  have he : (fun t => (miuraFiniteActionCoordinates a ha S (γ t) i).im) = fun _ : ℝ => 0 := by
    funext t
    exact finiteActionCoordinates_real_values a ha S (γ t) (hγ t) i
  rw [he] at hd
  exact hd.unique (hasDerivAt_const (0 : ℝ) 0)

end NLS.MKdV
