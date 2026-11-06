import NLS.SequenceSpaces.WeightedSourceSignedCompletion

/-! # Signed completion on genuine local complex domains

The positive function is needed at the source and its physical conjugate.
No ball centered at zero or zero-value premise is needed for local
analyticity. Exact native coefficient formulas and local norm bounds are
retained after transporting a weighted source through its isometry.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.Coeff

/-- Signed completion of normalized positive Hilbert coordinates. -/
def signedCompletion (F : Coeff 2 → Coeff 2) (q : Coeff 2) : Coeff 2 :=
  F q+Coeff.reflection (star (F (periodOneL2Conjugation q)))

/-- Both actual source germs give a complex analytic signed germ. -/
theorem analyticAt_signedCompletion (F : Coeff 2 → Coeff 2) (q : Coeff 2)
    (hF : AnalyticAt ℂ F q) (hFJ : AnalyticAt ℂ F (periodOneL2Conjugation q)) :
    AnalyticAt ℂ (signedCompletion F) q := by
  let L := (Coeff.reflection (p := 2)).toContinuousLinearEquiv.toContinuousLinearMap
  have hs := analyticAt_star_star hFJ
  simp only [periodOneL2Conjugation,star_star] at hs
  have hn := (L.analyticAt _).comp (f := (star ∘ F ∘ star) ∘ Coeff.reflection)
    (hs.comp (f := Coeff.reflection) (L.analyticAt q))
  exact hF.add hn

end NLS.Coeff
namespace NLS.WeightedCoeff

/-- Normalize only the source; the signed output retains its actual
Hilbert coefficients, ready for any exact target-weight transport. -/
def normalizedSignedCompletion (v : Weight)
    (F : WeightedCoeff v 2 → Coeff 2) (q : WeightedCoeff v 2) : Coeff 2 :=
  Coeff.signedCompletion (fun u => F ((weightIsometry v 2).symm u)) (weightIsometry v 2 q)

/-- Literal source conjugation and target reflection, without changing
any of the positive coefficients. -/
theorem normalizedSignedCompletion_eq (v : Weight) (hv : ∀ j, v (-j)=v j)
    (F : WeightedCoeff v 2 → Coeff 2) (q : WeightedCoeff v 2) :
    normalizedSignedCompletion v F q=
      F q+Coeff.reflection (star (F (conjugateReflection v hv q))) := by
  rw [normalizedSignedCompletion,Coeff.signedCompletion,weightIsometry_conjugateReflection v hv]
  simp only [LinearIsometryEquiv.symm_apply_apply]

@[simp] theorem normalizedSignedCompletion_apply (v : Weight) (hv : ∀ j, v (-j)=v j)
    (F : WeightedCoeff v 2 → Coeff 2) (q : WeightedCoeff v 2) (j : ℤ) :
    normalizedSignedCompletion v F q j=F q j+conj (F (conjugateReflection v hv q) (-j)) := by
  rw [normalizedSignedCompletion_eq v hv]
  simp only [lp.coeFn_add,Pi.add_apply,Coeff.reflection_apply,lp.star_apply,starRingEnd_apply]

/-- Physical conjugation is continuous in the actual native weighted norm. -/
theorem continuous_conjugateReflection (v : Weight) (hv : ∀ j, v (-j)=v j) :
    Continuous (conjugateReflection (p := 2) v hv) := by
  let I := weightIsometry v 2
  change Continuous (fun q => I.symm (star (Coeff.reflection (I q))))
  exact I.symm.continuous.comp
    ((continuous_star.comp (Coeff.reflection (p := 2)).continuous).comp I.continuous)

/-- Local analyticity on both conjugate source germs gives actual native
signed analyticity, with no zero-base or zero-value premise. -/
theorem analyticAt_normalizedSignedCompletion (v : Weight) (hv : ∀ j, v (-j)=v j)
    (F : WeightedCoeff v 2 → Coeff 2) (q : WeightedCoeff v 2)
    (hF : AnalyticAt ℂ F q) (hFJ : AnalyticAt ℂ F (conjugateReflection v hv q)) :
    AnalyticAt ℂ (normalizedSignedCompletion v F) q := by
  let I := weightIsometry v 2
  let G := fun u => F (I.symm u)
  have hq : AnalyticAt ℂ F (I.symm (I q)) := by
    simpa only [LinearIsometryEquiv.symm_apply_apply] using hF
  have hj : I.symm (periodOneL2Conjugation (I q))=conjugateReflection v hv q := by
    rw [weightIsometry_conjugateReflection v hv,LinearIsometryEquiv.symm_apply_apply]
  have hJ : AnalyticAt ℂ F (I.symm (periodOneL2Conjugation (I q))) := by
    rw [hj]
    exact hFJ
  have hG : AnalyticAt ℂ G (I q) :=
    hq.comp (I.symm.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt (I q))
  have hGJ : AnalyticAt ℂ G (periodOneL2Conjugation (I q)) :=
    hJ.comp (I.symm.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _)
  exact (Coeff.analyticAt_signedCompletion G (I q) hG hGJ).comp
    (I.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt q)

/-- One explicit intersection is the genuine complex domain of the local
signed completion, including arbitrary physically real native bases. -/
theorem analyticOnNhd_normalizedSignedCompletion (v : Weight) (hv : ∀ j, v (-j)=v j)
    (F : WeightedCoeff v 2 → Coeff 2) (U : Set (WeightedCoeff v 2))
    (hF : AnalyticOnNhd ℂ F U) :
    AnalyticOnNhd ℂ (normalizedSignedCompletion v F) (U∩conjugateReflection v hv ⁻¹' U) := by
  intro q hq
  exact analyticAt_normalizedSignedCompletion v hv F q (hF q hq.1) (hF _ hq.2)

/-- A common local bound for the positive map at both actual conjugate
sources bounds its full signed native output. -/
theorem norm_normalizedSignedCompletion_le (v : Weight) (hv : ∀ j, v (-j)=v j)
    (F : WeightedCoeff v 2 → Coeff 2) (q : WeightedCoeff v 2) (M : ℝ)
    (hF : ‖F q‖≤M) (hFJ : ‖F (conjugateReflection v hv q)‖≤M) :
    ‖normalizedSignedCompletion v F q‖≤2*M := by
  rw [normalizedSignedCompletion_eq v hv]
  apply (norm_add_le _ _).trans
  rw [Coeff.reflection.norm_map,norm_star]
  linarith

/-- The normalized completion is exactly the established weighted target
completion transported through its target isometry. -/
theorem weightedSourceSignedCompletion_eq_normalized (v w : Weight)
    (Y : WeightedCoeff v 2 → WeightedCoeff w 2) (q : WeightedCoeff v 2) :
    weightedSourceSignedCompletion v w Y q=
      (weightIsometry w 2).symm (normalizedSignedCompletion v (fun q => weightIsometry w 2 (Y q)) q) := rfl

end NLS.WeightedCoeff
