import NLS.SequenceSpaces.PositiveCartesianParameters
import NLS.SequenceSpaces.QuadraticActionsExponent

/-! # Quadratic auxiliary parameters retaining a literal signed mean

The auxiliary zero-mode action represents the mean itself. The isotropic
affine pair (m+1/2, i*(m-1/2)) has quadratic action m, so its section is
entire even when the signed mean is zero.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Coeff

def zeroPairRadius (z : Coeff 2 × Coeff 2) : ℂ := (z.1 0^2+z.2 0^2)/2

def zeroPairRadiusDerivative (z : Coeff 2 × Coeff 2) : (Coeff 2 × Coeff 2) →L[ℂ] ℂ :=
  (z.1 0) • ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).comp (ContinuousLinearMap.fst ℂ _ _))+
    (z.2 0) • ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).comp (ContinuousLinearMap.snd ℂ _ _))

theorem hasFDerivAt_zeroPairRadius (z : Coeff 2 × Coeff 2) :
    HasFDerivAt zeroPairRadius (zeroPairRadiusDerivative z) z := by
  let x := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).comp (ContinuousLinearMap.fst ℂ (Coeff 2) (Coeff 2))
  let y := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).comp (ContinuousLinearMap.snd ℂ (Coeff 2) (Coeff 2))
  have hx : HasFDerivAt (x : (Coeff 2 × Coeff 2) → ℂ) x z := x.hasFDerivAt
  have hy : HasFDerivAt (y : (Coeff 2 × Coeff 2) → ℂ) y z := y.hasFDerivAt
  have h := ((hx.mul hx).add (hy.mul hy)).const_mul (1/2 : ℂ)
  have he : (fun u => (1/2 : ℂ)*(x u*x u+y u*y u)) = zeroPairRadius := by
    funext u
    change (1/2 : ℂ)*(u.1 0*u.1 0+u.2 0*u.2 0) = (u.1 0^2+u.2 0^2)/2
    ring
  change HasFDerivAt (fun u => (1/2 : ℂ)*(x u*x u+y u*y u)) _ z at h
  rw [he] at h
  have hlin : (1/2 : ℂ) • (x z • x+x z • x+(y z • y+y z • y)) = zeroPairRadiusDerivative z := by
    apply ContinuousLinearMap.ext
    intro u
    change (1/2 : ℂ)*(z.1 0*u.1 0+z.1 0*u.1 0+(z.2 0*u.2 0+z.2 0*u.2 0)) =
      z.1 0*u.1 0+z.2 0*u.2 0
    ring
  rw [hlin] at h
  exact h

theorem analyticAt_zeroPairRadius (z : Coeff 2 × Coeff 2) : AnalyticAt ℂ zeroPairRadius z := by
  have hx : AnalyticAt ℂ (fun u : Coeff 2 × Coeff 2 => u.1 0) z :=
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).analyticAt _).comp analyticAt_fst
  have hy : AnalyticAt ℂ (fun u : Coeff 2 × Coeff 2 => u.2 0) z :=
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).analyticAt _).comp analyticAt_snd
  exact ((hx.pow 2).add (hy.pow 2)).div_const (c := (2 : ℂ))

theorem zeroPairRadiusDerivative_rotation (z : Coeff 2 × Coeff 2) (k : ℤ) :
    zeroPairRadiusDerivative z (actionRotationVectorCLM 2 k z) = 0 := by
  change z.1 0*(-(lp.single (E := fun _ : ℤ => ℂ) 2 k (z.2 k))) 0+
    z.2 0*(lp.single (E := fun _ : ℤ => ℂ) 2 k (z.1 k)) 0 = 0
  by_cases hk : k = 0
  · subst k
    simp only [lp.coeFn_neg,Pi.neg_apply,lp.single_apply,Pi.single_eq_same]
    ring
  · simp only [lp.coeFn_neg,Pi.neg_apply,lp.single_apply,Pi.single_eq_of_ne (Ne.symm hk),neg_zero,mul_zero,add_zero]

end NLS.Coeff
namespace NLS.WeightedCoeff
variable (w : Weight)

def positiveCartesianQuadraticMeanMap (z : Coeff 2 × Coeff 2) : PositiveCartesianTarget w 2 :=
  ((positiveCartesianParameterMap w 2 z).1,Coeff.zeroPairRadius z)

theorem positiveCartesianQuadraticMeanMap_eval (z : Coeff 2 × Coeff 2) (n : ℤ) :
    positiveCartesianEval w 2 n (positiveCartesianQuadraticMeanMap w z) =
      if 0 < n then (z.1 n/(w n : ℂ),z.2 n/(w n : ℂ)) else 0 :=
  positiveCartesianParameterMap_eval w 2 z n

theorem analyticAt_positiveCartesianQuadraticMeanMap (z : Coeff 2 × Coeff 2) :
    AnalyticAt ℂ (positiveCartesianQuadraticMeanMap w) z :=
  (analyticAt_fst.comp ((positiveCartesianParameterMap w 2).analyticAt z)).prod (Coeff.analyticAt_zeroPairRadius z)

def positiveCartesianQuadraticMeanDerivative (z : Coeff 2 × Coeff 2) :
    (Coeff 2 × Coeff 2) →L[ℂ] PositiveCartesianTarget w 2 :=
  ((ContinuousLinearMap.fst ℂ _ ℂ).comp (positiveCartesianParameterMap w 2)).prod
    (Coeff.zeroPairRadiusDerivative z)

theorem hasFDerivAt_positiveCartesianQuadraticMeanMap (z : Coeff 2 × Coeff 2) :
    HasFDerivAt (positiveCartesianQuadraticMeanMap w) (positiveCartesianQuadraticMeanDerivative w z) z :=
  (show HasFDerivAt (fun u : Coeff 2 × Coeff 2 => (positiveCartesianParameterMap w 2 u).1)
      ((ContinuousLinearMap.fst ℂ _ ℂ).comp (positiveCartesianParameterMap w 2)) z from
        ((ContinuousLinearMap.fst ℂ _ ℂ).comp (positiveCartesianParameterMap w 2)).hasFDerivAt).prodMk
    (Coeff.hasFDerivAt_zeroPairRadius z)

/-- The auxiliary mean action is stationary even for rotation at zero. -/
theorem positiveCartesianQuadraticMeanDerivative_rotation (z : Coeff 2 × Coeff 2) (k : ℤ) :
    positiveCartesianQuadraticMeanDerivative w z (Coeff.actionRotationVectorCLM 2 k z) =
      if 0 < k then -(positiveCartesianActionVector w 2 k (positiveCartesianQuadraticMeanMap w z)) else 0 := by
  apply positivePairMean_ext (w := w) (p := 2)
  · intro n hn
    change positiveCartesianEval w 2 n (positiveCartesianParameterMap w 2
      (Coeff.actionRotationVectorCLM 2 k z)) =
      positiveCartesianEval w 2 n (if 0 < k then
        -(positiveCartesianActionVector w 2 k (positiveCartesianQuadraticMeanMap w z)) else 0)
    rw [positiveCartesianParameterMap_eval,if_pos hn,Coeff.actionRotationVectorCLM_apply]
    split_ifs with hkp
    · rw [map_neg,positiveCartesianActionVector_eval,positiveCartesianQuadraticMeanMap_eval,if_pos hn]
      by_cases hnk : n = k
      · subst n
        simp [lp.single_apply,neg_div]
      · simp [lp.single_apply,hnk]
    · have hnk : n ≠ k := by omega
      simp [lp.single_apply,hnk]
  · change Coeff.zeroPairRadiusDerivative z (Coeff.actionRotationVectorCLM 2 k z) = _
    rw [Coeff.zeroPairRadiusDerivative_rotation]
    split_ifs
    · change (0 : ℂ) = -0
      exact (neg_zero).symm
    · rfl

def positiveCartesianIsotropicSection (z : PositiveCartesianTarget w 2) : Coeff 2 × Coeff 2 :=
  let q := positiveCartesianParameterSection w 2 z
  (q.1+lp.single 2 0 (1/2 : ℂ),q.2+lp.single 2 0 (I*(z.2-1/2)))

theorem positiveCartesianIsotropicSection_fst (z : PositiveCartesianTarget w 2) (n : ℤ) :
    (positiveCartesianIsotropicSection w z).1 n = (w n : ℂ)*z.1.1.val.val n+if n = 0 then z.2+1/2 else 0 := by
  change (positiveCartesianParameterSection w 2 z).1 n+(lp.single (E := fun _ : ℤ => ℂ) 2 0 (1/2 : ℂ)) n = _
  rw [positiveCartesianParameterSection_fst]
  by_cases hn : n = 0 <;> simp [lp.single_apply,hn]
  ring

theorem positiveCartesianIsotropicSection_snd (z : PositiveCartesianTarget w 2) (n : ℤ) :
    (positiveCartesianIsotropicSection w z).2 n = (w n : ℂ)*z.1.2.val.val n+if n = 0 then I*(z.2-1/2) else 0 := by
  change (positiveCartesianParameterSection w 2 z).2 n+(lp.single (E := fun _ : ℤ => ℂ) 2 0 (I*(z.2-1/2))) n = _
  rw [positiveCartesianParameterSection_snd]
  simp [lp.single_apply,Pi.single_apply]

theorem analyticAt_positiveCartesianIsotropicSection (z : PositiveCartesianTarget w 2) :
    AnalyticAt ℂ (positiveCartesianIsotropicSection w) z := by
  have hq := (positiveCartesianParameterSection w 2).analyticAt z
  have hmean : AnalyticAt ℂ (fun u : PositiveCartesianTarget w 2 => I*(u.2-1/2)) z :=
    analyticAt_const.mul (analyticAt_snd.sub analyticAt_const)
  exact ((analyticAt_fst.comp hq).add analyticAt_const).prod
    ((analyticAt_snd.comp hq).add (((lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 0).analyticAt _).comp hmean))

/-- An entire section recovers the original positive pair and signed
mean, including mean zero, without choosing any square root. -/
theorem positiveCartesianQuadraticMeanMap_isotropicSection (z : PositiveCartesianTarget w 2) :
    positiveCartesianQuadraticMeanMap w (positiveCartesianIsotropicSection w z) = z := by
  apply positivePairMean_ext (w := w) (p := 2)
  · intro n hn
    change positiveCartesianEval w 2 n (positiveCartesianQuadraticMeanMap w (positiveCartesianIsotropicSection w z)) =
      positiveCartesianEval w 2 n z
    rw [positiveCartesianQuadraticMeanMap_eval,if_pos hn,positiveCartesianIsotropicSection_fst,
      positiveCartesianIsotropicSection_snd,if_neg (ne_of_gt hn),if_neg (ne_of_gt hn)]
    simp only [add_zero,mul_div_cancel_left₀ _ (w.complex_ne_zero n)]
    rfl
  · change Coeff.zeroPairRadius (positiveCartesianIsotropicSection w z) = z.2
    have hx : (positiveCartesianIsotropicSection w z).1 0 = z.2+1/2 := by
      rw [positiveCartesianIsotropicSection_fst,z.1.1.property 0 le_rfl,mul_zero,zero_add]
      exact if_pos rfl
    have hy : (positiveCartesianIsotropicSection w z).2 0 = I*(z.2-1/2) := by
      rw [positiveCartesianIsotropicSection_snd,z.1.2.property 0 le_rfl,mul_zero,zero_add]
      exact if_pos rfl
    rw [Coeff.zeroPairRadius,hx,hy,mul_pow,Complex.I_sq]
    ring

end NLS.WeightedCoeff
