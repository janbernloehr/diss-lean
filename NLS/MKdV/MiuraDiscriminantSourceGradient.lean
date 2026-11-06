import NLS.MKdV.MiuraDiscriminantGradient
import NLS.MKdV.MiuraDiscriminantCotangent
import NLS.MKdV.MiuraGardnerTransfer
import NLS.Poisson.SobolevGardnerGradientPullback

/-! # Exact source-cotangent realization of the independent Hill trace gradient -/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.Fourier NLS.Poisson NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraSourceDifferenceCLM : (CoeffPair 2 →L[ℂ] ℂ) →L[ℂ] Coeff 2 :=
  I • (Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((ContinuousLinearMap.fst ℂ (Coeff 2) (Coeff 2))-
      (ContinuousLinearMap.snd ℂ (Coeff 2) (Coeff 2))).comp (CoeffPair.cotangentCoefficients le_rfl)))

theorem miuraSourceDifferenceCLM_apply (L : CoeffPair 2 →L[ℂ] ℂ) (m : ℤ) :
    miuraSourceDifferenceCLM L m = I*(L (CoeffPair.inlCLM (lp.single 2 (-m) 1))-
      L (CoeffPair.inrCLM (lp.single 2 (-m) 1))) := by
  change I*((CoeffPair.cotangentCoefficients le_rfl L).1 (-m)-
    (CoeffPair.cotangentCoefficients le_rfl L).2 (-m)) = _
  rw [CoeffPair.cotangentCoefficients_fst,CoeffPair.cotangentCoefficients_snd]

theorem miuraHillDiscriminantGradient_fourier (a : ScalarDomain 2) (z : ℂ) (m : ℤ) :
    (miuraHillDiscriminantGradient a (z^2)).gradient.val m =
      sourceDiscriminantCotangent (by simp) z (sobolevSourceInclusion (a,a))
        (CoeffPair.inlCLM (lp.single 2 (-m) 1))+
      sourceDiscriminantCotangent (by simp) z (sobolevSourceInclusion (a,a))
        (CoeffPair.inrCLM (lp.single 2 (-m) 1)) := by
  have hfun : (fun b : ScalarDomain 2 => hillL2Discriminant (sobolevMiuraHillPotential b) (z^2)) =
      (fun b : ScalarDomain 2 => canonicalDiscriminant (by simp) (periodOnePotential (sobolevSourceInclusion (b,b))) z) :=
    funext (fun b => hillL2Discriminant_miura_eq_canonical b z)
  have ha : AnalyticAt ℂ (fun φ : CoeffPair 2 => canonicalDiscriminant (by simp) (periodOnePotential φ) z)
      (sobolevSourceInclusion (a,a)) :=
    (analyticOnNhd_canonicalDiscriminant_periodOne (by simp) (by norm_num)
      (z,sobolevSourceInclusion (a,a)) (mem_univ _)).comp
      (f := fun φ : CoeffPair 2 => (z,φ)) (analyticAt_const.prod analyticAt_id)
  have hv := (miuraHillDiscriminantGradient a (z^2)).gradient_eval_of_pullback
    (fun φ : CoeffPair 2 => canonicalDiscriminant (by simp) (periodOnePotential φ) z)
    miuraActionSourceCLM ha.differentiableAt (fun b => congrFun hfun b) m
  have hm : miuraActionSourceCLM (scalarMode (-m) 1) =
      CoeffPair.inlCLM (lp.single 2 (-m) 1)+CoeffPair.inrCLM (lp.single 2 (-m) 1) := by
    rw [miuraActionSourceCLM_apply,← scalarL2Diagonal_scalarInclusion,scalarInclusion_scalarMode]
    rfl
  rw [hm,map_add] at hv
  exact hv

theorem periodOneDerivative_miuraHillDiscriminantGradient (a : ScalarDomain 2) (z : ℂ) :
    periodOneDerivative (miuraHillDiscriminantGradient a (z^2)).gradient =
      (2*z) • miuraSourceDifferenceCLM (sourceDiscriminantCotangent (by simp) z (sobolevSourceInclusion (a,a))) := by
  ext m
  rw [periodOneDerivative_apply,miuraHillDiscriminantGradient_fourier,lp.coeFn_smul,Pi.smul_apply,
    smul_eq_mul,miuraSourceDifferenceCLM_apply]
  have h := miuraDiscriminantCotangent_fourier a z m
  simp only [CoeffPair.cotangentCoefficients_fst,CoeffPair.cotangentCoefficients_snd] at h
  change _ = _
  linear_combination h

theorem miuraActionGardnerDirection_eq_sourceDifference (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    l2GardnerDirection (miuraL2Action n) (scalarInclusion a) =
      miuraSourceDifferenceCLM (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
        (sobolevSourceInclusion (a,a))) := by
  ext m
  rw [miuraSourceDifferenceCLM_apply]
  exact miuraActionGardnerDirection_apply a ha n hn m

end NLS.MKdV
