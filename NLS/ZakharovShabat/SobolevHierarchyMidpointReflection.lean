import NLS.ZakharovShabat.ClassicalNLSMidpointReflection
import NLS.ZakharovShabat.SobolevHierarchyGradientSymmetries
import NLS.Fourier.PeriodOneMidpointReflection

/-! # Pure spatial reflection of Hamiltonians and actual L2 gradients

Smooth density extends literal reflected physical integrals to the original
complex Sobolev domains. The chain rule and Fourier-mode uniqueness identify
the corresponding actual L2 gradients, with no smoothness assumption.
-/
noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

def hierarchyMidpointReflection (s : ℕ) : SobolevSource s →L[ℂ] SobolevSource s :=
  let T := (WeightedCoeff.reflection (p := 2) (s:ℝ)).toContinuousLinearEquiv.toContinuousLinearMap
  (T.comp (ContinuousLinearMap.fst ℂ _ _)).prod
    (T.comp (ContinuousLinearMap.snd ℂ _ _))

@[simp] theorem hierarchyMidpointReflection_apply (s : ℕ) (ab : SobolevSource s) :
    hierarchyMidpointReflection s ab =
      (WeightedCoeff.reflection (s:ℝ) ab.1,WeightedCoeff.reflection (s:ℝ) ab.2) := rfl

theorem sobolevNLSHamiltonian_midpointReflection (s k : ℕ) (hk : k+1 ≤ s+1)
    (ab : SobolevSource s) :
    sobolevNLSHamiltonian s (hierarchyMidpointReflection s ab) (k+1) hk =
      (-1:ℂ)^k*sobolevNLSHamiltonian s ab (k+1) hk := by
  let F := fun cd => sobolevNLSHamiltonian s cd (k+1) hk
  have hF : Continuous F := continuous_sobolevNLSHamiltonian s (k+1) hk
  have he := eq_of_continuous_of_smooth_sobolevSource s
    (fun cd => F (hierarchyMidpointReflection s cd)) (fun cd => (-1:ℂ)^k*F cd)
    (hF.comp (hierarchyMidpointReflection s).continuous) (continuous_const.mul hF) (by
      intro cd a b ha hb hpa hpb hca hcb
      have hpa' : Function.Periodic (fun x => a (1-x)) 1 := by
        intro x
        change a (1-(x+1)) = a (1-x)
        rw [show 1-(x+1) = -x by ring,show 1-x = -x+1 by ring,hpa]
      have hpb' : Function.Periodic (fun x => b (1-x)) 1 := by
        intro x
        change b (1-(x+1)) = b (1-x)
        rw [show 1-(x+1) = -x by ring,show 1-x = -x+1 by ring,hpb]
      have hca' (j : ℤ) : (hierarchyMidpointReflection s cd).1.val j =
          periodOneCoefficient (fun x => a (1-x)) j := by
        simp only [hierarchyMidpointReflection_apply,WeightedCoeff.reflection_apply,
          periodOneCoefficient_midpointReflection,hca]
      have hcb' (j : ℤ) : (hierarchyMidpointReflection s cd).2.val j =
          periodOneCoefficient (fun x => b (1-x)) j := by
        simp only [hierarchyMidpointReflection_apply,WeightedCoeff.reflection_apply,
          periodOneCoefficient_midpointReflection,hcb]
      dsimp only [F]
      rw [sobolevNLSHamiltonian_eq_classical s _ (fun x => a (1-x)) (fun x => b (1-x))
          (ha.comp (contDiff_const.sub contDiff_id)) (hb.comp (contDiff_const.sub contDiff_id))
          hpa' hpb' hca' hcb' (k+1) hk,
        sobolevNLSHamiltonian_eq_classical s cd a b ha hb hpa hpb hca hcb (k+1) hk,
        classicalNLSHamiltonian_midpointReflection])
  exact congrFun he ab

theorem fderiv_sobolevNLSHamiltonian_midpointReflection (s k : ℕ) (hk : k+1 ≤ s+1)
    (ab : SobolevSource s) :
    (fderiv ℂ (fun cd => sobolevNLSHamiltonian s cd (k+1) hk)
      (hierarchyMidpointReflection s ab)).comp (hierarchyMidpointReflection s) =
      (-1:ℂ)^k • fderiv ℂ (fun cd => sobolevNLSHamiltonian s cd (k+1) hk) ab := by
  have hl := ((analyticAt_sobolevNLSHamiltonian s (k+1) hk
    (hierarchyMidpointReflection s ab)).differentiableAt.hasFDerivAt).comp ab
      (hierarchyMidpointReflection s).hasFDerivAt
  have hr := ((analyticAt_sobolevNLSHamiltonian s (k+1) hk ab).differentiableAt.hasFDerivAt).const_mul ((-1:ℂ)^k)
  have he : (fun cd => sobolevNLSHamiltonian s (hierarchyMidpointReflection s cd) (k+1) hk) =
      (fun cd => (-1:ℂ)^k*sobolevNLSHamiltonian s cd (k+1) hk) :=
    funext (sobolevNLSHamiltonian_midpointReflection s k hk)
  simp only [Function.comp_def] at hl
  rw [he] at hl
  exact hl.unique hr

theorem sobolevNLSHierarchyGradient_midpointReflection (s k : ℕ) (hk : k+1 ≤ s+1)
    (ab : SobolevSource s) :
    sobolevNLSHierarchyGradient s (k+1) (hierarchyMidpointReflection s ab) =
      (-1:ℂ)^k • (Coeff.reflection (sobolevNLSHierarchyGradient s (k+1) ab).1,
        Coeff.reflection (sobolevNLSHierarchyGradient s (k+1) ab).2) := by
  have hd := fderiv_sobolevNLSHamiltonian_midpointReflection s k hk ab
  simp only [fderiv_sobolevNLSHamiltonian_eq_gradient] at hd
  have hmode (n : ℤ) (a b : ℂ) :
      hierarchyMidpointReflection s (sobolevSourceOfFinsupp s (Finsupp.single n a,Finsupp.single n b)) =
        sobolevSourceOfFinsupp s (Finsupp.single (-n) a,Finsupp.single (-n) b) := by
    apply Prod.ext <;> apply Subtype.ext <;> funext j <;>
      simp [hierarchyMidpointReflection_apply,sobolevSourceOfFinsupp,
        WeightedCoeff.reflection_apply,Finsupp.single_apply,neg_eq_iff_eq_neg]
  apply Prod.ext
  · ext n
    have h := congrArg (fun L : SobolevSource s →L[ℂ] ℂ =>
      L (sobolevSourceOfFinsupp s (Finsupp.single n 1,Finsupp.single n 0))) hd
    rw [ContinuousLinearMap.comp_apply,hmode] at h
    simp only [smul_apply,smul_eq_mul] at h
    rw [hierarchyL2GradientCovector_finite,hierarchyL2GradientCovector_finite] at h
    simpa using h
  · ext n
    have h := congrArg (fun L : SobolevSource s →L[ℂ] ℂ =>
      L (sobolevSourceOfFinsupp s (Finsupp.single n 0,Finsupp.single n 1))) hd
    rw [ContinuousLinearMap.comp_apply,hmode] at h
    simp only [smul_apply,smul_eq_mul] at h
    rw [hierarchyL2GradientCovector_finite,hierarchyL2GradientCovector_finite] at h
    simpa using h

end NLS.ZakharovShabat
