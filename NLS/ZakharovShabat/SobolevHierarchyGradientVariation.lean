import NLS.ZakharovShabat.SobolevHierarchyGradient
import NLS.ZakharovShabat.SobolevHierarchySymmetries

/-! # The physical L² gradient represents the Sobolev Fréchet derivative -/
noncomputable section
open NLS.Fourier NLS.DifferentialPolynomial Complex MeasureTheory Set
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The bounded bilinear physical L² pairing, as a covector on Hˢ pairs.
Frequency reversal expresses integration of a product without conjugation. -/
def hierarchyL2GradientCovector (s : ℕ) :
    (Coeff 2 × Coeff 2) →L[ℂ] (SobolevSource s →L[ℂ] ℂ) :=
  let L := hierarchySobolevJetL2 s 0 (by omega)
  let A := L.comp (ContinuousLinearMap.fst ℂ _ _)
  let B := L.comp (ContinuousLinearMap.snd ℂ _ _)
  let R := Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap
  (((ContinuousLinearMap.compL ℂ (SobolevSource s) (Coeff 2) ℂ).flip A).comp
    (Coeff.dualPairing.comp (R.comp (ContinuousLinearMap.fst ℂ _ _)))) +
  (((ContinuousLinearMap.compL ℂ (SobolevSource s) (Coeff 2) ℂ).flip B).comp
    (Coeff.dualPairing.comp (R.comp (ContinuousLinearMap.snd ℂ _ _))))

@[simp] theorem hierarchyL2GradientCovector_apply (s : ℕ) (g : Coeff 2 × Coeff 2)
    (h : SobolevSource s) :
    hierarchyL2GradientCovector s g h =
      Coeff.dualPairing (Coeff.reflection g.1) (hierarchySobolevJetL2 s 0 (by omega) h.1) +
        Coeff.dualPairing (Coeff.reflection g.2) (hierarchySobolevJetL2 s 0 (by omega) h.2) := rfl

theorem hierarchyL2GradientCovector_eq_integral (s k : ℕ) (hk : k ≤ s+1)
    (ab cd : SobolevSource s) (a b h l : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hh : ContDiff ℝ ∞ h) (hl : ContDiff ℝ ∞ l)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j)
    (hhq : ∀ j, cd.1.val j = periodOneCoefficient h j)
    (hlq : ∀ j, cd.2.val j = periodOneCoefficient l j) :
    hierarchyL2GradientCovector s (sobolevNLSHierarchyGradient s k ab) cd =
      ∫ x in (0 : ℝ)..1, h x * (classicalNLSHierarchyGradient a b k x).1 +
        l x * (classicalNLSHierarchyGradient a b k x).2 := by
  have hg := sobolevNLSHierarchyGradient_eq_classical s k hk ab a b ha hb hpa hpb haq hbq
  have hg1 (j : ℤ) : (sobolevNLSHierarchyGradient s k ab).1 j =
      periodOneCoefficient (fun x => (classicalNLSHierarchyGradient a b k x).1) j :=
    congrArg Prod.fst (hg j)
  have hg2 (j : ℤ) : (sobolevNLSHierarchyGradient s k ab).2 j =
      periodOneCoefficient (fun x => (classicalNLSHierarchyGradient a b k x).2) j :=
    congrArg Prod.snd (hg j)
  have hc := contDiff_classicalNLSHierarchyGradient a b ha hb k
  have hI1 := tsum_bilinear_unitFourierCoefficient hc.fst.continuous hh.continuous
  have hI2 := tsum_bilinear_unitFourierCoefficient hc.snd.continuous hl.continuous
  rw [hierarchyL2GradientCovector_apply]
  simp only [Coeff.dualPairing_apply, Coeff.reflection_apply, hierarchySobolevJetL2_apply,
    pow_zero, one_mul, hg1, hg2, hhq, hlq]
  have hunit (f : ℝ → ℂ) (j : ℤ) :
      unitFourierCoefficient f j = periodOneCoefficient f j :=
    unitFourierCoefficient_eq_fourierCoeffOn f j
  simp only [hunit] at hI1 hI2
  have hi1 : IntervalIntegrable (fun x => (classicalNLSHierarchyGradient a b k x).1*h x)
      volume 0 1 := (hc.fst.continuous.mul hh.continuous).intervalIntegrable 0 1
  have hi2 : IntervalIntegrable (fun x => (classicalNLSHierarchyGradient a b k x).2*l x)
      volume 0 1 := (hc.snd.continuous.mul hl.continuous).intervalIntegrable 0 1
  rw [hI1, hI2, ← intervalIntegral.integral_add hi1 hi2]
  apply intervalIntegral.integral_congr
  intro x _
  ring

private theorem coefficient_affine (s : ℕ) (a h : ScalarSobolev s) (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (ha : ∀ j, a.val j = periodOneCoefficient f j)
    (hh : ∀ j, h.val j = periodOneCoefficient g j) (z : ℂ) (j : ℤ) :
    (a+z • h).val j = periodOneCoefficient (fun t => f t + z*g t) j := by
  change a.val j + z*h.val j = periodOneCoefficient (f+z • g) j
  rw [periodOneCoefficient_add f (z • g) hf (hg.const_smul z)]
  have he : periodOneCoefficient (z • g) j = z*periodOneCoefficient g j := by
    rw [periodOneCoefficient, fourierCoeffOn.const_smul]
    rfl
  rw [he, ha, hh]

private theorem fderiv_hierarchy_smooth_direction (s k : ℕ) (hk : k ≤ s+1)
    (ab cd : SobolevSource s) (a b h l : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hh : ContDiff ℝ ∞ h) (hl : ContDiff ℝ ∞ l)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hph : Function.Periodic h 1) (hpl : Function.Periodic l 1)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j)
    (hhq : ∀ j, cd.1.val j = periodOneCoefficient h j)
    (hlq : ∀ j, cd.2.val j = periodOneCoefficient l j) :
    fderiv ℂ (fun ef => sobolevNLSHamiltonian s ef k hk) ab cd =
      hierarchyL2GradientCovector s (sobolevNLSHierarchyGradient s k ab) cd := by
  have he (z : ℂ) : sobolevNLSHamiltonian s (ab+z • cd) k hk =
      classicalNLSHamiltonian (fun t => a t+z*h t) (fun t => b t+z*l t) k :=
    sobolevNLSHamiltonian_eq_classical s (ab+z • cd) _ _
      (ha.add (contDiff_const.mul hh)) (hb.add (contDiff_const.mul hl))
      (fun x => by dsimp; rw [hpa x,hph x]) (fun x => by dsimp; rw [hpb x,hpl x])
      (coefficient_affine s ab.1 cd.1 a h ha.continuous hh.continuous haq hhq z)
      (coefficient_affine s ab.2 cd.2 b l hb.continuous hl.continuous hbq hlq z) k hk
  have hline : HasDerivAt (fun z : ℂ => ab+z • cd) cd 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const cd |>.const_add ab
  have hf := (analyticAt_sobolevNLSHamiltonian s k hk ab).differentiableAt.hasFDerivAt
  have hzero : ab+(0 : ℂ) • cd = ab := by module
  have hd := (hzero ▸ hf).comp_hasDerivAt 0 hline
  simp only [Function.comp_def, he] at hd
  rw [hierarchyL2GradientCovector_eq_integral s k hk ab cd a b h l
    ha hb hh hl hpa hpb haq hbq hhq hlq]
  simpa only [hzero] using hd.unique (hasDerivAt_classicalNLSHamiltonian a b h l
    ha hb hh hl hpa hpb hph hpl k)

/-- The analytic L² gradient represents the actual complex Fréchet derivative
on the full admissible Hˢ space, including k=1 on H⁰. -/
theorem fderiv_sobolevNLSHamiltonian_eq_gradient (s k : ℕ) (hk : k ≤ s+1)
    (ab : SobolevSource s) :
    fderiv ℂ (fun cd => sobolevNLSHamiltonian s cd k hk) ab =
      hierarchyL2GradientCovector s (sobolevNLSHierarchyGradient s k ab) := by
  have hF : Continuous (fderiv ℂ (fun cd => sobolevNLSHamiltonian s cd k hk)) :=
    continuous_iff_continuousAt.mpr (fun cd =>
      (analyticAt_sobolevNLSHamiltonian s k hk cd).contDiffAt.continuousAt_fderiv
        (n := 1) one_ne_zero)
  have hG : Continuous (fun cd => hierarchyL2GradientCovector s
      (sobolevNLSHierarchyGradient s k cd)) :=
    (hierarchyL2GradientCovector s).continuous.comp
      (continuous_iff_continuousAt.mpr (fun cd =>
        (analyticAt_sobolevNLSHierarchyGradient s k cd).continuousAt))
  have he := eq_of_continuous_of_smooth_sobolevSource s _ _ hF hG (by
    intro cd a b ha hb hpa hpb haq hbq
    apply ContinuousLinearMap.ext
    intro ef
    have hh := eq_of_continuous_of_smooth_sobolevSource s _ _
      (fderiv ℂ (fun fg => sobolevNLSHamiltonian s fg k hk) cd).continuous
      (hierarchyL2GradientCovector s (sobolevNLSHierarchyGradient s k cd)).continuous (by
        intro fg h l hh hl hph hpl hhq hlq
        exact fderiv_hierarchy_smooth_direction s k hk cd fg a b h l
          ha hb hh hl hpa hpb hph hpl haq hbq hhq hlq)
    exact congrFun hh ef)
  exact congrFun he ab

end NLS.ZakharovShabat
