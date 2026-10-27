import NLS.ZakharovShabat.ClassicalRenormalizedEnergyVariation
import NLS.ZakharovShabat.PeriodOneSobolevEnergyVariation

/-! # The renormalized energy on the full complex H1 space

The literal physical energy H - 2 M^2 is entire on the original Sobolev
pair space. Its full bounded complex derivative keeps the factor four.
On smooth representatives it agrees with the classical Hamiltonian and
both proved variational gradients.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The original physical renormalized energy on every complex H1 pair. -/
def periodOneSobolevRenormalizedEnergy (ab : ScalarDomain 2 × ScalarDomain 2) : ℂ :=
  periodOneSobolevHamiltonian ab - 2*(periodOneSobolevMass ab)^2

theorem analyticAt_periodOneSobolevRenormalizedEnergy (ab : ScalarDomain 2 × ScalarDomain 2) :
    AnalyticAt ℂ periodOneSobolevRenormalizedEnergy ab :=
  (analyticAt_periodOneSobolevHamiltonian ab).sub
    (analyticAt_const.mul ((analyticAt_periodOneSobolevMass ab).pow 2))

/-- The full Fréchet derivative is valid at arbitrary, possibly nonsmooth H1 pairs. -/
theorem hasFDerivAt_periodOneSobolevRenormalizedEnergy (ab : ScalarDomain 2 × ScalarDomain 2) :
    HasFDerivAt periodOneSobolevRenormalizedEnergy
      (fderiv ℂ periodOneSobolevHamiltonian ab -
        (4*periodOneSobolevMass ab) • fderiv ℂ periodOneSobolevMass ab) ab := by
  have hd := (analyticAt_periodOneSobolevHamiltonian ab).differentiableAt.hasFDerivAt.sub
    ((((analyticAt_periodOneSobolevMass ab).differentiableAt.hasFDerivAt).pow 2).const_mul 2)
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro h
  simp only [sub_apply, smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.reduceSub, pow_one]
  ring

/-- The Sobolev mass has its exact quadratic expansion in two arbitrary H1 directions. -/
theorem periodOneSobolevMass_line (a b h k : ScalarDomain 2) (z : ℂ) :
    periodOneSobolevMass (a+z • h,b+z • k) =
      periodOneSobolevMass (a,b) +
        z*(periodOneSobolevMass (h,b)+periodOneSobolevMass (a,k)) +
        z^2*periodOneSobolevMass (h,k) := by
  simp only [periodOneSobolevMass, map_add, map_smul,
    add_apply, smul_apply, smul_eq_mul]
  ring

/-- The entire mass derivative, without smoothness restrictions on the base or direction. -/
theorem fderiv_periodOneSobolevMass_apply (a b h k : ScalarDomain 2) :
    fderiv ℂ periodOneSobolevMass (a,b) (h,k) =
      periodOneSobolevMass (h,b)+periodOneSobolevMass (a,k) := by
  have hl : HasDerivAt (fun z : ℂ => (a,b)+z • (h,k)) (h,k) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (h,k)).const_add (a,b)
  have hd := (show HasFDerivAt periodOneSobolevMass (fderiv ℂ periodOneSobolevMass (a,b))
    ((a,b)+(0 : ℂ) • (h,k)) from by simpa using
      (analyticAt_periodOneSobolevMass (a,b)).differentiableAt.hasFDerivAt).comp_hasDerivAt 0 hl
  have he : HasDerivAt (fun z : ℂ => periodOneSobolevMass (a+z • h,b+z • k))
      (periodOneSobolevMass (h,b)+periodOneSobolevMass (a,k)) 0 := by
    simp_rw [periodOneSobolevMass_line]
    simpa using! ((hasDerivAt_const (0 : ℂ) (periodOneSobolevMass (a,b))).add
      ((hasDerivAt_id (0 : ℂ)).mul_const (periodOneSobolevMass (h,b)+periodOneSobolevMass (a,k)))).add
        (((hasDerivAt_id (0 : ℂ)).pow 2).mul_const (periodOneSobolevMass (h,k)))
  exact hd.unique he

theorem fderiv_periodOneSobolevRenormalizedEnergy_apply (a b h k : ScalarDomain 2) :
    fderiv ℂ periodOneSobolevRenormalizedEnergy (a,b) (h,k) =
      fderiv ℂ periodOneSobolevHamiltonian (a,b) (h,k) -
        4*periodOneSobolevMass (a,b)*(periodOneSobolevMass (h,b)+periodOneSobolevMass (a,k)) := by
  rw [(hasFDerivAt_periodOneSobolevRenormalizedEnergy (a,b)).fderiv]
  change fderiv ℂ periodOneSobolevHamiltonian (a,b) (h,k) -
    (4*periodOneSobolevMass (a,b))*fderiv ℂ periodOneSobolevMass (a,b) (h,k) = _
  rw [fderiv_periodOneSobolevMass_apply]

/-- The Banach energy agrees with the literal classical hierarchy on smooth representatives. -/
theorem periodOneSobolevRenormalizedEnergy_eq_classical (a b : ScalarDomain 2)
    (ha : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))))
    (hb : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis b (x : AddCircle (2 : ℝ)))) :
    periodOneSobolevRenormalizedEnergy (a,b) = classicalRenormalizedNLSEnergy
      (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ)))
      (fun x : ℝ => periodOneSobolevSynthesis b (x : AddCircle (2 : ℝ))) := by
  rw [periodOneSobolevRenormalizedEnergy, classicalRenormalizedNLSEnergy,
    periodOneSobolevHamiltonian_eq_classical a b ha hb,
    classicalNLSHamiltonian_one, periodOneSobolevMass_eq_integral]

/-- The first H¹ component variation has the classical spatial gradient. -/
theorem hasDerivAt_periodOneSobolevRenormalizedEnergy_fst (a b h : ScalarDomain 2)
    (ha : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))))
    (hb : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis b (x : AddCircle (2 : ℝ))))
    (hh : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis h (x : AddCircle (2 : ℝ)))) :
    HasDerivAt (fun z : ℂ => periodOneSobolevRenormalizedEnergy (a+z • h,b))
      (∫ x in (0 : ℝ)..1, periodOneSobolevSynthesis h (x : AddCircle (2 : ℝ)) *
        (classicalRenormalizedNLSEnergyGradient
          (fun y : ℝ => periodOneSobolevSynthesis a (y : AddCircle (2 : ℝ)))
          (fun y : ℝ => periodOneSobolevSynthesis b (y : AddCircle (2 : ℝ)))).1 x) 0 := by
  have he (z : ℂ) : (fun x : ℝ => periodOneSobolevSynthesis (a+z • h) (x : AddCircle (2 : ℝ))) =
      fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ)) +
        z*periodOneSobolevSynthesis h (x : AddCircle (2 : ℝ)) := by
    funext x
    simp only [map_add,map_smul,ContinuousMap.add_apply,ContinuousMap.smul_apply,smul_eq_mul]
  have hf (z : ℂ) := periodOneSobolevRenormalizedEnergy_eq_classical (a+z • h) b
    (by rw [he]; exact ha.add (contDiff_const.mul hh)) hb
  simp_rw [hf,he]
  exact hasDerivAt_classicalRenormalizedNLSEnergy_fst _ _ _ ha hb hh
    (periodOneSobolevSynthesis_periodic a) (periodOneSobolevSynthesis_periodic b)
    (periodOneSobolevSynthesis_periodic h)

/-- The second H¹ component variation has the other classical spatial gradient. -/
theorem hasDerivAt_periodOneSobolevRenormalizedEnergy_snd (a b h : ScalarDomain 2)
    (ha : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))))
    (hb : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis b (x : AddCircle (2 : ℝ))))
    (hh : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis h (x : AddCircle (2 : ℝ)))) :
    HasDerivAt (fun z : ℂ => periodOneSobolevRenormalizedEnergy (a,b+z • h))
      (∫ x in (0 : ℝ)..1, periodOneSobolevSynthesis h (x : AddCircle (2 : ℝ)) *
        (classicalRenormalizedNLSEnergyGradient
          (fun y : ℝ => periodOneSobolevSynthesis a (y : AddCircle (2 : ℝ)))
          (fun y : ℝ => periodOneSobolevSynthesis b (y : AddCircle (2 : ℝ)))).2 x) 0 := by
  have he (z : ℂ) : (fun x : ℝ => periodOneSobolevSynthesis (b+z • h) (x : AddCircle (2 : ℝ))) =
      fun x : ℝ => periodOneSobolevSynthesis b (x : AddCircle (2 : ℝ)) +
        z*periodOneSobolevSynthesis h (x : AddCircle (2 : ℝ)) := by
    funext x
    simp only [map_add,map_smul,ContinuousMap.add_apply,ContinuousMap.smul_apply,smul_eq_mul]
  have hf (z : ℂ) := periodOneSobolevRenormalizedEnergy_eq_classical a (b+z • h) ha
    (by rw [he]; exact hb.add (contDiff_const.mul hh))
  simp_rw [hf,he]
  exact hasDerivAt_classicalRenormalizedNLSEnergy_snd _ _ _ ha hb hh
    (periodOneSobolevSynthesis_periodic a) (periodOneSobolevSynthesis_periodic b)
    (periodOneSobolevSynthesis_periodic h)

/-- The full energy derivative is the sum of the two physical first variations. -/
theorem fderiv_periodOneSobolevRenormalizedEnergy_eq_integrals (a b h k : ScalarDomain 2)
    (ha : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))))
    (hb : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis b (x : AddCircle (2 : ℝ))))
    (hh : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis h (x : AddCircle (2 : ℝ))))
    (hk : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis k (x : AddCircle (2 : ℝ)))) :
    (fderiv ℂ periodOneSobolevRenormalizedEnergy (a,b)) (h,k) =
      (∫ x in (0 : ℝ)..1, periodOneSobolevSynthesis h (x : AddCircle (2 : ℝ)) *
        (classicalRenormalizedNLSEnergyGradient
          (fun y : ℝ => periodOneSobolevSynthesis a (y : AddCircle (2 : ℝ)))
          (fun y : ℝ => periodOneSobolevSynthesis b (y : AddCircle (2 : ℝ)))).1 x) +
      (∫ x in (0 : ℝ)..1, periodOneSobolevSynthesis k (x : AddCircle (2 : ℝ)) *
        (classicalRenormalizedNLSEnergyGradient
          (fun y : ℝ => periodOneSobolevSynthesis a (y : AddCircle (2 : ℝ)))
          (fun y : ℝ => periodOneSobolevSynthesis b (y : AddCircle (2 : ℝ)))).2 x) := by
  let L := fderiv ℂ periodOneSobolevRenormalizedEnergy (a,b)
  have hL : HasFDerivAt periodOneSobolevRenormalizedEnergy L (a,b) :=
    (analyticAt_periodOneSobolevRenormalizedEnergy (a,b)).differentiableAt.hasFDerivAt
  have hd₁ : HasDerivAt (fun z : ℂ => (a+z • h,b)) (h,0) 0 := by
    simpa using (((hasDerivAt_id (0 : ℂ)).smul_const h).const_add a).prodMk (hasDerivAt_const 0 b)
  have hd₂ : HasDerivAt (fun z : ℂ => (a,b+z • k)) (0,k) 0 := by
    simpa using (hasDerivAt_const (0 : ℂ) a).prodMk (((hasDerivAt_id (0 : ℂ)).smul_const k).const_add b)
  have hc₁ := (show HasFDerivAt periodOneSobolevRenormalizedEnergy L (a+(0 : ℂ) • h,b) by simpa using hL).comp_hasDerivAt 0 hd₁
  have hc₂ := (show HasFDerivAt periodOneSobolevRenormalizedEnergy L (a,b+(0 : ℂ) • k) by simpa using hL).comp_hasDerivAt 0 hd₂
  have he₁ := hc₁.unique (hasDerivAt_periodOneSobolevRenormalizedEnergy_fst a b h ha hb hh)
  have he₂ := hc₂.unique (hasDerivAt_periodOneSobolevRenormalizedEnergy_snd a b k ha hb hk)
  change L (h,k) = _
  rw [show (h,k) = (h,0)+(0,k) by simp,map_add,he₁,he₂]

end NLS.ZakharovShabat
