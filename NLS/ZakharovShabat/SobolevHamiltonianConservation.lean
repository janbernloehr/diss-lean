import NLS.ZakharovShabat.PeriodOneSobolevEnergyVariation
import NLS.ZakharovShabat.ClassicalNLSVectorField
import NLS.FunctionalAnalysis.ClosedDerivativeZero

/-! # Physical energy conservation from the strong H¹ equation

The first variation of the actual Sobolev Hamiltonian annihilates the
classical NLS vector field. This proves conservation along local H¹ curves
from their physical equation, without a spectral or finite-gap assumption.
-/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The full energy derivative is the sum of the two physical first variations. -/
theorem fderiv_periodOneSobolevHamiltonian_apply (a b h k : ScalarDomain 2)
    (ha : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))))
    (hb : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis b (x : AddCircle (2 : ℝ))))
    (hh : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis h (x : AddCircle (2 : ℝ))))
    (hk : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis k (x : AddCircle (2 : ℝ)))) :
    (fderiv ℂ periodOneSobolevHamiltonian (a,b)) (h,k) =
      (∫ x in (0 : ℝ)..1, periodOneSobolevSynthesis h (x : AddCircle (2 : ℝ)) *
        (classicalNLSEnergyGradient
          (fun y : ℝ => periodOneSobolevSynthesis a (y : AddCircle (2 : ℝ)))
          (fun y : ℝ => periodOneSobolevSynthesis b (y : AddCircle (2 : ℝ)))).1 x) +
      (∫ x in (0 : ℝ)..1, periodOneSobolevSynthesis k (x : AddCircle (2 : ℝ)) *
        (classicalNLSEnergyGradient
          (fun y : ℝ => periodOneSobolevSynthesis a (y : AddCircle (2 : ℝ)))
          (fun y : ℝ => periodOneSobolevSynthesis b (y : AddCircle (2 : ℝ)))).2 x) := by
  let L := fderiv ℂ periodOneSobolevHamiltonian (a,b)
  have hL : HasFDerivAt periodOneSobolevHamiltonian L (a,b) :=
    (analyticAt_periodOneSobolevHamiltonian (a,b)).differentiableAt.hasFDerivAt
  have hd₁ : HasDerivAt (fun z : ℂ => (a+z • h,b)) (h,0) 0 := by
    simpa using (((hasDerivAt_id (0 : ℂ)).smul_const h).const_add a).prodMk (hasDerivAt_const 0 b)
  have hd₂ : HasDerivAt (fun z : ℂ => (a,b+z • k)) (0,k) 0 := by
    simpa using (hasDerivAt_const (0 : ℂ) a).prodMk (((hasDerivAt_id (0 : ℂ)).smul_const k).const_add b)
  have hc₁ := (show HasFDerivAt periodOneSobolevHamiltonian L (a+(0 : ℂ) • h,b) by simpa using hL).comp_hasDerivAt 0 hd₁
  have hc₂ := (show HasFDerivAt periodOneSobolevHamiltonian L (a,b+(0 : ℂ) • k) by simpa using hL).comp_hasDerivAt 0 hd₂
  have he₁ := hc₁.unique (hasDerivAt_periodOneSobolevHamiltonian_fst a b h ha hb hh)
  have he₂ := hc₂.unique (hasDerivAt_periodOneSobolevHamiltonian_snd a b k ha hb hk)
  change L (h,k) = _
  rw [show (h,k) = (h,0)+(0,k) by simp,map_add,he₁,he₂]

/-- The physical Hamiltonian velocity has zero energy variation. -/
theorem fderiv_periodOneSobolevHamiltonian_eq_zero_of_field (a b h k : ScalarDomain 2)
    (ha : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))))
    (hb : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis b (x : AddCircle (2 : ℝ))))
    (he : ∀ x : ℝ,
      (periodOneSobolevSynthesis h (x : AddCircle (2 : ℝ)),periodOneSobolevSynthesis k (x : AddCircle (2 : ℝ))) =
        ((classicalNLSVectorField
          (fun y : ℝ => periodOneSobolevSynthesis a (y : AddCircle (2 : ℝ)))
          (fun y : ℝ => periodOneSobolevSynthesis b (y : AddCircle (2 : ℝ)))).1 x,
         (classicalNLSVectorField
          (fun y : ℝ => periodOneSobolevSynthesis a (y : AddCircle (2 : ℝ)))
          (fun y : ℝ => periodOneSobolevSynthesis b (y : AddCircle (2 : ℝ)))).2 x)) :
    (fderiv ℂ periodOneSobolevHamiltonian (a,b)) (h,k) = 0 := by
  let A := fun y : ℝ => periodOneSobolevSynthesis a (y : AddCircle (2 : ℝ))
  let B := fun y : ℝ => periodOneSobolevSynthesis b (y : AddCircle (2 : ℝ))
  have he₁ : (fun x : ℝ => periodOneSobolevSynthesis h (x : AddCircle (2 : ℝ))) =
      (classicalNLSVectorField A B).1 := funext (fun x => congrArg Prod.fst (he x))
  have he₂ : (fun x : ℝ => periodOneSobolevSynthesis k (x : AddCircle (2 : ℝ))) =
      (classicalNLSVectorField A B).2 := funext (fun x => congrArg Prod.snd (he x))
  have hh : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis h (x : AddCircle (2 : ℝ))) := by
    rw [he₁]; exact (contDiff_classicalNLSVectorField A B ha hb).1
  have hk : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis k (x : AddCircle (2 : ℝ))) := by
    rw [he₂]; exact (contDiff_classicalNLSVectorField A B ha hb).2
  rw [fderiv_periodOneSobolevHamiltonian_apply a b h k ha hb hh hk]
  have hgrad := contDiff_classicalNLSEnergyGradient A B ha hb
  have hi₁ : IntervalIntegrable (fun x : ℝ => periodOneSobolevSynthesis h (x : AddCircle (2 : ℝ)) *
      (classicalNLSEnergyGradient A B).1 x) volume 0 1 :=
    (hh.continuous.mul hgrad.1.continuous).intervalIntegrable 0 1
  have hi₂ : IntervalIntegrable (fun x : ℝ => periodOneSobolevSynthesis k (x : AddCircle (2 : ℝ)) *
      (classicalNLSEnergyGradient A B).2 x) volume 0 1 :=
    (hk.continuous.mul hgrad.2.continuous).intervalIntegrable 0 1
  rw [← intervalIntegral.integral_add hi₁ hi₂]
  have hz : (fun x : ℝ => periodOneSobolevSynthesis h (x : AddCircle (2 : ℝ)) *
      (classicalNLSEnergyGradient A B).1 x + periodOneSobolevSynthesis k (x : AddCircle (2 : ℝ)) *
      (classicalNLSEnergyGradient A B).2 x) = fun _ => 0 := by
    funext x
    rw [congrFun he₁ x,congrFun he₂ x]
    dsimp only [classicalNLSVectorField]
    ring
  change (∫ x in (0 : ℝ)..1, _) = 0
  rw [hz,intervalIntegral.integral_zero]

/-- Conservation for a local strong H¹ curve satisfying the physical pair equation.
Continuity includes the endpoints, so the conserved value does too. -/
theorem periodOneSobolevHamiltonian_eq_of_local_NLS
    {a b : ℝ} (u : ℝ → ScalarDomain 2 × ScalarDomain 2)
    (hc : ContinuousOn u (Icc a b))
    (hd : ∀ time ∈ Ioo a b, DifferentiableAt ℝ u time)
    (hs : ∀ time ∈ Ioo a b,
      ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis (u time).1 (x : AddCircle (2 : ℝ))) ∧
      ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis (u time).2 (x : AddCircle (2 : ℝ))))
    (he : ∀ time ∈ Ioo a b, ∀ x : ℝ,
      (periodOneSobolevSynthesis (deriv u time).1 (x : AddCircle (2 : ℝ)),
       periodOneSobolevSynthesis (deriv u time).2 (x : AddCircle (2 : ℝ))) =
      ((classicalNLSVectorField
        (fun y : ℝ => periodOneSobolevSynthesis (u time).1 (y : AddCircle (2 : ℝ)))
        (fun y : ℝ => periodOneSobolevSynthesis (u time).2 (y : AddCircle (2 : ℝ)))).1 x,
       (classicalNLSVectorField
        (fun y : ℝ => periodOneSobolevSynthesis (u time).1 (y : AddCircle (2 : ℝ)))
        (fun y : ℝ => periodOneSobolevSynthesis (u time).2 (y : AddCircle (2 : ℝ)))).2 x))
    {time initial : ℝ} (ht : time ∈ Icc a b) (hi : initial ∈ Icc a b) :
    periodOneSobolevHamiltonian (u time) = periodOneSobolevHamiltonian (u initial) := by
  apply FunctionalAnalysis.eq_of_hasDerivAt_zero_Icc
    (continuous_periodOneSobolevHamiltonian.comp_continuousOn hc) _ ht hi
  intro r hr
  have h := ((analyticAt_periodOneSobolevHamiltonian (u r)).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt r (hd r hr).hasDerivAt
  apply h.congr_deriv
  exact fderiv_periodOneSobolevHamiltonian_eq_zero_of_field _ _ _ _ (hs r hr).1 (hs r hr).2 (he r hr)

end NLS.ZakharovShabat
