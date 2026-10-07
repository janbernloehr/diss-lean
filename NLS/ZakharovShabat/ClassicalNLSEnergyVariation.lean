import NLS.ZakharovShabat.ClassicalNLSHamiltonians

/-! # First variations of the physical NLS energy

The complex directional derivatives of the actual third hierarchy
Hamiltonian are the classical variational gradients. Integration by parts
removes derivatives of the variation and fixes the PDE normalization.
-/
noncomputable section
open Set Complex MeasureTheory intervalIntegral
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The two variational gradients of the physical NLS energy. -/
def classicalNLSEnergyGradient (a b : ℝ → ℂ) : (ℝ → ℂ) × (ℝ → ℂ) :=
  (fun x => -deriv (deriv b) x + 2*a x*b x^2,
   fun x => -deriv (deriv a) x + 2*a x^2*b x)

/-- Periodic integration by parts has no boundary contribution. -/
theorem integral_deriv_mul_periodic (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) :
    (∫ x in (0 : ℝ)..1, deriv a x*b x) = -(∫ x in (0 : ℝ)..1, a x*deriv b x) := by
  have h := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    ha.continuous.continuousOn hb.continuous.continuousOn
    (fun x _ => ((contDiff_infty_iff_deriv.mp ha).1 x).hasDerivAt)
    (fun x _ => ((contDiff_infty_iff_deriv.mp hb).1 x).hasDerivAt)
    ((contDiff_infty_iff_deriv.mp ha).2.continuous.intervalIntegrable 0 1)
    ((contDiff_infty_iff_deriv.mp hb).2.continuous.intervalIntegrable 0 1)
  have henda : a 1 = a 0 := by simpa using hpa 0
  have hendb : b 1 = b 0 := by simpa using hpb 0
  have he : (∫ x in (0 : ℝ)..1, a x*deriv b x) =
      -(∫ x in (0 : ℝ)..1, deriv a x*b x) := by
    simpa only [henda,hendb,sub_self,zero_sub] using h
  rw [he,neg_neg]

/-- The physical third Hamiltonian is symmetric in its two complex fields. -/
theorem classicalNLSHamiltonian_three_comm (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) :
    classicalNLSHamiltonian a b 3 = classicalNLSHamiltonian b a 3 := by
  rw [classicalNLSHamiltonian_three a b ha hb hpa hpb,
    classicalNLSHamiltonian_three b a hb ha hpb hpa]
  apply intervalIntegral.integral_congr
  intro x _
  ring

/-- Varying the first field gives a quadratic polynomial in the complex parameter. -/
theorem classicalNLSHamiltonian_three_variation_fst (a b h : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hh : ContDiff ℝ ∞ h)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hph : Function.Periodic h 1) (z : ℂ) :
    classicalNLSHamiltonian (fun x => a x+z*h x) b 3 =
      classicalNLSHamiltonian a b 3 +
        z*(∫ x in (0 : ℝ)..1, h x*(classicalNLSEnergyGradient a b).1 x) +
        z^2*(∫ x in (0 : ℝ)..1, h x^2*b x^2) := by
  have hab : ContDiff ℝ ∞ (fun x => a x+z*h x) := ha.add (contDiff_const.mul hh)
  have hpab : Function.Periodic (fun x => a x+z*h x) 1 := by intro x; dsimp only; rw [hpa x,hph x]
  have hd (x : ℝ) : deriv (fun x => a x+z*h x) x = deriv a x+z*deriv h x := by
    exact (((contDiff_infty_iff_deriv.mp ha).1 x).hasDerivAt.add
      (((contDiff_infty_iff_deriv.mp hh).1 x).hasDerivAt.const_mul z)).deriv
  have hdb := (contDiff_infty_iff_deriv.mp hb).2
  have hda := (contDiff_infty_iff_deriv.mp ha).2
  have hdh := (contDiff_infty_iff_deriv.mp hh).2
  have hddb := (contDiff_infty_iff_deriv.mp hdb).2
  have hi₀ : IntervalIntegrable (fun x => deriv a x*deriv b x+a x^2*b x^2) volume 0 1 :=
    ((hda.continuous.mul hdb.continuous).add ((ha.continuous.pow 2).mul (hb.continuous.pow 2))).intervalIntegrable 0 1
  have hi₁ : IntervalIntegrable (fun x => deriv h x*deriv b x+2*a x*h x*b x^2) volume 0 1 :=
    ((hdh.continuous.mul hdb.continuous).add
      (((continuous_const.mul ha.continuous).mul hh.continuous).mul (hb.continuous.pow 2))).intervalIntegrable 0 1
  have hi₂ : IntervalIntegrable (fun x => h x^2*b x^2) volume 0 1 :=
    ((hh.continuous.pow 2).mul (hb.continuous.pow 2)).intervalIntegrable 0 1
  have he (x : ℝ) :
      deriv (fun x => a x+z*h x) x*deriv b x+(a x+z*h x)^2*b x^2 =
      (deriv a x*deriv b x+a x^2*b x^2)+
        z*(deriv h x*deriv b x+2*a x*h x*b x^2)+z^2*(h x^2*b x^2) := by rw [hd]; ring
  rw [classicalNLSHamiltonian_three _ b hab hb hpab hpb]
  simp_rw [he]
  rw [intervalIntegral.integral_add (hi₀.add (hi₁.const_mul z)) (hi₂.const_mul (z^2)),
    intervalIntegral.integral_add hi₀ (hi₁.const_mul z),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    ← classicalNLSHamiltonian_three a b ha hb hpa hpb]
  congr 2
  congr 1
  have hiK : IntervalIntegrable (fun x => deriv h x*deriv b x) volume 0 1 :=
    (hdh.continuous.mul hdb.continuous).intervalIntegrable 0 1
  have hiC : IntervalIntegrable (fun x => 2*a x*h x*b x^2) volume 0 1 :=
    (((continuous_const.mul ha.continuous).mul hh.continuous).mul (hb.continuous.pow 2)).intervalIntegrable 0 1
  have hiD : IntervalIntegrable (fun x => -(h x*deriv (deriv b) x)) volume 0 1 :=
    (hh.continuous.mul hddb.continuous).neg.intervalIntegrable 0 1
  rw [intervalIntegral.integral_add hiK hiC,
    integral_deriv_mul_periodic h (deriv b) hh hdb hph (periodic_deriv_of_periodic b 1 hpb),
    ← intervalIntegral.integral_neg,← intervalIntegral.integral_add hiD hiC]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp [classicalNLSEnergyGradient]
  ring

/-- The first complex directional derivative is integration against the first gradient. -/
theorem hasDerivAt_classicalNLSHamiltonian_three_fst (a b h : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hh : ContDiff ℝ ∞ h)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hph : Function.Periodic h 1) :
    HasDerivAt (fun z : ℂ => classicalNLSHamiltonian (fun x => a x+z*h x) b 3)
      (∫ x in (0 : ℝ)..1, h x*(classicalNLSEnergyGradient a b).1 x) 0 := by
  simp_rw [classicalNLSHamiltonian_three_variation_fst a b h ha hb hh hpa hpb hph]
  simpa using! ((hasDerivAt_const (0 : ℂ) (classicalNLSHamiltonian a b 3)).add
    ((hasDerivAt_id (0 : ℂ)).mul_const
      (∫ x in (0 : ℝ)..1, h x*(classicalNLSEnergyGradient a b).1 x))).add
      (((hasDerivAt_id (0 : ℂ)).pow 2).mul_const (∫ x in (0 : ℝ)..1, h x^2*b x^2))

/-- The second complex directional derivative is integration against the second gradient. -/
theorem hasDerivAt_classicalNLSHamiltonian_three_snd (a b h : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hh : ContDiff ℝ ∞ h)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hph : Function.Periodic h 1) :
    HasDerivAt (fun z : ℂ => classicalNLSHamiltonian a (fun x => b x+z*h x) 3)
      (∫ x in (0 : ℝ)..1, h x*(classicalNLSEnergyGradient a b).2 x) 0 := by
  have he (z : ℂ) : classicalNLSHamiltonian a (fun x => b x+z*h x) 3 =
      classicalNLSHamiltonian (fun x => b x+z*h x) a 3 :=
    classicalNLSHamiltonian_three_comm a _ ha (hb.add (contDiff_const.mul hh)) hpa
      (by intro x; dsimp only; rw [hpb x,hph x])
  simp_rw [he]
  convert hasDerivAt_classicalNLSHamiltonian_three_fst b a h hb ha hh hpb hpa hph using 1
  apply intervalIntegral.integral_congr
  intro x _
  dsimp [classicalNLSEnergyGradient]
  ring

end NLS.ZakharovShabat
