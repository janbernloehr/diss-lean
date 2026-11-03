import NLS.KdV.SingularHillMiuraPeriodOne
import NLS.KdV.SingularHillConstantShift
import NLS.SequenceSpaces.PeriodOneMiuraRealLift
import NLS.ZakharovShabat.FiniteDiscriminant

/-!
# The full physical characteristic divisor for real H-minus-one potentials

A real shifted Miura lift identifies the unchanged full-domain physical
Hill multiplicity with a fixed real-type Dirac multiplicity. The shift can
avoid zero frequency at any prescribed energy, so analytic order transport
also covers zero energy and multiple characteristic roots.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.KdV
open NLS.ZakharovShabat

/-- The entire even Miura frequency trace descends exactly under squaring. -/
theorem hillMiuraL2Discriminant_sq (u : Coeff 2) (z : ℂ) :
    hillMiuraL2Discriminant u (z^2) = hillMiuraFrequencyTrace u z := by
  rcases eq_or_eq_neg_of_sq_eq_sq (Complex.sqrt (z^2)) z
    (ComplexAnalysis.complex_sqrt_sq (z^2)) with h | h
  · rw [hillMiuraL2Discriminant,h]
  · rw [hillMiuraL2Discriminant,h,hillMiuraFrequencyTrace_even]

/-- The literal shifted Miura image identifies the entire physical trace
with the fixed Dirac trace after translating and squaring the parameter. -/
theorem hillHminusDiscriminant_shifted_miura_square (q : PeriodOneHminusOne)
    (u : Coeff 2) (c z : ℂ)
    (himage : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c)) :
    hillHminusDiscriminant q (z^2-c) =
      canonicalDiscriminant (by norm_num) (periodOnePotential (hillMiuraDiagonal u)) z := by
  rw [hillHminusDiscriminant_eq_miura_of_shifted_image q u c (z^2-c) himage,
    sub_add_cancel,hillMiuraL2Discriminant_sq]
  rfl

/-- For every real H-minus-one potential and every complex energy, the
analytic characteristic order is the ACTUAL full-domain physical algebraic
multiplicity. No endpoint regularity or nonzero-energy hypothesis is used. -/
theorem analyticOrderAt_hillHminusDiscriminant_eq_physicalMultiplicity
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (lambda : ℂ) :
    analyticOrderAt (fun w => hillHminusDiscriminant q w ^ 2-4) lambda =
      (singularHillAlgebraicMultiplicity (periodOneOriginal q) lambda : ℕ∞) := by
  obtain ⟨c,_,u,himage,havoid⟩ := exists_real_periodOneMiura_shift_avoiding q hq lambda
  obtain ⟨z,hsq⟩ := IsAlgClosed.exists_pow_nat_eq (lambda+(c:ℂ)^2) (by norm_num : 0 < 2)
  have hz : z ≠ 0 := by
    intro he
    apply havoid
    simpa only [he,zero_pow (by norm_num : 2 ≠ 0)] using hsq.symm
  let U := Coeff.periodDouble u.val
  have hpot : singularHillMiuraPotential U =
      periodOneOriginal q+l2OriginalHminus (lp.single 2 0 ((c:ℂ)^2)) := by
    calc
      _ = periodOneOriginal (periodOneMiura u.val) := singularHillMiuraPotential_periodDouble u.val
      _ = _ := (congrArg periodOneOriginal himage).trans (periodOneOriginal_add_constant q _)
  have hmult : singularHillAlgebraicMultiplicity (periodOneOriginal q) lambda =
      periodicAlgebraicMultiplicity (by norm_num) (U,U) z := by
    calc
      _ = singularHillAlgebraicMultiplicity
          (periodOneOriginal q+l2OriginalHminus (lp.single 2 0 ((c:ℂ)^2)))
          (lambda+(c:ℂ)^2) := (singularHillAlgebraicMultiplicity_add_constant _ _ _).symm
      _ = singularHillAlgebraicMultiplicity (singularHillMiuraPotential U) (z^2) := by rw [hpot,hsq]
      _ = _ := singularHillAlgebraicMultiplicity_miura_dirac U (periodDouble_realType_diagonal u) z hz
  let g : ℂ → ℂ := fun w => w^2-(c:ℂ)^2
  have hg : AnalyticAt ℂ g z := (analyticAt_id.pow 2).sub analyticAt_const
  have hd : HasDerivAt g (2*z) z := by
    simpa [g] using! ((hasDerivAt_id z).pow 2).sub_const ((c:ℂ)^2)
  have hdn : deriv g z ≠ 0 := by
    rw [hd.deriv]
    exact mul_ne_zero (by norm_num) hz
  have hgvalue : g z = lambda := by dsimp [g]; rw [hsq]; ring
  have hphi : periodOnePotential (hillMiuraDiagonal u.val) = (U,U) := by
    rw [periodOnePotential_apply,hillMiuraDiagonal_fst,hillMiuraDiagonal_snd]
  have hfun : (fun w => hillHminusDiscriminant q w ^ 2-4) ∘ g =
      fun w => canonicalDiscriminant (by norm_num) (periodOnePotential (hillMiuraDiagonal u.val)) w ^ 2-4 := by
    funext w
    change hillHminusDiscriminant q (w^2-(c:ℂ)^2) ^ 2-4 = _
    rw [hillHminusDiscriminant_shifted_miura_square q u.val ((c:ℂ)^2) w himage]
  have ho := analyticOrderAt_comp_of_deriv_ne_zero
    (f := fun w => hillHminusDiscriminant q w ^ 2-4) hg hdn
  rw [hgvalue,hfun] at ho
  rw [← ho,analyticOrderAt_canonicalDiscriminant_sq_sub_four (by norm_num) (by norm_num)
    _ (periodOnePotential_mem (hillMiuraDiagonal u.val)),hphi,hmult]

/-- The same full-domain divisor identity in natural-number order notation. -/
theorem analyticOrderNatAt_hillHminusDiscriminant_eq_physicalMultiplicity
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (lambda : ℂ) :
    analyticOrderNatAt (fun w => hillHminusDiscriminant q w ^ 2-4) lambda =
      singularHillAlgebraicMultiplicity (periodOneOriginal q) lambda := by
  have he := congrArg ENat.toNat
    (analyticOrderAt_hillHminusDiscriminant_eq_physicalMultiplicity q hq lambda)
  simpa only [analyticOrderNatAt,ENat.toNat_natCast] using he

end NLS.KdV
