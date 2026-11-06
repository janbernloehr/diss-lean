import NLS.KdV.MiuraCanonicalEndpoints
import NLS.KdV.HillMiuraL2Discriminant
import NLS.SequenceSpaces.OrderedPairedReflection
import NLS.ZakharovShabat.PeriodicEndpointGlobalMultiplicity

/-! Actual complex Miura periodic endpoints reflect at every signed index.
The proof uses the even physical discriminant, exact native multiplicities
and uniqueness of the original ordered L2 endpoint enumeration. -/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem periodicAlgebraicMultiplicity_hillMiuraDiagonal_neg (u : Coeff 2) (z : ℂ) :
    periodicAlgebraicMultiplicity (by norm_num) (periodOnePotential (hillMiuraDiagonal u)) (-z) =
      periodicAlgebraicMultiplicity (by norm_num) (periodOnePotential (hillMiuraDiagonal u)) z := by
  let f : ℂ → ℂ := fun w =>
    (canonicalDiscriminant (by norm_num) (periodOnePotential (hillMiuraDiagonal u)) w)^2-4
  have he : f ∘ Neg.neg = f := by
    funext w
    dsimp only [Function.comp_def,f]
    have h := hillMiuraFrequencyTrace_even u w
    change canonicalDiscriminant (by norm_num) (periodOnePotential (hillMiuraDiagonal u)) (-w) =
      canonicalDiscriminant (by norm_num) (periodOnePotential (hillMiuraDiagonal u)) w at h
    rw [h]
  have hg : AnalyticAt ℂ (fun w : ℂ => -w) z := analyticAt_id.neg
  have hd : deriv (fun w : ℂ => -w) z ≠ 0 := by
    have h : HasDerivAt (fun w : ℂ => -w) (-1) z := (hasDerivAt_id z).neg
    rw [h.deriv]
    norm_num
  have ho := analyticOrderAt_comp_of_deriv_ne_zero (f := f) hg hd
  rw [he] at ho
  dsimp only [f] at ho
  rw [analyticOrderAt_canonicalDiscriminant_sq_sub_four (by norm_num) (by norm_num)
    _ (periodOnePotential_mem _) z,
    analyticOrderAt_canonicalDiscriminant_sq_sub_four (by norm_num) (by norm_num)
    _ (periodOnePotential_mem _) (-z)] at ho
  exact_mod_cast ho.symm

/-- Both endpoint slots reflect with their order reversed, even in the central block. -/
theorem hillMiuraDiracPair_neg (u : Coeff 2) :
    (∀ n : ℤ, hillMiuraDiracLeft u (-n) = -hillMiuraDiracRight u n) ∧
      (∀ n : ℤ, hillMiuraDiracRight u (-n) = -hillMiuraDiracLeft u n) := by
  let φ := periodOnePotential (hillMiuraDiagonal u)
  have hs := canonicalPeriodicEndpoints_spec (by norm_num) (by norm_num) φ (periodOnePotential_mem _)
  apply ordered_paired_reflection_of_l2
    (hillMiuraDiracLeft u) (hillMiuraDiracRight u)
    hs.1.left_displacement hs.1.right_displacement hs.2.1 hs.2.2
  intro z
  calc
    _ = periodicAlgebraicMultiplicity (by norm_num) φ (-z) := hs.1.global_multiplicity (-z)
    _ = periodicAlgebraicMultiplicity (by norm_num) φ z :=
      periodicAlgebraicMultiplicity_hillMiuraDiagonal_neg u z
    _ = _ := (hs.1.global_multiplicity z).symm

end NLS.KdV
