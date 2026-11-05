import NLS.KdV.HillPhysical
import NLS.ZakharovShabat.Operator
import NLS.ZakharovShabat.PeriodicSpectrum

/-! # Literal constant-upper first-order reduction of the L2 Hill equation

The coefficient potential is `(-1,-q)`. Eliminating its second component
gives exactly the Hill symbol `pi^2*k^2` and energy `z^2`. The proved Hill
regularization places the recovered scalar vector in the actual H2 domain.
This is a specific operator comparison, not a reuse of a ZS spectral claim
without identifying the physical Hill operator.
-/

noncomputable section
open scoped ENNReal
open NLS.ZakharovShabat
namespace NLS.KdV

def hillFirstOrderPotential (q : Coeff 2) : PairSpace 2 := (lp.single 2 0 (-1), -q)

theorem hillFirstOrder_operator_fst_apply (q : Coeff 2) (a : Domain 2) (k : ℤ) :
    (operator (by simp) (hillFirstOrderPotential q) a).1 k =
      -(Real.pi : ℂ)*k*a.1.val k-a.2.val k := by
  rw [operator_fst_apply]
  change -(Real.pi : ℂ)*k*a.1.val k+
    (∑' j : ℤ, (lp.single 2 0 (-1) : Coeff 2) (k-j)*a.2.val j) = _
  have ht (j : ℤ) : (lp.single 2 0 (-1) : Coeff 2) (k-j)*a.2.val j =
      if j = k then -a.2.val j else 0 := by
    by_cases hj : j = k
    · subst j
      simp [lp.single_apply]
    · have hk : k-j ≠ 0 := sub_ne_zero.mpr (Ne.symm hj)
      simp [lp.single_apply, hj, hk]
  simp only [ht]
  simp only [tsum_ite_eq, sub_eq_add_neg]

theorem hillFirstOrder_operator_snd_apply (q : Coeff 2) (a : Domain 2) (k : ℤ) :
    (operator (by simp) (hillFirstOrderPotential q) a).2 k =
      (Real.pi : ℂ)*k*a.2.val k-
        Coeff.convolution q (WeightedCoeff.sobolevToL1CLM 2 (by simp) a.1) k := by
  simp only [operator_snd_apply, hillFirstOrderPotential, lp.coeFn_neg, Pi.neg_apply,
    neg_mul, tsum_neg, Coeff.convolution_apply, WeightedCoeff.sobolevToL1CLM_apply, sub_eq_add_neg]

theorem hillFirstOrder_eigen_equations (q : Coeff 2) (z : ℂ) (a : Domain 2)
    (he : operator (by simp) (hillFirstOrderPotential q) a = z • domainInclusion a) :
    (∀ k : ℤ, -(Real.pi : ℂ)*k*a.1.val k-a.2.val k = z*a.1.val k) ∧
    (∀ k : ℤ, (Real.pi : ℂ)*k*a.2.val k-
      Coeff.convolution q (WeightedCoeff.sobolevToL1CLM 2 (by simp) a.1) k = z*a.2.val k) := by
  constructor
  · intro k
    have h := congrArg (fun b : PairSpace 2 => b.1 k) he
    simpa only [hillFirstOrder_operator_fst_apply, domainInclusion_apply, Prod.smul_fst,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, scalarInclusion_apply] using h
  · intro k
    have h := congrArg (fun b : PairSpace 2 => b.2 k) he
    simpa only [hillFirstOrder_operator_snd_apply, domainInclusion_apply, Prod.smul_snd,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, scalarInclusion_apply] using h

theorem hillFirstOrder_scalar_equation (q : Coeff 2) (z : ℂ) (a : Domain 2)
    (he : operator (by simp) (hillFirstOrderPotential q) a = z • domainInclusion a) (k : ℤ) :
    (z^2-(freeHillValue k : ℂ))*a.1.val k =
      Coeff.convolution q (WeightedCoeff.sobolevToL1CLM 2 (by simp) a.1) k := by
  have hf := (hillFirstOrder_eigen_equations q z a he).1 k
  have hs := (hillFirstOrder_eigen_equations q z a he).2 k
  unfold freeHillValue
  push_cast
  linear_combination ((Real.pi : ℂ)*k-z)*hf+hs

/-- Every nonzero eigenvector of the identified first-order operator
produces a nonzero H2 eigenvector of the actual Hill operator. -/
theorem exists_hillEigenvector_of_firstOrder
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (z : ℂ) (a : Domain 2) (ha : a ≠ 0)
    (he : operator (by simp) (hillFirstOrderPotential (SpectralWeight.one.toCoeff q)) a =
      z • domainInclusion a) :
    ∃ f : HillSobolevDomain, f ≠ 0 ∧
      hillOperator (SpectralWeight.one.toCoeff q) f = z^2 • hillDomainToL2 f := by
  let F : WeightedCoeff SpectralWeight.one.toWeight 1 :=
    (WeightedCoeff.weightIsometry SpectralWeight.one.toWeight 1).symm
      (WeightedCoeff.sobolevToL1CLM 2 (by simp) a.1)
  have hF (k : ℤ) : F.val k = a.1.val k := by
    change (WeightedCoeff.sobolevToL1CLM 2 (by simp) a.1) k/(SpectralWeight.one k : ℂ) = _
    simp
  have hspec : IsHillFourierEigenvector SpectralWeight.one q (z^2) F := by
    intro k
    have hk := hillFirstOrder_scalar_equation (SpectralWeight.one.toCoeff q) z a he k
    simpa only [hF, SpectralWeight.convolution_apply, Coeff.convolution_apply,
      SpectralWeight.toCoeff_apply, WeightedCoeff.sobolevToL1CLM_apply] using hk
  have hne : F ≠ 0 := by
    intro hz
    have hz1 (k : ℤ) : a.1.val k = 0 := by
      have h := congrArg (fun b : WeightedCoeff SpectralWeight.one.toWeight 1 => b.val k) hz
      simpa only [hF, WeightedCoeff.zero_val] using h
    have hz2 (k : ℤ) : a.2.val k = 0 := by
      have h := (hillFirstOrder_eigen_equations _ z a he).1 k
      rw [hz1 k] at h
      simpa using h
    apply ha
    apply Prod.ext
    · apply Subtype.ext
      funext k
      exact hz1 k
    · apply Subtype.ext
      funext k
      exact hz2 k
  refine ⟨hillEigenvectorLift q (z^2) F hspec, ?_, (hillOperator_eigen_iff q (z^2) _).mpr ?_⟩
  · intro hz
    have h := congrArg hillDomainAsSummable hz
    simp only [hillDomainAsSummable_eigenvectorLift, map_zero] at h
    exact hne h
  · simpa only [hillDomainAsSummable_eigenvectorLift] using hspec

/-- Recover the second first-order coordinate from an actual H2 scalar vector. -/
def hillFirstOrderLift (z : ℂ) : HillSobolevDomain →L[ℂ] Domain 2 :=
  hillDomainToH1.prod (Complex.I • hillFirstDerivative-z • hillDomainToH1)

@[simp] theorem hillFirstOrderLift_fst_apply (z : ℂ) (f : HillSobolevDomain) (k : ℤ) :
    (hillFirstOrderLift z f).1.val k = f.val k := by
  simp [hillFirstOrderLift, hillDomainToH1]

@[simp] theorem hillFirstOrderLift_snd_apply (z : ℂ) (f : HillSobolevDomain) (k : ℤ) :
    (hillFirstOrderLift z f).2.val k = -((Real.pi : ℂ)*k+z)*f.val k := by
  change Complex.I*(Complex.I*(Real.pi : ℂ)*k*f.val k)-z*(hillDomainToH1 f).val k = _
  simp only [hillDomainToH1, WeightedCoeff.sobolevInclusion_apply]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem hillFirstOrderLift_injective (z : ℂ) : Function.Injective (hillFirstOrderLift z) := by
  intro f g he
  apply Subtype.ext
  funext k
  simpa only [hillFirstOrderLift_fst_apply] using
    congrArg (fun a : Domain 2 => a.1.val k) he

theorem hillFirstOrderLift_eigen (q : Coeff 2) (z : ℂ) (f : HillSobolevDomain)
    (he : hillOperator q f = z^2 • hillDomainToL2 f) :
    operator (by simp) (hillFirstOrderPotential q) (hillFirstOrderLift z f) =
      z • domainInclusion (hillFirstOrderLift z f) := by
  apply Prod.ext
  · ext k
    simp only [hillFirstOrder_operator_fst_apply, hillFirstOrderLift_fst_apply,
      hillFirstOrderLift_snd_apply, domainInclusion_apply, Prod.smul_fst,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, scalarInclusion_apply]
    ring
  · ext k
    simp only [hillFirstOrder_operator_snd_apply, hillFirstOrderLift_fst_apply,
      hillFirstOrderLift_snd_apply, domainInclusion_apply, Prod.smul_snd,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, scalarInclusion_apply,
      Coeff.convolution_apply, WeightedCoeff.sobolevToL1CLM_apply]
    have h := congrArg (fun b : Coeff 2 => b k) he
    simp only [hillOperator_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      hillDomainToL2_apply, freeHillValue] at h
    push_cast at h
    linear_combination -h

/-- Exact eigenvector existence equivalence for arbitrary complex L2 Hill potentials. -/
theorem hill_eigenvector_iff_firstOrder
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (z : ℂ) :
    (∃ f : HillSobolevDomain, f ≠ 0 ∧
      hillOperator (SpectralWeight.one.toCoeff q) f = z^2 • hillDomainToL2 f) ↔
    ∃ a : Domain 2, a ≠ 0 ∧ operator (by simp)
      (hillFirstOrderPotential (SpectralWeight.one.toCoeff q)) a = z • domainInclusion a := by
  constructor
  · rintro ⟨f, hf, he⟩
    refine ⟨hillFirstOrderLift z f, ?_, hillFirstOrderLift_eigen _ z f he⟩
    exact fun hz => hf (hillFirstOrderLift_injective z (hz.trans (map_zero _).symm))
  · rintro ⟨a, ha, he⟩
    exact exists_hillEigenvector_of_firstOrder q z a ha he

/-- The actual Hill H2 eigenvalue condition is the proved first-order
periodic spectral condition for this specific potential and square energy. -/
theorem hill_eigenvector_iff_firstOrder_spectrum
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (z : ℂ) :
    (∃ f : HillSobolevDomain, f ≠ 0 ∧
      hillOperator (SpectralWeight.one.toCoeff q) f = z^2 • hillDomainToL2 f) ↔
      z ∈ periodicSpectrum (by simp) (hillFirstOrderPotential (SpectralWeight.one.toCoeff q)) := by
  rw [mem_periodicSpectrum_iff_exists_eigenvector]
  exact hill_eigenvector_iff_firstOrder q z

end NLS.KdV
