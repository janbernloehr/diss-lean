import NLS.KdV.SingularDirichletGeometricMultiplicity
import NLS.KdV.HminusOneDirichletSimplicity

/-! # Actual real Dirichlet chains and characteristic multiplicities

Hermitian weak forms and positive domain energy exclude nonzero associated
vectors on the complete zero-trace H1 domain. Every actual finite chain of
the native partial operator collapses to its eigenspace. Geometric uniqueness
then identifies its full algebraic root-space dimension with characteristic
order for every real source potential, including central and zero energies.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.FunctionalAnalysis

/-- The native Dirichlet inclusion has the original Hermitian weak form. -/
theorem singularDirichletDomainInclusion_hermitian (f g : UnitDirichletH1) :
    singularDirichletDomainInclusion f (unitDirichletConjugate g) =
      star (singularDirichletDomainInclusion g (unitDirichletConjugate f)) := by
  change singularHillPairing (singularHillDomainInclusion (unitDirichletOriginalH1 f))
    (unitDirichletOriginalH1 (unitDirichletConjugate g)) =
      star (singularHillPairing (singularHillDomainInclusion (unitDirichletOriginalH1 g))
        (unitDirichletOriginalH1 (unitDirichletConjugate f)))
  rw [← unitDirichletOriginalH1_conjugate, ← unitDirichletOriginalH1_conjugate]
  exact singularHillDomainInclusion_hermitian _ _

/-- Every native real singular potential has the Hermitian Dirichlet form. -/
theorem singularDirichletOperator_hermitian
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (hq : q.val = q.val.conjugate)
    (f g : UnitDirichletH1) :
    singularDirichletOperator q f (unitDirichletConjugate g) =
      star (singularDirichletOperator q g (unitDirichletConjugate f)) := by
  change singularHillPairing (singularHillOperator q (unitDirichletOriginalH1 f))
    (unitDirichletOriginalH1 (unitDirichletConjugate g)) =
      star (singularHillPairing (singularHillOperator q (unitDirichletOriginalH1 g))
        (unitDirichletOriginalH1 (unitDirichletConjugate f)))
  rw [← unitDirichletOriginalH1_conjugate, ← unitDirichletOriginalH1_conjugate]
  exact singularHillOperator_hermitian q hq _ _

/-- The true native pencil annihilates the weak pairing with its own eigenvector. -/
theorem singularDirichletPencil_pair_eigenvector
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (hq : q.val = q.val.conjugate)
    (lambda : ℂ) (f g : UnitDirichletH1) (hf : f ≠ 0)
    (he : singularDirichletOperator q f = lambda • singularDirichletDomainInclusion f) :
    singularDirichletPencil q lambda g (unitDirichletConjugate f) = 0 := by
  have hl := singularDirichlet_eigenvalue_im_eq_zero q hq lambda f hf he
  have hstar : star lambda = lambda := by
    apply Complex.ext
    · simp only [Complex.star_def, Complex.conj_re]
    · simp only [Complex.star_def, Complex.conj_im, hl, neg_zero]
  have ht : singularDirichletOperator q f (unitDirichletConjugate g) =
      lambda*singularDirichletDomainInclusion f (unitDirichletConjugate g) :=
    congrArg (fun F : UnitDirichletHminus => F (unitDirichletConjugate g)) he
  change lambda*singularDirichletDomainInclusion g (unitDirichletConjugate f)-
    singularDirichletOperator q g (unitDirichletConjugate f) = 0
  rw [singularDirichletOperator_hermitian q hq g f, ht, star_mul, hstar,
    ← singularDirichletDomainInclusion_hermitian g f]
  ring

/-- A nonzero actual native eigenvector has no native associated vector. -/
theorem singularDirichlet_no_associated_vector
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (hq : q.val = q.val.conjugate)
    (lambda : ℂ) (f : UnitDirichletH1) (hf : f ≠ 0)
    (he : singularDirichletOperator q f = lambda • singularDirichletDomainInclusion f)
    (g : UnitDirichletH1) :
    singularDirichletPencil q lambda g ≠ singularDirichletDomainInclusion f := by
  intro hg
  have hz := singularDirichletPencil_pair_eigenvector q hq lambda f g hf he
  rw [hg] at hz
  have hp := singularDirichletDomainInclusion_energy_pos f hf
  rw [hz, Complex.zero_re] at hp
  exact lt_irrefl 0 hp

/-- Every actual finite chain of the real native partial operator is an eigenvector. -/
theorem singularDirichletRootSpace_le_one_of_real
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (hq : q.val = q.val.conjugate)
    (lambda : ℂ) (n : ℕ) :
    singularDirichletRootSpace q lambda n ≤ singularDirichletRootSpace q lambda 1 := by
  apply pencilRootSpace_le_one_of_no_associated
  intro f g hf hg
  by_contra hn
  exact singularDirichlet_no_associated_vector q hq lambda f hn
    ((singularDirichletPencil_eq_zero_iff q lambda f).mp hf) g hg

/-- The full actual algebraic root space of a real native potential is its eigenspace. -/
theorem singularDirichletRootSpaceTop_eq_one_of_real
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (hq : q.val = q.val.conjugate) (lambda : ℂ) :
    singularDirichletRootSpaceTop q lambda = singularDirichletRootSpace q lambda 1 := by
  apply pencilRootSpaceTop_eq_one_of_no_associated
  intro f g hf hg
  by_contra hn
  exact singularDirichlet_no_associated_vector q hq lambda f hn
    ((singularDirichletPencil_eq_zero_iff q lambda f).mp hf) g hg

/-- The complete actual algebraic root space is finite dimensional for every
real original source potential, with no assumed resolvent or root enumeration. -/
theorem finiteDimensional_singularDirichletRootSpaceTop_of_real
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (lambda : ℂ) :
    FiniteDimensional ℂ (singularDirichletRootSpaceTop (periodOneOriginal q) lambda) := by
  rw [singularDirichletRootSpaceTop_eq_one_of_real (periodOneOriginal q)
    ((periodOneOriginal_real_iff q).mpr hq)]
  let := finiteDimensional_singularDirichletEigenspace q lambda
  exact (singularDirichletEigenspaceRootEquiv (periodOneOriginal q) lambda).finiteDimensional

/-- Full actual algebraic root multiplicity is one precisely at a real-potential
characteristic zero, including ALL energies and central indices. -/
theorem finrank_singularDirichletRootSpaceTop_of_real
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (lambda : ℂ) :
    Module.finrank ℂ (singularDirichletRootSpaceTop (periodOneOriginal q) lambda) =
      if hillHminusDirichlet q lambda = 0 then 1 else 0 := by
  rw [singularDirichletRootSpaceTop_eq_one_of_real (periodOneOriginal q)
    ((periodOneOriginal_real_iff q).mpr hq),
    ← (singularDirichletEigenspaceRootEquiv (periodOneOriginal q) lambda).finrank_eq]
  exact finrank_singularDirichletEigenspace q lambda

/-- The actual native algebraic root-space dimension equals normalized
characteristic order for EVERY energy of EVERY real original source potential. -/
theorem finrank_singularDirichletRootSpaceTop_eq_analyticOrder_of_real
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (lambda : ℂ) :
    Module.finrank ℂ (singularDirichletRootSpaceTop (periodOneOriginal q) lambda) =
      analyticOrderNatAt (hillHminusDirichlet q) lambda := by
  rw [finrank_singularDirichletRootSpaceTop_of_real q hq lambda]
  by_cases hd : hillHminusDirichlet q lambda = 0
  · rw [if_pos hd, analyticOrderNatAt_hillHminusDirichlet_eq_one_of_real q hq lambda hd]
  · rw [if_neg hd, analyticOrderNatAt,
      analyticOrderAt_eq_zero.mpr (Or.inr hd), ENat.toNat_zero]

end NLS.KdV
