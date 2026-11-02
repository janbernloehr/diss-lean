import NLS.ZakharovShabat.NLSEvenHamiltonianReducedPolynomial
import NLS.ZakharovShabat.SobolevHierarchySymmetries
import NLS.ZakharovShabat.SobolevPolynomialVariation

/-! # Even physical Hamiltonians on the sharp complex Sobolev scale

The integral of the reduced L² density defines H_(2m) on H^m. This is an
analytic extension of the original physical Hamiltonian on all complex
pairs, before any diagonal restriction. Its uniqueness and compatibility
with the existing higher-regularity hierarchy are proved by smooth density.
-/
noncomputable section
open NLS.Fourier NLS.DifferentialPolynomial Set MeasureTheory Complex
open scoped ContDiff
namespace NLS.ZakharovShabat

def nlsEvenReducedPolynomial (m : ℕ) (hm : 1 ≤ m) : DifferentialPolynomial.Polynomial :=
  Classical.choose (exists_classicalNLSHamiltonian_even_reduced_polynomial m hm)

theorem nlsEvenReducedPolynomial_order (m : ℕ) (hm : 1 ≤ m) :
    JetOrderLE (nlsEvenReducedPolynomial m hm) m :=
  (Classical.choose_spec (exists_classicalNLSHamiltonian_even_reduced_polynomial m hm)).1

theorem nlsEvenReducedPolynomial_derivativeOrder (m : ℕ) (hm : 1 ≤ m) :
    DerivativeOrderLE (nlsEvenReducedPolynomial m hm) (2*(m : ℤ)-1) :=
  (Classical.choose_spec (exists_classicalNLSHamiltonian_even_reduced_polynomial m hm)).2.1

theorem nlsEvenReducedPolynomial_classical (m : ℕ) (hm : 1 ≤ m)
    (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) :
    classicalNLSHamiltonian a b (2*m) =
      ∫ x in (0 : ℝ)..1, evaluate a b (nlsEvenReducedPolynomial m hm) x :=
  (Classical.choose_spec (exists_classicalNLSHamiltonian_even_reduced_polynomial m hm)).2.2
    a b ha hb hpa hpb

/-- The actual bounded physical integral of the reduced L² density. -/
def sobolevEvenHamiltonian (m : ℕ) (hm : 1 ≤ m) (ab : SobolevSource m) : ℂ :=
  sobolevPolynomialL2Mean m (nlsEvenReducedPolynomial m hm) ab

theorem analyticAt_sobolevEvenHamiltonian (m : ℕ) (hm : 1 ≤ m) (ab : SobolevSource m) :
    AnalyticAt ℂ (sobolevEvenHamiltonian m hm) ab :=
  analyticAt_sobolevPolynomialL2Mean m _ ab

theorem continuous_sobolevEvenHamiltonian (m : ℕ) (hm : 1 ≤ m) :
    Continuous (sobolevEvenHamiltonian m hm) :=
  continuous_iff_continuousAt.mpr fun ab => (analyticAt_sobolevEvenHamiltonian m hm ab).continuousAt

theorem sobolevEvenHamiltonian_eq_classical (m : ℕ) (hm : 1 ≤ m)
    (ab : SobolevSource m) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j) :
    sobolevEvenHamiltonian m hm ab = classicalNLSHamiltonian a b (2*m) := by
  rw [nlsEvenReducedPolynomial_classical m hm a b ha hb hpa hpb]
  exact sobolevPolynomialL2Mean_eq_classical m hm _
    (nlsEvenReducedPolynomial_derivativeOrder m hm) (nlsEvenReducedPolynomial_order m hm)
    ab a b ha hb hpa hpb haq hbq

/-- The full endpoint Fréchet derivative is represented by the bounded
physical partial-jet covector, on every complex H^m pair. -/
theorem fderiv_sobolevEvenHamiltonian_eq_covector (m : ℕ) (hm : 1 ≤ m)
    (ab : SobolevSource m) :
    fderiv ℂ (sobolevEvenHamiltonian m hm) ab =
      sobolevPolynomialCovector m (nlsEvenReducedPolynomial m hm) ab :=
  fderiv_sobolevPolynomialL2Mean m hm _ (nlsEvenReducedPolynomial_derivativeOrder m hm)
    (nlsEvenReducedPolynomial_order m hm) ab

/-- Smooth agreement determines the extension on the entire complex H^m domain. -/
theorem sobolevEvenHamiltonian_unique_continuous (m : ℕ) (hm : 1 ≤ m)
    (F : SobolevSource m → ℂ) (hF : Continuous F)
    (hclassical : ∀ (ab : SobolevSource m) (a b : ℝ → ℂ),
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b → Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) → F ab = classicalNLSHamiltonian a b (2*m)) :
    F = sobolevEvenHamiltonian m hm := by
  apply eq_of_continuous_of_smooth_sobolevSource m F _ hF (continuous_sobolevEvenHamiltonian m hm)
  intro ab a b ha hb hpa hpb haq hbq
  exact (hclassical ab a b ha hb hpa hpb haq hbq).trans
    (sobolevEvenHamiltonian_eq_classical m hm ab a b ha hb hpa hpb haq hbq).symm

/-- The new endpoint construction extends the existing physical hierarchy
without changing its value on any original higher-regularity input. -/
theorem sobolevEvenHamiltonian_eq_original (m : ℕ) (hm : 1 ≤ m) (s : ℕ)
    (hk : 2*m ≤ s+1) (ab : SobolevSource s) :
    sobolevEvenHamiltonian m hm
      (hierarchySobolevInclusion s m (by omega) ab.1,
        hierarchySobolevInclusion s m (by omega) ab.2) =
      sobolevNLSHamiltonian s ab (2*m) hk := by
  have he := eq_of_continuous_of_smooth_sobolevSource s
    (fun cd => sobolevEvenHamiltonian m hm
      (hierarchySobolevInclusion s m (by omega) cd.1,
        hierarchySobolevInclusion s m (by omega) cd.2))
    (fun cd => sobolevNLSHamiltonian s cd (2*m) hk)
    ((continuous_sobolevEvenHamiltonian m hm).comp
      (((hierarchySobolevInclusion s m (by omega)).continuous.comp continuous_fst).prodMk
        ((hierarchySobolevInclusion s m (by omega)).continuous.comp continuous_snd)))
    (continuous_sobolevNLSHamiltonian s (2*m) hk) (by
      intro cd a b ha hb hpa hpb haq hbq
      rw [sobolevEvenHamiltonian_eq_classical m hm _ a b ha hb hpa hpb
        (fun j => by simpa only [hierarchySobolevInclusion_apply] using haq j)
        (fun j => by simpa only [hierarchySobolevInclusion_apply] using hbq j),
        sobolevNLSHamiltonian_eq_classical s cd a b ha hb hpa hpb haq hbq])
  exact congrFun he ab

/-- Component exchange is antisymmetric at every even order on complex H^m. -/
theorem sobolevEvenHamiltonian_swap (m : ℕ) (hm : 1 ≤ m) (ab : SobolevSource m) :
    sobolevEvenHamiltonian m hm (ab.2,ab.1) = -sobolevEvenHamiltonian m hm ab := by
  have he := eq_of_continuous_of_smooth_sobolevSource m
    (fun cd => sobolevEvenHamiltonian m hm (cd.2,cd.1))
    (fun cd => -sobolevEvenHamiltonian m hm cd)
    ((continuous_sobolevEvenHamiltonian m hm).comp (continuous_snd.prodMk continuous_fst))
    (continuous_sobolevEvenHamiltonian m hm).neg (by
      intro cd a b ha hb hpa hpb haq hbq
      rw [sobolevEvenHamiltonian_eq_classical m hm _ b a hb ha hpb hpa hbq haq,
        sobolevEvenHamiltonian_eq_classical m hm cd a b ha hb hpa hpb haq hbq]
      have hs := classicalNLSHamiltonian_signedSwap a b ha hb hpa hpb (2*m-1)
      have hn : classicalNLSHamiltonian (-b) (-a) (2*m) = classicalNLSHamiltonian b a (2*m) := by
        simpa only [neg_one_smul, neg_neg] using
          classicalNLSHamiltonian_field_rescaling (-b) a (-1) (2*m)
      have hp : (-1 : ℂ)^(2*m-1) = -1 := by
        obtain ⟨r,rfl⟩ : ∃ r, m = r+1 := ⟨m-1, by omega⟩
        rw [show 2*(r+1)-1 = 2*r+1 by omega, pow_succ, pow_mul,
          neg_one_sq, one_pow, one_mul]
      simpa only [show 2*m-1+1 = 2*m by omega, hn, hp, neg_one_mul] using hs)
  exact congrFun he ab

end NLS.ZakharovShabat
