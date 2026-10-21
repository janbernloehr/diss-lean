import NLS.ZakharovShabat.ConstantPeriodicSpectrum
import NLS.ZakharovShabat.PeriodOneEmbedding

noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Opposite period-one modes give an original source with a translated constant spectrum. -/
def sourcePlaneWave (n : ℤ) (a b : ℂ) : CoeffPair p :=
  WithLp.toLp p (lp.single p (-n) a, lp.single p n b)

omit [Fact (1 ≤ p)] in
@[simp] theorem sourcePlaneWave_fst (n j : ℤ) (a b : ℂ) :
    (sourcePlaneWave (p := p) n a b).fst j = if j = -n then a else 0 := by
  simp [sourcePlaneWave, lp.single_apply, Pi.single_apply]

omit [Fact (1 ≤ p)] in
@[simp] theorem sourcePlaneWave_snd (n j : ℤ) (a b : ℂ) :
    (sourcePlaneWave (p := p) n a b).snd j = if j = n then b else 0 := by
  simp [sourcePlaneWave, lp.single_apply, Pi.single_apply]

private theorem periodDouble_single (n : ℤ) (a : ℂ) :
    Coeff.periodDouble (lp.single p n a) = lp.single p (2*n) a := by
  ext k
  by_cases hk : k % 2 = 0
  · have he : k = 2*(k/2) := by omega
    rw [he, Coeff.periodDouble_even]
    simp [lp.single_apply, Pi.single_apply]
  · have he : k = 2*(k/2)+1 := by omega
    rw [he, Coeff.periodDouble_odd]
    simp [lp.single_apply, show 2*(k/2)+1 ≠ 2*n by omega]

@[simp] theorem periodOnePotential_sourcePlaneWave (n : ℤ) (a b : ℂ) :
    periodOnePotential (sourcePlaneWave (p := p) n a b) =
      (lp.single p (-2*n) a, lp.single p (2*n) b) := by
  change (Coeff.periodDouble (lp.single p (-n) a), Coeff.periodDouble (lp.single p n b)) = _
  rw [periodDouble_single, periodDouble_single]
  congr 2
  ring

theorem operator_sourcePlaneWave_fst (hp : p ≠ ⊤) (n : ℤ) (a b : ℂ)
    (f : Domain p) (j : ℤ) :
    (operator hp (periodOnePotential (sourcePlaneWave n a b)) f).1 j =
      -(Real.pi:ℂ)*j*f.1.val j + a*f.2.val (j+2*n) := by
  rw [operator_fst_apply, periodOnePotential_sourcePlaneWave]
  simp [lp.single_apply, Pi.single_apply, ite_mul, sub_eq_iff_eq_add,
    show ∀ k : ℤ, j = -(2*n)+k ↔ k=j+2*n from fun k => by omega]

theorem operator_sourcePlaneWave_snd (hp : p ≠ ⊤) (n : ℤ) (a b : ℂ)
    (f : Domain p) (j : ℤ) :
    (operator hp (periodOnePotential (sourcePlaneWave n a b)) f).2 j =
      (Real.pi:ℂ)*j*f.2.val j + b*f.1.val (j-2*n) := by
  rw [operator_snd_apply, periodOnePotential_sourcePlaneWave]
  simp [lp.single_apply, Pi.single_apply, ite_mul, sub_eq_iff_eq_add,
    show ∀ k : ℤ, j = 2*n+k ↔ k=j-2*n from fun k => by omega]

/-- The original operator has a two-mode eigenvector at every translated constant root. -/
theorem sourcePlaneWave_mem_spectrum_of_equation (hp : p ≠ ⊤)
    (n k : ℤ) (a b z : ℂ) (ha : a ≠ 0)
    (hz : (z-(Real.pi:ℂ)*n)^2 = ((Real.pi:ℂ)*k)^2+a*b) :
    z ∈ periodicSpectrum hp (periodOnePotential (sourcePlaneWave n a b)) := by
  let f : Domain p := (scalarMode (k-n) a, scalarMode (k+n) (z+(Real.pi:ℂ)*(k-n)))
  apply (mem_periodicSpectrum_iff_exists_eigenvector hp _ z).mpr
  refine ⟨f,?_,?_⟩
  · intro hf
    have h := congrArg (fun u : Domain p => u.1.val (k-n)) hf
    simp [f,ha] at h
  · apply Prod.ext <;> ext j
    · simp only [Prod.smul_fst, lp.coeFn_smul, Pi.smul_apply,
        smul_eq_mul, domainInclusion_apply, scalarInclusion_apply]
      change (operator hp (periodOnePotential (sourcePlaneWave n a b)) f).1 j = z*f.1.val j
      rw [operator_sourcePlaneWave_fst]
      have he : j+2*n=k+n ↔ j=k-n := by omega
      by_cases hj : j=k-n
      · subst j
        simp only [f,scalarMode_apply,ite_true,show k-n+2*n=k+n by omega,Int.cast_sub]
        ring
      · simp [f,scalarMode_apply,hj,he]
    · simp only [Prod.smul_snd, lp.coeFn_smul, Pi.smul_apply,
        smul_eq_mul, domainInclusion_apply, scalarInclusion_apply]
      change (operator hp (periodOnePotential (sourcePlaneWave n a b)) f).2 j = z*f.2.val j
      rw [operator_sourcePlaneWave_snd]
      have he : j-2*n=k-n ↔ j=k+n := by omega
      by_cases hj : j=k+n
      · subst j
        simp only [f,scalarMode_apply,ite_true,show k+n-2*n=k-n by omega,Int.cast_add]
        linear_combination -hz
      · simp [f,scalarMode_apply,hj,he]

/-- Every eigenvalue of the plane wave satisfies the translated constant equation. -/
theorem sourcePlaneWave_spectrum_equation (hp : p ≠ ⊤)
    (n : ℤ) (a b z : ℂ) (ha : a ≠ 0)
    (hz : z ∈ periodicSpectrum hp (periodOnePotential (sourcePlaneWave n a b))) :
    ∃ k : ℤ, (z-(Real.pi:ℂ)*n)^2 = ((Real.pi:ℂ)*k)^2+a*b := by
  obtain ⟨f,hf,he⟩ := (mem_periodicSpectrum_iff_exists_eigenvector hp _ z).mp hz
  have hfst : ∃ j : ℤ, f.1.val j ≠ 0 := by
    by_contra h
    push Not at h
    have hs (j : ℤ) : f.2.val j = 0 := by
      have hj := congrArg (fun u : PairSpace p => u.1 (j-2*n)) he
      simp only [operator_sourcePlaneWave_fst,Prod.smul_fst,lp.coeFn_smul,
        Pi.smul_apply,smul_eq_mul,domainInclusion_apply,scalarInclusion_apply] at hj
      push_cast at hj
      change -(Real.pi:ℂ)*(j-2*n)*f.1.val (j-2*n)+a*f.2.val (j-2*n+2*n) =
        z*f.1.val (j-2*n) at hj
      rw [h,mul_zero,zero_add,mul_zero,sub_add_cancel] at hj
      exact (mul_eq_zero.mp hj).resolve_left ha
    apply hf
    apply Prod.ext <;> apply Subtype.ext <;> funext j
    · exact h j
    · exact hs j
  obtain ⟨j,hj⟩ := hfst
  refine ⟨j+n,?_⟩
  have h₁ := congrArg (fun u : PairSpace p => u.1 j) he
  have h₂ := congrArg (fun u : PairSpace p => u.2 (j+2*n)) he
  simp only [operator_sourcePlaneWave_fst,Prod.smul_fst,lp.coeFn_smul,
    Pi.smul_apply,smul_eq_mul,domainInclusion_apply,scalarInclusion_apply] at h₁
  simp only [operator_sourcePlaneWave_snd,Prod.smul_snd,lp.coeFn_smul,
    Pi.smul_apply,smul_eq_mul,domainInclusion_apply,scalarInclusion_apply] at h₂
  change -(Real.pi:ℂ)*j*f.1.val j+a*f.2.val (j+2*n) = z*f.1.val j at h₁
  push_cast at h₂
  change (Real.pi:ℂ)*(j+2*n)*f.2.val (j+2*n)+b*f.1.val (j+2*n-2*n) =
    z*f.2.val (j+2*n) at h₂
  rw [add_sub_cancel_right] at h₂
  have hm : ((z-(Real.pi:ℂ)*n)^2-(((Real.pi:ℂ)*(j+n))^2+a*b))*f.1.val j = 0 := by
    linear_combination -(z-(Real.pi:ℂ)*(j+2*n))*h₁-a*h₂
  have heq := sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hj)
  simpa only [Int.cast_add] using heq

/-- Exact translation of the actual periodic spectrum for opposite Fourier modes. -/
theorem sourcePlaneWave_mem_spectrum_iff (hp : p ≠ ⊤)
    (n : ℤ) (a b z : ℂ) (ha : a ≠ 0) :
    z ∈ periodicSpectrum hp (periodOnePotential (sourcePlaneWave n a b)) ↔
      ∃ k : ℤ, (z-(Real.pi:ℂ)*n)^2 = ((Real.pi:ℂ)*k)^2+a*b := by
  constructor
  · exact sourcePlaneWave_spectrum_equation hp n a b z ha
  · rintro ⟨k,hk⟩
    exact sourcePlaneWave_mem_spectrum_of_equation hp n k a b z ha hk

/-- The translation is of the original spectrum, not merely its asymptotic labels. -/
theorem sourcePlaneWave_mem_spectrum_iff_constant (hp : p ≠ ⊤)
    (n : ℤ) (a b z : ℂ) (ha : a ≠ 0) :
    z ∈ periodicSpectrum hp (periodOnePotential (sourcePlaneWave n a b)) ↔
      z-(Real.pi:ℂ)*n ∈ periodicSpectrum hp (constantPeriodicPair a b) := by
  rw [sourcePlaneWave_mem_spectrum_iff hp n a b z ha,
    mem_periodicSpectrum_constantPeriodicPair_iff hp a b _ ha]

end NLS.ZakharovShabat
