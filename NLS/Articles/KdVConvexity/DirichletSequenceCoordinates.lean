import NLS.KdV.HillHminusOneDirichletCommonAnalytic
import NLS.Articles.KdVConvexity.ActionEmbedding
import NLS.SequenceSpaces.HilbertSampling
import NLS.SequenceSpaces.Multiplier

/-! # Analytic normalized Dirichlet energy sequences

Squaring the common ell2 frequency displacement gives the normalized
energy displacement (mu_n-pi^2*n^2)/(1+n). Its quadratic term is first
formed in ell1 and continuously included in ell2. Thus the result is
analytic in the actual Hilbert norm, including all low indices.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Articles.KdVConvexity
open NLS.KdV

def positiveDirichletIndex : ℤ ↪ ℤ where
  toFun k := (actionIndexEquiv k : ℤ)
  inj' := by
    intro i j hij
    apply actionIndexEquiv.injective
    apply Subtype.ext
    change ((actionIndexEquiv i : ℕ) : ℤ) = ((actionIndexEquiv j : ℕ) : ℤ) at hij
    exact Int.ofNat.inj hij

@[simp] theorem positiveDirichletIndex_apply (k : ℤ) :
    positiveDirichletIndex k = (actionIndexEquiv k : ℤ) := rfl

def dirichletReciprocal : Coeff 2 := ⟨fun k => (baseActionWeight k : ℂ),memlp_baseActionWeight⟩

def dirichletReciprocalSymbol : Coeff ⊤ := Coeff.exponentInclusion (by simp : (2 : ℝ≥0∞) ≤ ⊤) dirichletReciprocal

def normalizedDirichletEnergies (c : ℝ) (d : Coeff 2) : Coeff 2 :=
  let a := Coeff.hilbertSampleCLM positiveDirichletIndex d
  let M := Coeff.multiplierCLM (p := 2) dirichletReciprocalSymbol
  (2*(Real.pi : ℂ)) • (a-M a)+
    M (Coeff.exponentInclusion (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (Coeff.holderProduct (p := 2) (r := 2) (q := 1) a a))-(c : ℂ)^2 • dirichletReciprocal

theorem analyticOnNhd_normalizedDirichletEnergies (c : ℝ) :
    AnalyticOnNhd ℂ (normalizedDirichletEnergies c) univ := by
  intro d _
  let S := Coeff.hilbertSampleCLM positiveDirichletIndex
  let M := Coeff.multiplierCLM (p := 2) dirichletReciprocalSymbol
  have hs : AnalyticAt ℂ (fun d : Coeff 2 => S d) d := S.analyticAt d
  have hm : AnalyticAt ℂ (fun d : Coeff 2 => M (S d)) d := (M.analyticAt _).comp hs
  have hp := ((Coeff.holderProduct (p := 2) (r := 2) (q := 1)).analyticAt_bilinear _).comp₂ hs hs
  have hi := ((Coeff.exponentInclusion (by norm_num : (1 : ℝ≥0∞) ≤ 2)).analyticAt _).comp hp
  exact (((hs.sub hm).const_smul (c := 2*(Real.pi : ℂ))).add ((M.analyticAt _).comp hi)).sub analyticAt_const

theorem normalizedDirichletEnergies_apply (c : ℝ) (d : Coeff 2) (k : ℤ) :
    normalizedDirichletEnergies c d k =
      (((Real.pi : ℂ)*(actionIndexEquiv k : ℕ)+d (actionIndexEquiv k : ℤ))^2-
        (c : ℂ)^2-(freeHillValue (actionIndexEquiv k : ℕ) : ℂ))/(1+(actionIndexEquiv k : ℕ) : ℂ) := by
  have hn : (1+(actionIndexEquiv k : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (1+(actionIndexEquiv k : ℕ) : ℝ) ≠ 0)
  simp only [normalizedDirichletEnergies,lp.coeFn_add,Pi.add_apply,lp.coeFn_sub,Pi.sub_apply,
    lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,Coeff.multiplierCLM_apply,Coeff.multiplier_apply,
    Coeff.hilbertSampleCLM_apply,positiveDirichletIndex_apply,Coeff.exponentInclusion_apply,
    Coeff.holderProduct_apply,dirichletReciprocalSymbol,dirichletReciprocal,baseActionWeight,
    freeHillValue]
  push_cast
  field_simp [hn]
  ring

theorem exists_local_analytic_normalized_Dirichlet_energies
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    ∃ V : Set PeriodOneHminusOne, ∃ E : PeriodOneHminusOne → Coeff 2,
      IsOpen V ∧ q ∈ V ∧ AnalyticOnNhd ℂ E V ∧
      (∀ p ∈ V, ∀ n : ℕ+, hillHminusDirichlet p
        ((freeHillValue (n : ℕ) : ℂ)+(1+(n : ℕ) : ℂ)*E p (actionIndexEquiv.symm n)) = 0) ∧
      ∀ p ∈ V, ∀ hp : IsRealPeriodOneHminusOne p, ∀ n : ℕ+,
        E p (actionIndexEquiv.symm n) =
          ((hillHminusDirichletEnergy p hp n : ℂ)-(freeHillValue (n : ℕ) : ℂ))/(1+(n : ℕ) : ℂ) := by
  obtain ⟨c,_,V,mu,d,hV,hqV,hd,_,hroot,hmatch,hformula⟩ :=
    exists_hillHminusDirichlet_common_analytic_branches q hr
  let E : PeriodOneHminusOne → Coeff 2 := fun p => normalizedDirichletEnergies c (d p)
  have hE (p : PeriodOneHminusOne) (hp : p ∈ V) (n : ℕ+) :
      E p (actionIndexEquiv.symm n) = (mu n p-(freeHillValue (n : ℕ) : ℂ))/(1+(n : ℕ) : ℂ) := by
    rw [normalizedDirichletEnergies_apply,Equiv.apply_symm_apply,← hformula p hp n]
  refine ⟨V,E,hV,hqV,fun p hp =>
    (analyticOnNhd_normalizedDirichletEnergies c _ (mem_univ _)).comp (hd p hp),?_,?_⟩
  · intro p hp n
    have hn : (1+(n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (1+(n : ℕ) : ℝ) ≠ 0)
    rw [hE p hp n,mul_div_cancel₀ _ hn,add_sub_cancel]
    exact hroot p hp n
  intro p hp hpr n
  rw [hE p hp n,hmatch p hp hpr n]

end NLS.Articles.KdVConvexity
