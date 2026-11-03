import NLS.KdV.HminusOneDirichletComplexLabeling
import NLS.KdV.HminusOneDirichletAsymptotics
import NLS.SequenceSpaces.FiniteModificationGeneral
import NLS.SequenceSpaces.OrderedComplexNatEnumeration

/-! Full complex Dirichlet labels have the literal n-times-l2 asymptotic
at the SAME original positive index, and are independent of all Miura and
central-cutoff choices. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.KdV.HillHminusDirichletComplexLabeling
variable {q : PeriodOneHminusOne} {u : Coeff 2} {c : ℂ} {N : ℕ} {mu : ℕ → ℂ}
variable (h : HillHminusDirichletComplexLabeling q u c N mu)
include h

/-- Joining the finite central block preserves the entire inverse-bracket
weighted l2 asymptotic at original index j+1. -/
theorem inverseBracket_error :
    Memℓp (fun j : ℕ => inverseBracketCoefficients (j+1:ℕ)*
      (mu j-((Real.pi:ℂ)*(j+1:ℕ))^2)) 2 := by
  have hb := memlp_hillMiuraDirichletEnergy_inverseBracket_error u c
  have hinj : Function.Injective (fun j : ℕ => ((j+1:ℕ):ℤ)) := by
    intro i j he
    have hh := Int.ofNat.inj he
    omega
  have ht : Memℓp (fun j : ℕ => inverseBracketCoefficients (j+1:ℕ)*
      (hillMiuraDirichletEnergy u c (j+1:ℕ)-((Real.pi:ℂ)*(j+1:ℕ))^2)) 2 := by
    apply (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mpr
    simpa only [Function.comp_def,Int.cast_natCast] using!
      (hb.summable (by norm_num)).comp_injective hinj
  apply NLS.memℓp_of_eq_outside_finset_on ht (Finset.range N)
  intro j hj
  rw [h.distant j (by simpa only [Finset.mem_range,not_lt] using hj)]

/-- The source's literal asymptotic: error divided by its original positive
index is in l2, for EVERY complex original H-minus-one potential. -/
theorem inverseIndex_error :
    Memℓp (fun j : ℕ => (mu j-((Real.pi:ℂ)*(j+1:ℕ))^2)/(j+1:ℕ)) 2 := by
  have hb := h.inverseBracket_error
  apply (hb.norm.const_mul (2:ℝ)).mono
  intro j
  let E := mu j-((Real.pi:ℂ)*(j+1:ℕ))^2
  let k : ℝ := (j+1:ℕ)
  have hk : (1:ℝ) ≤ k := by dsimp [k]; exact_mod_cast (show 1 ≤ j+1 by omega)
  have hkpos : 0 < k := by linarith
  have hB : ‖inverseBracketCoefficients (j+1:ℕ)‖ = (1+k)⁻¹ := by
    have hb := norm_inverseBracketCoefficients_apply (j+1:ℕ)
    simp only [Int.cast_natCast] at hb
    rw [abs_of_nonneg (show (0:ℝ) ≤ (j+1:ℕ) from Nat.cast_nonneg _)] at hb
    exact hb
  have hineq : ‖E‖/k ≤ (2*‖E‖)/(1+k) := by
    apply (div_le_div_iff₀ hkpos (by positivity : 0 < 1+k)).mpr
    have hp := mul_nonneg (sub_nonneg.mpr hk) (norm_nonneg E)
    nlinarith
  change ‖E/(j+1:ℕ)‖ ≤ 2*‖inverseBracketCoefficients (j+1:ℕ)*E‖
  calc
    ‖E/(j+1:ℕ)‖ = ‖E‖/k := by rw [norm_div,Complex.norm_natCast]
    _ ≤ (2*‖E‖)/(1+k) := hineq
    _ = _ := by rw [norm_mul,hB]; ring

/-- Full actual multiplicities and ordering determine the ENTIRE complex
sequence, independently of lift, shift and cutoff, without assuming a common tail. -/
theorem unique {v : Coeff 2} {d : ℂ} {M : ℕ} {nu : ℕ → ℂ}
    (g : HillHminusDirichletComplexLabeling q v d M nu) : mu = nu :=
  NLS.ordered_complex_nat_enumeration_unique mu nu h.finite_fiber g.finite_fiber
    h.ordered g.ordered fun e => (h.multiplicity e).trans (g.multiplicity e).symm

end NLS.KdV.HillHminusDirichletComplexLabeling
