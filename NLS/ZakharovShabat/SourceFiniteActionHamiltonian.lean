import NLS.ZakharovShabat.SourceComplexActionHamiltonian
import NLS.ZakharovShabat.SourceBirkhoffProposition17_1
import NLS.Dynamics.FiniteHamiltonianPhaseDerivative

/-! # Finite sums of the original source action Hamiltonian fields

The actual complex Birkhoff differential is injective. It sends each
finite frequency-weighted sum of original action Hamiltonian fields to
the corresponding finite coordinate velocity, with the physical signs.
-/
noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A finite combination of the original source action Hamiltonian fields. -/
def sourceFiniteActionHamiltonianVector (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p)
    (freq : ℤ → ℝ) (S : Finset ℤ) (φ : CoeffPair p) : CoeffPair p :=
  ∑ k ∈ S, (freq k : ℂ) • sourceHamiltonianVector h2p (sourceComplexAction hp hp1 k) φ

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
variable {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The complex Birkhoff differential is the rectangular differential followed by the fixed coordinate change. -/
theorem complex_jacobian_eq (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) :
    fderiv ℂ (sourceComplexBirkhoffMap hp hp1 s) φ =
      Birkhoff.rectangularToComplex.toContinuousLinearMap.comp (sourceBirkhoffJacobian hp hp1 s φ) :=
  ((Birkhoff.rectangularToComplex (p := p)).toContinuousLinearMap.hasFDerivAt.comp φ
    (D.analytic φ hφ).differentiableAt.hasFDerivAt).fderiv

/-- The actual complex differential is injective at every real source. -/
theorem complex_jacobian_injective (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) :
    Function.Injective (fderiv ℂ (sourceComplexBirkhoffMap hp hp1 s) φ.val) := by
  rw [D.complex_jacobian_eq φ.val (D.real_subset φ.property)]
  exact Birkhoff.rectangularToComplex.injective.comp (D.jacobian_bijective_all_exponents φ).1

/-- Coordinate evaluation commutes with the actual complex Banach differential. -/
theorem complex_jacobian_coordinates (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) (v : CoeffPair p) (n : ℤ) :
    ((fderiv ℂ (sourceComplexBirkhoffMap hp hp1 s) φ) v).1 n =
      (fderiv ℂ (fun ψ => (sourceComplexBirkhoffMap hp hp1 s ψ).1 n) φ) v ∧
    ((fderiv ℂ (sourceComplexBirkhoffMap hp hp1 s) φ) v).2 n =
      (fderiv ℂ (fun ψ => (sourceComplexBirkhoffMap hp hp1 s ψ).2 n) φ) v := by
  let ex := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).comp (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p))
  let ey := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).comp (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p))
  have hx := (ex.hasFDerivAt.comp φ (D.complex_map_analytic φ hφ).differentiableAt.hasFDerivAt).fderiv
  have hy := (ey.hasFDerivAt.comp φ (D.complex_map_analytic φ hφ).differentiableAt.hasFDerivAt).fderiv
  exact ⟨(congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L v) hx).symm,
    (congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L v) hy).symm⟩

/-- Every finite sum of action fields has precisely the frequency-weighted complex phase velocity. -/
theorem complex_jacobian_finiteActionHamiltonian
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (h2p : 2 ≤ p)
    (freq : ℤ → ℝ) (S : Finset ℤ) (φ : realTypeSourceSubmodule p) :
    (fderiv ℂ (sourceComplexBirkhoffMap hp hp1 s) φ.val)
      (sourceFiniteActionHamiltonianVector hp hp1 h2p freq S φ.val) =
        Birkhoff.finiteHamiltonianPhaseVelocity freq S (sourceComplexBirkhoffMap hp hp1 s φ.val) := by
  apply Prod.ext <;> ext n
  · rw [(D.complex_jacobian_coordinates φ.val (D.real_subset φ.property) _ n).1]
    simp only [sourceFiniteActionHamiltonianVector,map_sum,map_smul,smul_eq_mul,
      (D.complex_coordinates_actionHamiltonian h2p _ n φ).1]
    change _ = (lp.evalₗ (𝕜 := ℂ) (fun _ : ℤ => ℂ) p n)
      (∑ k ∈ S, lp.single p k (-I*(freq k : ℂ)*(sourceComplexBirkhoffMap hp hp1 s φ.val).1 k))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [lp.evalₗ_apply,lp.single_apply,Pi.single_apply]
    split_ifs <;> simp_all only [mul_one,mul_zero]; ring
  · rw [(D.complex_jacobian_coordinates φ.val (D.real_subset φ.property) _ n).2]
    simp only [sourceFiniteActionHamiltonianVector,map_sum,map_smul,smul_eq_mul,
      (D.complex_coordinates_actionHamiltonian h2p _ n φ).2]
    change _ = (lp.evalₗ (𝕜 := ℂ) (fun _ : ℤ => ℂ) p n)
      (∑ k ∈ S, lp.single p k (I*(freq k : ℂ)*(sourceComplexBirkhoffMap hp hp1 s φ.val).2 k))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [lp.evalₗ_apply,lp.single_apply,Pi.single_apply]
    split_ifs <;> simp_all only [mul_one,mul_zero]; ring

/-- Enlarging or changing a finite cutoff containing the active coordinates does not change the source field. -/
theorem finiteActionHamiltonianVector_eq_of_support
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (h2p : 2 ≤ p)
    (freq : ℤ → ℝ) (S T : Finset ℤ) (φ : realTypeSourceSubmodule p)
    (hS : ∀ n ∉ S, (sourceComplexBirkhoffMap hp hp1 s φ.val).1 n = 0 ∧
      (sourceComplexBirkhoffMap hp hp1 s φ.val).2 n = 0)
    (hT : ∀ n ∉ T, (sourceComplexBirkhoffMap hp hp1 s φ.val).1 n = 0 ∧
      (sourceComplexBirkhoffMap hp hp1 s φ.val).2 n = 0) :
    sourceFiniteActionHamiltonianVector hp hp1 h2p freq S φ.val =
      sourceFiniteActionHamiltonianVector hp hp1 h2p freq T φ.val := by
  apply D.complex_jacobian_injective φ
  rw [D.complex_jacobian_finiteActionHamiltonian,D.complex_jacobian_finiteActionHamiltonian]
  apply Prod.ext <;> ext n
  · simp only [Birkhoff.finiteHamiltonianPhaseVelocity_fst]
    by_cases hnS : n ∈ S
    · by_cases hnT : n ∈ T
      · simp [hnS,hnT]
      · simp [hnS,hnT,(hT n hnT).1]
    · simp only [if_neg hnS]
      by_cases hnT : n ∈ T
      · simp [hnT,(hS n hnS).1]
      · simp [hnT]
  · simp only [Birkhoff.finiteHamiltonianPhaseVelocity_snd]
    by_cases hnS : n ∈ S
    · by_cases hnT : n ∈ T
      · simp [hnS,hnT]
      · simp [hnS,hnT,(hT n hnT).2]
    · simp only [if_neg hnS]
      by_cases hnT : n ∈ T
      · simp [hnT,(hS n hnS).2]
      · simp [hnT]

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
