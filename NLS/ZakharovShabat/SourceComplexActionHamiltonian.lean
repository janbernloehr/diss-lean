import NLS.ZakharovShabat.SourceBirkhoffActionHamiltonian
import NLS.ZakharovShabat.SourceComplexBirkhoffMap

/-! # Hamiltonian signs in the actual complex Birkhoff coordinates

For z=(x-iy)/sqrt(2), the proved action Hamiltonian rotation (-y,x)
has complex velocity (-i*z,+i*w). This fixes the physical time orientation
independently of the opposite phase signs printed in equation (4.14).
-/
noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W₀ B W : Set (CoeffPair p)} {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The original source action Hamiltonian has negative phase on z and positive phase on w. -/
theorem complex_coordinates_actionHamiltonian
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (h2p : 2 ≤ p) (k n : ℤ) (φ : realTypeSourceSubmodule p) :
    let v := sourceHamiltonianVector h2p (sourceComplexAction hp hp1 k) φ.val
    (fderiv ℂ (fun ψ => (sourceComplexBirkhoffMap hp hp1 s ψ).1 n) φ.val) v =
      -I*(sourceComplexBirkhoffMap hp hp1 s φ.val).1 k*(if n = k then 1 else 0) ∧
    (fderiv ℂ (fun ψ => (sourceComplexBirkhoffMap hp hp1 s ψ).2 n) φ.val) v =
      I*(sourceComplexBirkhoffMap hp hp1 s φ.val).2 k*(if n = k then 1 else 0) := by
  dsimp only
  let ex := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).comp (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p))
  let ey := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).comp (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p))
  have hx : DifferentiableAt ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 n) φ.val :=
    ex.differentiableAt.comp φ.val (D.analytic φ.val (D.real_subset φ.property)).differentiableAt
  have hy : DifferentiableAt ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).2 n) φ.val :=
    ey.differentiableAt.comp φ.val (D.analytic φ.val (D.real_subset φ.property)).differentiableAt
  have he₁ : (fun ψ => (sourceComplexBirkhoffMap hp hp1 s ψ).1 n) =
      fun ψ => Birkhoff.complexCoordinateScale*((sourceBirkhoffMap hp hp1 s ψ).1 n-I*(sourceBirkhoffMap hp hp1 s ψ).2 n) := by
    funext ψ; exact Birkhoff.rectangularToComplex_fst _ n
  have he₂ : (fun ψ => (sourceComplexBirkhoffMap hp hp1 s ψ).2 n) =
      fun ψ => Birkhoff.complexCoordinateScale*((sourceBirkhoffMap hp hp1 s ψ).1 n+I*(sourceBirkhoffMap hp hp1 s ψ).2 n) := by
    funext ψ; exact Birkhoff.rectangularToComplex_snd _ n
  have hdx := ((hx.hasFDerivAt.sub (hy.hasFDerivAt.const_mul I)).const_mul Birkhoff.complexCoordinateScale).fderiv
  have hdy := ((hx.hasFDerivAt.add (hy.hasFDerivAt.const_mul I)).const_mul Birkhoff.complexCoordinateScale).fderiv
  have hact := D.map_coordinates_actionHamiltonian h2p k n φ
  simp only [Pi.sub_apply,Pi.add_apply] at hdx hdy
  rw [he₁,he₂,hdx,hdy]
  simp only [smul_apply,sub_apply,add_apply,
    smul_eq_mul,hact.1,hact.2,sourceComplexBirkhoffMap,Birkhoff.rectangularToComplex_fst,
    Birkhoff.rectangularToComplex_snd]
  constructor <;> ring_nf <;> simp [I_sq]

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
