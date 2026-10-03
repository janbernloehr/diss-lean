import NLS.ZakharovShabat.SourceBirkhoffJacobian
import NLS.Poisson.SourceHamiltonianDirection

/-! # Action Hamiltonians in actual Birkhoff coordinates

Differentiating the full analytic action-radius identity gives `dI =
x dx + y dy`, also at collapsed gaps. The canonical Poisson identities
then give the one-mode rotation velocity `(-y,x)` for the actual action
Hamiltonian, with every other coordinate stationary.
-/
noncomputable section
open Set Complex Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ B W : Set (CoeffPair p)} {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The full action cotangent in rectangular coordinates, including closed gaps. -/
theorem actionDifferential_eq_map_rectangular
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (k : ℤ) (φ : CoeffPair p) (hφ : φ ∈ W) :
    fderiv ℂ (sourceComplexAction hp hp1 k) φ =
      (sourceBirkhoffMap hp hp1 s φ).1 k •
        fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 k) φ +
      (sourceBirkhoffMap hp hp1 s φ).2 k •
        fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).2 k) φ := by
  let ex := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p k).comp (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p))
  let ey := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p k).comp (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p))
  have hx : DifferentiableAt ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 k) φ :=
    ex.differentiableAt.comp φ (D.analytic φ hφ).differentiableAt
  have hy : DifferentiableAt ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).2 k) φ :=
    ey.differentiableAt.comp φ (D.analytic φ hφ).differentiableAt
  have he : sourceComplexAction hp hp1 k =ᶠ[𝓝 φ]
      (fun ψ => (1/2 : ℂ)*(((sourceBirkhoffMap hp hp1 s ψ).1 k)^2+
        ((sourceBirkhoffMap hp hp1 s ψ).2 k)^2)) := by
    filter_upwards [D.source_open.mem_nhds hφ] with ψ hψ
    rw [D.action_radius ψ hψ k]
    ring
  have hd := ((hx.hasFDerivAt.pow 2).add (hy.hasFDerivAt.pow 2)).const_smul (1/2 : ℂ)
  rw [he.fderiv_eq]
  convert! hd.fderiv using 1
  ext h
  simp only [smul_apply,add_apply,smul_eq_mul]
  norm_num
  ring

/-- The actual action Hamiltonian rotates precisely the selected coordinate pair. -/
theorem map_coordinates_actionHamiltonian
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (k n : ℤ) (φ : realTypeSourceSubmodule p) :
    let v := sourceHamiltonianVector h2p (sourceComplexAction hp hp1 k) φ.val
    (fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 n) φ.val) v =
      -(sourceBirkhoffMap hp hp1 s φ.val).2 k * (if n = k then 1 else 0) ∧
    (fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).2 n) φ.val) v =
      (sourceBirkhoffMap hp hp1 s φ.val).1 k * (if n = k then 1 else 0) := by
  dsimp only
  rw [sourceHamiltonianVector,apply_sourceHamiltonianDirection,apply_sourceHamiltonianDirection,
    D.actionDifferential_eq_map_rectangular k φ.val (D.real_subset φ.property)]
  have hnk := D.sourceBracket_canonical h2p n k φ
  have hkn := D.sourceBracket_canonical h2p k n φ
  change sourceBivector h2p _ _ = 0 ∧ sourceBivector h2p _ _ = _ ∧ sourceBivector h2p _ _ = 0 at hnk hkn
  have hrev : sourceBivector h2p
      (fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).2 n) φ.val)
      (fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 k) φ.val) = (if n = k then 1 else 0) := by
    rw [sourceBivector_antisymm,hkn.2.1]
    simp only [neg_neg,eq_comm]
  simp only [map_add,map_smul,smul_eq_mul,hnk.1,hnk.2.1,hnk.2.2,hrev]
  constructor <;> ring

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
