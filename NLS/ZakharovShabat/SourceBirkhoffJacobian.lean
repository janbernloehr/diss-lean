import NLS.ZakharovShabat.SourceBirkhoffLemma15_3

/-! # The analytic Jacobian of the actual Birkhoff map

Section 16 begins with the derivative as a map into bounded linear
operators. Its coordinate evaluations are the full rectangular
cotangents already used by the physical canonical identities.
-/

noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceBirkhoffJacobian (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (φ : CoeffPair p) :
    CoeffPair p →L[ℂ] (Coeff p × Coeff p) :=
  fderiv ℂ (sourceBirkhoffMap hp hp1 s) φ

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

theorem jacobian_analytic
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) :
    AnalyticOnNhd ℂ (sourceBirkhoffJacobian hp hp1 s) W := D.analytic.fderiv

/-- Evaluation of the actual bounded Jacobian at every signed index. -/
theorem jacobian_coordinates
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) (h : CoeffPair p) (n : ℤ) :
    (sourceBirkhoffJacobian hp hp1 s φ h).1 n = (fderiv ℂ (sourceBirkhoffX hp hp1 n s) φ) h ∧
    (sourceBirkhoffJacobian hp hp1 s φ h).2 n = (fderiv ℂ (sourceBirkhoffY hp hp1 n s) φ) h := by
  let ex := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).comp (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p))
  let ey := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).comp (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p))
  have hx := (ex.hasFDerivAt.comp φ (D.analytic φ hφ).differentiableAt.hasFDerivAt).fderiv
  have hy := (ey.hasFDerivAt.comp φ (D.analytic φ hφ).differentiableAt.hasFDerivAt).fderiv
  have hd := D.fderiv_coordinates n φ hφ
  exact ⟨(congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hx).symm.trans (congrArg (fun L => L h) hd.1),
    (congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hy).symm.trans (congrArg (fun L => L h) hd.2)⟩

/-- The Jacobian is represented coordinatewise by actual regular
cotangents, whose canonical pairings hold also at closed gaps. -/
theorem jacobian_regular_coordinates
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (φ : realTypeSourceSubmodule p) :
    ∃ X Y : ℤ → RegularSourceCotangent p,
      (∀ h n, (sourceBirkhoffJacobian hp hp1 s φ.val h).1 n = (X n).toCotangent h ∧
        (sourceBirkhoffJacobian hp hp1 s φ.val h).2 n = (Y n).toCotangent h) ∧
      ∀ n m, (X n).bivector (X m) = 0 ∧
        (X n).bivector (Y m) = -(if n = m then 1 else 0) ∧ (Y n).bivector (Y m) = 0 := by
  obtain ⟨X,Y,hd,hb⟩ := D.angular.exists_birkhoff_regular_canonical W D.source_open D.source_subset D.real_subset φ
  refine ⟨X,Y,?_,hb⟩
  intro h n
  rw [(hd n).1,(hd n).2]
  exact D.jacobian_coordinates φ.val (D.real_subset φ.property) h n

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
