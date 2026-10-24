import NLS.FunctionalAnalysis.SelfAdjointCayley
import NLS.FunctionalAnalysis.CayleyResolventFunction
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary

/-! # The actual self-adjoint resolvent is the Cayley functional calculus -/
noncomputable section
set_option autoImplicit false
open Complex
namespace NLS.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {T : E →ₗ.[ℂ] E}

/-- The actual bounded nonreal resolvent equals the continuous Cayley
resolvent function of the original self-adjoint partial operator. -/
theorem selfAdjointNonrealResolvent_eq_cayley_cfc (hT : IsSelfAdjoint T)
    (z : ℂ) (hz : z.im ≠ 0) :
    selfAdjointNonrealResolvent hT z hz =
      cfcHom (isStarNormal_of_mem_unitary (selfAdjointCayley_mem_unitary hT))
        (cayleyResolventFunction (spectrum ℂ (selfAdjointCayley hT))
          (spectrum_subset_unitary_of_mem_unitary (selfAdjointCayley_mem_unitary hT)) z hz) := by
  let U := selfAdjointCayley hT
  have hU : IsStarNormal U := isStarNormal_of_mem_unitary (selfAdjointCayley_mem_unitary hT)
  have hs : spectrum ℂ U ⊆ unitary ℂ :=
    spectrum_subset_unitary_of_mem_unitary (selfAdjointCayley_mem_unitary hT)
  let Φ : C(spectrum ℂ U, ℂ) →⋆ₐ[ℂ] (E →L[ℂ] E) := cfcHom hU
  let c : C(spectrum ℂ U, ℂ) := ContinuousMap.restrict (spectrum ℂ U) (ContinuousMap.id ℂ)
  let d : C(spectrum ℂ U, ℂ) := z • (1-c)-I • (1+c)
  let D : E →L[ℂ] E := z • (1-U)-I • (1+U)
  let r := cayleyResolventFunction (spectrum ℂ U) hs z hz
  have hd (x : spectrum ℂ U) : d x ≠ 0 :=
    cayleyResolventDenominator_ne_zero z hz x (hs x.property)
  let di : C(spectrum ℂ U, ℂ) := ⟨fun x => (d x)⁻¹,d.continuous.inv₀ hd⟩
  have hc : Φ c = U := cfcHom_id hU
  have hD : Φ d = D := by
    dsimp only [d,D]
    rw [map_sub,map_smul,map_smul,map_sub,map_add,map_one,hc]
  have hdi : D*(Φ di) = 1 := by
    rw [← hD,← map_mul]
    have hi : d*di = 1 := by
      ext x
      exact mul_inv_cancel₀ (hd x)
    rw [hi,map_one]
  have hrd : Φ r*D = 1-U := by
    rw [← hD,← map_mul]
    have he : r*d = 1-c := by
      ext x
      exact div_mul_cancel₀ (1-(x : ℂ)) (hd x)
    rw [he,map_sub,map_one,hc]
  let Rz := selfAdjointNonrealResolvent hT z hz
  let Rm := selfAdjointNonrealResolvent hT (-I) (by simp)
  have hres : Rz-Rm = (-(z+I)) • (Rz*Rm) := by
    have hn : -I-z = -(z+I) := by ring
    simpa only [Rz,Rm,hn,ContinuousLinearMap.mul_def] using selfAdjointNonrealResolvent_sub hT z (-I) hz (by simp)
  have hr : Rz+(z+I) • (Rz*Rm) = Rm := by
    calc
      _ = (Rz-Rm)+Rm+(z+I) • (Rz*Rm) := by module
      _ = Rm := by rw [hres]; module
  have hRD : Rz*D = 1-U := by
    calc
      Rz*D = (-(2*I)) • (Rz+(z+I) • (Rz*Rm)) := by
        dsimp only [D,U,selfAdjointCayley]
        simp only [mul_sub,mul_add,mul_smul_comm,mul_one]
        module
      _ = (-(2*I)) • Rm := by rw [hr]
      _ = 1-U := by change _ = 1-(1+(2*I) • Rm); module
  change Rz = Φ r
  calc
    Rz = Rz*(D*(Φ di)) := by rw [hdi,mul_one]
    _ = (Rz*D)*(Φ di) := by rw [mul_assoc]
    _ = (Φ r*D)*(Φ di) := by rw [hRD,hrd]
    _ = Φ r := by rw [mul_assoc,hdi,mul_one]

end NLS.FunctionalAnalysis
