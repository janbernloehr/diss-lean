import NLS.Fourier.UnitIntervalDirichlet

/-! # Explicit modes in the native zero-trace domain -/
noncomputable section
namespace NLS.Fourier
open NLS.ZakharovShabat

/-- Subtracting the constant mode removes both endpoint traces. -/
def unitDirichletMode (n : ℤ) : UnitDirichletH1 :=
  ⟨scalarMode n 1-scalarMode 0 1, by
    change unitDirichletTrace (scalarMode n 1-scalarMode 0 1) = 0
    rw [map_sub, unitDirichletTrace_scalarMode, unitDirichletTrace_scalarMode, sub_self]⟩

theorem unitDirichletMode_coefficient (n k : ℤ) :
    (unitDirichletMode n).val.val k = (if k = n then 1 else 0)-(if k = 0 then 1 else 0) := by
  change (scalarMode n 1).val k-(scalarMode 0 1).val k = _
  simp only [scalarMode_apply]

instance : Nontrivial UnitDirichletH1 := by
  apply nontrivial_of_ne (unitDirichletMode 1) 0
  intro h
  have he := congrArg (fun f : UnitDirichletH1 => f.val.val 1) h
  norm_num [unitDirichletMode_coefficient] at he

end NLS.Fourier
