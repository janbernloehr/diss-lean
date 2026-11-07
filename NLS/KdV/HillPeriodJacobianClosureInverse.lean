import NLS.KdV.HillPeriodJacobianLimitFredholm
import NLS.KdV.HillProductEquationRealInverse
import NLS.FunctionalAnalysis.EscapingClosureProperty

/-! EVERY operator in the full norm closure of the actual real Hill
period Jacobian family is bijective: fixed indices use the original real
inverse, and escaping indices use the proved full-product limit inverse. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem sequenceJacobian_actual_real_closure_bijective (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)
    (hT : T ∈ closure (range (fun n : ℕ+ => P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q)))) :
    Function.Bijective T := by
  let J (n : ℕ+) := P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q)
  let F (j : ℕ) := J ⟨j+1,by omega⟩
  have hrange : range F = range J := by
    ext S
    constructor
    · rintro ⟨j,rfl⟩
      exact ⟨⟨j+1,by omega⟩,rfl⟩
    · rintro ⟨n,rfl⟩
      refine ⟨(n:ℕ)-1,?_⟩
      have he : (⟨(n:ℕ)-1+1,by omega⟩:ℕ+) = n := by
        apply Subtype.ext
        change (n:ℕ)-1+1 = (n:ℕ)
        exact Nat.sub_add_cancel n.property
      change J ⟨(n:ℕ)-1+1,by omega⟩ = J n
      rw [he]
  apply NLS.FunctionalAnalysis.property_on_closure_range_of_escaping_limits F (fun S => Function.Bijective S)
    (fun j => P.sequenceJacobian_actual_real_bijective ⟨j+1,by omega⟩ q hq hr) ?_ T ?_
  · intro n hn S hS
    have hn' : Tendsto (fun j => n j+1) atTop atTop := (tendsto_add_atTop_nat 1).comp hn
    exact P.sequenceJacobian_actual_real_escaping_limit_bijective q hq hr (fun j => ⟨n j+1,by omega⟩) hn' S hS
  · rwa [hrange]

end NLS.KdV.HillProductEquationPatch
