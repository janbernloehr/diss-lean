import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Surjective finite projections from independent continuous cotangents

Independence of finitely many actual bounded linear functionals gives a
surjective projection and a bounded linear right inverse. The source
may be infinite dimensional.
-/
noncomputable section
open Set
namespace NLS.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {ι : Type*} [Fintype ι]

theorem surjective_pi_of_cotangent_independent (L : ι → E →L[ℂ] ℂ)
    (hL : ∀ c : ι → ℂ, (∑ i, c i • L i) = 0 → c = 0) :
    Function.Surjective (ContinuousLinearMap.pi L) := by
  classical
  let T := (ContinuousLinearMap.pi L).toLinearMap
  apply (LinearMap.dualMap_injective_iff (f := T)).mp
  intro f g hfg
  have hdecomp (z : ι → ℂ) : z = ∑ i, z i • Pi.single i (1 : ℂ) := by
    ext j
    simp [Pi.single_apply]
  have hsum (h : Module.Dual ℂ (ι → ℂ)) (z : ι → ℂ) :
      h z = ∑ i, z i*h (Pi.single i (1 : ℂ)) := by
    conv_lhs => rw [hdecomp z,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact map_smul h (z i) (Pi.single i (1 : ℂ))
  let c : ι → ℂ := fun i => f (Pi.single i 1)-g (Pi.single i 1)
  have hz : (∑ i, c i • L i) = 0 := by
    ext x
    have he := congrArg (fun h : Module.Dual ℂ E => h x) hfg
    change f (T x) = g (T x) at he
    have hs := sub_eq_zero.mpr he
    rw [hsum f (T x),hsum g (T x),← Finset.sum_sub_distrib] at hs
    simp only [sum_apply,smul_apply,smul_eq_mul,zero_apply]
    calc
      _ = ∑ i, ((L i x)*f (Pi.single i 1)-(L i x)*g (Pi.single i 1)) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [c]
        ring
      _ = 0 := hs
  have hc := hL c hz
  apply LinearMap.ext
  intro z
  rw [hsum f z,hsum g z]
  apply Finset.sum_congr rfl
  intro i _
  have he : f (Pi.single i 1) = g (Pi.single i 1) := by
    apply sub_eq_zero.mp
    exact congrFun hc i
  rw [he]

theorem exists_continuousLinear_rightInverse_of_surjective
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    (T : E →L[ℂ] F) (hT : Function.Surjective T) :
    ∃ R : F →L[ℂ] E, T.comp R = ContinuousLinearMap.id ℂ F := by
  obtain ⟨r,hr⟩ := T.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hT)
  let R : F →L[ℂ] E := ⟨r,r.continuous_of_finiteDimensional⟩
  refine ⟨R,?_⟩
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg (fun h : F →ₗ[ℂ] F => h x) hr

end NLS.FunctionalAnalysis
