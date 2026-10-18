import NLS.ZakharovShabat.ClassicalFundamentalSolution
import NLS.ZakharovShabat.NLSWKBComparison

/-! # Signed swap symmetry of the classical equation

Spectral reflection and the signed potential swap exchange the actual solution components by ODE uniqueness.
-/

noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The potential transformation paired with spectral reflection and component swap. -/
def classicalSwapPotential (Φ : Curve (ℂ × ℂ)) : Curve (ℂ × ℂ) :=
  ⟨fun t => (-(Φ t).2,-(Φ t).1),Φ.continuous.snd.neg.prodMk Φ.continuous.fst.neg⟩

@[simp] theorem classicalSwapPotential_apply (Φ : Curve (ℂ × ℂ)) (t : Icc (0:ℝ) 1) :
    classicalSwapPotential Φ t = (-(Φ t).2,-(Φ t).1) := rfl

/-- The exact ODE covariance includes a sign on both swapped components. -/
theorem classicalODECoefficient_swap (φ y : ℂ × ℂ) (z : ℂ) :
    classicalODECoefficient φ z y.swap =
      (classicalODECoefficient (-φ.2,-φ.1) (-z) y).swap := by
  apply Prod.ext <;> simp [classicalODECoefficient_apply] <;> ring

/-- Spectral reflection with the signed swapped potential exchanges the
actual solution components, for every initial vector and time. -/
theorem classicalSolution_swap (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (v : ℂ × ℂ) (t : Icc (0:ℝ) 1) :
    classicalSolution Φ z v.swap t =
      (classicalSolution (classicalSwapPotential Φ) (-z) v t).swap := by
  let u : ℝ → ℂ × ℂ := fun x => (classicalSolution (classicalSwapPotential Φ) (-z) v x).swap
  have hu : ContinuousOn u (Icc 0 1) :=
    ((continuous_classicalSolution (classicalSwapPotential Φ) (-z) v).snd.prodMk
      (continuous_classicalSolution (classicalSwapPotential Φ) (-z) v).fst).continuousOn
  have h0 : u 0 = v.swap := by simp [u]
  have hd (x : Icc (0:ℝ) 1) (_ : x.val ∈ Ioo (0:ℝ) 1) :
      HasDerivAt u (classicalODECoefficient (Φ x) z (u x)) x := by
    have h := hasDerivAt_classicalSolution (classicalSwapPotential Φ) (-z) v x
    have hh := (HasFDerivAt.hasDerivAt h.snd).prodMk (HasFDerivAt.hasDerivAt h.fst)
    convert hh using 1
    · rfl
    · apply Prod.ext <;>
        simp [u,classicalODECoefficient_apply,ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.toSpanSingleton_apply] <;> ring
  exact (classicalSolution_unique Φ z v.swap u hu h0 hd t.property).symm

/-- The signed swap preserves the original physical functions exactly. -/
theorem classicalSwapPotential_ofFunctions (a b : ℝ → ℂ)
    (ha : Continuous a) (hb : Continuous b) :
    classicalSwapPotential (classicalPotentialOfFunctions a b ha hb) =
      classicalPotentialOfFunctions (-b) (-a) hb.neg ha.neg := by
  apply ContinuousMap.ext
  intro t
  rfl

end NLS.ZakharovShabat
