import NLS.ZakharovShabat.L2FloquetColumnRegularity
import NLS.ZakharovShabat.L2WholeLineMatrixMultiplication

/-! # Returning from the diagonal equation to the original physical equation -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Module Complex
open NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- Recombine the original normalized physical columns. -/
def l2FloquetRecombine (u : IntervalPairL2) (z : ℂ)
    (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (μ : Fin 2 → ℂ) (y : ℝ → ℂ × ℂ) :
    ℝ → ℂ × ℂ := fun t =>
  (y t).1 • l2FloquetPeriodicColumn u z (b 0) (μ 0) t+
    (y t).2 • l2FloquetPeriodicColumn u z (b 1) (μ 1) t

theorem l2FloquetRecombine_eq_matrix_action (u : IntervalPairL2) (z : ℂ)
    (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (μ : Fin 2 → ℂ) (y : ℝ → ℂ × ℂ) (t : ℝ) :
    l2FloquetRecombine u z b μ y t =
      wholeLineMatrixAction (l2FloquetPeriodicMatrix u z b μ t) (y t) := by
  rw [wholeLineMatrixAction_columns]
  rfl

/-- The actual Floquet recombination preserves local absolute continuity. -/
theorem absolutelyContinuousOnInterval_l2FloquetRecombine (u : IntervalPairL2) (z : ℂ)
    (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (μ : Fin 2 → ℂ) (y : ℝ → ℂ × ℂ)
    (a c : ℝ) (hy : AbsolutelyContinuousOnInterval y a c) :
    AbsolutelyContinuousOnInterval (l2FloquetRecombine u z b μ y) a c := by
  exact ((absolutelyContinuousOnInterval_clm hy (ContinuousLinearMap.fst ℝ ℂ ℂ)).smul
    (absolutelyContinuousOnInterval_l2FloquetPeriodicColumn u z (b 0) (μ 0) a c)).add
    ((absolutelyContinuousOnInterval_clm hy (ContinuousLinearMap.snd ℝ ℂ ℂ)).smul
      (absolutelyContinuousOnInterval_l2FloquetPeriodicColumn u z (b 1) (μ 1) a c))

/-- The logarithmic terms cancel in the original differential equation. -/
theorem ae_hasDerivAt_l2FloquetRecombine (u : IntervalPairL2) (z : ℂ)
    (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (μ : Fin 2 → ℂ) (y h : ℝ → ℂ × ℂ)
    (hy : ∀ᵐ t : ℝ, HasDerivAt y
      (Complex.log (μ 0)*(y t).1+(h t).1,Complex.log (μ 1)*(y t).2+(h t).2) t) :
    ∀ᵐ t : ℝ, HasDerivAt (l2FloquetRecombine u z b μ y)
      (classicalODECoefficient (l2WholeLinePotential u t) z (l2FloquetRecombine u z b μ y t)+
        wholeLineMatrixAction (l2FloquetPeriodicMatrix u z b μ t) (h t)) t := by
  filter_upwards [hy,ae_hasDerivAt_l2FloquetPeriodicColumn u z (b 0) (μ 0),
    ae_hasDerivAt_l2FloquetPeriodicColumn u z (b 1) (μ 1)] with t hyt hc0 hc1
  have hd1 : HasDerivAt (fun s => (y s).1) (Complex.log (μ 0)*(y t).1+(h t).1) t := by
    simpa using HasFDerivAt.hasDerivAt hyt.fst
  have hd2 : HasDerivAt (fun s => (y s).2) (Complex.log (μ 1)*(y t).2+(h t).2) t := by
    simpa using HasFDerivAt.hasDerivAt hyt.snd
  convert! (hd1.smul hc0).add (hd2.smul hc1) using 1
  rw [wholeLineMatrixAction_columns]
  simp only [l2FloquetRecombine,map_add,map_smul]
  rw [← l2FloquetPeriodicColumn_eq_matrix_column u z b μ 0 t,
    ← l2FloquetPeriodicColumn_eq_matrix_column u z b μ 1 t]
  module

/-- The inhomogeneous first-order equation yields the original signed pencil. -/
theorem physicalOperator_of_inhomogeneous_ode (φ F : ℝ → ℂ × ℂ) (z : ℂ)
    (g : ℂ × ℂ) (t : ℝ)
    (hF : HasDerivAt F (classicalODECoefficient (φ t) z (F t)+(I*g.1,-I*g.2)) t) :
    physicalOperator φ F t = z • F t-g := by
  have h1 : deriv (fun s => (F s).1) t = -I*z*(F t).1+I*(φ t).1*(F t).2+I*g.1 := by
    simpa using (HasFDerivAt.hasDerivAt hF.fst).deriv
  have h2 : deriv (fun s => (F s).2) t = -I*(φ t).2*(F t).1+I*z*(F t).2-I*g.2 := by
    simpa [sub_eq_add_neg] using (HasFDerivAt.hasDerivAt hF.snd).deriv
  ext <;> simp only [physicalOperator,h1,h2,Prod.fst_sub,Prod.snd_sub,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring_nf <;> simp [I_sq] <;> ring

end NLS.ZakharovShabat
