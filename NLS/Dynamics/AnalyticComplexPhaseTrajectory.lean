import NLS.SequenceSpaces.AnalyticPhaseTrajectory
import NLS.Dynamics.ComplexPhaseFlow

/-! # Analytic compact-time trajectories of complex coordinate pairs

The two signs of the phase flow are assembled in the uniform norm on
continuous pair-valued trajectories. The bounded complex frequency
correction and both initial coordinate sequences enter entirely.
-/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Birkhoff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Pairing continuous trajectories is bounded complex linear. -/
def pairTrajectoriesCLM : (C(K, Coeff p) × C(K, Coeff p)) →L[ℂ] C(K, Coeff p × Coeff p) :=
  LinearMap.mkContinuous
    { toFun := fun z => z.1.prodMk z.2
      map_add' := by intro a b; rfl
      map_smul' := by intro c a; rfl }
    1 (by
      intro z
      apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ 1*‖z‖)).mpr
      intro k
      change max ‖z.1 k‖ ‖z.2 k‖ ≤ 1*max ‖z.1‖ ‖z.2‖
      simpa only [one_mul] using max_le_max (z.1.norm_coe_le_norm k) (z.2.norm_coe_le_norm k))

@[simp] theorem pairTrajectoriesCLM_apply (z : C(K, Coeff p) × C(K, Coeff p)) (k : K) :
    pairTrajectoriesCLM z k = (z.1 k,z.2 k) := rfl

/-- Opposite complex phases, with an arbitrary fixed real frequency sequence. -/
def analyticPhaseTrajectory (hp : p ≠ ⊤) (ω : ℤ → ℝ) (θ : C(K, ℝ))
    (b : Coeff ⊤) (z : Coeff p × Coeff p) : C(K, Coeff p × Coeff p) :=
  pairTrajectoriesCLM (Coeff.analyticPhaseTrajectory hp ω θ b z.1,
    Coeff.analyticPhaseTrajectory hp ω (-θ) b z.2)

/-- Entire dependence in the Banach space of compact-time pair trajectories. -/
theorem analyticAt_analyticPhaseTrajectory (hp : p ≠ ⊤) (ω : ℤ → ℝ) (θ : C(K, ℝ))
    (x : Coeff ⊤ × (Coeff p × Coeff p)) :
    AnalyticAt ℂ (fun y : Coeff ⊤ × (Coeff p × Coeff p) =>
      analyticPhaseTrajectory hp ω θ y.1 y.2) x := by
  apply ((pairTrajectoriesCLM (p := p) (K := K)).analyticAt _).comp
    (f := fun y : Coeff ⊤ × (Coeff p × Coeff p) =>
      (Coeff.analyticPhaseTrajectory hp ω θ y.1 y.2.1,
       Coeff.analyticPhaseTrajectory hp ω (-θ) y.1 y.2.2))
  have hb : AnalyticAt ℂ (fun y : Coeff ⊤ × (Coeff p × Coeff p) => y.1) x := analyticAt_fst
  have hz₁ : AnalyticAt ℂ (fun y : Coeff ⊤ × (Coeff p × Coeff p) => y.2.1) x :=
    ((ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)).analyticAt _).comp analyticAt_snd
  have hz₂ : AnalyticAt ℂ (fun y : Coeff ⊤ × (Coeff p × Coeff p) => y.2.2) x :=
    ((ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p)).analyticAt _).comp analyticAt_snd
  exact ((Coeff.analyticAt_analyticPhaseTrajectory hp ω θ _).comp
    (f := fun y : Coeff ⊤ × (Coeff p × Coeff p) => (y.1,y.2.1)) (hb.prod hz₁)).prod
    ((Coeff.analyticAt_analyticPhaseTrajectory hp ω (-θ) _).comp
      (f := fun y : Coeff ⊤ × (Coeff p × Coeff p) => (y.1,y.2.2)) (hb.prod hz₂))

@[simp] theorem analyticPhaseTrajectory_fst (hp : p ≠ ⊤) (ω : ℤ → ℝ) (θ : C(K, ℝ))
    (b : Coeff ⊤) (z : Coeff p × Coeff p) (k : K) (n : ℤ) :
    (analyticPhaseTrajectory hp ω θ b z k).1 n =
      Complex.exp ((θ k : ℂ)*I*((ω n : ℂ)+b n))*z.1 n :=
  Coeff.analyticPhaseTrajectory_apply hp ω θ b z.1 k n

@[simp] theorem analyticPhaseTrajectory_snd (hp : p ≠ ⊤) (ω : ℤ → ℝ) (θ : C(K, ℝ))
    (b : Coeff ⊤) (z : Coeff p × Coeff p) (k : K) (n : ℤ) :
    (analyticPhaseTrajectory hp ω θ b z k).2 n =
      Complex.exp (-(θ k : ℂ)*I*((ω n : ℂ)+b n))*z.2 n := by
  simpa only [analyticPhaseTrajectory, pairTrajectoriesCLM_apply, ContinuousMap.neg_apply, Complex.ofReal_neg] using!
    Coeff.analyticPhaseTrajectory_apply hp ω (-θ) b z.2 k n

end NLS.Birkhoff
