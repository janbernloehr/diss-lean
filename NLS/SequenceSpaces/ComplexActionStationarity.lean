import NLS.SequenceSpaces.RealActionRotation
import NLS.SequenceSpaces.RealFormIdentity

/-! # Complex infinitesimal action invariance

Real action invariance kills the derivative along each real coordinate
rotation. Holomorphic uniqueness extends this identity to every point of
an open convex complex domain meeting the real form. The selected action
may vanish; no square root or inverse action is used.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The bounded complex-linear coordinate rotation vector field. -/
def actionRotationVectorCLM (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℤ) :
    (Coeff p × Coeff p) →L[ℂ] (Coeff p × Coeff p) :=
  let P := (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p k).comp
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p k)
  (-(P.comp (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p)))).prod
    (P.comp (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)))

@[simp] theorem actionRotationVectorCLM_apply (k : ℤ) (z : Coeff p × Coeff p) :
    actionRotationVectorCLM p k z = (-lp.single p k (z.2 k),lp.single p k (z.1 k)) := rfl

/-- Real coordinate rotations have the same velocity after complex inclusion. -/
theorem complex_actionRotationVector (z : RealCoeff p × RealCoeff p) (k : ℤ) :
    ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p))
        (RealCoeff.actionRotationVector z k) =
      actionRotationVectorCLM p k (((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) z) := by
  classical
  apply Prod.ext <;> ext n <;>
    by_cases hn : n = k <;>
    simp [actionRotationVectorCLM,RealCoeff.actionRotationVector,lp.single_apply,hn]
    <;> rfl

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Local real action invariance makes the complex derivative vanish on the
rotation vector at every real point of the domain. -/
theorem fderiv_actionRotationVector_eq_zero_at_real
    (f : (Coeff p × Coeff p) → F) (U : Set (Coeff p × Coeff p)) (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U)
    (hinv : ∀ z ∈ U, ∀ w ∈ U, z ∈ realPairLocus p → w ∈ realPairLocus p →
      (∀ n, w.1 n^2+w.2 n^2 = z.1 n^2+z.2 n^2) → f w = f z)
    (z : Coeff p × Coeff p) (hz : z ∈ U) (hzr : z ∈ realPairLocus p) (k : ℤ) :
    fderiv ℂ f z (actionRotationVectorCLM p k z) = 0 := by
  obtain ⟨x,rfl⟩ := (mem_realPairLocus_iff z).mp hzr
  let J := (RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)
  let γ : ℝ → Coeff p × Coeff p := fun t => J (RealCoeff.actionRotation x k t)
  have hγ0 : γ 0 = J x := by simp [γ]
  have hγ : HasDerivAt γ (actionRotationVectorCLM p k (J x)) 0 := by
    have hh := J.hasFDerivAt.comp_hasDerivAt 0 (RealCoeff.hasDerivAt_actionRotation x k 0)
    simpa only [γ,J,Function.comp_def,RealCoeff.actionRotation_zero,complex_actionRotationVector] using hh
  have hstay : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ U := by
    have hmem : U ∈ 𝓝 (γ 0) := by simpa only [hγ0] using hU.mem_nhds hz
    exact hγ.continuousAt hmem
  have heq : (fun t => f (γ t)) =ᶠ[𝓝 (0 : ℝ)] (fun _ => f (J x)) := by
    filter_upwards [hstay] with t ht
    apply hinv (J x) hz (γ t) ht
    · exact (mem_realPairLocus_iff _).mpr ⟨x,rfl⟩
    · exact (mem_realPairLocus_iff _).mpr ⟨RealCoeff.actionRotation x k t,rfl⟩
    · intro n
      have he := RealCoeff.pairAction_actionRotation x k n t
      unfold RealCoeff.pairAction at he
      have he' : (RealCoeff.actionRotation x k t).1 n^2+(RealCoeff.actionRotation x k t).2 n^2 =
          x.1 n^2+x.2 n^2 := by linarith
      change (((RealCoeff.actionRotation x k t).1 n : ℝ) : ℂ)^2+
        (((RealCoeff.actionRotation x k t).2 n : ℝ) : ℂ)^2 = (x.1 n : ℂ)^2+(x.2 n : ℂ)^2
      exact_mod_cast he'
  have hdf : HasFDerivAt f ((fderiv ℂ f (J x)).restrictScalars ℝ) (γ 0) := by
    rw [hγ0]
    exact ((hf _ hz).differentiableAt (hU.mem_nhds hz)).hasFDerivAt.restrictScalars ℝ
  have hd := hdf.comp_hasDerivAt (f := γ) 0 hγ
  have hd0 : HasDerivAt (fun t => f (γ t)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (f (J x))).congr_of_eventuallyEq heq
  exact hd.unique hd0

/-- Real action invariance extends to complex infinitesimal rotations on
an open convex domain. This holds in the full Banach target norm. -/
theorem fderiv_actionRotationVector_eq_zero_of_real_action_invariance
    (f : (Coeff p × Coeff p) → F) (U : Set (Coeff p × Coeff p))
    (hU : IsOpen U) (hconv : Convex ℝ U)
    (c : Coeff p × Coeff p) (hc : c ∈ U) (hcr : c ∈ realPairLocus p)
    (hf : AnalyticOnNhd ℂ f U)
    (hinv : ∀ z ∈ U, ∀ w ∈ U, z ∈ realPairLocus p → w ∈ realPairLocus p →
      (∀ n, w.1 n^2+w.2 n^2 = z.1 n^2+z.2 n^2) → f w = f z)
    (z : Coeff p × Coeff p) (hz : z ∈ U) (k : ℤ) :
    fderiv ℂ f z (actionRotationVectorCLM p k z) = 0 := by
  have hg : AnalyticOnNhd ℂ (fun z => fderiv ℂ f z (actionRotationVectorCLM p k z)) U := by
    intro a ha
    exact ((ContinuousLinearMap.id ℂ ((Coeff p × Coeff p) →L[ℂ] F)).analyticAt_bilinear _).comp₂
      (hf.fderiv a ha) ((actionRotationVectorCLM p k).analyticAt a)
  exact eqOn_of_realPair_agreement _ (fun _ => (0 : F)) U hU hconv c hc hcr
    hg.differentiableOn (differentiableOn_const (0 : F))
    (fun a ha har => fderiv_actionRotationVector_eq_zero_at_real f U hU hf.differentiableOn hinv a ha har k)
    hz

end NLS.Coeff
