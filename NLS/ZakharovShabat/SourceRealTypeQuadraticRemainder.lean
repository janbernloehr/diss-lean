import NLS.ZakharovShabat.SourceRealTypeBanachSpace
import NLS.ZakharovShabat.SourcePsiGapRootDerivativeLipschitz

/-!
# Quadratic approximation on the real-type source Banach space

The complex local quadratic estimate for the canonical gap roots
restricts to the complete real-type source space. Its linear term is
the actual real Fréchet derivative of the globally selected root map,
because the complex branch agrees with that map on a neighborhood.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat

/-- On the real-type Banach source space, the canonical gap-root map
has a locally uniform quadratic remainder around every source. -/
theorem exists_local_quadratic_remainder_sourcePsiGapRoot_realDerivative
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : realTypeSourceSubmodule p) :
    ∃ R K : ℝ, 0 < R ∧ 0 ≤ K ∧
      ∀ ψ : realTypeSourceSubmodule p, ‖ψ - φ‖ < R →
        ‖sourcePsiGapRoot hp hp1 n ψ - sourcePsiGapRoot hp hp1 n φ -
            (fderiv ℝ
              (fun χ : realTypeSourceSubmodule p =>
                sourcePsiGapRoot hp hp1 n χ) φ) (ψ - φ)‖ ≤
          K * ‖ψ - φ‖ ^ 2 := by
  obtain ⟨s,hsφ,hsDiff,R,K,hR,hK,hreal,hbound⟩ :=
    exists_local_quadratic_remainder_sourcePsiGapRoot hp hp1 n φ
  let I : realTypeSourceSubmodule p →L[ℝ] CoeffPair p :=
    (realTypeSourceSubmodule p).subtypeL
  have hI : DifferentiableAt ℝ
      (fun ψ : realTypeSourceSubmodule p => (ψ : CoeffPair p)) φ :=
    I.differentiableAt
  have hsReal : DifferentiableAt ℝ s (φ : CoeffPair p) :=
    hsDiff.restrictScalars ℝ
  have hIderiv :
      fderiv ℝ (fun ψ : realTypeSourceSubmodule p => (ψ : CoeffPair p)) φ = I := by
    change fderiv ℝ I φ = I
    exact I.hasFDerivAt.fderiv
  have hcomp :
      fderiv ℝ (fun ψ : realTypeSourceSubmodule p => s (ψ : CoeffPair p)) φ =
        ((fderiv ℂ s (φ : CoeffPair p)).restrictScalars ℝ).comp I := by
    calc
      _ = (fderiv ℝ s (φ : CoeffPair p)).comp
          (fderiv ℝ (fun ψ : realTypeSourceSubmodule p => (ψ : CoeffPair p)) φ) := by
            simpa only [Function.comp_def] using (fderiv_comp φ hsReal hI)
      _ = ((fderiv ℂ s (φ : CoeffPair p)).restrictScalars ℝ).comp I := by
        rw [hIderiv, hsDiff.fderiv_restrictScalars (𝕜 := ℝ)]
  have hnear : {ψ : realTypeSourceSubmodule p |
      (ψ : CoeffPair p) ∈ ball (φ : CoeffPair p) R} ∈ 𝓝 φ :=
    ((isOpen_ball.preimage continuous_subtype_val).mem_nhds (mem_ball_self hR))
  have hEq : (fun ψ : realTypeSourceSubmodule p => s (ψ : CoeffPair p)) =ᶠ[𝓝 φ]
      (fun ψ => sourcePsiGapRoot hp hp1 n ψ) := by
    filter_upwards [hnear] with ψ hψ
    exact hreal ψ hψ ψ.property
  have hrootDeriv :
      fderiv ℝ
        (fun ψ : realTypeSourceSubmodule p => sourcePsiGapRoot hp hp1 n ψ) φ =
        ((fderiv ℂ s (φ : CoeffPair p)).restrictScalars ℝ).comp I :=
    hEq.fderiv_eq.symm.trans hcomp
  refine ⟨R,K,hR,hK,?_⟩
  intro ψ hψ
  have hnorm : ‖(ψ : CoeffPair p) - (φ : CoeffPair p)‖ = ‖ψ - φ‖ := rfl
  have hψball : (ψ : CoeffPair p) ∈ ball (φ : CoeffPair p) R := by
    simpa only [mem_ball,dist_eq_norm,hnorm] using hψ
  have hderivApply :
      (fderiv ℝ
        (fun χ : realTypeSourceSubmodule p => sourcePsiGapRoot hp hp1 n χ) φ) (ψ - φ) =
        (fderiv ℂ s (φ : CoeffPair p))
          ((ψ : CoeffPair p) - (φ : CoeffPair p)) := by
    rw [hrootDeriv]
    simp [I]
  have hψeq :
      (⟨(ψ : CoeffPair p),ψ.property⟩ : realTypeSourceLocus p) = ψ :=
    Subtype.ext rfl
  simpa only [hreal ψ hψball ψ.property,hψeq,hsφ,hnorm,← hderivApply] using
    hbound ψ hψball

end NLS.ZakharovShabat
