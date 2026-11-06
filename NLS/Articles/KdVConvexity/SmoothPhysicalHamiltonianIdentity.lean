import NLS.Articles.KdVConvexity.UnconditionalContourExtension
import NLS.KdV.HillSmoothIntrinsicQuarticTrace

/-! # Physical renormalized energy on smooth sources in the summable action domain -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ContDiff
namespace NLS.Articles.KdVConvexity
open NLS.KdV

/-- Exact agreement with the physical renormalized KdV energy at smooth
sources in the original summable linear-action domain. The recovery and
cubic summability inputs are supplied by the constructed contour family;
no energy identity or primitive asymptotics is assumed. Extension of this
physical identity to the entire original action domain remains separate. -/
theorem contourHamiltonian_eq_physical_renormalized_smooth
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0)
    (a : ActionSpace) (R : ℕ+ → BaseActionSpace → ℂ)
    (ha : ∀ n : ℕ+, a n = hillHminusRealGapContourMoment
      (hillOriginalHminusSource (hillContinuousCoefficients Q)) (hillOriginalHminusSource_real _ hr) n 0)
    (hR : ∀ n : ℕ+, R n (baseActionInclusion a) = hillHminusRealGapCubicContourMoment
      (hillOriginalHminusSource (hillContinuousCoefficients Q)) (hillOriginalHminusSource_real _ hr) n)
    (hlinear : Summable (fun n : ℕ+ => ‖((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ)*a n‖))
    (hcubic : Summable (fun n => ‖weightedContourTerm R n (baseActionInclusion a)‖)) :
    contourHamiltonian R a = classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))-
      ∑' n : ℕ+, ((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ)*a n := by
  let L : ℕ+ → ℂ := fun n => ((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ)*a n
  let C : ℕ+ → ℂ := fun n => weightedContourTerm R n (baseActionInclusion a)
  have hs : HasSum (fun n : ℕ+ => L n+C n) ((∑' n, L n)+(∑' n, C n)) :=
    hlinear.of_norm.hasSum.add hcubic.of_norm.hasSum
  have hsn : HasSum (fun k : ℕ => L ⟨k+1,by omega⟩+C ⟨k+1,by omega⟩)
      ((∑' n, L n)+(∑' n, C n)) := by
    simpa only [Function.comp_def,Equiv.pnatEquivNat_symm_apply,Nat.succPNat] using
      Equiv.pnatEquivNat.symm.hasSum_iff.mpr hs
  have hphysical : Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range N, (L ⟨k+1,by omega⟩+C ⟨k+1,by omega⟩)) atTop
      (nhds (classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))) := by
    apply (tendsto_intrinsic_Arnold_cubic_trace_Hamiltonian_smooth Q hq hr hreal hf hp hmean).congr'
    apply Eventually.of_forall
    intro N
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [L,C,weightedContourTerm]
    simpa only [] using! (congrArg₂
      (fun x y : ℂ => ((8*((k+1 : ℕ) : ℝ)^3*Real.pi^3 : ℝ) : ℂ)*x+
        ((8*((k+1 : ℕ) : ℝ)*Real.pi : ℝ) : ℂ)*y)
      (ha ⟨k+1,by omega⟩) (hR ⟨k+1,by omega⟩)).symm
  have he := tendsto_nhds_unique hsn.tendsto_sum_nat hphysical
  change (∑' n, C n) = _
  linear_combination he

end NLS.Articles.KdVConvexity
