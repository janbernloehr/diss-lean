import NLS.ZakharovShabat.SourceWeightedEtaRemainderComplex
import NLS.SequenceSpaces.BoundedCoordinateAnalytic

/-! # Native weighted eta-remainder analyticity

Coordinate analyticity and locally bounded native weighted realizations give the Banach-valued analytic map, with exact evaluations.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Actual weighted eta remainder, with local membership proved below. -/
def normalizedWeightedEtaRemainderSequence (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (w : SpectralWeight)
    (ψ : CoeffPair p) : Coeff p :=
  Coeff.ofFunctionOrZero p (fun n => (w (2*n):ℂ)*sourceAngularEtaRemainder hp hp1 n s
    (normalizedWeightedSource w ψ))

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
include D

/-- Native weighted eta remainders are locally bounded and analytic over complex sources, with exact coordinates. -/
theorem exists_local_normalizedWeightedEtaRemainder_analytic
    (w : SpectralWeight) (φ : realTypeSourceLocus p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧
      AnalyticOnNhd ℂ (normalizedWeightedEtaRemainderSequence hp hp1 s w) U ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ U,
        ‖normalizedWeightedEtaRemainderSequence hp hp1 s w ψ‖ ≤ M ∧
        ∀ n, normalizedWeightedEtaRemainderSequence hp hp1 s w ψ n =
          (w (2*n):ℂ)*sourceAngularEtaRemainder hp hp1 n s (normalizedWeightedSource w ψ) := by
  let φu : realTypeSourceSubmodule p :=
    ⟨normalizedWeightedSource w φ.val,normalizedWeightedSource_realType w φ.val φ.property⟩
  obtain ⟨Vb,hVb,hφb,_,M,hM,hb⟩ := D.exists_local_normalizedWeightedEtaRemainder_bound w φ
  obtain ⟨Va,hVa,hφa,_,ha⟩ := D.exists_local_etaRemainder_allIndices_analytic φu
  let U := Vb ∩ normalizedWeightedSource w ⁻¹' Va
  have hU : IsOpen U := hVb.inter (hVa.preimage (continuous_normalizedWeightedSource w))
  have hcoord (ψ : CoeffPair p) (hψ : ψ ∈ U) (n : ℤ) :
      normalizedWeightedEtaRemainderSequence hp hp1 s w ψ n =
        (w (2*n):ℂ)*sourceAngularEtaRemainder hp hp1 n s (normalizedWeightedSource w ψ) :=
    Coeff.ofFunctionOrZero_apply_of_mem p _ (hb ψ hψ.1).1 n
  refine ⟨U,hU,⟨hφb,hφa⟩,?_,M,hM,fun ψ hψ => ⟨(hb ψ hψ.1).2,hcoord ψ hψ⟩⟩
  apply Coeff.analyticOnNhd_of_bounded_coordinatewise _ hU _ M (fun ψ hψ => (hb ψ hψ.1).2)
  intro n ψ hψ
  have hcomp : AnalyticAt ℂ (fun χ : CoeffPair p => sourceAngularEtaRemainder hp hp1 n s
      (normalizedWeightedSource w χ)) ψ :=
    (ha n _ hψ.2).comp (f := normalizedWeightedSource w) (x := ψ)
      ((normalizedWeightedSourceCLM (p := p) w).analyticAt ψ)
  have hweighted : AnalyticAt ℂ (fun χ : CoeffPair p => (w (2*n):ℂ)*sourceAngularEtaRemainder hp hp1 n s
      (normalizedWeightedSource w χ)) ψ := analyticAt_const.mul hcomp
  apply hweighted.congr
  filter_upwards [hU.mem_nhds hψ] with χ hχ
  exact (hcoord χ hχ n).symm

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
