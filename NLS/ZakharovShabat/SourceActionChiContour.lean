import NLS.ZakharovShabat.SourceActionChi
import NLS.ZakharovShabat.SourceLemma11_1
import NLS.ComplexAnalysis.PiecewiseContourCongruence

/-!
# The recentered action integral following equation (2.18)

The vanishing unweighted period allows the spectral variable to be
recentered at the actual critical point. Substituting the literal deleted
product gives the exact factor i/π for every admissible piecewise C¹
circuit in each original disk, at every complex source of the same W.
-/

noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual indexed action is the recentered χ_n contour integral.
The selected gap may be collapsed, and the contour may have corners. -/
theorem SourceLemma11_1Data.action_eq_chi_circuit
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (H : SourceLemma11_1Data hp hp1 W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V) (n : ℤ)
    (Γ : PiecewiseC1Loop) (hΓ : Γ.Inside (D n \ sourcePeriodicSegment hp hp1 ψ n))
    (hw : Γ.windingIntegral
      (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) = 1) :
    sourceIndexedAction hp hp1 n ψ = Complex.I/(Real.pi : ℂ)*Γ.integral (fun z =>
      (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z)^2 /
        sourceStandardRoot hp hp1 ψ n z*sourceActionChi hp hp1 n ψ z) := by
  let a := canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let f := fun z => sourceCriticalRootRatioJoint hp hp1 (z,ψ)
  have hroot : D n \ sourcePeriodicSegment hp hp1 ψ n ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
    intro z hz m
    by_cases hm : m = n
    · subst m; exact hz.2
    · exact hD.disk_subset_omittedDomain ψ hψV n hz.1 m hm
  have hf : ContinuousOn f (D n \ sourcePeriodicSegment hp hp1 ψ n) :=
    (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ).continuousOn.mono hroot
  have hz : Γ.integral f = 0 :=
    H.previous.previous.previous.previous.originalDisk_loopIntegral_zero hD ψ hψW hψV n Γ hΓ
  have hshift : Γ.integral (fun z => (z-a)*f z) = Γ.integral (fun z => z*f z) := by
    have he : (fun z => (z-a)*f z) = (fun z => z*f z-a*f z) := by funext z; ring
    rw [he,Γ.integral_sub (fun z => z*f z) (fun z => a*f z)
      (continuousOn_id.mul hf) (continuousOn_const.mul hf) hΓ,
      Γ.integral_const_mul,hz,mul_zero,sub_zero]
  have heq : Γ.integral (fun z => (z-a)*f z) = Γ.integral (fun z =>
      Complex.I*((a-z)^2/sourceStandardRoot hp hp1 ψ n z*sourceActionChi hp hp1 n ψ z)) := by
    apply Γ.integral_congr hΓ
    intro z hz
    dsimp only [f,sourceCriticalRootRatioJoint]
    rw [sourceCriticalRootRatio_eq_selectedFactor_mul_chi hp hp1 ψ n z (hroot hz)]
    dsimp only [a]
    ring
  calc
    sourceIndexedAction hp hp1 n ψ = (Real.pi : ℂ)⁻¹*Γ.integral (fun z => z*f z) := by
      simpa only [f,sourceCriticalRootRatioJoint,mul_div_assoc] using H.previous.circuit hD ψ hψW hψV n Γ hΓ hw
    _ = (Real.pi : ℂ)⁻¹*Γ.integral (fun z => (z-a)*f z) := by rw [hshift]
    _ = _ := by rw [heq,Γ.integral_const_mul]; dsimp only [a]; ring

end NLS.ZakharovShabat
