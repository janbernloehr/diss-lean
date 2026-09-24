import NLS.ZakharovShabat.SourceCriticalRootRatioCircleZeroRealNeighborhood
import NLS.ComplexAnalysis.RealLineIdentity

/-!
# Complex-line continuation of gap-contour vanishing

The fixed contour integral vanishes along real-type source lines for
real line parameters. Holomorphy in the complex line parameter and
the one-variable identity principle extend the vanishing to complex
parameters near zero.
-/

noncomputable section
open Set Metric Filter Complex
open scoped ENNReal Topology
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- From an open real-type source gap, the fixed enclosing-circle
integral vanishes on a complex neighborhood along every real-type
direction in source space. -/
theorem exists_local_sourceCriticalRootRatio_circleIntegral_complexLine_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ)
        (periodOnePotential_mem φ) n).re) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
      ∀ h : CoeffPair p, IsRealType (CoeffPair.toMax p h) →
        ∀ᶠ t in 𝓝 (0:ℂ),
          (∮ z in C(c,R),
            sourceCriticalRootRatioJoint hp hp1 (z,φ+t•h)) = 0 := by
  obtain ⟨V,hVopen,hφV,c,R,hR,_,hdiff,hzero⟩ :=
    exists_local_sourceCriticalRootRatio_circleIntegral_zero_on_realType
      hp hp1 φ hφ n hopen
  refine ⟨c,R,hR,?_⟩
  intro h hh
  let a : ℂ → CoeffPair p := fun t => φ+t•h
  let F : CoeffPair p → ℂ := fun ψ =>
    ∮ z in C(c,R), sourceCriticalRootRatioJoint hp hp1 (z,ψ)
  let U : Set ℂ := a ⁻¹' V
  have ha : Differentiable ℂ a := by
    dsimp [a]
    fun_prop
  have hUopen : IsOpen U := hVopen.preimage ha.continuous
  have h0 : (0:ℂ) ∈ U := by simpa [U,a] using hφV
  have hline : DifferentiableOn ℂ (fun t : ℂ => F (a t)) U := by
    intro t ht
    exact (((hdiff (a t) ht).differentiableAt (hVopen.mem_nhds ht)).comp t
      (ha t)).differentiableWithinAt
  have hanalytic : AnalyticAt ℂ (fun t : ℂ => F (a t)) 0 :=
    hline.analyticAt (hUopen.mem_nhds h0)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds h0)
  have hrealzero : ∃ ε : ℝ, 0 < ε ∧
      ∀ t : ℝ, |t| < ε → F (a (t:ℂ)) = 0 := by
    refine ⟨ε,hε,?_⟩
    intro t ht
    have htball : (t:ℂ) ∈ ball (0:ℂ) ε := by
      change dist (t:ℂ) 0 < ε
      simpa [dist_eq_norm, Complex.norm_real] using ht
    have hψV : a (t:ℂ) ∈ V := hball htball
    have hrealψ : IsRealType (CoeffPair.toMax p (a (t:ℂ))) := by
      change IsRealType (CoeffPair.toMax p (φ+(t:ℂ)•h))
      rw [map_add, map_smul]
      exact hφ.add (hh.ofReal_smul t)
    exact hzero (a (t:ℂ)) hψV hrealψ
  exact NLS.ComplexAnalysis.AnalyticAt.eventually_eq_zero_of_real_interval
    hanalytic hrealzero

end NLS.ZakharovShabat
