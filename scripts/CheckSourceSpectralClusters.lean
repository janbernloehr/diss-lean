import NLS.ZakharovShabat.SourceSpectralClusters

open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

example {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ)
    {z : ℂ} (hz : z ∈ sourceSpectralCluster hp hp1 φ n) :
    z.re ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re :=
  sourceSpectralCluster_mem_gap hp hp1 φ hφ n hz

example {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    {i j : ℤ} (hij : i < j) {z w : ℂ}
    (hz : z ∈ sourceSpectralCluster hp hp1 φ i)
    (hw : w ∈ sourceSpectralCluster hp hp1 φ j) : z.re < w.re :=
  sourceSpectralCluster_re_lt_of_lt hp hp1 φ hφ hij hz hw

example {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    {i j : ℤ} (hij : i < j) {z w : ℂ}
    (hz : z ∈ sourceSpectralCluster hp hp1 φ i)
    (hw : w ∈ sourceSpectralCluster hp hp1 φ j) :
    (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) j).re -
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) i).re ≤
        dist z w :=
  sourceSpectralCluster_dist_ge_gap hp hp1 φ hφ hij hz hw

end NLS.ZakharovShabat
