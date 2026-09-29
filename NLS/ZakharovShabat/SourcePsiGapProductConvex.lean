import NLS.ZakharovShabat.SourcePsiGapProductCompact
import Mathlib.Analysis.Convex.Basic

/-! # Real convexity of the full periodic gap product -/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem convex_sourcePeriodicGapRootSet
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    Convex ℝ (sourcePeriodicGapRootSet hp hp1 φ) := by
  intro a ha b hb u v hu hv huv m
  have hm := (convex_segment (𝕜 := ℝ)
    (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m)
    (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m))
      (ha m) (hb m) hu hv huv
  have heq : displacedRoots (u • a+v • b) m =
      u • displacedRoots a m+v • displacedRoots b m := by
    simp only [displacedRoots,lp.coeFn_add,lp.coeFn_smul,Pi.add_apply,Pi.smul_apply,smul_add]
    have hfree : u • ((Real.pi:ℂ)*m)+v • ((Real.pi:ℂ)*m) = (Real.pi:ℂ)*m := by
      rw [← add_smul,huv,one_smul]
    calc
      _ = (u • ((Real.pi:ℂ)*m)+v • ((Real.pi:ℂ)*m))+(u • a m+v • b m) := by rw [hfree]
      _ = _ := by abel
  rw [heq]
  exact hm

end NLS.ZakharovShabat
