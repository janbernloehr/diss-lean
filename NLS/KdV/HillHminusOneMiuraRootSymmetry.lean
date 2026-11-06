import NLS.KdV.HillHminusOneCriticalPoints
import NLS.ZakharovShabat.EvenDiscriminantCanonicalRoot

/-! # Actual canonical root symmetry on rough Miura charts

The even diagonal L2 trace supplies complete endpoint reflection and
oddness of the actual NLS canonical root at every complex chart input.
-/
noncomputable section
open Set Complex
namespace NLS.KdV
open NLS.ZakharovShabat

theorem hillMiuraCanonicalEndpoints_neg (u : Coeff 2) (n : ℤ) :
    canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential (hillMiuraDiagonal u))
        (periodOnePotential_mem _) (-n) =
      -canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential (hillMiuraDiagonal u))
        (periodOnePotential_mem _) n ∧
    canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential (hillMiuraDiagonal u))
        (periodOnePotential_mem _) (-n) =
      -canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential (hillMiuraDiagonal u))
        (periodOnePotential_mem _) n :=
  canonicalPeriodicEndpoints_neg_of_discriminant_even (by simp) (by norm_num) _
    (periodOnePotential_mem _) (hillMiuraFrequencyTrace_even u) n

namespace HillHminusMiuraChart

theorem sourceCanonicalRoot_neg (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (z : ℂ) :
    sourceCanonicalRoot (by simp) (by norm_num) (C.criticalSource q) (-z) =
      -sourceCanonicalRoot (by simp) (by norm_num) (C.criticalSource q) z :=
  sourceCanonicalRoot_neg_of_discriminant_even (by simp) (by norm_num) _
    (hillMiuraFrequencyTrace_even (C.lift q)) z

theorem neg_mem_sourceCanonicalRootDomain_iff (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (z : ℂ) :
    -z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (C.criticalSource q) ↔
      z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (C.criticalSource q) :=
  neg_mem_sourceCanonicalRootDomain_iff_of_discriminant_even (by simp) (by norm_num) _
    (hillMiuraFrequencyTrace_even (C.lift q)) z

end HillHminusMiuraChart
end NLS.KdV
