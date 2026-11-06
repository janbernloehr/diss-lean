import NLS.KdV.MiuraPeriodicReflection
import NLS.ZakharovShabat.SourceCanonicalRootReflection

/-! The actual Miura canonical root is odd on the ENTIRE complex source
space. Its sign follows from the literal product, including the central factor. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV

theorem sourcePeriodicReflection_hillMiuraDiagonal (u : Coeff 2) :
    SourcePeriodicReflection (by norm_num) (by norm_num) (hillMiuraDiagonal u) := by
  intro n
  exact ⟨(hillMiuraDiracPair_neg u).1 n,(hillMiuraDiracPair_neg u).2 n⟩

theorem sourceCanonicalRoot_hillMiuraDiagonal_neg (u : Coeff 2) (z : ℂ) :
    sourceCanonicalRoot (by norm_num) (by norm_num) (hillMiuraDiagonal u) (-z) =
      -sourceCanonicalRoot (by norm_num) (by norm_num) (hillMiuraDiagonal u) z :=
  (sourcePeriodicReflection_hillMiuraDiagonal u).canonicalRoot_neg z

end NLS.KdV
