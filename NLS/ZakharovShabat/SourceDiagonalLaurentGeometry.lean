import NLS.ZakharovShabat.SourceComponentSwapEndpoints
import NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
import NLS.ZakharovShabat.RealDeletedPeriodicProduct

/-! # Zero-excluding action discs around the full real diagonal

No H1 hypothesis is used. Fixed-index component reflection places zero
in the original central gap at every real coefficient diagonal. Every
noncentral isolating disc therefore excludes zero simultaneously.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def realDiagonalSourceLocus (p : ℝ≥0∞) [Fact (1 ≤ p)] : Set (CoeffPair p) :=
  {φ | IsRealType (CoeffPair.toMax p φ) ∧ φ.fst = φ.snd}

theorem zero_mem_central_segment_of_diagonal (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hdiag : φ.val.fst = φ.val.snd) :
    (0 : ℂ) ∈ sourcePeriodicSegment hp hp1 φ.val 0 := by
  have hs := (sourceComponentSwap_eq_self_iff φ.val).mpr hdiag
  have he := (sourceCanonicalPeriodicEndpoints_componentSwap hp hp1 φ.val 0).1
  rw [hs,neg_zero] at he
  have hre := congrArg Complex.re he
  simp only [neg_re] at hre
  have ho := re_le_of_complexLexLE
    ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _)).2.1 0)
  apply sourcePeriodicSegment_mem_of_realIcc hp hp1 φ.val φ.property 0 0
  constructor <;> linarith

namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem zero_not_mem_noncentral_disc_of_diagonal
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (hdiag : C.discs.source.val.fst = C.discs.source.val.snd) (n : ℤ) (hn : n ≠ 0) :
    (0 : ℂ) ∉ closedBall (C.discs.center n) (C.discs.outer n) := by
  intro hz
  exact C.discs.avoids_other _ (mem_ball_self C.discs.sourceRadius_pos) n hz 0 hn.symm
    (zero_mem_central_segment_of_diagonal hp hp1 C.discs.source hdiag)

end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
