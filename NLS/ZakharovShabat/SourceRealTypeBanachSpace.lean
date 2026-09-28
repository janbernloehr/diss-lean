import NLS.ZakharovShabat.SourcePsiGapRootMap
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The real-type source Banach space

The Fourier real-type relation is closed under addition and real
scalar multiplication, and is topologically closed. Its source locus
therefore carries the inherited complete real normed-space structure
needed to formulate real differentiability and analyticity.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal ComplexConjugate ContDiff
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Real-type coefficient pairs form a real linear subspace. -/
def realTypeSourceSubmodule (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Submodule ℝ (CoeffPair p) where
  carrier := realTypeSourceLocus p
  zero_mem' := by simp [realTypeSourceLocus]
  add_mem' := by
    intro φ ψ hφ hψ
    change IsRealType (CoeffPair.toMax p (φ + ψ))
    simpa only [map_add] using (hφ.add hψ)
  smul_mem' := by
    intro r φ hφ
    change IsRealType (CoeffPair.toMax p (r • φ))
    change IsRealType (CoeffPair.toMax p ((r : ℂ) • φ))
    simpa only [map_smul] using hφ.ofReal_smul r

@[simp] theorem mem_realTypeSourceSubmodule (φ : CoeffPair p) :
    φ ∈ realTypeSourceSubmodule p ↔
      IsRealType (CoeffPair.toMax p φ) := Iff.rfl

/-- The real-type relation is closed under norm limits of source
coefficient pairs. -/
theorem isClosed_realTypeSourceLocus :
    IsClosed (realTypeSourceLocus p) := by
  have hcoord (m : ℤ) : IsClosed
      {φ : CoeffPair p |
        (CoeffPair.toMax p φ).2 m =
          conj ((CoeffPair.toMax p φ).1 (-m))} := by
    have hsnd : Continuous
        (fun φ : CoeffPair p => (CoeffPair.toMax p φ).2 m) :=
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).continuous.comp
        (continuous_snd.comp (CoeffPair.toMax p).continuous)
    have hfst : Continuous
        (fun φ : CoeffPair p => conj ((CoeffPair.toMax p φ).1 (-m))) :=
      continuous_conj.comp
        ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p (-m)).continuous.comp
          (continuous_fst.comp (CoeffPair.toMax p).continuous))
    exact isClosed_eq hsnd hfst
  have hset : realTypeSourceLocus p =
      ⋂ m : ℤ,
        {φ : CoeffPair p |
          (CoeffPair.toMax p φ).2 m =
            conj ((CoeffPair.toMax p φ).1 (-m))} := by
    ext φ
    simp [realTypeSourceLocus,IsRealType]
  rw [hset]
  exact isClosed_iInter hcoord

/-- The real-type subspace is closed in the ambient coefficient space. -/
theorem isClosed_realTypeSourceSubmodule :
    IsClosed (realTypeSourceSubmodule p : Set (CoeffPair p)) :=
  isClosed_realTypeSourceLocus (p := p)

/-- Real-type coefficient pairs form a complete real normed space. -/
instance : CompleteSpace (realTypeSourceSubmodule p) :=
  (isClosed_realTypeSourceSubmodule (p := p)).completeSpace_coe

/-- On the complete real-type source space, the canonical gap root
map is continuously Fréchet differentiable at every point. -/
theorem contDiffAt_sourcePsiGapRoot_real
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : realTypeSourceSubmodule p) :
    ContDiffAt ℝ 1
      (fun ψ : realTypeSourceSubmodule p => sourcePsiGapRoot hp hp1 n ψ) φ := by
  obtain ⟨s,hs,hsφ,hlocal⟩ :=
    exists_C1_local_extension_sourcePsiGapRoot hp hp1 n φ
  have hsub : ContDiffAt ℝ 1
      (fun ψ : realTypeSourceSubmodule p => (ψ : CoeffPair p)) φ := by
    exact (realTypeSourceSubmodule p).subtypeL.contDiff.contDiffAt
  have hscomp : ContDiffAt ℝ 1
      (fun ψ : realTypeSourceSubmodule p => s (ψ : CoeffPair p)) φ :=
    (hs.restrict_scalars ℝ).comp φ hsub
  have hval : Tendsto
      (fun ψ : realTypeSourceSubmodule p => (ψ : CoeffPair p))
      (𝓝 φ) (𝓝 (φ : CoeffPair p)) :=
    continuous_subtype_val.continuousAt
  have hEq : (fun ψ : realTypeSourceSubmodule p =>
        sourcePsiGapRoot hp hp1 n ψ) =ᶠ[𝓝 φ]
      (fun ψ => s (ψ : CoeffPair p)) := by
    have h := hval.eventually hlocal
    apply h.mono
    intro ψ hψ
    exact (hψ ψ.property).symm
  exact hscomp.congr_of_eventuallyEq hEq

/-- The canonical gap-root map is globally `C¹` on the real Banach
source space. -/
theorem contDiff_sourcePsiGapRoot_real
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    ContDiff ℝ 1
      (fun ψ : realTypeSourceSubmodule p => sourcePsiGapRoot hp hp1 n ψ) :=
  contDiff_iff_contDiffAt.mpr
    (fun φ => contDiffAt_sourcePsiGapRoot_real hp hp1 n φ)

end NLS.ZakharovShabat
