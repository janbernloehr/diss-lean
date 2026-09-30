import NLS.ZakharovShabat.SourceRealTypeBanachSpace
import NLS.SequenceSpaces.Truncation

/-! # Finite real-type Fourier approximation in the source topology

Symmetric frequency truncation preserves real type and converges in
every finite source exponent. A continuous scalar identity on an open
source set therefore follows from its values at finite real potentials.
The open set may impose nonzero gaps: the truncations eventually stay
in it. This supplies the density step used in Corollary 13.2.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceSymmetricTruncate (N : ℕ) (ψ : CoeffPair p) : CoeffPair p :=
  (CoeffPair.toMax p).symm
    (Coeff.truncate (Finset.Icc (-(N:ℤ)) N) ψ.fst,Coeff.truncate (Finset.Icc (-(N:ℤ)) N) ψ.snd)

theorem sourceSymmetricTruncate_realType (N : ℕ) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) :
    IsRealType (CoeffPair.toMax p (sourceSymmetricTruncate N ψ)) := by
  intro n
  have hneg : -n ∈ Finset.Icc (-(N:ℤ)) N ↔ n ∈ Finset.Icc (-(N:ℤ)) N := by
    simp only [Finset.mem_Icc]
    omega
  change Coeff.truncate _ ψ.snd n = conj (Coeff.truncate _ ψ.fst (-n))
  by_cases hn : n ∈ Finset.Icc (-(N:ℤ)) N
  · simp only [Coeff.truncate_apply,if_pos hn,if_pos (hneg.mpr hn)]
    exact hreal n
  · simp only [Coeff.truncate_apply,if_neg hn,if_neg (fun h => hn (hneg.mp h)),map_zero]

theorem sourceSymmetricTruncate_finite (N : ℕ) (ψ : CoeffPair p) :
    Coeff.HasFiniteSupport (sourceSymmetricTruncate N ψ).fst ∧
      Coeff.HasFiniteSupport (sourceSymmetricTruncate N ψ).snd :=
  ⟨Coeff.truncate_hasFiniteSupport _ _,Coeff.truncate_hasFiniteSupport _ _⟩

theorem tendsto_sourceSymmetricTruncate (hp : p ≠ ⊤) (ψ : CoeffPair p) :
    Tendsto (fun N : ℕ => sourceSymmetricTruncate N ψ) atTop (𝓝 ψ) := by
  have h := ((Coeff.tendsto_truncate hp ψ.fst).comp Finset.tendsto_Icc_neg).prodMk_nhds
    ((Coeff.tendsto_truncate hp ψ.snd).comp Finset.tendsto_Icc_neg)
  exact ((CoeffPair.toMax p).symm.continuous.tendsto (ψ.fst,ψ.snd)).comp h

/-- Continuous identities extend from finite real potentials even on an
open subset that removes one or several closed-gap loci. -/
theorem eq_of_continuousOn_of_finite_realType (hp : p ≠ ⊤)
    {U : Set (CoeffPair p)} (hU : IsOpen U) {H : CoeffPair p → ℂ}
    (hH : ContinuousOn H U) (c : ℂ)
    (hfinite : ∀ ψ ∈ U, IsRealType (CoeffPair.toMax p ψ) →
      Coeff.HasFiniteSupport ψ.fst → Coeff.HasFiniteSupport ψ.snd → H ψ = c)
    (φ : CoeffPair p) (hφ : φ ∈ U) (hreal : IsRealType (CoeffPair.toMax p φ)) : H φ = c := by
  have hT := tendsto_sourceSymmetricTruncate hp φ
  have hlim := ((hH φ hφ).continuousAt (hU.mem_nhds hφ)).tendsto.comp hT
  have heq : (fun N : ℕ => H (sourceSymmetricTruncate N φ)) =ᶠ[atTop] fun _ => c := by
    filter_upwards [hT.eventually (hU.mem_nhds hφ)] with N hN
    exact hfinite _ hN (sourceSymmetricTruncate_realType N φ hreal)
      (sourceSymmetricTruncate_finite N φ).1 (sourceSymmetricTruncate_finite N φ).2
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' heq.symm)

end NLS.ZakharovShabat
