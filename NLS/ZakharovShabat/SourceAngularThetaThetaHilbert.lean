import NLS.ZakharovShabat.SourceAngularThetaThetaFiniteGap
import NLS.ZakharovShabat.SourceFiniteGapDensity

/-!
# Angle/angle involution at every real Hilbert source

The actual angle/angle bracket is analytic on the joint open-gap
domain. Actual finite-gap sources are dense there in the real source
topology. The proved finite-gap spectral-flow identity therefore
extends to every real Hilbert source with the two selected gaps open.
-/

noncomputable section
open Set NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}

/-- Actual finite-gap density transfers the angle/angle identity
within the same joint open-gap domain. This transfer applies whenever
the finite-gap identity has been proved at the given exponent. -/
theorem thetaThetaBracket_eq_zero_of_finiteGap
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m : ℤ)
    (hfinite : ∀ ψ : realTypeSourceLocus p,
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) n ≠ 0 →
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) m ≠ 0 →
      ψ ∈ sourceFiniteGapLocus hp hp1 → sourceAngularThetaThetaBracket hp hp1 h2p n m s ψ.val = 0)
    (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0) :
    sourceAngularThetaThetaBracket hp hp1 h2p n m s φ.val = 0 := by
  let U : Set (CoeffPair p) :=
    {ψ | ψ ∈ W ∧ canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0} ∩
    {ψ | ψ ∈ W ∧ canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0}
  have ho : IsOpen U := (D.open_gap n).inter (D.open_gap m)
  let V : Set (realTypeSourceLocus p) := Subtype.val ⁻¹' U
  have hH : ContinuousOn (fun ψ : realTypeSourceLocus p =>
      sourceAngularThetaThetaBracket hp hp1 h2p n m s ψ.val) V := by
    intro ψ hψ
    exact ((D.analyticOnNhd_thetaThetaBracket h2p n m ψ.val hψ).continuousAt.comp
      continuous_subtype_val.continuousAt).continuousWithinAt
  exact eq_of_continuousOn_of_sourceFiniteGap hp hp1 (ho.preimage continuous_subtype_val) hH 0
    (fun ψ hψ hψfinite => hfinite ψ hψ.1.2 hψ.2.2 hψfinite)
    φ ⟨⟨D.real_subset φ.property,hn⟩,⟨D.real_subset φ.property,hm⟩⟩

/-- The full actual angle/angle bracket vanishes at every real
Hilbert source with both selected angle gaps open. Finite-gap density
and the finite-gap bracket identity are both proved inputs. -/
theorem thetaThetaBracket_eq_zero_of_realType
    {W₀ B W : Set (CoeffPair 2)} {s : (j : ℤ) → CoeffPair 2 → DeletedCoeff 2 j}
    (D : SourceAngularThetaCommonDomainData (p := 2) (by simp) (by norm_num) W₀ B W s)
    (n m : ℤ) (φ : realTypeSourceLocus 2)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0) :
    sourceAngularThetaThetaBracket (by simp) (by norm_num) (by norm_num) n m s φ.val = 0 :=
  D.thetaThetaBracket_eq_zero_of_finiteGap (by norm_num) n m
    (fun ψ hnψ hmψ hfinite => D.thetaThetaBracket_eq_zero_of_mem_sourceFiniteGapLocus
      n m ψ hnψ hmψ hfinite) φ hn hm

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
