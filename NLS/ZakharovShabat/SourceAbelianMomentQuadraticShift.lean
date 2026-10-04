import NLS.ZakharovShabat.SourceAbelianMomentFiniteSums

/-! # Shifting the quadratic primitive contour to normalized moments

The identity `F_0 = F_k - i*k*pi` separates the quadratic moment, the
vanishing first moment, and the exact zero-order period. Summing on a
finite gap support gives the free-frequency correction in Lemma 20.2.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- The quadratic shift identity before using the normalized periods. -/
theorem sourceAbelianMomentCircle_quadratic_shift
    (n k : ℤ) (a : Coeff p) (ψ : CoeffPair p) (D : SourceAbelianSpectralChart hp hp1 W ψ)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ) :
    sourceAbelianMomentCircle hp hp1 W n 0 2 a ψ c R =
      sourceAbelianMomentCircle hp hp1 W n k 2 a ψ c R-
        (2*I*(Real.pi : ℂ)*k)*sourceAbelianMomentCircle hp hp1 W n k 1 a ψ c R-
        ((Real.pi : ℂ)*k)^2*sourceAbelianMomentCircle hp hp1 W n k 0 a ψ c R := by
  let f (m : ℕ) (z : ℂ) := sourceAbelianMomentIntegrand hp hp1 W n k m (z,(a,ψ))
  have hci (m : ℕ) : CircleIntegrable (f m) c R :=
    ((analyticOnNhd_sourceAbelianMomentIntegrand_fixed hp hp1 W n k m a ψ D).continuousOn.mono hcircle).circleIntegrable hR
  have he (z : ℂ) (hz : z ∈ sphere c R) :
      sourceAbelianMomentIntegrand hp hp1 W n 0 2 (z,(a,ψ)) =
        f 2 z-(2*I*(Real.pi : ℂ)*k)*f 1 z-((Real.pi : ℂ)*k)^2*f 0 z := by
    dsimp [f,sourceAbelianMomentIntegrand]
    rw [sourceFullAbelianPrimitive_index_shift D k z
      (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ (hcircle hz))]
    simp only [pow_one,pow_zero,one_mul]
    ring_nf
    simp only [I_sq]
    ring
  have hci1 : CircleIntegrable (fun z => (2*I*(Real.pi : ℂ)*k)*f 1 z) c R := (hci 1).const_mul _
  have hci0 : CircleIntegrable (fun z => ((Real.pi : ℂ)*k)^2*f 0 z) c R := (hci 0).const_mul _
  have hci21 : CircleIntegrable (fun z => f 2 z-(2*I*(Real.pi : ℂ)*k)*f 1 z) c R := (hci 2).sub hci1
  calc
    _ = ∮ z in C(c,R), f 2 z-(2*I*(Real.pi : ℂ)*k)*f 1 z-((Real.pi : ℂ)*k)^2*f 0 z :=
      circleIntegral.integral_congr hR he
    _ = _ := by
      rw [circleIntegral.integral_sub hci21 hci0,
        circleIntegral.integral_sub (hci 2) hci1,
        circleIntegral.integral_const_mul,circleIntegral.integral_const_mul]
      rfl

namespace SourceAbelianMomentAtlas
variable {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable (A : SourceAbelianMomentAtlas hp hp1 W s)

/-- On any assigned local circle, the unshifted quadratic contour is
exactly the second moment minus its normalized Kronecker correction. -/
theorem unshifted_quadratic_circle (φ : realTypeSourceLocus p) (ψ : CoeffPair p)
    (hψ : ψ ∈ A.sourceBall φ) (n k : ℤ) :
    sourceAbelianMomentCircle hp hp1 W n 0 2 (s n ψ : Coeff p) ψ
      ((A.localChart φ).center k) ((A.localChart φ).contourRadius k) =
        A.moment n k 2 ψ-((Real.pi : ℂ)*k)^2*((2*Real.pi : ℂ)*(if k = n then 1 else 0)) := by
  obtain ⟨D⟩ := (A.localChart φ).charts ψ hψ
  have hfamily := (A.localChart φ).family ψ hψ
  have hψU : ψ ∈ A.domain := mem_iUnion.mpr ⟨φ,hψ⟩
  rw [sourceAbelianMomentCircle_quadratic_shift n k (s n ψ : Coeff p) ψ D _ _
    (hfamily.2 k).1.le (hfamily.2 k).2.2.2]
  change A.localMoment φ n k 2 ψ-(2*I*(Real.pi : ℂ)*k)*A.localMoment φ n k 1 ψ-
    ((Real.pi : ℂ)*k)^2*A.localMoment φ n k 0 ψ = _
  rw [← A.moment_eq_local n k 2 φ hψ,← A.moment_eq_local n k 1 φ hψ,
    ← A.moment_eq_local n k 0 φ hψ,A.moment_odd ψ hψU n k 0,A.moment_zero_order ψ hψU n k]
  ring

/-- The finite contour sum contributes the exact `(2*n*pi)^2` free
frequency correction when the selected gap index is in the support. -/
theorem quadratic_contour_sum_renormalization (φ : realTypeSourceLocus p) (ψ : CoeffPair p)
    (hψ : ψ ∈ A.sourceBall φ) (S : Finset ℤ)
    (hS : ∀ k ∉ S, canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k = 0)
    (n : ℤ) (hn : n ∈ S) :
    -(4/(2*Real.pi) : ℂ)*(∑ k ∈ S, sourceAbelianMomentCircle hp hp1 W n 0 2
      (s n ψ : Coeff p) ψ ((A.localChart φ).center k) ((A.localChart φ).contourRadius k))-
      (2*(n : ℂ)*Real.pi)^2 = -(4/(2*Real.pi) : ℂ)*(∑' k : ℤ, A.moment n k 2 ψ) := by
  have hψU : ψ ∈ A.domain := mem_iUnion.mpr ⟨φ,hψ⟩
  have hsum := (A.positive_moment_hasSum_of_gap_support ψ hψU S hS n 1).tsum_eq
  simp_rw [A.unshifted_quadratic_circle φ ψ hψ n]
  rw [Finset.sum_sub_distrib,hsum]
  have hdelta : (∑ k ∈ S, ((Real.pi : ℂ)*k)^2*((2*Real.pi : ℂ)*(if k = n then 1 else 0))) =
      ((Real.pi : ℂ)*n)^2*(2*Real.pi : ℂ) := by
    simp [mul_ite,hn]
  rw [hdelta]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
