import NLS.ZakharovShabat.SourceAbelianMomentFiniteGapContour

/-! # The linear primitive moment and its exact integer normalization

The shift F₀=Fₖ−ikπ, the vanishing first moment, and the zero-order
period 2πδₖₙ evaluate the large linear psi contour at real finite-gap sources.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
open NLS.ComplexAnalysis NLS.Poisson
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W : Set (CoeffPair p)}

/-- Shifting the primitive index subtracts the corresponding zero-order period. -/
theorem sourceAbelianMomentCircle_linear_shift
    (n k : ℤ) (a : Coeff p) (ψ : CoeffPair p) (D : SourceAbelianSpectralChart hp hp1 W ψ)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ) :
    sourceAbelianMomentCircle hp hp1 W n 0 1 a ψ c R =
      sourceAbelianMomentCircle hp hp1 W n k 1 a ψ c R-
        (I*(Real.pi : ℂ)*k)*sourceAbelianMomentCircle hp hp1 W n k 0 a ψ c R := by
  let f (m : ℕ) (z : ℂ) := sourceAbelianMomentIntegrand hp hp1 W n k m (z,(a,ψ))
  have hci (m : ℕ) : CircleIntegrable (f m) c R :=
    ((analyticOnNhd_sourceAbelianMomentIntegrand_fixed hp hp1 W n k m a ψ D).continuousOn.mono hcircle).circleIntegrable hR
  have he (z : ℂ) (hz : z ∈ sphere c R) :
      sourceAbelianMomentIntegrand hp hp1 W n 0 1 (z,(a,ψ)) =
        f 1 z-(I*(Real.pi : ℂ)*k)*f 0 z := by
    dsimp [f,sourceAbelianMomentIntegrand]
    rw [sourceFullAbelianPrimitive_index_shift D k z
      (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ (hcircle hz))]
    simp only [pow_one,pow_zero,one_mul]
    ring
  have hci0 : CircleIntegrable (fun z => (I*(Real.pi : ℂ)*k)*f 0 z) c R := (hci 0).const_mul _
  calc
    _ = ∮ z in C(c,R), f 1 z-(I*(Real.pi : ℂ)*k)*f 0 z :=
      circleIntegral.integral_congr hR he
    _ = _ := by
      rw [circleIntegral.integral_sub (hci 1) hci0,circleIntegral.integral_const_mul]
      rfl

namespace SourceAbelianMomentAtlas
variable {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The first moment vanishes and the zero-order period gives the exact Kronecker correction. -/
theorem unshifted_linear_circle (A : SourceAbelianMomentAtlas hp hp1 W s)
    (φ : realTypeSourceLocus p) (ψ : CoeffPair p) (hψ : ψ ∈ A.sourceBall φ) (n k : ℤ) :
    sourceAbelianMomentCircle hp hp1 W n 0 1 (s n ψ : Coeff p) ψ
      ((A.localChart φ).center k) ((A.localChart φ).contourRadius k) =
        -(I*(Real.pi : ℂ)*k)*((2*Real.pi : ℂ)*(if k = n then 1 else 0)) := by
  obtain ⟨D⟩ := (A.localChart φ).charts ψ hψ
  have hfamily := (A.localChart φ).family ψ hψ
  have hψU : ψ ∈ A.domain := mem_iUnion.mpr ⟨φ,hψ⟩
  rw [sourceAbelianMomentCircle_linear_shift n k (s n ψ : Coeff p) ψ D _ _
    (hfamily.2 k).1.le (hfamily.2 k).2.2.2]
  change A.localMoment φ n k 1 ψ-(I*(Real.pi : ℂ)*k)*A.localMoment φ n k 0 ψ = _
  rw [← A.moment_eq_local n k 1 φ hψ,← A.moment_eq_local n k 0 φ hψ,
    A.moment_odd ψ hψU n k 0,A.moment_zero_order ψ hψU n k]
  ring

/-- Finite-gap contour decomposition evaluates the linear moment with its exact 2πn factor. -/
theorem exists_finiteGap_linear_contour_formula
    {V : Set (CoeffPair p)} (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiNormalizedComplexExtension hp hp1 V s)
    (φ : realTypeSourceLocus p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      sphere (0 : ℂ) R ⊆ sourceCanonicalRootDomain hp hp1 φ.val →
      ∀ n : ℤ, canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
        (periodOnePotential_mem φ.val) n ≠ 0 →
      (I/Real.pi : ℂ)*sourceAbelianMomentCircle hp hp1 W n 0 1 (s n φ.val) φ.val 0 R =
        2*(Real.pi : ℂ)*n := by
  classical
  obtain ⟨T,hT,hdec⟩ := A.exists_finiteGap_contour_decomposition hs φ hf
  refine ⟨T,hT,fun R hR hcircle n hn => ?_⟩
  rw [hdec R hR hcircle n hn 0 1]
  simp_rw [A.unshifted_linear_circle φ φ.val (mem_ball_self (A.localChart φ).radius_pos) n]
  have hmem : n ∈ hf.toFinset := (Set.Finite.mem_toFinset hf).mpr hn
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',hmem,ite_true]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  simp only [I_sq]
  ring
end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
