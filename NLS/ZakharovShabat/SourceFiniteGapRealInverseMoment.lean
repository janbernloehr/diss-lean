import NLS.ZakharovShabat.SourceRealInverseAction
import NLS.ZakharovShabat.SourceFiniteGapInverseMoment

/-! The actual signed finite-gap inverse moment in real cosine gap
coordinates, with exact pi normalization and no central contribution. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
namespace SourceFullAbelianUniformCauchyFamily

theorem zero_not_mem_selected_disc_of_central_zero
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (ψ : CoeffPair p)
    (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (h0 : (0:ℂ) ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) 0,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) 0} : Set ℂ))
    (n : ℤ) (hn : n ≠ 0) (R : ℝ) (ho : R < C.discs.outer n) :
    (0:ℂ) ∉ closedBall (C.discs.center n) R := by
  intro hz
  exact Set.disjoint_left.mp (C.discs.disjoint n 0 hn)
    (closedBall_subset_ball ho hz) (C.endpoint_mem_ball 0 ψ hψ 0 h0)

theorem inverse_primitive_circle_eq_neg_pi_inverseAction
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (R : ℝ) (hi : C.discs.inner n ≤ R) (ho : R < C.discs.outer n)
    (hz : (0:ℂ) ∉ closedBall (C.discs.center n) R) :
    (∮ z in C(C.discs.center n,R), sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)/z)=
      -(Real.pi:ℂ)*(sourceRealInverseAction hp hp1 φ n:ℂ) := by
  have h := C.inverse_primitive_circle_eq_real_inverseAction φ hφ n R hi ho hz
  have hπ : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  calc
    _ = -(Real.pi:ℂ)*(-(Real.pi:ℂ)⁻¹*(∮ z in C(C.discs.center n,R),
        sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)/z)) := by field_simp
    _ = _ := by rw [h]

end SourceFullAbelianUniformCauchyFamily

theorem sourceFiniteGap_real_inverse_moment_balance
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0=0)
    (h0 : (0:ℂ) ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0,
      canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0} : Set ℂ)) :
    (∑' k : ℤ, φ.val.fst k*φ.val.snd (-k))=
      (Real.pi:ℂ)*((∑ n ∈ hf.toFinset, (n:ℝ)*sourceRealInverseAction hp hp1 φ n:ℝ):ℂ) := by
  classical
  rw [sourceFiniteGap_inverse_moment_balance C φ hφ hf hgap h0,
    ← Finset.sum_neg_distrib,Complex.ofReal_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by
    intro he
    subst n
    exact (Set.Finite.mem_toFinset hf).mp hn hgap
  let R := (C.discs.inner n+C.discs.outer n)/2
  have hi : C.discs.inner n ≤ R := by dsimp [R]; linarith [C.discs.inner_lt n]
  have ho : R < C.discs.outer n := by dsimp [R]; linarith [C.discs.inner_lt n]
  have hz := C.zero_not_mem_selected_disc_of_central_zero φ.val hφ h0 n hn0 R ho
  rw [C.inverse_primitive_circle_eq_neg_pi_inverseAction φ hφ n R hi ho hz]
  push_cast
  ring

end NLS.ZakharovShabat
