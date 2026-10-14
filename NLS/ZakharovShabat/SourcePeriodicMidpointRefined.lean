import NLS.ZakharovShabat.SourceDiagonalCenterSummability

/-!
# Half-exponent and endpoint summability of actual periodic midpoints

The improved diagonal centers and the ℓ(p/2) midpoint-center comparison
give locally uniform refined bounds for the full canonical midpoint
sequence. A single ℓ(p/2)+ℓ(1+) pair works for all endpoint projections.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The full canonical midpoint displacement has all refined bounds on one neighborhood. -/
theorem exists_uniform_sourcePeriodicMidpoint_refined (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ (r : ℝ≥0∞), 1 < r → r ≠ ⊤ → p/2 ≤ r →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ V, ∃ D : Coeff r,
          (∀ n : ℤ, D n = sourcePeriodicMidpointDisplacement hp hp1 ψ n) ∧ ‖D‖ ≤ K := by
  obtain ⟨V₁,ho₁,hφ₁,h₁⟩ := exists_uniform_sourceDiagonalCenter_refined hp hp1 φ
  obtain ⟨V₂,ho₂,hφ₂,L,hL,h₂⟩ := exists_uniform_sourceMidpointCenterError hp hp1 φ
  refine ⟨V₁ ∩ V₂,ho₁.inter ho₂,⟨hφ₁,hφ₂⟩,?_⟩
  intro r hr1 hr hpr
  let : Fact (1 ≤ r) := ⟨hr1.le⟩
  obtain ⟨K,hK,h⟩ := h₁ r hr1 hr hpr
  refine ⟨K+L,add_nonneg hK hL,?_⟩
  intro ψ hψ
  obtain ⟨C,hC,hCn⟩ := h ψ hψ.1
  obtain ⟨B,hB,hBn⟩ := h₂ ψ hψ.2
  let E : Coeff r := ⟨fun n => B n,(lp.memℓp B).of_exponent_ge hpr⟩
  have hE : ‖E‖ ≤ L :=
    (Coeff.norm_quasiExponentInclusion_le
      (ENNReal.div_pos (zero_lt_one.trans hp1).ne' (by norm_num))
      (zero_lt_one.trans hr1) hr hpr B).trans hBn
  refine ⟨C+E,?_,(norm_add_le C E).trans (add_le_add hCn hE)⟩
  intro n
  change C n+B n = _
  rw [hC,hB,sourcePeriodicMidpointDisplacement_apply]
  simp only [sourceDiagonalCenterDisplacement,sourcePeriodicMidpointCenterError]
  ring

/-- Every source has the refined midpoint membership, including the half exponent when p>2. -/
theorem memℓp_sourcePeriodicMidpoint_refined {r : ℝ≥0∞}
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hr1 : 1 < r) (hr : r ≠ ⊤) (hpr : p/2 ≤ r) (φ : CoeffPair p) :
    Memℓp (fun n => sourcePeriodicMidpointDisplacement hp hp1 φ n) r := by
  obtain ⟨V,_,hφ,h⟩ := exists_uniform_sourcePeriodicMidpoint_refined hp hp1 φ
  obtain ⟨_,_,hb⟩ := h r hr1 hr hpr
  obtain ⟨D,hD,_⟩ := hb φ hφ
  have he : (fun n => D n) = (fun n => sourcePeriodicMidpointDisplacement hp hp1 φ n) := funext hD
  rw [← he]
  exact lp.memℓp D

/-- One mixed pair is chosen before every finite projection of the genuine ℓ(1+) summand. -/
theorem exists_uniform_sourcePeriodicMidpoint_decomposition (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ A : CoeffPair p → Coeff (p/2), ∃ B : CoeffPair p → CoeffOnePlus,
        (∀ ψ ∈ V, ∀ n : ℤ, sourcePeriodicMidpointDisplacement hp hp1 ψ n = A ψ n+(B ψ).1 n) ∧
        (∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ V, ‖A ψ‖ ≤ K) ∧
        ∀ (r : ℝ≥0∞) (hr1 : 1 < r) (hr : r ≠ ⊤),
          ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ V, ‖CoeffOnePlus.toCoeff r hr1 hr (B ψ)‖ ≤ K := by
  obtain ⟨V,ho,hφ,h⟩ := exists_uniform_sourcePeriodicMidpoint_refined hp hp1 φ
  refine ⟨V,ho,hφ,?_⟩
  exact Coeff.exists_onePlus_decomposition_of_refined V
    (fun ψ n => sourcePeriodicMidpointDisplacement hp hp1 ψ n)
    (ENNReal.div_ne_top hp (by norm_num)) (fun r hr hr1 hpr => h r hr1 hr hpr)

end NLS.ZakharovShabat
