import NLS.ZakharovShabat.SourceDiagonalRemainderMajorants
import NLS.ZakharovShabat.SourceMidpointCenterSummability

/-!
# Refined summability of the actual diagonal centers

The quadratic disk estimate and the half-exponent nonlinear remainder
control the moving fixed points on one source neighborhood. A fixed
finite head covers the total center's free fallback. The neighborhood is
independent of the requested target exponent.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The named original-source diagonal center, relative to the free lattice. -/
def sourceDiagonalCenterDisplacement (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) : ℂ :=
  weightedResonantDiagonalCenter hp SpectralWeight.one (sourceWeightedPeriodOne φ) n-(Real.pi:ℂ)*n

private theorem center_pullback {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (e : A → B) (he : Continuous e) (a : A) (P : ℕ → B → Prop)
    (h : ∃ N : ℕ, ∃ U : Set B, IsOpen U ∧ e a ∈ U ∧ ∀ x ∈ U, P N x) :
    ∃ N : ℕ, ∃ V : Set A, IsOpen V ∧ a ∈ V ∧ ∀ x ∈ V, P N (e x) := by
  obtain ⟨N,U,ho,ha,hP⟩ := h
  exact ⟨N,e ⁻¹' U,ho.preimage he,ha,fun x hx => hP (e x) hx⟩

/-- One original-source neighborhood supplies the actual distant fixed-point equations. -/
theorem exists_uniform_sourceDiagonalCenters (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ n : ℤ, N ≤ n.natAbs →
        let ζ := weightedResonantDiagonalCenter hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n;
        ζ ∈ refinedResonantDisk n ∧ ζ = (Real.pi:ℂ)*n+
          weightedResonantAExtension hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n ζ := by
  have hw : ∃ N : ℕ, ∃ U : Set (WeightedCoeffPair SpectralWeight.one.toWeight p),
      IsOpen U ∧ sourceWeightedPeriodOne φ ∈ U ∧ ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs →
        let ζ := weightedResonantDiagonalCenter hp SpectralWeight.one ψ n;
        ζ ∈ refinedResonantDisk n ∧ ζ = (Real.pi:ℂ)*n+weightedResonantAExtension hp SpectralWeight.one ψ n ζ := by
    obtain ⟨N,_,U,ho,_,hφ,_,h⟩ := exists_uniform_weightedResonantDiagonalCenters hp hp1
      SpectralWeight.one (sourceWeightedPeriodOne φ)
    exact ⟨N,U,ho,hφ,fun ψ hψ n hn => ⟨(h ψ hψ n hn).1.1,(h ψ hψ n hn).1.2.2.1⟩⟩
  exact center_pullback sourceWeightedPeriodOne sourceWeightedPeriodOne.toContinuousLinearMap.continuous φ _ hw

private theorem center_head_mem (N : ℕ) :
    Memℓp (fun n : ℤ => if N ≤ n.natAbs then (0:ℂ) else (Real.pi/4:ℂ)) 1 := by
  apply (memℓp_zero_iff.mpr ?_).of_exponent_ge bot_le
  apply (Finset.finite_toSet (Finset.Icc (-(N:ℤ)) N)).subset
  intro n hn
  have hlt : n.natAbs < N := by
    by_contra h
    exact hn (by simp [show N ≤ n.natAbs by omega])
  simp only [Finset.mem_coe,Finset.mem_Icc]
  omega

/-- Every finite target above one and at least p/2 is uniformly bounded on the same neighborhood. -/
theorem exists_uniform_sourceDiagonalCenter_refined (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ (r : ℝ≥0∞), 1 < r → r ≠ ⊤ → p/2 ≤ r →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ V, ∃ D : Coeff r,
          (∀ n : ℤ, D n = sourceDiagonalCenterDisplacement hp ψ n) ∧ ‖D‖ ≤ K := by
  obtain ⟨N₁,V₁,ho₁,hφ₁,h₁⟩ := exists_uniform_sourceDiagonalCenters hp hp1 φ
  obtain ⟨N₂,_,V₂,ho₂,hφ₂,L,hL,h₂⟩ := exists_uniform_sourceDiagonalRemainderMajorant hp hp1 φ
  let N := max N₁ N₂
  let H : Coeff 1 := ⟨_,center_head_mem N⟩
  let R := ‖φ‖+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨V₁ ∩ V₂ ∩ ball φ 1,(ho₁.inter ho₂).inter isOpen_ball,
    ⟨⟨hφ₁,hφ₂⟩,mem_ball_self (by norm_num)⟩,?_⟩
  intro r hr1 hr hpr
  let : Fact (1 ≤ r) := ⟨hr1.le⟩
  let C := Real.pi⁻¹*(Fourier.hilbertTransformBound hr1 hr+‖Fourier.hilbertSquareCoeffs‖)
  have hC : 0 ≤ C := by
    have := Fourier.hilbertTransformBound_nonneg hr1 hr
    dsimp [C]
    positivity
  refine ⟨C*R^2+L+‖H‖,by positivity,?_⟩
  intro ψ hψ
  have hψR : ‖ψ‖ ≤ R := by
    have hb := mem_ball.mp hψ.2
    rw [dist_eq_norm] at hb
    have ht := norm_le_norm_sub_add ψ φ
    dsimp [R]
    linarith
  obtain ⟨B,hBn,hB⟩ := h₂ ψ hψ.1.2
  obtain ⟨Q,_,hQ,hQn⟩ := exists_sourceResonantDiagonalQuadraticSup hp hr1 hr hpr ψ
  let E : Coeff r := ⟨fun n => B n,(lp.memℓp B).of_exponent_ge hpr⟩
  have hE : ‖E‖ ≤ L :=
    (Coeff.norm_quasiExponentInclusion_le
      (ENNReal.div_pos (zero_lt_one.trans hp1).ne' (by norm_num))
      (zero_lt_one.trans hr1) hr hpr B).trans hBn
  let J := Coeff.exponentInclusion hr1.le H
  let G := Coeff.magnitude Q+Coeff.magnitude E+J
  have hGn (n : ℤ) : ‖G n‖ = ‖Q n‖+‖B n‖+(if N ≤ n.natAbs then 0 else Real.pi/4) := by
    change ‖(‖Q n‖:ℂ)+(‖E n‖:ℂ)+J n‖ = _
    change ‖(‖Q n‖:ℂ)+(‖B n‖:ℂ)+(if N ≤ n.natAbs then 0 else (Real.pi/4:ℂ))‖ = _
    split_ifs
    · rw [add_zero,add_zero,← Complex.ofReal_add,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
    · have he : (‖Q n‖:ℂ)+(‖B n‖:ℂ)+(Real.pi:ℂ)/4 =
          ((‖Q n‖+‖B n‖+Real.pi/4:ℝ):ℂ) := by push_cast; rfl
      rw [he,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  have hpoint (n : ℤ) : ‖sourceDiagonalCenterDisplacement hp ψ n‖ ≤ ‖G n‖ := by
    rw [hGn]
    by_cases hn : N ≤ n.natAbs
    · rw [if_pos hn,add_zero]
      obtain ⟨hz,hfix⟩ := h₁ ψ hψ.1.1 n (le_trans (le_max_left _ _) hn)
      let ζ := weightedResonantDiagonalCenter hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n
      have he : sourceDiagonalCenterDisplacement hp ψ n =
          weightedResonantAExtension hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n ζ := by
        dsimp [sourceDiagonalCenterDisplacement,ζ]
        linear_combination hfix
      rw [he]
      have ht := norm_le_norm_sub_add
        (weightedResonantAExtension hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n ζ)
        (sourceResonantDiagonalQuadratic ψ n ζ)
      have hb := hB n (le_trans (le_max_right _ _) hn) ζ (refinedResonantDisk_subset_strip n hz)
      have hq := hQ n ζ hz
      linarith
    · rw [if_neg hn]
      exact (norm_weightedResonantDiagonalCenter_sub_free_le hp SpectralWeight.one
        (sourceWeightedPeriodOne ψ) n).trans (by linarith [norm_nonneg (Q n),norm_nonneg (B n)])
  let D : Coeff r := ⟨sourceDiagonalCenterDisplacement hp ψ,(lp.memℓp G).mono' hpoint⟩
  refine ⟨D,fun _ => rfl,(lp.norm_mono (zero_lt_one.trans hr1).ne' hpoint).trans ?_⟩
  calc
    ‖G‖ ≤ ‖Q‖+‖E‖+‖H‖ := by
      apply (norm_add_le _ _).trans
      exact add_le_add ((norm_add_le _ _).trans_eq (by rw [Coeff.norm_magnitude,Coeff.norm_magnitude]))
        (Coeff.norm_exponentInclusion_le hr1.le H)
    _ ≤ C*R^2+L+‖H‖ := by
      exact add_le_add (add_le_add (hQn.trans (by change C*‖ψ‖^2 ≤ C*R^2; gcongr)) hE) le_rfl

end NLS.ZakharovShabat
