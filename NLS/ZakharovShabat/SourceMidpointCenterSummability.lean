import NLS.ZakharovShabat.SourceResonantMidpointCenter
import NLS.SequenceSpaces.QuasiExponentEmbedding

/-!
# Half-exponent summability of the actual midpoint-center difference

The full-strip product majorant gives a uniform ℓ(p/2) bound on the
midpoint-center tail. A fixed finite head gives the full sequence bound,
including exponents below one. Consequently improved summability of the
actual midpoint is equivalent to that of the actual diagonal center.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual canonical periodic midpoint minus the named diagonal center. -/
def sourcePeriodicMidpointCenterError (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (n : ℤ) : ℂ :=
  canonicalPeriodicMidpoint hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n-
    weightedResonantDiagonalCenter hp SpectralWeight.one (sourceWeightedPeriodOne φ) n

/-- The selected center, including its free fallback, always lies within the refined radius. -/
theorem norm_weightedResonantDiagonalCenter_sub_free_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) :
    ‖weightedResonantDiagonalCenter hp w φ n-(Real.pi:ℂ)*n‖ ≤ Real.pi/4 := by
  unfold weightedResonantDiagonalCenter
  split_ifs with h
  · exact (show ‖Classical.choose h-(Real.pi:ℂ)*n‖ < Real.pi/4 by
      simpa only [refinedResonantDisk,mem_ball,dist_eq_norm] using (Classical.choose_spec h).1).le
  · simp only [sub_self,norm_zero]
    positivity

/-- The original-source midpoint-center difference has a uniformly bounded half-exponent tail. -/
theorem exists_uniform_sourceMidpointCenterError_tail (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ ψ ∈ V, ∃ D : Coeff (p/2),
        (∀ n : ℤ, D n = if N ≤ n.natAbs then sourcePeriodicMidpointCenterError hp hp1 ψ n else 0) ∧ ‖D‖ ≤ K := by
  obtain ⟨N₁,V₁,ho₁,hφ₁,h₁⟩ := exists_uniform_sourceMidpointCenterBound hp hp1 φ
  obtain ⟨N₂,V₂,ho₂,hφ₂,L,hL,h₂⟩ := exists_uniform_sourceBProductMajorants hp hp1 φ
  let N := max N₁ N₂
  let K := (8*Real.pi⁻¹)*L^2
  have hpR : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  have hh0 : p/2 ≠ 0 := (ENNReal.div_pos (zero_lt_one.trans hp1).ne' (by norm_num)).ne'
  let : p.HolderTriple p (p/2) := Coeff.holderTriple_half p
  refine ⟨N,V₁ ∩ V₂,ho₁.inter ho₂,⟨hφ₁,hφ₂⟩,K,by dsimp [K]; positivity,?_⟩
  intro ψ hψ
  obtain ⟨B,C,hB,hC,hBC⟩ := h₂ ψ hψ.2
  let A : Coeff (p/2) := ((8*Real.pi⁻¹:ℝ):ℂ) • Coeff.quasiHolderProduct B C
  have hAn (n : ℤ) : ‖A n‖ = (8*Real.pi⁻¹)*‖B n‖*‖C n‖ := by
    simp only [A,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,Coeff.quasiHolderProduct_apply,
      norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ 8*Real.pi⁻¹)]
    ring
  have hdom (n : ℤ) : ‖(if N ≤ n.natAbs then sourcePeriodicMidpointCenterError hp hp1 ψ n else 0)‖ ≤ ‖A n‖ := by
    split_ifs with hn
    · rw [hAn]
      have h := h₁ ψ hψ.1 n (le_trans (le_max_left _ _) hn)
      have hprod := hBC n (le_trans (le_max_right _ _) hn)
      change ‖sourcePeriodicMidpointCenterError hp hp1 ψ n‖ ≤ _ at h
      exact h.trans ((mul_le_mul_of_nonneg_left hprod (by positivity)).trans_eq (by ring))
    · simp only [norm_zero]
      exact norm_nonneg _
  let D : Coeff (p/2) := ⟨_,(lp.memℓp A).mono' hdom⟩
  refine ⟨D,fun _ => rfl,(lp.norm_mono hh0 hdom).trans ?_⟩
  rw [lp.norm_const_smul hh0,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ 8*Real.pi⁻¹)]
  apply (mul_le_mul_of_nonneg_left (Coeff.norm_quasiHolderProduct_le hpR hpR B C) (by positivity)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [pow_two] using mul_le_mul hB hC (norm_nonneg C) hL

private theorem finite_head_mem (r : ℝ≥0∞) (N : ℕ) (f : ℤ → ℂ) :
    Memℓp (fun n : ℤ => if N ≤ n.natAbs then 0 else f n) r := by
  apply (memℓp_zero_iff.mpr ?_).of_exponent_ge bot_le
  apply (Finset.finite_toSet (Finset.Icc (-(N:ℤ)) N)).subset
  intro n hn
  have hlt : n.natAbs < N := by
    by_contra h
    have hh : N ≤ n.natAbs := by omega
    exact hn (by simp [hh])
  simp only [Finset.mem_coe,Finset.mem_Icc]
  omega

/-- A common finite head and a bounded half-exponent tail control the full sequence. -/
private theorem full_sequence_of_tail {X : Type*} {r : ℝ≥0∞} (hr : 0 < r.toReal)
    (S : Set X) (F : X → ℤ → ℂ) (N : ℕ) (H K : ℝ) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hhead : ∀ x ∈ S, ∀ n : ℤ, ‖F x n‖ ≤ H)
    (htail : ∀ x ∈ S, ∃ D : Coeff r, (∀ n : ℤ, D n = if N ≤ n.natAbs then F x n else 0) ∧ ‖D‖ ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∃ D : Coeff r, (∀ n : ℤ, D n = F x n) ∧ ‖D‖ ≤ C := by
  let B : Coeff r := ⟨fun n : ℤ => if N ≤ n.natAbs then 0 else (H:ℂ),finite_head_mem r N _⟩
  let C := max (‖B‖+K) ((‖B‖^r.toReal+K^r.toReal)^(r.toReal)⁻¹)
  refine ⟨C,le_trans (Real.rpow_nonneg (add_nonneg (Real.rpow_nonneg (lp.norm_nonneg' B) _) (Real.rpow_nonneg hK _)) _) (le_max_right _ _),?_⟩
  intro x hx
  obtain ⟨D,hD,hDn⟩ := htail x hx
  let A : Coeff r := ⟨fun n : ℤ => if N ≤ n.natAbs then 0 else F x n,finite_head_mem r N _⟩
  have hAB : ‖A‖ ≤ ‖B‖ := by
    apply lp.norm_mono (by intro he; simp [he] at hr)
    intro n
    change ‖(if N ≤ n.natAbs then 0 else F x n)‖ ≤ ‖(if N ≤ n.natAbs then 0 else (H:ℂ))‖
    split_ifs
    · rfl
    · simpa only [Complex.norm_real,Real.norm_of_nonneg hH] using hhead x hx n
  refine ⟨A+D,?_,Coeff.norm_add_le_uniform hr A D hAB hDn⟩
  intro n
  change (if N ≤ n.natAbs then 0 else F x n)+D n = F x n
  rw [hD]
  split_ifs <;> simp

/-- On one original-source neighborhood the entire midpoint-center error lies in ℓ(p/2),
with a common norm bound, including the quasi-normed range 1<p<2. -/
theorem exists_uniform_sourceMidpointCenterError (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ ψ ∈ V, ∃ D : Coeff (p/2),
        (∀ n : ℤ, D n = sourcePeriodicMidpointCenterError hp hp1 ψ n) ∧ ‖D‖ ≤ K := by
  obtain ⟨N,V₁,ho₁,hφ₁,K,hK,h₁⟩ := exists_uniform_sourceMidpointCenterError_tail hp hp1 φ
  obtain ⟨_,_,V₂,ho₂,hφ₂,R,hR,h₂⟩ := exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ (by norm_num : (0:ℝ)<1)
  have hr : 0 < (p/2).toReal := ENNReal.toReal_pos
    (ENNReal.div_pos (zero_lt_one.trans hp1).ne' (by norm_num)).ne' (ENNReal.div_ne_top hp (by norm_num))
  have hhead (ψ : CoeffPair p) (hψ : ψ ∈ V₁ ∩ V₂) (n : ℤ) :
      ‖sourcePeriodicMidpointCenterError hp hp1 ψ n‖ ≤ R+Real.pi/4 := by
    have hmid := (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne'
      (sourcePeriodicMidpointDisplacement hp hp1 ψ) n).trans (h₂ ψ hψ.2).1
    rw [sourcePeriodicMidpointDisplacement_apply] at hmid
    have hcenter := norm_weightedResonantDiagonalCenter_sub_free_le hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n
    have he : sourcePeriodicMidpointCenterError hp hp1 ψ n =
        (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-(Real.pi:ℂ)*n)-
          (weightedResonantDiagonalCenter hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n-(Real.pi:ℂ)*n) := by
      unfold sourcePeriodicMidpointCenterError
      ring
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add hmid hcenter)
  obtain ⟨C,hC,h⟩ := full_sequence_of_tail hr (V₁ ∩ V₂) (sourcePeriodicMidpointCenterError hp hp1) N
    (R+Real.pi/4) K (by positivity) hK hhead (fun ψ hψ => h₁ ψ hψ.1)
  exact ⟨V₁ ∩ V₂,ho₁.inter ho₂,⟨hφ₁,hφ₂⟩,C,hC,h⟩

/-- Every original source has a half-exponent midpoint-center difference sequence. -/
theorem memℓp_sourceMidpointCenterError (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    Memℓp (sourcePeriodicMidpointCenterError hp hp1 φ) (p/2) := by
  obtain ⟨V,_,hφ,_,_,h⟩ := exists_uniform_sourceMidpointCenterError hp hp1 φ
  obtain ⟨D,hD,_⟩ := h φ hφ
  have he : (fun n => D n) = sourcePeriodicMidpointCenterError hp hp1 φ := funext hD
  rw [← he]
  exact lp.memℓp D

/-- At every exponent at least p/2, improved midpoint membership is equivalent to
improved diagonal-center membership. The comparison is between the actual sequences. -/
theorem memℓp_sourceMidpointDisplacement_iff_center {r : ℝ≥0∞}
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hpr : p/2 ≤ r) (φ : CoeffPair p) :
    Memℓp (fun n : ℤ => canonicalPeriodicMidpoint hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) n-(Real.pi:ℂ)*n) r ↔
    Memℓp (fun n : ℤ => weightedResonantDiagonalCenter hp SpectralWeight.one
      (sourceWeightedPeriodOne φ) n-(Real.pi:ℂ)*n) r := by
  have hE := (memℓp_sourceMidpointCenterError hp hp1 φ).of_exponent_ge hpr
  constructor
  · intro h
    convert h.sub hE using 1
    funext n
    simp only [Pi.sub_apply,sourcePeriodicMidpointCenterError]
    ring
  · intro h
    convert h.add hE using 1
    funext n
    simp only [Pi.add_apply,sourcePeriodicMidpointCenterError]
    ring

end NLS.ZakharovShabat
