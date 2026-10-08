import NLS.ZakharovShabat.SourceFiniteGapHigherActionExterior
import NLS.ZakharovShabat.SourceHigherActionBoundary
import NLS.ComplexAnalysis.FiniteCircleHoleDecomposition

/-! # The all-order physical trace formula at actual real finite-gap sources

The outer contour splits into the finitely many open-gap contours. Its
Hamiltonian coefficient gives `sum J_(n,k+1) = H_(k+1)/2^k` at every level.
The Hamiltonians are the physical differential hierarchy of the source's
smooth Fourier representative, not definitions by spectral sums.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Theorem 24.1 at every order for actual real finite-gap sources. -/
theorem sourceFiniteGap_sum_higherActions_eq_hamiltonian
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (k : ℕ) :
    (∑ n ∈ hf.toFinset, (sourceRealHigherAction hp hp1 φ n k : ℂ)) =
      sourceFiniteGapNLSHamiltonian hp hp1 φ hf (k+1)/2^k := by
  classical
  obtain ⟨W,_,_,hC⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  obtain ⟨C,hcenter⟩ := hC φ
  have hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hcenter]
    exact mem_ball_self C.discs.sourceRadius_pos
  obtain ⟨D⟩ := C.charts φ.val hφ
  let s : Finset ℤ := hf.toFinset
  let ρ : ℤ → ℝ := fun n => (C.discs.inner n+C.discs.outer n)/2
  have hi (n : ℤ) : C.discs.inner n < ρ n := by dsimp [ρ]; linarith [C.discs.inner_lt n]
  have ho (n : ℤ) : ρ n < C.discs.outer n := by dsimp [ρ]; linarith [C.discs.inner_lt n]
  have hs (n : ℤ) : n ∈ s ↔ canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0 := Set.Finite.mem_toFinset hf
  have hcompact : IsCompact (⋃ n ∈ s, closedBall (C.discs.center n) (ρ n)) :=
    s.finite_toSet.isCompact_biUnion fun n _ => isCompact_closedBall _ _
  obtain ⟨B,hB⟩ := hcompact.isBounded.exists_norm_le
  obtain ⟨T,hT,houter⟩ := exists_sourceFiniteGap_higherAction_exterior C φ hφ hf
  let R := max B T+1
  have hTR : T ≤ R := by dsimp [R]; linarith [le_max_right B T]
  have hR : 0 < R := hT.trans_le hTR
  have henclosed (n : ℤ) (hn : n ∈ s) : closedBall (C.discs.center n) (ρ n) ⊆ ball 0 R := by
    intro z hz
    have hb := hB z (mem_iUnion₂.mpr ⟨n,hn,hz⟩)
    rw [mem_ball,dist_zero_right]
    dsimp [R]
    linarith [le_max_left B T]
  have hdisj (n : ℤ) (_ : n ∈ s) (j : ℤ) (_ : j ∈ s) (hne : n ≠ j) :
      Disjoint (closedBall (C.discs.center n) (ρ n)) (closedBall (C.discs.center j) (ρ j)) :=
    (C.discs.disjoint n j hne).mono (closedBall_subset_ball (ho n)) (closedBall_subset_ball (ho j))
  have ha : AnalyticOnNhd ℂ (fun z => z^k*sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val))
      (circleHoleDomain 0 R s C.discs.center C.discs.inner) := by
    intro z hz
    apply (analyticAt_id.pow k).mul
    apply sourceFullAbelianPrimitive_spectral_analytic D 0 z
    intro n hn hzn
    exact hz.2 n ((hs n).mpr hn) (C.discs.segment_subset φ.val hφ n hzn)
  have hdec := circleIntegral_eq_sum_of_finite_holes 0 R hR.le s C.discs.center C.discs.inner ρ
    (fun z => z^k*sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val))
    (fun n _ => C.discs.inner_pos n) (fun n _ => hi n) henclosed hdisj ha
  have hinner (n : ℤ) :
      -(Real.pi : ℂ)⁻¹ * (∮ z in C(C.discs.center n,C.discs.inner n),
        z^k*sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val)) =
      (sourceRealHigherAction hp hp1 φ n k : ℂ) := by
    rw [← sourceHigherActionCircle_eq_primitive hp hp1 W 0 φ.val D _ _ (C.discs.inner_pos n).le
      (C.intermediate_circle_root n φ.val hφ _ le_rfl (C.discs.inner_lt n))]
    exact C.higherActionCircle_eq_real n k φ hφ _ le_rfl (C.discs.inner_lt n)
  have he := houter R hTR k
  rw [hdec,Finset.mul_sum] at he
  simpa only [hinner] using he

/-- The all-order trace identity as an infinite sum: closed-gap terms vanish. -/
theorem sourceFiniteGap_tsum_higherActions_eq_hamiltonian
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (k : ℕ) :
    (∑' n : ℤ, (sourceRealHigherAction hp hp1 φ n k : ℂ)) =
      sourceFiniteGapNLSHamiltonian hp hp1 φ hf (k+1)/2^k := by
  classical
  rw [tsum_eq_sum (s := hf.toFinset)]
  · exact sourceFiniteGap_sum_higherActions_eq_hamiltonian hp hp1 φ hf k
  · intro n hn
    have hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0 := by
      by_contra hgap
      exact hn ((Set.Finite.mem_toFinset hf).mpr hgap)
    rw [sourceRealHigherAction_of_collapsed hp hp1 φ n hgap k,ofReal_zero]

/-- Every physical Hamiltonian of positive order is real at a real finite-gap source. -/
theorem sourceFiniteGapNLSHamiltonian_im_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (k : ℕ) :
    (sourceFiniteGapNLSHamiltonian hp hp1 φ hf (k+1)).im = 0 := by
  have he := sourceFiniteGap_sum_higherActions_eq_hamiltonian hp hp1 φ hf k
  have hpow : (2 : ℂ)^k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hH : sourceFiniteGapNLSHamiltonian hp hp1 φ hf (k+1) =
      (∑ n ∈ hf.toFinset, (sourceRealHigherAction hp hp1 φ n k : ℂ)) * (2 : ℂ)^k :=
    ((eq_div_iff hpow).mp he).symm
  rw [hH, show (2 : ℂ)^k = Complex.ofReal ((2 : ℝ)^k) by norm_cast,
    ← ofReal_sum, ← ofReal_mul, ofReal_im]

/-- Odd physical Hamiltonians are nonnegative, at every order. -/
theorem sourceFiniteGapNLSHamiltonian_odd_nonneg
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (m : ℕ) :
    0 ≤ (sourceFiniteGapNLSHamiltonian hp hp1 φ hf (2*m+1)).re := by
  have he := sourceFiniteGap_sum_higherActions_eq_hamiltonian hp hp1 φ hf (2*m)
  have hpow : (2 : ℂ)^(2*m) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hH := ((eq_div_iff hpow).mp he).symm
  rw [hH, show (2 : ℂ)^(2*m) = Complex.ofReal ((2 : ℝ)^(2*m)) by norm_cast,
    ← ofReal_sum, ← ofReal_mul, ofReal_re]
  apply mul_nonneg
  · exact Finset.sum_nonneg (fun n _ => sourceRealHigherAction_even_nonneg hp hp1 φ n m)
  · norm_num

end NLS.ZakharovShabat
