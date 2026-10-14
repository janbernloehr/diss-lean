import NLS.ZakharovShabat.SourcePsiOriginalOmega
import NLS.ZakharovShabat.SourcePsiInterpolationQuotientExterior

/-!
# The outer circles in Lemma 12.7

All sufficiently large half-integer-radius circles avoid the full
original disk family. The entire variation multiplied by its omitted
root factor and divided by two has a quotient by sine tending uniformly
to zero on these circles, for every deleted lp direction.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source's outer circles eventually avoid every original disk at once. -/
theorem SourceIsolatingNeighborhoods.eventually_centralCircle_avoids_originalDiscs
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k),
      ∀ m : ℤ, z ∉ D m := by
  choose d r hr he using hD.discs
  obtain ⟨N,hN⟩ := hD.tail
  let S := Finset.Icc (-(N:ℤ)) (N:ℤ)
  let M : ℝ := ∑ m ∈ S, (|d m|+r m)
  obtain ⟨K,hK⟩ := exists_nat_gt (M/Real.pi)
  have hMK : M < (K:ℝ)*Real.pi := (div_lt_iff₀ Real.pi_pos).mp hK
  refine ⟨K,?_⟩
  intro k hk z hz m hm
  have hzNorm : ‖z‖ = centralCircleRadius k := by
    simpa only [mem_sphere,dist_zero_right] using hz
  by_cases hmn : m.natAbs ≤ N
  · have hmS : m ∈ S := by simp only [S,Finset.mem_Icc]; omega
    have hmM : |d m|+r m ≤ M := Finset.single_le_sum
      (fun j _ => add_nonneg (abs_nonneg _) (hr j).le) hmS
    have hball : ‖z-(d m:ℂ)‖ < r m := by
      simpa only [he m,mem_ball,dist_eq_norm] using hm
    have ht := norm_add_le (z-(d m:ℂ)) (d m:ℂ)
    rw [sub_add_cancel,Complex.norm_real,Real.norm_eq_abs] at ht
    have hkreal : (K:ℝ) ≤ k := by exact_mod_cast hk
    rw [hzNorm] at ht
    dsimp only [centralCircleRadius] at ht
    nlinarith [Real.pi_pos]
  · have ht := centralCircle_lattice_gap k hz m
    rw [hN m (by omega)] at hm
    have hsmall : ‖z-(Real.pi:ℂ)*m‖ < Real.pi/4 := by
      simpa only [refinedResonantDisk,mem_ball,dist_eq_norm] using hm
    linarith [Real.pi_pos]

/-- The exact sine normalization of the original product in the source proof. -/
theorem sourcePsiCandidate_mul_omitted_div_sin
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p) (z : ℂ) (hz : z ∉ freeLattice) :
    sourcePsiCandidate n (z,a)*(displacedRoots a n-z)/(2*Complex.sin z) =
      ∏' m : ℤ, (displacedRoots a m-z)/((Real.pi:ℂ)*m-z) := by
  have hprod := entireSingleSpectralProduct_div_free hp (displacedRoots a) (memℓp_displacedRoots a) z hz
  change jointSingleSpectralProduct (z,a)/(-2*Complex.sin z) = _ at hprod
  rw [jointSingleSpectralProduct_eq_deleted hp hp1 n (z,a)] at hprod
  simp only [spectralRelativeFactor] at hprod
  rw [← hprod]
  simp only [sourcePsiCandidate,neg_mul,div_neg]
  ring

/-- The literal product factor tends uniformly to one on the outer circles. -/
theorem eventually_centralCircle_sourcePsiRelativeProduct_close
    (hp : p ≠ ⊤) (a : Coeff p) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k),
      ‖(∏' m : ℤ, (displacedRoots a m-z)/((Real.pi:ℂ)*m-z))-1‖ ≤ ε := by
  obtain ⟨K,hK⟩ := eventually_centralCircle_entireSingleSpectralProduct_div_free_close
    hp (displacedRoots a) (memℓp_displacedRoots a) hε
  refine ⟨K,?_⟩
  intro k hk z hz
  have hsep (m : ℤ) : Real.pi/4 ≤ ‖z-(Real.pi:ℂ)*m‖ := by
    have hs := centralCircle_lattice_gap k hz m
    linarith [Real.pi_pos]
  have hzfree := notMem_freeLattice_of_separated (by positivity : 0 < Real.pi/4) hsep
  simpa only [entireSingleSpectralProduct_div_free hp (displacedRoots a)
    (memℓp_displacedRoots a) z hzfree,spectralRelativeFactor] using hK k hk z hz

/-- The sine quotient is exactly the root-resolvent series times the literal product. -/
theorem sourcePsiVariation_div_sin_eq_resolvent_mul_product
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a h : Coeff p) (z : ℂ) (hz : z ∉ freeLattice)
    (hv : sourcePsiCandidateVariation n a h z = sourcePsiCandidate n (z,a)*
      ∑' m : ℤ, h m/(displacedRoots a m-z)) :
    ((displacedRoots a n-z)*sourcePsiCandidateVariation n a h z/2)/Complex.sin z =
      (∑' m : ℤ, h m/(displacedRoots a m-z)) *
        ∏' m : ℤ, (displacedRoots a m-z)/((Real.pi:ℂ)*m-z) := by
  rw [hv,← sourcePsiCandidate_mul_omitted_div_sin hp hp1 n a z hz,div_div]
  ring

/-- The literal numerator phi=(sigma_n-z)*phi_n/2 has phi/sin uniformly tending to zero. -/
theorem eventually_centralCircle_sourcePsiVariation_div_sin_small
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a h : Coeff p) (hn : h n = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k),
      ‖((displacedRoots a n-z)*sourcePsiCandidateVariation n a h z/2)/Complex.sin z‖ ≤ ε := by
  have hfree : Memℓp (fun m : ℤ => (Real.pi:ℂ)*m-(Real.pi:ℂ)*m) p := by
    simpa only [sub_self] using (zero_mem_ℓp' (E := fun _ : ℤ => ℂ) (p := p))
  obtain ⟨K,hK⟩ := eventually_centralCircle_sourcePsi_interpolationQuotient_small
    hp hp1 (fun m => (Real.pi:ℂ)*m) hfree n a h hn hε
  refine ⟨K,?_⟩
  intro k hk z hz
  have h := (hK k hk z hz).2
  rw [entireSingleSpectralProduct_free,neg_mul,div_neg,norm_neg] at h
  simpa only [div_div] using h

end NLS.ZakharovShabat
