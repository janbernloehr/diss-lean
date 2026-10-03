import NLS.ZakharovShabat.SourceOpenGapComplement
import NLS.ZakharovShabat.SourceCanonicalRootExterior
import NLS.ZakharovShabat.LocallyUniformDiscriminantAsymptotics

/-! # Uniform exterior circle bounds for the Floquet logarithmic derivative -/
noncomputable section
open Set Complex Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem norm_quotient_le_four (a b s : ℂ) (hs : s ≠ 0)
    (ha : ‖a/s - 1‖ ≤ 1) (hb : ‖b/(I*s) - 1‖ ≤ 1/2) : ‖a/b‖ ≤ 4 := by
  have ha' : ‖a/s‖ ≤ 2 := by
    have h := norm_add_le (a/s - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at h
    linarith
  have hb' : (1/2 : ℝ) ≤ ‖b/(I*s)‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (b/(I*s))
    rw [norm_one, norm_sub_rev] at h
    linarith
  have hspos := norm_pos_iff.mpr hs
  rw [norm_div] at ha'
  rw [norm_div, norm_mul, norm_I, one_mul] at hb'
  have hab := (div_le_iff₀ hspos).mp ha'
  have hbb := (le_div_iff₀ hspos).mp hb'
  have hbpos : 0 < ‖b‖ := by linarith
  rw [norm_div, div_le_iff₀ hbpos]
  linarith

/-- Every real source has a uniform bound on all sufficiently large
half-integer circles; finite-gap membership is not required here. -/
theorem eventually_centralCircle_sourceFloquetLogDerivative_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∀ᶠ k : ℕ in atTop, ∀ z ∈ sphere (0 : ℂ) (centralCircleRadius k),
      ‖sourceFloquetLogDerivative hp hp1 φ z‖ ≤ 4 := by
  obtain ⟨U, _, _, hφU, _, R, hD⟩ := exists_uniform_discriminant_derivative_div_free
    hp hp1 (periodOnePotential φ) (by positivity : 0 < Real.pi/4) le_rfl (by norm_num : (0 : ℝ) < 1)
  have hderiv : ∀ᶠ k : ℕ in atTop, ∀ z ∈ sphere (0 : ℂ) (centralCircleRadius k),
      ‖deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / (-2*sin z) - 1‖ ≤ 1 :=
    eventually_centralCircle_of_separated_threshold
      ⟨R, hD (periodOnePotential φ) hφU (periodOnePotential_mem φ)⟩
  obtain ⟨K, hK⟩ := eventually_centralCircle_sourceCanonicalRoot_div_free_close hp hp1 φ
    (by norm_num : (0 : ℝ) < 1/2)
  filter_upwards [hderiv, eventually_ge_atTop K,
    eventually_centralCircle_sourceCanonicalRootDomain hp hp1 φ] with k hd hk hdom
  intro z hz
  rw [sourceFloquetLogDerivative_eq_criticalRootRatio hp hp1 φ hφ z (hdom hz)]
  have hsin : sin z ≠ 0 := sin_ne_zero_of_notMem_freeLattice
    (notMem_freeLattice_of_separated (by positivity : 0 < Real.pi/4) (fun n => by
      have h := centralCircle_lattice_gap k hz n
      nlinarith [Real.pi_pos]))
  apply norm_quotient_le_four _ _ (-2*sin z) (mul_ne_zero (by norm_num) hsin) (hd z hz)
  convert hK k hk z hz using 2
  ring

/-- The free leading value of the actual logarithmic derivative along
any escaping path uniformly separated from the free spectral lattice. -/
theorem tendsto_sourceFloquetLogDerivative_of_separated {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (z : α → ℂ)
    (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (hsep : ∀ i (n : ℤ), r ≤ ‖z i-(Real.pi : ℂ)*n‖) :
    Tendsto (fun i => sourceFloquetLogDerivative hp hp1 φ (z i)) l (𝓝 (-I)) := by
  have hd := tendsto_discriminant_derivative_ratio_of_potential_tendsto hp hp1
    (fun _ : α => periodOnePotential φ) tendsto_const_nhds
    (fun _ => periodOnePotential_mem φ) z hescape hr hrπ hsep
  have hs := tendsto_sourceCanonicalRoot_div_free_of_separated hp hp1 φ z hescape hr hrπ hsep
  have ht := (hd.div hs (by norm_num)).const_mul (-I)
  simp only [div_self (one_ne_zero : (1 : ℂ) ≠ 0), mul_one] at ht
  apply ht.congr'
  filter_upwards [eventually_sourceCanonicalRootDomain_of_separated hp hp1 φ z hescape hr hrπ hsep] with i hi
  rw [sourceFloquetLogDerivative_eq_criticalRootRatio hp hp1 φ hφ (z i) hi]
  have hsin := sin_ne_zero_of_notMem_freeLattice (notMem_freeLattice_of_separated hr (hsep i))
  have hroot := sourceCanonicalRoot_ne_zero_off_gaps hp hp1 φ (z i) hi
  change -I * ((deriv (canonicalDiscriminant hp (periodOnePotential φ)) (z i) / (-2*sin (z i))) /
    (sourceCanonicalRoot hp hp1 φ (z i) / (-2*I*sin (z i)))) = _
  field_simp
  ring_nf
  simp only [I_sq, neg_mul, one_mul, neg_neg]

end NLS.ZakharovShabat
