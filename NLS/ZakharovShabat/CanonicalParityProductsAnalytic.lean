import NLS.ZakharovShabat.CanonicalParityProductsUniform
import NLS.ZakharovShabat.PeriodOneEmbedding
import NLS.ComplexAnalysis.LocalAnalyticApproximation
import NLS.ComplexAnalysis.BanachSmoothAnalytic

/-!
# Joint analyticity of the intrinsic parity products

Uniform analytic approximation on actual Banach neighborhoods gives joint
analyticity, including spectral collisions. Pullback along the period-one
embedding gives the source coefficient-potential domain. The discriminant
compatibility identity remains a separate assertion.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Intrinsic parity products have uniform analytic approximation on joint open balls. -/
theorem localUniformAnalyticApproximation_canonicalParityProduct (hp : p ≠ ⊤) (hp1 : 1 < p)
    (r : ℤ) (hr : r = 0 ∨ r = 1) :
    NLS.ComplexAnalysis.HasLocalUniformAnalyticApproximation
      (fun (M : ℕ) (t : ℂ × pairParitySubspace (p := p) 0) =>
        normalizedCentralParityPolynomial hp t.2 (2*M) r t.1)
      (fun t => canonicalParityProduct hp t.2 r t.1) := by
  intro t
  obtain ⟨U,ho,_,ht,_,hU⟩ := exists_uniform_canonicalParityProducts hp hp1 t.2
  obtain ⟨N,V,_,hV,_,htV,_,hA⟩ := exists_uniform_analytic_normalizedCentralParityPolynomials hp (t.2 : PairSpace p)
  let W := (Subtype.val : pairParitySubspace (p := p) 0 → PairSpace p) ⁻¹' V
  have hW : IsOpen W := hV.preimage continuous_subtype_val
  have hn : ball t.1 1 ×ˢ (U ∩ W) ∈ 𝓝 t :=
    prod_mem_nhds (ball_mem_nhds t.1 (by norm_num)) ((ho.inter hW).mem_nhds ⟨ht,htV⟩)
  obtain ⟨ρ,hρ,hs⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨ρ/2,half_pos hρ,?_,?_⟩
  · rw [show 2*(ρ/2) = ρ by ring]
    apply (hU r hr _ (isCompact_closedBall t.1 1)).mono
    exact fun x hx => ⟨ball_subset_closedBall (hs hx).1,(hs hx).2.1⟩
  · filter_upwards [eventually_ge_atTop N] with M hM
    apply (hA (2*M) (by omega) r).mono
    rw [show 2*(ρ/2) = ρ by ring]
    exact fun x hx => (hs hx).2.2

/-- Both intrinsic parity products are jointly complex smooth on the even-supported potential space. -/
theorem contDiff_canonicalParityProduct_joint (hp : p ≠ ⊤) (hp1 : 1 < p)
    (r : ℤ) (hr : r = 0 ∨ r = 1) :
    ContDiff ℂ ∞ (fun t : ℂ × pairParitySubspace (p := p) 0 => canonicalParityProduct hp t.2 r t.1) :=
  (localUniformAnalyticApproximation_canonicalParityProduct hp hp1 r hr).contDiff

/-- Joint parity-polynomial derivatives converge uniformly in operator norm on a neighborhood. -/
theorem exists_uniform_fderiv_canonicalParityProduct (hp : p ≠ ⊤) (hp1 : 1 < p)
    (r : ℤ) (hr : r = 0 ∨ r = 1) (t : ℂ × pairParitySubspace (p := p) 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ TendstoUniformlyOn
      (fun M => fderiv ℂ (fun t : ℂ × pairParitySubspace (p := p) 0 =>
        normalizedCentralParityPolynomial hp t.2 (2*M) r t.1))
      (fderiv ℂ (fun t : ℂ × pairParitySubspace (p := p) 0 => canonicalParityProduct hp t.2 r t.1))
      atTop (ball t ρ) :=
  (localUniformAnalyticApproximation_canonicalParityProduct hp hp1 r hr).uniform_fderiv t

/-- The intrinsic parity products are jointly Banach-space analytic, including at spectral zeros. -/
theorem analyticOnNhd_canonicalParityProduct_joint (hp : p ≠ ⊤) (hp1 : 1 < p)
    (r : ℤ) (hr : r = 0 ∨ r = 1) :
    AnalyticOnNhd ℂ (fun t : ℂ × pairParitySubspace (p := p) 0 => canonicalParityProduct hp t.2 r t.1) Set.univ :=
  NLS.ComplexAnalysis.analyticOnNhd_of_complexSmooth _ (contDiff_canonicalParityProduct_joint hp hp1 r hr)

/-- The actual Fréchet Taylor series represents each parity product on a positive-radius ball. -/
theorem hasFPowerSeriesOnBall_canonicalParityProduct (hp : p ≠ ⊤) (hp1 : 1 < p)
    (r : ℤ) (hr : r = 0 ∨ r = 1) (t : ℂ × pairParitySubspace (p := p) 0) :
    let q := NLS.ComplexAnalysis.complexTaylorSeries
      (fun t : ℂ × pairParitySubspace (p := p) 0 => canonicalParityProduct hp t.2 r t.1) t
    0 < q.radius ∧ HasFPowerSeriesOnBall
      (fun t : ℂ × pairParitySubspace (p := p) 0 => canonicalParityProduct hp t.2 r t.1) q t q.radius := by
  exact ⟨NLS.ComplexAnalysis.complexTaylorSeries_radius_pos _
    (contDiff_canonicalParityProduct_joint hp hp1 r hr) t,
    NLS.ComplexAnalysis.hasFPowerSeriesOnBall_of_complexSmooth _
      (contDiff_canonicalParityProduct_joint hp hp1 r hr) t⟩

/-- Every mixed iterated Fréchet derivative of either parity product is analytic. -/
theorem analyticOnNhd_iteratedFDeriv_canonicalParityProduct (hp : p ≠ ⊤) (hp1 : 1 < p)
    (r : ℤ) (hr : r = 0 ∨ r = 1) (n : ℕ) :
    AnalyticOnNhd ℂ (iteratedFDeriv ℂ n
      (fun t : ℂ × pairParitySubspace (p := p) 0 => canonicalParityProduct hp t.2 r t.1)) Set.univ :=
  (analyticOnNhd_canonicalParityProduct_joint hp hp1 r hr).iteratedFDeriv n

/-- Joint analyticity holds on the source period-one coefficient-potential space. -/
theorem analyticOnNhd_canonicalParityProduct_periodOne (hp : p ≠ ⊤) (hp1 : 1 < p)
    (r : ℤ) (hr : r = 0 ∨ r = 1) :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p =>
      canonicalParityProduct hp (periodOnePotential t.2) r t.1) Set.univ := by
  let L : CoeffPair p →L[ℂ] pairParitySubspace (p := p) 0 :=
    (periodOnePotential (p := p)).codRestrict _ periodOnePotential_mem
  intro t _
  have hmap : AnalyticAt ℂ (fun s : ℂ × CoeffPair p => (s.1,L s.2)) t :=
    analyticAt_fst.prod ((L.analyticAt t.2).comp analyticAt_snd)
  exact (analyticOnNhd_canonicalParityProduct_joint hp hp1 r hr (t.1,L t.2) (Set.mem_univ _)).comp
    (f := fun s : ℂ × CoeffPair p => (s.1,L s.2)) hmap

end NLS.ZakharovShabat
