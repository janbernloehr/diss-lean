import NLS.ZakharovShabat.SourceCanonicalRootExterior
import NLS.ZakharovShabat.SourcePsiEquationContourHomotopy
import NLS.ComplexAnalysis.CircleIntegralExteriorNormalization

/-!
# The large-circle psi normalization in Lemma 12.11

Restoring the deleted numerator root expresses the psi quotient as the
elementary pole times the ratio of two free-normalized products. The
actual canonical-root exterior asymptotic proves that this product ratio
tends uniformly to one. Consequently the actual large-circle integral
tends to `2π`, for every ℓp root vector and every complex source potential.
Identifying this integral with the omitted-gap contour is a separate
contour-decomposition step.
-/

noncomputable section
open Set Complex Filter Topology Metric NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The full numerator product divided by the canonical root, with both
products normalized by their free values. -/
def sourcePsiExteriorProductRatio (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  (entireSingleSpectralProduct (displacedRoots a) z/(-2*sin z)) /
    (sourceCanonicalRoot hp hp1 ψ z/(-2*I*sin z))

/-- Restoring the deleted factor gives the exact relative pole formula.
The identity also holds when the omitted root coincides with `z` or
the canonical root vanishes, using the totalized division convention. -/
theorem sourcePsiContourIntegrand_relative_pole_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (a : Coeff p) (ψ : CoeffPair p) (z : ℂ) (hz : z ∉ freeLattice) :
    (displacedRoots a n-z)*sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ))/I =
      sourcePsiExteriorProductRatio hp hp1 a ψ z := by
  have hsin := sin_ne_zero_of_notMem_freeLattice hz
  have hfull := jointSingleSpectralProduct_eq_deleted hp hp1 n (z,a)
  change entireSingleSpectralProduct (displacedRoots a) z =
    2*(displacedRoots a n-z)*jointDeletedSingleSpectralProduct n (z,a) at hfull
  by_cases hroot : sourceCanonicalRoot hp hp1 ψ z = 0
  · simp [sourcePsiContourIntegrandJoint, sourcePsiExteriorProductRatio, hroot]
  · unfold sourcePsiContourIntegrandJoint sourcePsiCandidate sourcePsiExteriorProductRatio
    rw [hfull]
    field_simp
    simp

/-- The exact relative pole ratio tends to one in every separated
escaping direction, for the actual numerator and canonical root. -/
theorem tendsto_sourcePsiExteriorProductRatio_of_separated {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a : Coeff p) (ψ : CoeffPair p)
    (z : α → ℂ) (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (hsep : ∀ i (m : ℤ), r ≤ ‖z i-(Real.pi : ℂ)*m‖) :
    Tendsto (fun i => sourcePsiExteriorProductRatio hp hp1 a ψ (z i)) l (𝓝 1) := by
  have hnum := tendsto_entireSingleSpectralProduct_div_free_of_separated
    hp (displacedRoots a) (memℓp_displacedRoots a) z hescape hr hrπ hsep
  have hden := tendsto_sourceCanonicalRoot_div_free_of_separated hp hp1 ψ z hescape hr hrπ hsep
  simpa only [sourcePsiExteriorProductRatio, Pi.div_def,
    div_self (by norm_num : (1 : ℂ) ≠ 0)] using
    hnum.div hden (by norm_num : (1 : ℂ) ≠ 0)

/-- The actual relative pole ratio tends uniformly to one on the
half-integer circles, with no supplied asymptotic hypothesis. -/
theorem eventually_centralCircle_sourcePsiExteriorProductRatio_close
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a : Coeff p) (ψ : CoeffPair p)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ z ∈ sphere (0 : ℂ) (centralCircleRadius k),
      ‖sourcePsiExteriorProductRatio hp hp1 a ψ z-1‖ ≤ ε := by
  let S := {z : ℂ // ∀ m : ℤ, Real.pi/4 ≤ ‖z-(Real.pi : ℂ)*m‖}
  have ht := tendsto_sourcePsiExteriorProductRatio_of_separated hp hp1 a ψ
    (fun z : S => z.val) tendsto_comap (by positivity : 0 < Real.pi/4) le_rfl
    (fun z => z.property)
  have hn := (ht.sub_const 1).norm
  simp only [sub_self, norm_zero] at hn
  obtain ⟨R, hR⟩ := exists_threshold_of_eventually_comap_atTop
    (fun z : S => ‖z.val‖) (hn.eventually (gt_mem_nhds hε))
  apply eventually_centralCircle_of_separated_threshold
  exact ⟨R, fun z hz hsep => (hR ⟨z,hsep⟩ hz).le⟩

/-- For the actual psi quotient, the raw large-circle integral has
limit `2π`, the exterior normalization used in Lemma 12.11. -/
theorem tendsto_centralCircle_sourcePsi_raw_integral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p) (ψ : CoeffPair p) :
    Tendsto (fun k : ℕ => ∮ z in C(0,centralCircleRadius k),
      sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ))) atTop (𝓝 (2*Real.pi : ℂ)) := by
  apply tendsto_circleIntegral_of_pole_relative_error (displacedRoots a n)
    centralCircleRadius (fun _ z => sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ)))
    tendsto_centralCircleRadius_atTop
  · filter_upwards [eventually_centralCircle_sourceCanonicalRootDomain hp hp1 ψ] with k hk
    exact (analyticOnNhd_sourcePsiContourIntegrand_fixed hp hp1 n a ψ).continuousOn.mono hk
  · intro ε hε
    filter_upwards [eventually_centralCircle_sourcePsiExteriorProductRatio_close hp hp1 a ψ hε]
      with k hk z hz
    rw [sourcePsiContourIntegrand_relative_pole_eq hp hp1 n a ψ z
      (notMem_freeLattice_of_separated (by positivity : 0 < Real.pi/2)
        (fun m => centralCircle_lattice_gap k hz m))]
    exact hk z hz

/-- The corresponding normalized large-circle contour functional tends
to one. This statement applies in particular to the analytic root family
constructed in Lemma 12.10. -/
theorem tendsto_centralCircle_sourcePsiContour
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p) (ψ : CoeffPair p) :
    Tendsto (fun k : ℕ => sourcePsiContour hp hp1 n a ψ 0 (centralCircleRadius k))
      atTop (𝓝 1) := by
  have hπ : (2*Real.pi : ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  simpa only [sourcePsiContour, inv_mul_cancel₀ hπ] using
    (tendsto_centralCircle_sourcePsi_raw_integral hp hp1 n a ψ).const_mul (2*Real.pi : ℂ)⁻¹

end NLS.ZakharovShabat
