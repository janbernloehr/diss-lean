import NLS.ZakharovShabat.SourceMidpointDiscSeparation
import NLS.ZakharovShabat.SourcePeriodicMidpointAsymptotics
import NLS.Fourier.SeparatedReciprocalRows

/-!
# Physical midpoint correction for the first-order omitted-index sum

On distant source discs, the difference between the physical reciprocal
midpoint row and the free lattice row has a uniform square-kernel bound.
This is the summable correction in the Hilbert-transform argument for
Lemma 10.8.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source midpoint, any admissible spectral samples, and the free
lattice satisfy the abstract separated-row hypotheses. -/
theorem sourceMidpoint_separatedReciprocalRows
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p)
    (N : ℕ) (ε C R : ℝ) (hC : 1 ≤ C) (hR : 0 ≤ R)
    (hdisp : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ R)
    (hsep : ∀ i j : ℤ, i ≠ j →
      ∀ w ∈ sourceIsolatingDisc hp hp1 φ N ε i,
        |((i-j : ℤ) : ℝ)| ≤ C *
          ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) j-w‖)
    (z : ℤ → ℂ)
    (hz : ∀ n : ℤ, N < n.natAbs →
      z n ∈ sourceIsolatingDisc hp hp1 φ N ε n) :
    Fourier.SeparatedReciprocalRows {n : ℤ | N < n.natAbs} C R
      (fun m => canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m) z := by
  refine ⟨hR, by linarith, ?_, ?_, ?_⟩
  · intro m
    rw [← sourcePeriodicMidpointDisplacement_apply hp hp1 ψ]
    exact (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
      (sourcePeriodicMidpointDisplacement hp hp1 ψ) m).trans hdisp
  · intro n hn m hmn
    exact hsep n m (Ne.symm hmn) (z n) (hz n hn)
  · intro n hn m hmn
    have hn' : N < n.natAbs := hn
    have hzn : z n ∈ refinedResonantDisk n := by
      simpa only [sourceIsolatingDisc, if_neg (not_le.mpr hn')] using hz n hn'
    have hwm : (Real.pi : ℂ)*m ∈ refinedResonantDisk m := by
      simp only [refinedResonantDisk, mem_ball, dist_self]
      positivity
    have hsepFree := (refinedResonantDisk_pointwise_separation hmn hwm hzn).1
    have habs : |((m-n : ℤ) : ℝ)| = |((n-m : ℤ) : ℝ)| := by
      rw [show m-n = -(n-m) by ring, Int.cast_neg, abs_neg]
    rw [habs, dist_eq_norm] at hsepFree
    have hπ : 1 ≤ Real.pi/2 := by nlinarith [Real.pi_gt_three]
    have hnonneg : 0 ≤ |((n-m : ℤ) : ℝ)| := abs_nonneg _
    nlinarith

/-- The physical-to-free first-order correction is an `ℓq` sequence,
uniformly in all choices of spectral points in the distant discs. -/
theorem exists_sourceMidpointHilbertCorrection
    {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p)
    (N : ℕ) (ε C R : ℝ) (hC : 1 ≤ C) (hR : 0 ≤ R)
    (hdisp : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ R)
    (hsep : ∀ i j : ℤ, i ≠ j →
      ∀ w ∈ sourceIsolatingDisc hp hp1 φ N ε i,
        |((i-j : ℤ) : ℝ)| ≤ C *
          ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) j-w‖)
    (z : ℤ → ℂ)
    (hz : ∀ n : ℤ, N < n.natAbs →
      z n ∈ sourceIsolatingDisc hp hp1 φ N ε n)
    (α : Coeff q) :
    ∃ b : Coeff q,
      (∀ n : ℤ, N < n.natAbs →
        b n = ∑' m : ℤ,
          (if m = n then 0 else
            α m / (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
              (periodOnePotential_mem ψ) m-z n) -
            α m / ((Real.pi : ℂ)*m-z n))) ∧
      ‖b‖ ≤ C*R*(‖α‖*‖Fourier.hilbertSquareCoeffs‖) := by
  let τ : ℤ → ℂ := fun m => canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) m
  have hrows : Fourier.SeparatedReciprocalRows {n : ℤ | N < n.natAbs} C R τ z :=
    sourceMidpoint_separatedReciprocalRows hp hp1 φ ψ N ε C R hC hR hdisp hsep z hz
  refine ⟨Fourier.separatedReciprocalCorrection hrows α, ?_,
    Fourier.norm_separatedReciprocalCorrection_le hrows α⟩
  intro n hn
  rw [Fourier.separatedReciprocalCorrection_apply hrows α hn]
  rfl

/-- A common connected neighborhood supplies both midpoint separation and
a uniform midpoint displacement norm bound for the correction theorem. -/
theorem exists_local_sourceMidpointHilbertCorrection_data
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧
        ∃ C R : ℝ, 1 ≤ C ∧ 0 ≤ R ∧
          ∀ ψ ∈ V,
            ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ R ∧
            ∀ i j : ℤ, i ≠ j →
              ∀ w ∈ sourceIsolatingDisc hp hp1 φ N ε i,
                |((i-j : ℤ) : ℝ)| ≤ C *
                  ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
                    (periodOnePotential_mem ψ) j-w‖ := by
  obtain ⟨N,ε,hε,hεmax,Vsep,hVsepOpen,_,hφVsep,C,hC,hsep⟩ :=
    exists_local_source_midpoint_index_separation hp hp1 φ hφ
  obtain ⟨_,_,Vmid,hVmidOpen,hφVmid,R,hR,hmid⟩ :=
    exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ
      (by norm_num : (0 : ℝ) < 1)
  have hUopen : IsOpen (Vsep ∩ Vmid) := hVsepOpen.inter hVmidOpen
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp
    (hUopen.mem_nhds ⟨hφVsep,hφVmid⟩)
  refine ⟨N,ε,hε,hεmax,ball φ r,Metric.isOpen_ball,
    isConnected_ball hr,mem_ball_self hr,C,R,hC,hR,?_⟩
  intro ψ hψ
  have hψU : ψ ∈ Vsep ∩ Vmid := hrU hψ
  exact ⟨(hmid ψ hψU.2).1, hsep ψ hψU.1⟩

end NLS.ZakharovShabat
