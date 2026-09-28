import NLS.ZakharovShabat.SourcePsiGapRootMap
import NLS.ComplexAnalysis.BanachHolomorphicAffineLineTaylor

/-!
# Complex-line Taylor expansions of the canonical psi roots

The canonical root map on real-type sources agrees locally with a
complex `C¹` branch. That branch is holomorphic on a neighborhood, so
its restriction to every sufficiently short complex affine line has
a Banach-valued Cauchy power series. On real-type endpoints, the sum
is the canonical root vector.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff
namespace NLS.ZakharovShabat

/-- A common source radius gives a convergent Cauchy–Taylor series
along every short complex direction from a real-type source. The
first coefficient is the Fréchet derivative of the local branch;
when the endpoint is real type, the sum is the canonical gap root. -/
theorem exists_local_affineLineTaylor_sourcePsiGapRoot
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : realTypeSourceLocus p) :
    ∃ s : CoeffPair p → DeletedCoeff p n,
      ContDiffAt ℂ 1 s φ.val ∧
      s φ.val = sourcePsiGapRoot hp hp1 n φ ∧
      ∃ R : ℝ, 0 < R ∧
        ∀ h : CoeffPair p, ‖h‖ < R/3 →
          let g : ℂ → DeletedCoeff p n := fun z => s (φ.val + z • h)
          ∃ P : FormalMultilinearSeries ℂ ℂ (DeletedCoeff p n),
            HasFPowerSeriesOnBall g P 0 (2 : ℝ≥0) ∧
            P 1 (fun _ : Fin 1 => 1) = (fderiv ℂ s φ.val) h ∧
            HasSum (fun k : ℕ => P k (fun _ : Fin k => 1))
              (s (φ.val + h)) ∧
            ∀ hreal : IsRealType (CoeffPair.toMax p (φ.val + h)),
              HasSum (fun k : ℕ => P k (fun _ : Fin k => 1))
                (sourcePsiGapRoot hp hp1 n ⟨φ.val + h,hreal⟩) := by
  obtain ⟨s,hs,hsφ,hlocal⟩ :=
    exists_C1_local_extension_sourcePsiGapRoot hp hp1 n φ
  obtain ⟨δ,hδ,hδball⟩ := Metric.mem_nhds_iff.mp hlocal
  obtain ⟨U,hUopen,hφU,hC1raw⟩ := hs.contDiffOn' le_rfl (by simp)
  have hC1 : ContDiffOn ℂ 1 s U := by
    simpa only [insert_eq_of_mem (mem_univ φ.val),univ_inter] using hC1raw
  obtain ⟨R₀,hR₀,hR₀ball,hTaylor⟩ :=
    NLS.ComplexAnalysis.exists_local_affineLine_cauchyTaylor
      s hUopen hC1.differentiableOn_one φ.val hφU
  let R : ℝ := min R₀ δ
  have hR : 0 < R := lt_min hR₀ hδ
  refine ⟨s,hs,hsφ,R,hR,?_⟩
  intro h hh
  have hh₀ : ‖h‖ < R₀/3 := by
    have hle : R ≤ R₀ := min_le_left _ _
    linarith
  have hhδ : ‖h‖ < δ := by
    have hle : R ≤ δ := min_le_right _ _
    linarith
  obtain ⟨P,hP,hPfirst,hPsum⟩ := hTaylor h hh₀
  refine ⟨P,hP,hPfirst,hPsum,?_⟩
  intro hreal
  have hχ : φ.val + h ∈ ball φ.val δ := by
    simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left] using hhδ
  have hEq : s (φ.val + h) =
      sourcePsiGapRoot hp hp1 n ⟨φ.val + h,hreal⟩ :=
    hδball hχ hreal
  simpa only [hEq] using hPsum

/-- The complex local extension of the canonical roots is analytic
along every affine complex line through a real-type source. -/
theorem exists_analytic_affineLine_extension_sourcePsiGapRoot
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : realTypeSourceLocus p) :
    ∃ s : CoeffPair p → DeletedCoeff p n,
      s φ.val = sourcePsiGapRoot hp hp1 n φ ∧
      (∀ᶠ χ in 𝓝 φ.val,
        ∀ hχ : IsRealType (CoeffPair.toMax p χ),
          s χ = sourcePsiGapRoot hp hp1 n ⟨χ,hχ⟩) ∧
      ∀ h : CoeffPair p,
        AnalyticAt ℂ (fun z : ℂ => s (φ.val + z • h)) 0 := by
  obtain ⟨s,hs,hsφ,hlocal⟩ :=
    exists_C1_local_extension_sourcePsiGapRoot hp hp1 n φ
  obtain ⟨U,hUopen,hφU,hC1raw⟩ := hs.contDiffOn' le_rfl (by simp)
  have hC1 : ContDiffOn ℂ 1 s U := by
    simpa only [insert_eq_of_mem (mem_univ φ.val),univ_inter] using hC1raw
  refine ⟨s,hsφ,hlocal,?_⟩
  intro h
  let line : ℂ → CoeffPair p := fun z => φ.val + z • h
  let T : Set ℂ := line ⁻¹' U
  have hlineCont : Continuous line := by
    dsimp [line]
    fun_prop
  have hTopen : IsOpen T := hUopen.preimage hlineCont
  have hzeroT : (0 : ℂ) ∈ T := by
    simpa only [T,line,Set.mem_preimage,zero_smul,add_zero] using hφU
  have hlineDiff : Differentiable ℂ line := by
    dsimp [line]
    fun_prop
  have hdiff : DifferentiableOn ℂ (fun z => s (line z)) T := by
    intro z hz
    have hsDiff : DifferentiableAt ℂ s (line z) :=
      (hC1.differentiableOn_one (line z) hz).differentiableAt
        (hUopen.mem_nhds hz)
    exact (hsDiff.comp z (hlineDiff z)).differentiableWithinAt
  simpa only [line] using hdiff.analyticAt (hTopen.mem_nhds hzeroT)

end NLS.ZakharovShabat
