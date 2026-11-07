import NLS.KdV.PseudomeasureChainJets
import NLS.ComplexAnalysis.MatrixAnalyticJetAction
import NLS.ComplexAnalysis.AffinePencilJets

/-!
# Exact physical chain and effective matrix Taylor-kernel equivalence

The forward map takes the original resonant coefficients of every H1 chain.
For the converse, the actual analytic H1 reconstruction of an arbitrary
amplitude polynomial supplies its full-domain Taylor coefficients. No inverse
of the singular effective matrix or semisimplicity assumption is used.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal Matrix.Norms.Elementwise
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.FunctionalAnalysis NLS.ComplexAnalysis

/-- The actual reduced matrix in the original two-mode coordinates, centered at a spectral point. -/
def endpointReducedMatrixSpectral (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z t : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  pairOperatorMatrixCLM (endpointReducedFamily r hr hr1 n (q,z+t))

variable (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 1 ≤ n)
variable (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ)
variable (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)

include hn hs in
/-- The centered actual reduced operator is norm-analytic in its increment. -/
theorem analyticAt_endpointReduced_increment (hz : z ∈ reducedHillStrip n) :
    AnalyticAt ℂ (fun t : ℂ => endpointReducedFamily r hr hr1 n (q,z+t)) 0 := by
  have hB : AnalyticAt ℂ (endpointReducedFamily r hr hr1 n) (q,z+(0:ℂ)) := by
    simpa only [add_zero] using analyticAt_endpointReducedFamily r hr hr1 n hn (q,z) hz hs
  exact hB.comp (f := fun t : ℂ => (q,z+t))
    (analyticAt_const.prod (analyticAt_const.add analyticAt_id))

include hn hs in
/-- The centered actual reduced matrix has a genuine convergent matrix Taylor series. -/
theorem analyticAt_endpointReducedMatrixSpectral (hz : z ∈ reducedHillStrip n) :
    AnalyticAt ℂ (endpointReducedMatrixSpectral r hr hr1 n q z) 0 :=
  (pairOperatorMatrixCLM.analyticAt _).comp
    (f := fun t : ℂ => endpointReducedFamily r hr hr1 n (q,z+t))
    (analyticAt_endpointReduced_increment r hr hr1 n hn q z hs hz)

include hn hs in
/-- Centering the reconstruction retains analyticity in the original H1 operator norm. -/
theorem analyticAt_endpointReconstruction_increment (hz : z ∈ reducedHillStrip n) :
    AnalyticAt ℂ (fun t : ℂ => endpointReconstructionFamily r hr hr1 n (q,z+t)) 0 := by
  have hF : AnalyticAt ℂ (fun y : ℂ => endpointReconstructionFamily r hr hr1 n (q,y)) (z+(0:ℂ)) := by
    simpa only [add_zero] using analyticAt_endpointReconstruction_spectral r hr hr1 n hn q z hz hs
  exact hF.comp (f := fun t : ℂ => z+t) (analyticAt_const.add analyticAt_id)

variable (p : FormalMultilinearSeries ℂ ℂ (Matrix (Fin 2) (Fin 2) ℂ))
variable (hp : HasFPowerSeriesAt (endpointReducedMatrixSpectral r hr hr1 n q z) p 0)
variable (N : ℕ)

include hr hn hs hp in
/-- The projected coefficients of every physical chain lie in the actual formal matrix Taylor kernel. -/
theorem endpointChainCoordinates_mem_TaylorKernel
    (hz : |z.re-freeHillValue n| < 6*(n:ℝ))
    (v : singularHillChainSpace (endpointHillHminusOne SpectralWeight.one r hr1 q) z N) :
    singularHillChainCoordinates (endpointHillHminusOne SpectralWeight.one r hr1 q) z N n v ∈
      LinearMap.ker (matrixTaylorJetMap (matrixFormalTaylor p) N) := by
  apply (mem_pairOperatorTaylorKernel_iff_derivatives
    (fun t => endpointReducedFamily r hr hr1 n (q,z+t)) hp N _).mpr
  intro k
  have he : (fun t : ℂ => endpointReducedFamily r hr hr1 n (q,z+t)
      (pencilChainPolynomial N
        (singularHillChainCoordinates (endpointHillHminusOne SpectralWeight.one r hr1 q) z N n v) t)) =
      (fun t : ℂ => endpointReducedFamily r hr hr1 n (q,z+t)
        (endpointHillH1Coordinates n (pencilChainPolynomial N v.val t))) := by
    funext t
    rw [chainPolynomial_compCLM (endpointHillH1Coordinates n) N v.val t]
    rfl
  rw [he]
  exact endpointHillChain_reduced_derivatives_zero r hr hr1 n hn q z hs N v.val hz v.property k.val k.isLt

include hr hn hs hp in
/-- The actual two-mode coefficient projection, with its precise formal kernel codomain. -/
def endpointChainToTaylorKernel (hz : |z.re-freeHillValue n| < 6*(n:ℝ)) :
    singularHillChainSpace (endpointHillHminusOne SpectralWeight.one r hr1 q) z N →ₗ[ℂ]
      LinearMap.ker (matrixTaylorJetMap (matrixFormalTaylor p) N) where
  toFun v := ⟨singularHillChainCoordinates (endpointHillHminusOne SpectralWeight.one r hr1 q) z N n v,
    endpointChainCoordinates_mem_TaylorKernel r hr hr1 n hn q z hs p hp N hz v⟩
  map_add' := by intro v w; apply Subtype.ext; exact (singularHillChainCoordinates _ z N n).map_add _ _
  map_smul' := by intro c v; apply Subtype.ext; exact (singularHillChainCoordinates _ z N n).map_smul c _

include hr hn hs hp in
/-- No physical finite chain is lost by the map into the actual formal kernel. -/
theorem endpointChainToTaylorKernel_injective (hz : |z.re-freeHillValue n| < 6*(n:ℝ)) :
    Function.Injective (endpointChainToTaylorKernel r hr hr1 n hn q z hs p hp N hz) := by
  intro v w he
  exact endpointHillChainCoordinates_injective r hr hr1 n hn q z hs N hz (congrArg Subtype.val he)

include hr hn hs hp in
/-- Every formal effective-matrix Taylor kernel vector reconstructs to a
full original H1 chain with precisely those resonant coefficients. -/
theorem endpointChainToTaylorKernel_surjective (hz : |z.re-freeHillValue n| < 6*(n:ℝ)) :
    Function.Surjective (endpointChainToTaylorKernel r hr hr1 n hn q z hs p hp N hz) := by
  intro u
  let a := pencilChainPolynomial N u.val
  let B := fun t : ℂ => endpointReducedFamily r hr hr1 n (q,z+t)
  let F := fun t : ℂ => endpointReconstructionFamily r hr hr1 n (q,z+t)
  let f := fun t : ℂ => F t (a t)
  let C := endpointHillH1Coordinates n
  let M := singularHillDomainInclusion.comp (endpointHillH1Modes n)
  let P := singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q)-z • singularHillDomainInclusion
  have ha : AnalyticAt ℂ a 0 := analyticAt_chainPolynomial N u.val 0
  have hB : AnalyticAt ℂ B 0 := analyticAt_endpointReduced_increment r hr hr1 n hn q z hs hz.le
  have hF : AnalyticAt ℂ F 0 := analyticAt_endpointReconstruction_increment r hr hr1 n hn q z hs hz.le
  have hf : AnalyticAt ℂ f 0 := analyticAt_operatorApply hF ha
  have hBa : AnalyticAt ℂ (fun t => B t (a t)) 0 := analyticAt_operatorApply hB ha
  have hzero : analyticFiniteJet N (fun t => B t (a t)) = 0 :=
    (analyticFiniteJet_eq_zero_iff N _).mpr
      ((mem_pairOperatorTaylorKernel_iff_derivatives B hp N u.val).mp u.property)
  have hMzero : analyticFiniteJet N (fun t => M (B t (a t))) = 0 := by
    rw [analyticFiniteJet_compCLM M hBa, hzero]
    exact funext (fun _ => M.map_zero)
  have hres : (fun t : ℂ => t • singularHillDomainInclusion (f t)-P (f t)) =ᶠ[𝓝 0]
      (fun t : ℂ => M (B t (a t))) := by
    filter_upwards [eventually_shift_mem_reducedHillStrip n z hz] with t ht
    have he := congrArg (fun S => S (a t))
      (endpointReconstructionFamily_residual r hr hr1 n hn (q,z+t) ht hs)
    change endpointPhysicalPencilFamily r hr1 (q,z+t) (f t) = M (B t (a t)) at he
    rw [← he]
    change t • singularHillDomainInclusion (f t) -
      (singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) (f t)-
        z • singularHillDomainInclusion (f t)) =
      (z+t) • singularHillDomainInclusion (f t)-
        singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) (f t)
    rw [add_smul]
    abel
  have hreszero := (analyticFiniteJet_congr hres N).trans hMzero
  have hv : analyticFiniteJet N f ∈
      singularHillChainSpace (endpointHillHminusOne SpectralWeight.one r hr1 q) z N :=
    analyticFiniteJet_mem_pencilChainSpace singularHillDomainInclusion P hf N
      ((analyticFiniteJet_eq_zero_iff N _).mp hreszero)
  have hC : (fun t => C (f t)) =ᶠ[𝓝 0] a := by
    filter_upwards [eventually_shift_mem_reducedHillStrip n z hz] with t ht
    exact congrArg (fun S => S (a t))
      (endpointReconstructionFamily_coordinates r hr hr1 n hn (q,z+t) ht hs)
  have hCv : (fun k => C (analyticFiniteJet N f k)) = u.val := by
    rw [← analyticFiniteJet_compCLM C hf N, analyticFiniteJet_congr hC N]
    exact analyticFiniteJet_chainPolynomial N u.val
  exact ⟨⟨analyticFiniteJet N f,hv⟩, Subtype.ext hCv⟩

include hr hn hs hp in
/-- Exact linear equivalence between every finite full-domain physical chain
space and the actual effective-matrix Taylor kernel at the same length. -/
def endpointChainTaylorKernelEquiv (hz : |z.re-freeHillValue n| < 6*(n:ℝ)) :
    singularHillChainSpace (endpointHillHminusOne SpectralWeight.one r hr1 q) z N ≃ₗ[ℂ]
      LinearMap.ker (matrixTaylorJetMap (matrixFormalTaylor p) N) :=
  LinearEquiv.ofBijective (endpointChainToTaylorKernel r hr hr1 n hn q z hs p hp N hz)
    ⟨endpointChainToTaylorKernel_injective r hr hr1 n hn q z hs p hp N hz,
      endpointChainToTaylorKernel_surjective r hr hr1 n hn q z hs p hp N hz⟩

include hr hn hs hp in
/-- The actual finite physical root-space dimension equals the actual matrix Taylor nullity. -/
theorem finrank_endpointHillRootSpace_eq_TaylorKernel (hz : |z.re-freeHillValue n| < 6*(n:ℝ)) :
    Module.finrank ℂ (singularHillRootSpace
      (endpointHillHminusOne SpectralWeight.one r hr1 q) z N) =
      Module.finrank ℂ (LinearMap.ker (matrixTaylorJetMap (matrixFormalTaylor p) N)) := by
  rw [← finrank_singularHillChainSpace]
  exact (endpointChainTaylorKernelEquiv r hr hr1 n hn q z hs p hp N hz).finrank_eq

end NLS.KdV
