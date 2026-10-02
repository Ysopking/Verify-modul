import YangMills.RG.NeumannFlatInternalBondAction
import YangMills.RG.RILapStrictMasks

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

variable {N Nc : ℕ} [NeZero N] [NeZero Nc]

/-- Under strict rectangle fit, the cold finite regional flat Laplacian is
exactly the half-open Neumann stencil: no torus-wrap branch survives. -/
theorem neumannFlatRectangle_laplacian_eq_halfOpen_reconstruct
    {m : Fin 4 → ℤ}
    (hm : ∀ mu, 0 < m mu)
    (hfit : ∀ mu, m mu < (N : ℤ))
    (rho : SUNAdjointModel Nc)
    (spacing : ℝ)
    (f : GaugeZeroCochain 4 N (SUNLieCoord Nc))
    (x : ActiveGaugeRegion.Site
      (cmp89SourceNeumannRectangleActiveRegion (N := N) m)) :
    cmp89SourceNeumannRegionalLaplacian
        (cmp89SourceNeumannRectangleActiveRegion (N := N) m)
        rho
        (cmp99SourceFlatGaugeConfig 4 N Nc)
        spacing
        (restrictZeroCLM
          (cmp89SourceNeumannRectangleActiveRegion (N := N) m) f) x =
      spacing⁻¹ • ∑ i : Fin 4,
        ((if (x.1 i).val + 1 < Int.toNat (m i) then
            spacing⁻¹ • (f x.1 - f (x.1.shift i)) else 0) -
          (if 0 < (x.1 i).val then
            spacing⁻¹ • (f (x.1.shiftBack i) - f x.1) else 0)) := by
  rw [neumannFlatInternalBond_laplacian_apply]
  apply congrArg (fun z => spacing⁻¹ • z)
  apply Finset.sum_congr rfl
  intro i _
  rw [neumannRectangle_outgoingBond_iff_strict_reconstruct hm hfit x i]
  rw [neumannRectangle_incomingBond_iff_strict_reconstruct hm hfit x i]

end

end YangMills.RG
