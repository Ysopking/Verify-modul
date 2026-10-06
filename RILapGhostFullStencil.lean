import YangMills.RG.RILapHalfOpenFinite

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

variable {N Nc : ℕ} [NeZero N] [NeZero Nc]

/-- Under strict rectangle fit, a field whose missing upper/lower neighbours
are Neumann ghosts has the literal full symmetric flat stencil.  This is the
abstract glue between the half-open regional operator and the reflected-image
boundary equalities; it makes no claim yet that the CMP89 reflection field
satisfies the two ghost hypotheses. -/
theorem neumannFlatRectangle_laplacian_eq_fullStencil_of_ghost_reconstruct
    {m : Fin 4 → ℤ}
    (hm : ∀ mu, 0 < m mu)
    (hfit : ∀ mu, m mu < (N : ℤ))
    (rho : SUNAdjointModel Nc)
    (spacing : ℝ)
    (f : GaugeZeroCochain 4 N (SUNLieCoord Nc))
    (x : ActiveGaugeRegion.Site
      (cmp89SourceNeumannRectangleActiveRegion (N := N) m))
    (hupper : ∀ i,
      (x.1 i).val + 1 = Int.toNat (m i) →
        f (x.1.shift i) = f x.1)
    (hlower : ∀ i,
      (x.1 i).val = 0 →
        f (x.1.shiftBack i) = f x.1) :
    cmp89SourceNeumannRegionalLaplacian
        (cmp89SourceNeumannRectangleActiveRegion (N := N) m)
        rho
        (cmp99SourceFlatGaugeConfig 4 N Nc)
        spacing
        (restrictZeroCLM
          (cmp89SourceNeumannRectangleActiveRegion (N := N) m) f) x =
      spacing⁻¹ • ∑ i : Fin 4,
        (spacing⁻¹ • (f x.1 - f (x.1.shift i)) -
          spacing⁻¹ • (f (x.1.shiftBack i) - f x.1)) := by
  rw [neumannFlatRectangle_laplacian_eq_halfOpen_reconstruct
    hm hfit rho spacing f x]
  apply congrArg (fun z => spacing⁻¹ • z)
  apply Finset.sum_congr rfl
  intro i _
  have hx :=
    (mem_cmp89SourceNeumannRectangleActiveRegion_sites_iff x.1).mp x.2 i
  by_cases hout : (x.1 i).val + 1 < Int.toNat (m i)
  · rw [if_pos hout]
  · have heq : (x.1 i).val + 1 = Int.toNat (m i) := by omega
    have hu := hupper i heq
    rw [if_neg hout, hu, sub_self, smul_zero]
  by_cases hin : 0 < (x.1 i).val
  · rw [if_pos hin]
  · have hz : (x.1 i).val = 0 := by omega
    have hl := hlower i hz
    rw [if_neg hin, hl, sub_self, smul_zero, sub_zero]

end

end YangMills.RG
