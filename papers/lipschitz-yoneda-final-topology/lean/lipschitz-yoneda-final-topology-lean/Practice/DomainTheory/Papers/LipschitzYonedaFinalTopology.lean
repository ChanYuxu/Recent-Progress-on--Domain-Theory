import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.LayeredTopology
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.QuasiMetric
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.Cones
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.CenterPoints
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.Interpolation
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.Forest
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.ConeForest
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.Upperness
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.Retract
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.CompletionVisibility
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.OrderExample
import Practice.DomainTheory.Papers.LipschitzYonedaFinalTopology.MainTheorem

/-!
# Final topologies of Lipschitz Yoneda-continuous maps

This is the import facade for the mechanized core of
`lipschitz_yoneda_final_topology_paper_fifth_audit.tex`.

The manuscript's headline theorem is declared and proved in
`MainTheorem.lean`.  Its proof combines the kernel-checked cone-forest
argument for algebraic Yoneda-complete spaces with the explicitly
constructed rounded-ideal completion retract.  See
`FORMALIZATION_STATUS.md` for the claim-by-claim audit trail.
-/
