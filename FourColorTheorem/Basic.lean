import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Data.Setoid.Partition
import Mathlib.Topology.MetricSpace.Pseudo.Defs

set_option linter.style.longLine false

abbrev R3 := EuclideanSpace ℝ (Fin 3)
abbrev S2 := Metric.sphere (0 : R3) 1

def closureMinusItself {T : Type*} [TopologicalSpace T] (e : Set T) := closure e \ e
def IsDrawingEdge (e : Set S2) : Prop :=
  ∃ f : unitInterval ≃ₜ closure e, closureMinusItself e = {↑(f 0), ↑(f 1)}

structure PreDrawing where
  univ : Set S2
  vertices : Finset S2

def PreDrawing.edges_union (g : PreDrawing) : Set S2 := g.univ \ g.vertices
def PreDrawing.edges (g : PreDrawing) : Set (Set g.edges_union) :=
  (pathSetoid g.edges_union).classes
def PreDrawing.edge_ends {g : PreDrawing} (e : g.edges) : Set S2 :=
  closureMinusItself (T := S2) e.val
-- def PreDrawing.edge_vertex_incident {g : PreDrawing} (v : g.vertices) (e : g.edges) :=
--   (v: S2) ∈ g.edge_ends e

structure Drawing extends PreDrawing where
  univ_closed : IsClosed univ
  vertices_in_univ : ↑vertices ⊆ univ
  edges_finite : Finite toPreDrawing.edges
  edges_IsDrawingEdge : ∀ e ∈ toPreDrawing.edges, IsDrawingEdge e

theorem Drawing.edge_ends_are_vertices
    {g : Drawing} {e : g.edges} {v : S2} (h : v ∈ g.edge_ends e) : v ∈ g.vertices := by
  unfold PreDrawing.edge_ends closureMinusItself at h
  set e' := (e.val: Set S2) with he'
  have: closure e' ⊆ g.univ := by
    refine closure_minimal ?_ g.univ_closed
    unfold PreDrawing.edges at e
    sorry
  sorry

def Drawing.toGraph (g : Drawing) : Graph g.vertices g.edges where
  vertexSet := Set.univ
  IsLink e u v := g.edge_ends e = {(u: S2), (v: S2)}
  edgeSet := Set.univ
  isLink_symm := by intro e he u v; grind
  eq_or_eq_of_isLink_of_isLink := by
    intro e u v x y huv hxy
    rw [huv, Set.pair_eq_pair_iff] at hxy
    grind
  edge_mem_iff_exists_isLink := by
    simp only [Set.mem_univ, true_iff]
    intro e
    obtain ⟨hom, hhom⟩ := g.edges_IsDrawingEdge e.val e.prop
    sorry
  left_mem_of_isLink := by simp

-- structure Drawing where
--   univ : Set S2
--   univ_closed : IsClosed univ
--   vertices : Finset S2
--   vertices_in_univ : ↑vertices ⊆ univ
--   edges_finite : Finite (ZerothHomotopy ↑(univ \ vertices))
--   edges_are_line : ∀ x ∈ (univ \ vertices), IsDrawingEdge (pathComponentIn (univ \ vertices) x)
-- 
-- def Drawing.edge_set (g : Drawing) := g.univ \ g.vertices
-- def Drawing.Edge (g : Drawing) := ZerothHomotopy ↑g.edge_set
-- def edge_ends {g: Drawing} (e: g.Edge) := closure e \ e
-- def Drawing.edge_vertex_incident {g: Drawing} (v: g.vertices) (e: g.Edge) := v ∈ edge_ends e
-- 
-- def Drawing.HasEdge (g : Drawing) (u v : g.vertices) :=
--   ∃ x ∈ (g.univ \ g.vertices),
--     let e := pathComponentIn (g.univ \ g.vertices) x
--     closure e \ e = {↑u, ↑v}
-- 
-- def IsColoring (g : Drawing) (α : Type*) (f : g.vertices → α) :=
--   ∀ u v : g.vertices, g.HasEdge u v → f u ≠ f v
-- 
-- theorem four_color_theorem (g : Drawing) : ∃ f, IsColoring g (Fin 4) f := by
--   sorry
