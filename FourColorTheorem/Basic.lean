import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Data.Setoid.Partition
import Mathlib.Topology.MetricSpace.Pseudo.Defs

set_option linter.style.longLine false

abbrev R3 := EuclideanSpace ℝ (Fin 3)
abbrev S2 := ↥(Metric.sphere (0 : R3) 1)

def closureMinusItself {T : Type*} [TopologicalSpace T] (e : Set T) := closure e \ e
def IsDrawingEdge (e : Set S2) : Prop :=
  ∃ f : unitInterval ≃ₜ closure e, closureMinusItself e = {↑(f 0), ↑(f 1)}

structure PreDrawing where
  univ : Set S2
  vertices : Finset S2

def PreDrawing.edges_union (g : PreDrawing) : Set S2 := g.univ \ g.vertices
def PreDrawing.edges (g : PreDrawing) : Set (Set S2) :=
  (fun (x: Set g.edges_union) ↦ ↑x) '' (pathSetoid g.edges_union).classes
def PreDrawing.edge_ends {g : PreDrawing} (e : g.edges) : Set S2 :=
  closureMinusItself (T := S2) e.val
-- def PreDrawing.edge_vertex_incident {g : PreDrawing} (v : g.vertices) (e : g.edges) :=
--   (v: S2) ∈ g.edge_ends e

structure Drawing extends PreDrawing where
  univ_closed : IsClosed univ
  vertices_in_univ : ↑vertices ⊆ univ
  edges_finite : Finite toPreDrawing.edges
  edges_IsDrawingEdge : ∀ e: toPreDrawing.edges, IsDrawingEdge e

lemma my_lemma
    {α : Type*} {r : Setoid α} {c : Set α} (hc : c ∈ r.classes)
    {x y : α} (hx : x ∈ c) (hy : y ∉ c) :
      ¬ r x y := by
  contrapose hy
  simp only [Setoid.classes, Set.mem_setOf_eq] at hc
  obtain ⟨z, hz⟩ := hc
  simp only [hz, Set.mem_setOf_eq] at hx ⊢
  trans x
  · symm; tauto
  · tauto

-- obtain ⟨patt⟩ : type := proof
-- is equivalent to
-- 
-- have h : type := proof
-- rcases h with ⟨patt⟩

-- set_option pp.fieldNotation false
-- set_option pp.coercions false
-- set_option pp.proofs.threshold 50
-- set_option pp.numericTypes true

instance : PathConnectedSpace unitInterval := by
  unfold unitInterval 
  have := (convex_Icc (0 : ℝ) 1).isPathConnected (by exact Set.Nonempty.of_subtype)
  rw [← isPathConnected_iff_pathConnectedSpace]
  tauto

-- example: True := 
--   #loogle Joined
-- 
theorem Drawing.edge_ends_are_vertices
    {g : Drawing} {e : g.edges} {v : S2} (hvee : v ∈ g.edge_ends e) : v ∈ g.vertices := by
  -- by_contra hvv

  -- obtain ⟨f, hf⟩ := g.edges_IsDrawingEdge e
  -- have v_in_univ: v ∈ g.univ := by
  --   sorry
  -- have x_in_univ (x: e.val): x.val ∈ g.univ := by
  --   sorry
  -- let joined (x: e.val) := Joined (⟨x.val, x_in_univ x⟩: g.univ) ⟨v, v_in_univ⟩
  -- have h_not_joined (x: e.val) : ¬joined x := by
  --   -- change ¬ pathSetoid _ _ _
  --   -- apply my_lemma
  --   all_goals sorry
  -- have h_joined (x: e.val) : joined x := by
  --   let g (t: univInterval) := 
  --   unfold joined Joined
  --   sorry

  obtain ⟨f, hf⟩ := g.edges_IsDrawingEdge e
  let tx: unitInterval := ⟨1/2, by simp; linarith⟩
  set x: S2 := (f tx).val with hx

  have x_in_closure_e: x ∈ closure e.val := by simp only [hx, Subtype.coe_prop]
  have x_in_univ : x ∈ g.univ := by
    sorry
  have v_in_closure_e : v ∈ closure e.val := by
    sorry
  have v_in_univ : v ∈ g.univ := by
    sorry
  have closure_e_in_univ : closure e.val ⊆ g.univ := by
    sorry

  have x_in_e : x ∈ e.val := by
    by_contra h2
    have := Set.mem_diff_of_mem x_in_closure_e h2
    unfold closureMinusItself at hf
    simp only [hx, hf, Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h | h <;> (
      rw [← Subtype.ext_iff] at h
      rw [Function.Injective.eq_iff (Homeomorph.injective f)] at h
      apply congr_arg Subtype.val at h
      simp [tx] at h
    )

  have h_joined : Joined (⟨x, x_in_univ⟩: g.univ) ⟨v, v_in_univ⟩ := by
    let tv := f.symm ⟨v, v_in_closure_e⟩
    let h := Set.inclusion closure_e_in_univ ∘ f
    let p := PathConnectedSpace.joined tx tv |>.somePath |>.map (f := h) ?cont
    case cont =>
      simp only [Homeomorph.comp_continuous_iff', h]
      apply continuous_inclusion
    use p <;> (
      unfold p h
      simp only [Function.comp_apply]
      simp only [ContinuousMap.toFun_eq_coe]
      simp only [ContinuousMap.coe_coe]
      erw [Path.map_coe]
      simp
    )
    · tauto
    · simp [tv]
  have h_not_joined : ¬Joined (⟨x, x_in_univ⟩: g.univ) ⟨v, v_in_univ⟩ := by
    sorry
  
  tauto

  -- have h_joined (x: e.val) : joined x := by

  -- specialize h_joined x
  -- specialize h_not_joined x
  -- tauto

  -- all_goals sorry

  -- have : x ∈ (e.val : Set S2) := by
  --   simp only [PreDrawing.edge_ends, closureMinusItself] at hvee
  --   sorry
  -- have hx : x ∈ g.edges_union := by
  --   sorry
  -- have hx' : ⟨x, hx⟩ ∈ e.val := by
  --   sorry
  -- specialize h_joined ⟨x, hx⟩ hx'
  -- specialize h_not_joined ⟨x, hx⟩ hx'
  -- tauto
  -- sorry

  -- have hv: v ∈ g.edges_union := by
  --   sorry
  -- obtain ⟨e, he⟩ := e
  -- rcases e with ⟨e, he⟩
  -- obtain ⟨f, hf⟩ := g.edges_IsDrawingEdge e he
  -- have: ∃ t: unitInterval, v = f t := by
  --   unfold PreDrawing.edge_ends at hv
  --   rw [hf] at hv
  --   simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  --   cases hv
  --   · use 0
  --   · use 1
  -- obtain ⟨t, ht⟩ := this
  -- have {x: g.edges_union} (hx: x ∈ e): ¬ Joined x ⟨v, hv⟩ := by
  --   change ¬ pathSetoid _ _ _
  --   apply my_lemma he hx
  --   grind

  -- unfold PreDrawing.edge_ends at hv
  -- unfold PreDrawing.edge_ends at h
  -- obtain ⟨f, hf⟩ := g.edges_IsDrawingEdge e.val e.prop
  -- have: ∃ t: unitInterval, v = f t := by
  --   rw [hf] at h
  --   simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  --   cases h
  --   · use 0
  --   · use 1
  -- obtain ⟨t, ht⟩ := this
  -- unfold closureMinusItself at h
  -- rw [Set.mem_diff] at h
  -- obtain ⟨hvce', hve'⟩ := h
  -- set e' := (e.val: Set S2) with he'
  -- have: closure e' ⊆ g.univ := by
  --   apply closure_minimal _ g.univ_closed
  --   trans g.edges_union
  --   · unfold e'; simp
  --   · simp [PreDrawing.edges_union]
  -- have hvu: v ∈ g.univ := Set.mem_of_mem_of_subset (by tauto) this
  -- by_contra hvv
  -- have hv: v ∈ g.edges_union := by simp [PreDrawing.edges_union]; tauto
  -- unfold PreDrawing.edges at e
  -- clear hvu hvv
  -- obtain ⟨e, he⟩ := e
  -- have {x: g.edges_union} (hx: x ∈ e): ¬ Joined x ⟨v, hv⟩ := by
  --   change ¬ pathSetoid _ _ _
  --   apply my_lemma he hx
  --   grind

example {α : Type*} (s : Set α) (e : s) : e.val ∈ s := by
  simp only [Subtype.coe_prop]

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
    -- obtain ⟨hom, hhom⟩ := g.edges_IsDrawingEdge e.val e.prop
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
