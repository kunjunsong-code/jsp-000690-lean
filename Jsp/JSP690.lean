import Mathlib

/-!
# JSP-000690 — three-uniform three-chromatic-critical hypergraph of minimum degree 7

**Problem.** *Is there a three-uniform, three-chromatic-critical hypergraph with minimum
degree at least seven?*

**Answer.** Yes.  Following Li (2025), arXiv:2512.24850, we exhibit a 9-vertex 3-uniform
hypergraph `H` with `χ(H) = 3` and `δ(H) = 7`, such that deleting any edge or any vertex
makes it 2-colourable (i.e. `H` is 3-chromatic-critical).

`H` has 22 edges; the vertex set is `{1,…,9}` and the 22 edges are listed verbatim from
the paper.  All the finite verifications (3-uniformity, minimum degree, non-2-colourability,
3-colourability and the edge/vertex criticality certificates) are carried out by `decide`,
so the file is `sorry`-free and uses no `native_decide`.

Vertices are `Fin 10` with labels `1,…,9` (the label `0` is unused).  Keeping the paper's
labels avoids any re-indexing of the 22 edges.
-/

set_option maxRecDepth 100000

namespace JSP690

open Finset

/-! ## The hypergraph and its auxiliary data -/

/-- A colouring `c` makes the edge `e` monochromatic. -/
abbrev IsMono {V γ : Type*} [DecidableEq γ] (c : V → γ) (e : Finset V) : Prop :=
  ∀ x ∈ e, ∀ y ∈ e, c x = c y

/-- The vertex set `{1,…,9}`. -/
def V : Finset (Fin 10) := {1, 2, 3, 4, 5, 6, 7, 8, 9}

/-- The 22 edges of `H`. -/
def E : Finset (Finset (Fin 10)) :=
  { {1,2,3},{1,2,9},{1,3,8},{1,4,6},{1,4,8},{1,4,9},{1,5,7},{1,5,8},{1,5,9},
    {1,6,7},{2,3,6},{2,3,7},{2,4,9},{2,5,9},{2,6,7},{3,4,8},{3,5,8},{3,6,7},
    {4,6,8},{4,6,9},{5,7,8},{5,7,9} }

/-- The vertices different from `1`. -/
def J : Finset (Fin 10) := {2, 3, 4, 5, 6, 7, 8, 9}

/-- The graph `G` on `J` whose edges `{x,y}` give the `H`-edges `{1,x,y}`. -/
def aux : Finset (Finset (Fin 10)) :=
  { {2,3}, {2,9}, {3,8}, {4,6}, {4,8}, {4,9}, {5,7}, {5,8}, {5,9}, {6,7} }

/-- The edges of `H` avoiding the vertex `1`. -/
def H0 : Finset (Finset (Fin 10)) :=
  { {2,3,6}, {2,3,7}, {2,4,9}, {2,5,9}, {2,6,7}, {3,4,8}, {3,5,8}, {3,6,7},
    {4,6,8}, {4,6,9}, {5,7,8}, {5,7,9} }

/-- A proper 3-colouring of `H`: `1,2,4,5 ↦ 0`, `3,6,8,9 ↦ 1`, `7 ↦ 2`. -/
def psi : Fin 10 → Fin 3 := fun i =>
  if i = 1 ∨ i = 2 ∨ i = 4 ∨ i = 5 then 0
  else if i = 3 ∨ i = 6 ∨ i = 8 ∨ i = 9 then 1 else 2

/-- For the edge `e`, the "blue" side of the 2-colouring witnessing that `H - e` is
2-colourable (Table 1 of the paper). -/
def eblue (e : Finset (Fin 10)) : Finset (Fin 10) :=
  if e = {1,2,3} then {6,7,8,9}
  else if e = {1,2,9} then {3,4,5,6}
  else if e = {1,3,8} then {2,4,5,6}
  else if e = {1,4,6} then {2,7,8,9}
  else if e = {1,4,8} then {3,5,6,9}
  else if e = {1,4,9} then {2,5,6,8}
  else if e = {1,5,7} then {2,6,8,9}
  else if e = {1,5,8} then {3,4,7,9}
  else if e = {1,5,9} then {2,4,7,8}
  else if e = {1,6,7} then {2,3,4,5}
  else if e = {2,3,6} then {1,7,8,9}
  else if e = {2,3,7} then {1,6,8,9}
  else if e = {2,4,9} then {1,3,5,6}
  else if e = {2,5,9} then {1,3,4,7}
  else if e = {2,6,7} then {1,3,4,5}
  else if e = {3,4,8} then {1,2,5,6}
  else if e = {3,5,8} then {1,2,4,7}
  else if e = {3,6,7} then {1,2,4,5}
  else if e = {4,6,8} then {1,3,7,9}
  else if e = {4,6,9} then {1,2,7,8}
  else if e = {5,7,8} then {1,3,6,9}
  else if e = {5,7,9} then {1,2,6,8}
  else ∅

/-- For the vertex `v`, the "blue" side of the 2-colouring witnessing that `H - v` is
2-colourable (Table 2 of the paper). -/
def vblue (v : Fin 10) : Finset (Fin 10) :=
  if v = 1 then {2,3,4,5}
  else if v = 2 then {1,3,4,5}
  else if v = 3 then {1,2,4,5}
  else if v = 4 then {1,2,5,6}
  else if v = 5 then {1,2,4,7}
  else if v = 6 then {1,2,4,5}
  else if v = 7 then {1,2,4,5}
  else if v = 8 then {1,2,4,7}
  else if v = 9 then {1,2,6,8}
  else ∅

/-! ## Two generic helpers turning a `filter`-cardinality count into a `∀`-statement -/

lemma forall_mem_of_filter_card_eq {α : Type*} [DecidableEq α] (s : Finset α) (P : α → Prop)
    [DecidablePred P] (h : (s.filter (fun x => decide (P x) = true)).card = s.card) :
    ∀ x ∈ s, P x := by
  have hsub : s.filter (fun x => decide (P x) = true) ⊆ s := Finset.filter_subset _ _
  have heq : s.filter (fun x => decide (P x) = true) = s :=
    Finset.eq_of_subset_of_card_le hsub (le_of_eq h.symm)
  intro x hx
  have hx' : x ∈ s.filter (fun x => decide (P x) = true) := by
    rw [heq]; exact hx
  exact of_decide_eq_true (Finset.mem_filter.mp hx').2

lemma not_forall_mem_of_filter_card_eq_zero {α : Type*} [DecidableEq α] (s : Finset α)
    (P : α → Prop) [DecidablePred P] (h : (s.filter (fun x => decide (P x) = true)).card = 0) :
    ∀ x ∈ s, ¬ P x := by
  have hempty : s.filter (fun x => decide (P x) = true) = ∅ := Finset.card_eq_zero.mp h
  intro x hx hP
  have hx' : x ∈ s.filter (fun x => decide (P x) = true) :=
    Finset.mem_filter.mpr ⟨hx, decide_eq_true hP⟩
  rw [hempty] at hx'
  exact Finset.notMem_empty x hx'

/-! ## Monochromatic-edge characterisation for explicit 2-colourings -/

/-- A `Bool`-valued colouring given by a "blue" set `B` makes `f` monochromatic exactly
when `f` lies entirely in `B` or entirely outside `B`. -/
lemma isMono_decide_iff (B f : Finset (Fin 10)) :
    IsMono (fun u => decide (u ∈ B)) f ↔ f ⊆ B ∨ f ∩ B = ∅ := by
  constructor
  · intro h
    rcases f.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · exact Or.inl (Finset.empty_subset B)
    · by_cases hxB : x ∈ B
      · left
        intro y hy
        have hxT : decide (x ∈ B) = true := by simp [hxB]
        have h2 : decide (x ∈ B) = decide (y ∈ B) := h x hx y hy
        rw [hxT] at h2
        exact of_decide_eq_true h2.symm
      · right
        rw [Finset.eq_empty_iff_forall_notMem]
        intro y hy
        rw [Finset.mem_inter] at hy
        obtain ⟨hyf, hyB⟩ := hy
        have hxF : decide (x ∈ B) = false := by simp [hxB]
        have hyT : decide (y ∈ B) = true := by simp [hyB]
        have h2 : decide (x ∈ B) = decide (y ∈ B) := h x hx y hyf
        rw [hxF, hyT] at h2
        exact absurd h2 (by decide)
  · rintro (hsub | hdisj)
    · intro x hx y hy
      show decide (x ∈ B) = decide (y ∈ B)
      simp [hsub hx, hsub hy]
    · intro x hx y hy
      show decide (x ∈ B) = decide (y ∈ B)
      have hx' : x ∉ B :=
        fun h => (Finset.eq_empty_iff_forall_notMem.mp hdisj) x (Finset.mem_inter.mpr ⟨hx, h⟩)
      have hy' : y ∉ B :=
        fun h => (Finset.eq_empty_iff_forall_notMem.mp hdisj) y (Finset.mem_inter.mpr ⟨hy, h⟩)
      simp [hx', hy']

/-! ## Basic invariants of `H` -/

theorem V_card : V.card = 9 := by decide

theorem E_card : E.card = 22 := by decide

theorem J_card : J.card = 8 := by decide

/-- Every vertex of `V` occurs in an edge. -/
theorem vertex_set : E.biUnion id = V := by decide

/-- `H` is 3-uniform. -/
theorem uniform : ∀ e ∈ E, e.card = 3 :=
  forall_mem_of_filter_card_eq E (fun e => e.card = 3) (by decide)

/-- Every edge is contained in `V`. -/
theorem edge_subset_V : ∀ e ∈ E, e ⊆ V :=
  forall_mem_of_filter_card_eq E (fun e => e ⊆ V) (by decide)

/-- The minimum degree of `H` is at least `7`. -/
theorem min_degree : ∀ v ∈ V, 7 ≤ (E.filter (fun e => v ∈ e)).card :=
  forall_mem_of_filter_card_eq V (fun v => 7 ≤ (E.filter (fun e => v ∈ e)).card) (by decide)

/-- `H0` consists of edges of `H`. -/
theorem H0_subset_E : H0 ⊆ E :=
  forall_mem_of_filter_card_eq H0 (fun e => e ∈ E) (by decide)

/-- Adding the vertex `1` to a graph edge of `aux` yields an edge of `H`. -/
theorem aux_bridge : ∀ e ∈ aux, insert 1 e ∈ E :=
  forall_mem_of_filter_card_eq aux (fun e => insert 1 e ∈ E) (by decide)

/-! ## The two combinatorial facts driving non-2-colourability -/

/-- Every 4-element subset of `J` contains an edge of the graph `aux`. -/
theorem no_indep4 : ∀ S ∈ J.powersetCard 4, ∃ e ∈ aux, e ⊆ S :=
  forall_mem_of_filter_card_eq (J.powersetCard 4) (fun S => ∃ e ∈ aux, e ⊆ S) (by decide)

/-- Every 5-element subset of `J` contains an edge of `H0`. -/
theorem hitting5 : ∀ T ∈ J.powersetCard 5, ∃ f ∈ H0, f ⊆ T :=
  forall_mem_of_filter_card_eq (J.powersetCard 5) (fun T => ∃ f ∈ H0, f ⊆ T) (by decide)

/-! ## `H` is not 2-colourable -/

theorem not_two_colorable : ¬ ∃ c : Fin 10 → Bool, ∀ e ∈ E, ¬ IsMono c e := by
  rintro ⟨c, hc⟩
  -- `S` = vertices of `J` sharing the colour of vertex `1`
  let S : Finset (Fin 10) := J.filter (fun v => c v = c 1)
  have hSsub : S ⊆ J := Finset.filter_subset _ _
  have hSno : ¬ ∃ e ∈ aux, e ⊆ S := by
    rintro ⟨e, he, heS⟩
    have hins : insert 1 e ∈ E := aux_bridge e he
    have hmono : IsMono c (insert 1 e) := by
      intro x hx y hy
      have hx1 : c x = c 1 := by
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · rfl
        · exact (Finset.mem_filter.mp (heS hx)).2
      have hy1 : c y = c 1 := by
        rw [Finset.mem_insert] at hy
        rcases hy with rfl | hy
        · rfl
        · exact (Finset.mem_filter.mp (heS hy)).2
      rw [hx1, hy1]
    exact hc (insert 1 e) hins hmono
  have hcardS : S.card ≤ 3 := by
    by_contra h
    rw [not_le] at h
    obtain ⟨S', hS'S, hS'card⟩ := Finset.exists_subset_card_eq (show 4 ≤ S.card by omega)
    have hS'J : S' ⊆ J := hS'S.trans hSsub
    have hS'pow : S' ∈ J.powersetCard 4 := Finset.mem_powersetCard.mpr ⟨hS'J, hS'card⟩
    obtain ⟨e, he, heS'⟩ := no_indep4 S' hS'pow
    exact hSno ⟨e, he, heS'.trans hS'S⟩
  -- `T` = vertices of `J` with a colour different from the colour of vertex `1`
  let T : Finset (Fin 10) := J \ S
  have hTsubJ : T ⊆ J := Finset.sdiff_subset
  have hTcard : 5 ≤ T.card := by
    have h1 : T.card = J.card - S.card := Finset.card_sdiff hSsub
    have h2 : J.card = 8 := J_card
    omega
  have hTne : ∀ v ∈ T, c v ≠ c 1 := by
    intro v hv hvc
    have hvJ : v ∈ J := hTsubJ hv
    have hvnS : v ∉ S := (Finset.mem_sdiff.mp hv).2
    exact hvnS (Finset.mem_filter.mpr ⟨hvJ, hvc⟩)
  obtain ⟨T', hT'T, hT'card⟩ := Finset.exists_subset_card_eq hTcard
  have hT'J : T' ⊆ J := hT'T.trans hTsubJ
  have hT'pow : T' ∈ J.powersetCard 5 := Finset.mem_powersetCard.mpr ⟨hT'J, hT'card⟩
  obtain ⟨f, hf, hfT'⟩ := hitting5 T' hT'pow
  have hfE : f ∈ E := H0_subset_E hf
  have hfmono : IsMono c f := by
    intro x hx y hy
    have hxn : c x ≠ c 1 := hTne x (hT'T (hfT' hx))
    have hyn : c y ≠ c 1 := hTne y (hT'T (hfT' hy))
    have hx1 : c x = !(c 1) := by revert hxn; cases c x <;> cases c 1 <;> simp
    have hy1 : c y = !(c 1) := by revert hyn; cases c y <;> cases c 1 <;> simp
    rw [hx1, hy1]
  exact hc f hfE hfmono

/-! ## `H` is 3-colourable, and is critical for 3-colourability -/

theorem three_colorable : ∃ c : Fin 10 → Fin 3, ∀ e ∈ E, ¬ IsMono c e :=
  ⟨psi, not_forall_mem_of_filter_card_eq_zero E (fun e => IsMono psi e) (by decide)⟩

/-- Deleting any edge makes `H` 2-colourable. -/
theorem edge_critical :
    ∀ e ∈ E, ∃ c : Fin 10 → Bool, ∀ f ∈ E, f ≠ e → ¬ IsMono c f := by
  intro e he
  refine ⟨fun u => decide (u ∈ eblue e), ?_⟩
  have hcard :
      (E.filter (fun f => decide (f ≠ e ∧ (f ⊆ eblue e ∨ f ∩ eblue e = ∅)) = true)).card = 0 :=
    forall_mem_of_filter_card_eq E
      (fun e => (E.filter (fun f => decide (f ≠ e ∧ (f ⊆ eblue e ∨ f ∩ eblue e = ∅)) = true)).card = 0)
      (by decide) e he
  have hz := not_forall_mem_of_filter_card_eq_zero E
    (fun f => f ≠ e ∧ (f ⊆ eblue e ∨ f ∩ eblue e = ∅)) hcard
  intro f hf hne hmono
  exact (hz f hf ⟨hne, (isMono_decide_iff (eblue e) f).mp hmono⟩)

/-- Deleting any vertex makes `H` 2-colourable. -/
theorem vertex_critical :
    ∀ v ∈ V, ∃ c : Fin 10 → Bool, ∀ f ∈ E, v ∉ f → ¬ IsMono c f := by
  intro v hv
  refine ⟨fun u => decide (u ∈ vblue v), ?_⟩
  have hcard :
      (E.filter (fun f => decide (v ∉ f ∧ (f ⊆ vblue v ∨ f ∩ vblue v = ∅)) = true)).card = 0 :=
    forall_mem_of_filter_card_eq V
      (fun v => (E.filter (fun f => decide (v ∉ f ∧ (f ⊆ vblue v ∨ f ∩ vblue v = ∅)) = true)).card = 0)
      (by decide) v hv
  have hz := not_forall_mem_of_filter_card_eq_zero E
    (fun f => v ∉ f ∧ (f ⊆ vblue v ∨ f ∩ vblue v = ∅)) hcard
  intro f hf hvf hmono
  exact hz f hf ⟨hvf, (isMono_decide_iff (vblue v) f).mp hmono⟩

/-! ## Main theorem -/

/-- **JSP-000690.** There exists a 3-uniform, 3-chromatic-critical hypergraph with
minimum degree at least `7`. -/
theorem JSP000690 :
    ∃ (W : Finset (Fin 10)) (F : Finset (Finset (Fin 10))),
      W.card = 9 ∧ F.card = 22 ∧
      (∀ e ∈ F, e.card = 3) ∧
      (∀ e ∈ F, e ⊆ W) ∧
      (∀ v ∈ W, 7 ≤ (F.filter (fun e => v ∈ e)).card) ∧
      (¬ ∃ c : Fin 10 → Bool, ∀ e ∈ F, ¬ IsMono c e) ∧
      (∃ c : Fin 10 → Fin 3, ∀ e ∈ F, ¬ IsMono c e) ∧
      (∀ e ∈ F, ∃ c : Fin 10 → Bool, ∀ f ∈ F, f ≠ e → ¬ IsMono c f) ∧
      (∀ v ∈ W, ∃ c : Fin 10 → Bool, ∀ f ∈ F, v ∉ f → ¬ IsMono c f) :=
  ⟨V, E, V_card, E_card, uniform, edge_subset_V, min_degree, not_two_colorable,
    three_colorable, edge_critical, vertex_critical⟩

#print axioms JSP000690

end JSP690
