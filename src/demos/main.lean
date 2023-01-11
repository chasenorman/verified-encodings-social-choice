import cnf.literal
import cnf.assignment
import cnf.cnf
import cnf.encoding

import cardinality.direct_amo
import cardinality.sinz_amo
import cardinality.distinct
import cardinality.alk
import cardinality.amk

import data.nat.basic
import data.list.basic
import data.list.range

open nat
open list
open function
open literal
open encoding
open clause cnf
open assignment
open alk amk distinct
open direct_amo
open sinz_amo



structure graph := (V : Type) (f : fintype V) (i : inhabited V) (d : decidable_eq V) (w : V → V → ℤ) --(a : anti_symmetric w)


instance i {g : graph} : fintype g.V := g.f

/-instance v_decidable_eq {g : graph} : decidable_eq g.V := g.d
instance w_decidable_eq {g : graph} : decidable_eq (g.V → g.V → ℤ) := by apply_instance
--instance g_decidable_eq : decidable_eq graph := by tactic.mk_dec_eq_instance
instance g_decidable_eq : decidable_eq graph := 
begin 
  intros a b,
  cases a,
  cases b,
  simp,
  exact and.decidable,
end-/



structure pointed_graph := (g : graph) (v : g.V)




instance pointed_graph_inhabited : inhabited pointed_graph := inhabited.mk ⟨⟨bool, bool.fintype, inhabited.mk ff, bool.decidable_eq, λ x y, 0⟩, ff⟩

structure graph_embedding := (g₁ : graph) (g₂ : graph) (f : g₁.V → g₂.V) (x : g₂.V) (p : set.univ \ (set.range f) = {x})

def simple {V : Type} (a b : V) : bool → V
| ff := a
| tt := b

def special1 (e : graph_embedding) (v : e.g₁.V) : graph := 
  ⟨bool, bool.fintype, inhabited.mk ff, bool.decidable_eq, 
    (ite (e.g₂.w (e.f v) e.x > 0) 
      (λ a b, e.g₂.w (simple (e.f v) e.x a) (simple (e.f v) e.x b))
      (λ a b, e.g₂.w (simple (e.f v) e.x b) (simple (e.f v) e.x a)))⟩

def special2 (e : graph_embedding) (v : e.g₁.V) : bool := 
  (ite (e.g₂.w (e.f v) e.x > 0) ff tt)

def encoding (D : list graph) (E : list graph_embedding) : cnf pointed_graph := 
  -- at least one literal selected for each graph
  (D.map (λ g: graph, ((fintype.elems (g.V)).to_list.map (λ v, Pos ⟨g, v⟩)))) ++ 
  -- at most one literal selected for each graph
  join (D.map (λ g: graph, direct_amo ((fintype.elems (g.V)).to_list.map (λ v, Pos ⟨g, v⟩)))) ++
  -- binary gamma for each embedding
  join (E.map (λ e, ((fintype.elems e.g₁.V).to_list.map (λ v, [Neg ⟨special1 e v, special2 e v⟩, Neg ⟨e.g₁, v⟩, Pos ⟨e.g₂, e.f v⟩])) ))

--#eval encoding nil nil

def binary_gamma (E : list graph_embedding) (f : Π g : graph, g.V) := ∀ e : graph_embedding, e ∈ E → (f (special1 e (f e.g₁))) = (special2 e (f e.g₁)) → (f e.g₂ = e.f (f e.g₁))

lemma lemma1 {n : ℕ} (a : ¬ n = 1) (b : ¬ n ≥ 2) : n = 0 := by omega

theorem encodes_binary_gamma : ∀ D E f, binary_gamma E f → (((encoding D E).eval (λ ⟨g, v⟩, f g = v)) = tt) := 
begin
  intros D E f bg,
  rw eval_tt_iff_forall_clause_eval_tt,
  intros cl hcl,
  simp [encoding] at hcl,
  rcases hcl with (⟨g, gd, h⟩ | ⟨g, gd, hcl⟩ | ⟨e, ee, v, p, h⟩),
  {
    subst h,
    simp [eval_tt_iff_exists_literal_eval_tt],
    use f g,
    use i.complete (f g),
    simp [literal.eval],
  },
  {
    by_cases (length ((fintype.elems (g.V)).to_list.map (λ v, Pos (pointed_graph.mk g v)))) ≥ 2,
    {
      rcases exists_double_flip_eq_of_mem h hcl with ⟨lit₁, lit₂, rfl⟩,
      rcases distinct_iff_mem.mpr hcl with ⟨i, j, hi, hj, hij, rfl, rfl⟩,
      rw eval_tt_iff_exists_literal_eval_tt,
      simp [eval_flip, literal.flip],
      by_contradiction,
      simp [literal.eval] at h,
      cases h with h1 h2,
      rw h2 at h1,
      let test := (fintype.elems g.V).nodup_to_list,
      unfold nodup at test,
      rw list.pairwise_iff_nth_le at test,
      rw list.length_map at hj,
      rw list.length_map at hi,
      specialize test i j hj hij,
      change ((fintype.elems g.V).to_list.nth_le i hi ≠ (fintype.elems g.V).to_list.nth_le j hj) at test,
      change ((fintype.elems g.V).to_list.nth_le j hj = (fintype.elems g.V).to_list.nth_le i hi) at h1,
      exact test (eq.symm h1),
    },
    let h2 := h,
    by_cases (length ((fintype.elems (g.V)).to_list.map (λ v, Pos (pointed_graph.mk g v)))) = 1,
    {
      rw list.length_eq_one at h,
      cases h with a h,
      rw h at hcl,
      rw direct_amo_singleton at hcl,
      exfalso,
      exact list.not_mem_nil cl hcl,
    },
    let h3 := lemma1 h h2,
    {
      rw list.length_eq_zero at h3,
      rw h3 at hcl,
      rw direct_amo_nil at hcl,
      exfalso,
      exact list.not_mem_nil cl hcl,
    },
  },
  {
    subst h,
    simp [eval_tt_iff_exists_literal_eval_tt],
    simp [literal.eval],
    
    apply not_or_of_imp,
    intro sp,
    apply not_or_of_imp,
    intro veq,

    unfold binary_gamma at bg,
    specialize bg e ee,
    rw <-veq at sp,
    specialize bg sp,
    rw <-veq,
    exact bg,
  }
end