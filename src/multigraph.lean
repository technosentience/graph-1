import data.rel
import data.set.finite
import data.sym.sym2
import set_theory.cardinal.finite
import algebra.big_operators.finprod

open_locale classical big_operators

noncomputable theory

open finset
universes u v w

variables {V : Type u} {E : Type v}

structure graph (V : Type u) (E : Type v) :=
(ends : E → sym2 V)

namespace graph

section basic

variables {G : graph V E} {u v : V} {e f : E}

def adj (G : graph V E) : V → V → Prop :=
  λ v w, ∃ (e : E), G.ends e = ⟦(v, w)⟧

def inc (G : graph V E) : V → E → Prop :=
  λ v e, v ∈ G.ends e

/-- Set of edges incident to a given vertex, aka incidence set. -/
def incidence_set (G : graph V E) (v : V) : set E := {e : E | v ∈ G.ends e}

/-- Make a graph from the digraph -/
def graph.mk {V : Type u} {E : Type v} (ends : E → sym2 V) : graph V E := { ends := ends }

@[symm] lemma adj_symm (h : G.adj u v) : G.adj v u :=
begin
  dunfold adj at *,
  rwa [sym2.eq_swap],
end

/-!
A dart is an edge with a chosen orientation - graphs are naturally unoriented,
but in order to talk about things like walks, the handshaking lemma, etc you have to
pick a "direction" to traverse the edges.
-/
structure dart (G : graph V E) : Type (max u v) :=
(head : V)
(tail : V)
(e : E)
(h : G.ends e = ⟦(head, tail)⟧)

/-!
Flipping a dart around
-/
def reverse_dart (G : graph V E) (d : G.dart) : G.dart :=
{ head := d.tail,
  tail := d.head,
  e := d.e,
  h := by {
    rw [sym2.eq_swap],
    exact d.h,
  } }

@[simp]
lemma reverse_head_tail (G : graph V E) (d : G.dart) : (G.reverse_dart d).tail = d.head :=
begin
  refl,
end

@[simp]
lemma reverse_tail_head (G : graph V E) (d : G.dart) : (G.reverse_dart d).head = d.tail :=
begin
  refl,
end

end basic

section walks

variables (G : graph V E)
/-!
We have a very clever definition of walks here that one of my colleagues at Waterloo
came up with. One of the issues we had when talk about walks was, when we'd try to talk
about them in an inductive way, we'd end up missing the start or end vertex. This definition
includes both in a neat way.
-/
structure walk (G : graph V E) : Type (max u v) :=
(head : V)
(tail : V)
(darts : list G.dart)
(is_walk :
  [head] ++ (list.map dart.tail darts)
  = (list.map dart.head darts) ++ [tail])

lemma walk_rev_head (p : walk G) :
  list.map dart.head (list.map G.reverse_dart p.darts) =
    (list.map dart.tail p.darts) :=
begin
  finish,
end

lemma walk_rev_tail (p : walk G) :
  list.map dart.tail (list.map G.reverse_dart p.darts) =
    (list.map dart.head p.darts) :=
begin
  finish,
end

/-!
Having seen how to write some definitions, try writing the definition of
the empty walk! Hint: By our definition, we do need a start and end vertex, so
we have to use arbitrary vertex v.
-/
def empty_walk (v : V) : walk G :=
{ head := v,
  tail := v,
  darts := [],
  is_walk := rfl }

/-!
The reverse of a walk p.
-/
def reverse (p : walk G) : walk G :=
{ head := p.tail,
  tail := p.head,
  darts := (list.map G.reverse_dart p.darts.reverse),
  -- including the above because you probably haven't seen lists in lean yet (?)
  is_walk :=
    begin
      rcases p with ⟨head, tail, darts, is_walk⟩,
      simp only [list.map_reverse, list.map_map, list.singleton_append],
      change [tail].reverse ++ (list.map dart.head darts).reverse =
        (list.map dart.tail darts).reverse ++ [head].reverse,
      rw [←list.reverse_append, ←list.reverse_append, list.reverse_inj],
      tauto,
    end }

/-!
Appending two walks p and q, where the tail of p is the head of q.
-/
def append (p q : walk G) (h : p.tail = q.head) : walk G :=
{ head := p.head,
  tail := q.tail,
  darts := p.darts ++ q.darts,
  is_walk :=
    begin
      rw [list.map_append, list.map_append, list.append_assoc, ←list.append_assoc,
          p.is_walk, ←q.is_walk, h, list.append_assoc],
    end }

/-!
We have reachable as a definition here so that we can start talking about connectivity.
You'll find that the previous definitions of various walks are useful in showing that
reachability is an equivalence relation:
-/
def reachable (u v : V) : Prop := ∃ (p : G.walk), p.head = u ∧ p.tail = v

namespace walk

/-!
Reachability is reflexive, i.e. a vertex can reach itself
-/
@[refl] protected lemma reachable.refl (u : V) : G.reachable u u :=
begin
  use empty_walk G u,
  tauto,
end
protected lemma reachable.rfl {u : V} : G.reachable u u := reachable.refl _ _

/-!
If you have a walk from u to v, you have a walk from v to u
-/
@[symm] protected lemma reachable.symm {u v : V} (huv : G.reachable u v) : G.reachable v u :=
begin
  rcases huv with ⟨w, h₁, h₂⟩,
  use reverse G w,
  tauto,
end

/-!
If you have a walk from u to v and a walk from v to w, then you have a walk from
u to w
-/
@[trans] protected lemma reachable.trans {u v w : V} (huv : G.reachable u v) (hvw : G.reachable v w)
  : G.reachable u w :=
begin
  rcases huv with ⟨w₁, h₁, h₂⟩,
  rcases hvw with ⟨w₂, h₃, h₄⟩,
  use append G w₁ w₂ (by finish),
  tauto,
end

def edges {G : graph V E} (p : G.walk) : list E := list.map dart.e p.darts

def support {G : graph V E} (p : G.walk) : list V := [p.head] ++ list.map dart.head p.darts

/-! ### Trails, paths, circuits, cycles -/

/-- A *trail* is a walk with no repeating edges. -/
structure is_trail {G : graph V E} (p : G.walk) : Prop :=
(edges_nodup : p.edges.nodup)

/-- A *path* is a walk with no repeating vertices. -/
structure is_path {G : graph V E} (p : G.walk) : Prop :=
(support_nodup : p.support.nodup)

/-- A *circuit* is a nonempty trail beginning and ending at the same vertex. -/
-- extends path & need to get rid of loops
structure is_circuit {G : graph V E} (p : G.walk) : Prop :=
(start_end : p.head = p.tail)
(ne_nil : p.darts ≠ [])

/-- A *cycle* at `u : V` is a circuit at `u` whose only repeating vertex
is `u` (which appears exactly twice). -/
structure is_cycle {G : graph V E} (p : G.walk) : Prop :=
(support_nodup : p.support.tail.nodup)

end walk

end walks

section conn

def connected (G : graph V E) : Prop := ∀ u v : V, G.reachable u v

def is_loop_edge_of (G : graph V E) (v : V) (e : E) : Prop := G.ends e = sym2.diag v

def is_loop_edge (G : graph V E) (e : E) : Prop := sym2.is_diag (G.ends e)

def degree (G : graph V E) (v : V) : ℕ := nat.card (G.incidence_set v)
  + nat.card {e | G.is_loop_edge_of v e}
-- double count loop edges

/-!
This is a harder problem so don't sweat it - honestly I haven't even proven this
version of the handshaking lemma yet! We do have the handshaking lemma in lean,
it just has a different appearance due to different definitions.
-/

def degree' (V : Type u) (E' : sym2 V → Type v) (v : V) : ℕ
  := nat.card (Σ v', E' ⟦(v, v')⟧) + nat.card (E' ⟦(v, v)⟧)



def aux₁ (G : E → sym2 V) (v : V) : 
  {x // v ∈ G x} ≃ (Σ (v' : V), {e // G e = ⟦(v, v')⟧}) :=
  {
    to_fun := (λ e, begin
      rcases e with ⟨e, h⟩,
      let v' := sym2.mem.other h,
      refine ⟨v', ⟨e, _⟩⟩,
      simp only [sym2.other_spec],
    end),
    inv_fun := (λ e, begin
      rcases e with ⟨v', e, h⟩,
      use e,
      simp only [h, sym2.mem_iff, eq_self_iff_true, true_or],
    end),
    left_inv := by {
      rintro ⟨e, h⟩,
      simp only,
    },
    right_inv := by {
      rintro ⟨v', e, h⟩,
      sorry, 
      
    }
  }



def degree_agree (G : graph V E) (v : V) :
  G.degree v = degree' V (λ p, { e : E // G.ends e = p }) v :=
begin
  cases G,
  simp [degree, degree', incidence_set, is_loop_edge_of],
  sorry,
end

-- lemma handshake' {m n} (G : graph (fin m) (fin n)) :
--   ∑ᶠ (x : fin m), degree' (fin n) x = 2 * n :=
-- begin
--   sorry,
-- end

lemma finsum_zero {X} [add_comm_monoid X] (f : fin 0 → X) :
  ∑ (v : fin 0), f v = 0 := rfl


lemma finset_step_aux {n} : (fintype.elems (fin (n + 1))).val = (fintype.elems (fin n)).val.map
  fin.cast_succ + {fin.last n} :=
begin
  rw [multiset.nodup.ext],
  intros v,
  change v ∈ (fintype.elems (fin (n + 1))) ↔ _,
  simp [fintype.complete],
  cases lt_or_eq_of_le v.le_last,
  cases n, simp at *,
  use v.cast_pred,
  change v.cast_pred ∈ (fintype.elems (fin n.succ)) ∧ _,
  simp [fintype.complete],
  exact fin.cast_succ_cast_pred h,
  cc,
  refine (fintype.elems _).nodup,
  rw [multiset.nodup.add_iff],
  simp, intros x h h',
  have h'' := fin.cast_succ_lt_last x,
  rw h' at h'', simp at *, assumption,
  apply multiset.nodup.map,
  exact rel_embedding.injective fin.cast_succ,
  refine (fintype.elems _).nodup,
  simp,
end

lemma finsum_step {X n} [add_comm_monoid X] (f : fin (n + 1) → X) :
  ∑ (v : fin (n + 1)), f v = (∑ (v : fin n), f (v.cast_succ)) + f (fin.last n) :=
begin
  simp only,
  change univ.sum f = univ.sum (f ∘ fin.cast_succ) + f (fin.last n),
  dsimp [finset.sum],
  nth_rewrite 1 [←multiset.map_map],
  have h₁ : f (fin.last n) = (multiset.map f {fin.last n}).sum := by simp,
  simp_rw [h₁], clear h₁,
  simp_rw [←multiset.sum_add],
  congr,
  simp_rw [←multiset.map_add],
  congr,
  apply finset_step_aux,
end

def sym2_eqv {n} : { p : fin n × fin n // p.1 ≤ p.2 } ≃ sym2 (fin n) :=
  {
    to_fun := λ p, ⟦p⟧,
    inv_fun := λ p, begin
      refine quot.lift _ _ p,
      rintro ⟨v₁, v₂⟩,
      by_cases h : v₁ ≤ v₂,
      exact ⟨(v₁, v₂), h⟩,
      exact ⟨(v₂, v₁), le_of_lt (lt_of_not_le h)⟩,
      rintros p₁ p₂ h,
      cases h, refl,
      cases (lt_trichotomy h_x h_y) with h₁ h₁,
      have h₂ := le_of_lt h₁,
      simp [h₁, h₂],
      cases h₁ with h₁,
      subst h₁,
      have h₂ := le_of_lt h₁,
      simp [h₁, h₂],
    end,
    left_inv := begin
      intro p,
      unfold quotient.mk,
      have h : (p : fin n × fin n) = p.val := rfl,
      rw [h], clear h,
      rcases p with ⟨⟨v₁, v₂⟩, h₁⟩,
      simp [h₁],
    end,
    right_inv := begin
      intro p,
      refine quot.ind _ p, clear p,
      rintro ⟨v₁, v₂⟩,
      by_cases h₁ : v₁ ≤ v₂,
      simp [h₁], refl,
      simp [h₁], change ⟦(v₂, v₁)⟧ = ⟦(v₁, v₂)⟧,
      simp only [quotient.eq, sym2.rel_iff, eq_self_iff_true, and_self, or_true],
    end
  }

def emb_sym2 {n} : { p : fin n × fin n // p.1 ≤ p.2 } ↪ sym2 (fin n) :=
  ⟨(λ p, ⟦p⟧), begin
    rintros ⟨⟨v₁, v₂⟩, h₁⟩ ⟨⟨v₃, v₄⟩, h₂⟩,
    simp only [subtype.coe_mk, quotient.eq, sym2.rel_iff, prod.mk.inj_iff],
    simp only at h₁ h₂,
    intro h₃,
    cases h₃,
    assumption,
    rcases h₃ with ⟨h₃, h₄⟩,
    subst h₃, subst h₄,
    have h₃ : v₁ = v₂ := ge_antisymm h₂ h₁,
    tauto,
  end⟩


lemma sym2_elems {n} : fintype.elems (sym2 (fin n)) = 
  (fintype.elems ({ p : fin n × fin n // p.1 ≤ p.2 })).map emb_sym2 :=
begin
  ext p,
  simp [fintype.complete],
  have h : ∃ (v v' : fin n), p = ⟦(v, v')⟧ := sym2.exists.mp ⟨p, rfl⟩,
  rcases h with ⟨v, v', h⟩,
  by_cases h' : v ≤ v',
  use v, use v', tauto,
  use v', use v, have h'' : v' ≤ v := le_of_not_ge h',
  split, rw h, change ⟦(v', v)⟧ = ⟦(v, v')⟧,
  simp only [quotient.eq, sym2.rel_iff, eq_self_iff_true, and_self, or_true],
  assumption,
end

lemma finsum_sym2 {X n} [add_comm_monoid X] (f : sym2 (fin n) → X)
  : ∑ (p : sym2 (fin n)), f p = ∑ (p : { p : fin n × fin n // p.1 ≤ p.2 }), f ⟦p⟧ :=
begin
  change (fintype.elems _).sum f = (fintype.elems _).sum (f ∘ emb_sym2),
  rw sym2_elems,
  simp only [sum_map],
end

lemma finsum_aux₁ {X n} [add_comm_monoid X] (f : fin n × fin n → X)
  : ∑ (p : { p : fin n × fin n // p.1 ≤ p.2 }), f p =
    ∑ (v : fin n), ∑ (v' : fin n), ite (v ≤ v') (f (v, v')) 0 :=
begin
  dsimp [finset.sum],
  have h' : ∀ v v', ite (v ≤ v') (f (v, v')) 0 = multiset.sum (multiset.map f (multiset.map (λ v', (v, v')) (ite (v ≤ v') {v'} {}))) := by {
    intros v v',
    by_cases h : v ≤ v',
    simp [h], simp [h],
  },
  simp_rw [h'], clear h',
  simp_rw [←multiset.sum_bind],
  congr,
  nth_rewrite 0 [←multiset.map_map],
  simp_rw [←multiset.map_bind],
  congr, clear f,
  have h' : ∀ (v v' : fin n), ite (v ≤ v') {v'} {} = multiset.filter (λ v', v ≤ v') {v'} := by {
    intros v v',
    simp_rw [←multiset.filter_singleton],
  },
  simp_rw [h'], clear h',
  simp_rw [multiset.map_bind],
  ext p,
  rcases p with ⟨v₁, v₂⟩,

  simp_rw [multiset.count_bind],
  simp_rw [multiset.count_map],
  simp_rw [multiset.filter_filter],
  simp_rw [←multiset.countp_eq_card_filter],

  by_cases h : v₁ ≤ v₂,
  let p : { p : fin n × fin n // p.1 ≤ p.2 } := ⟨⟨v₁, v₂⟩, h⟩,
  have h₁ : ∀ p', p = p' ↔ (v₁, v₂) = ↑p' := by simp,
  simp_rw [←h₁], clear h₁,
  have h₃ : ∀ x, (λ a, (v₁, v₂) = (x, a) ∧ x ≤ a) = ite (x = v₁) (λ a, v₂ = a) (λ _, false) := by {
    intro x, ext a,
    split,
    rintro ⟨h₃, h₄⟩,
    cases h₃, simp,
    by_cases h₃ : x = v₁,
    simp [h₃, h], cc,
    simp [h₃],
  },
  simp_rw [h₃], clear h₃,
  have h₄ : ∀ v v', multiset.countp (ite (v = v₁) (eq v₂) (λ (_ : fin n), false)) {v'}
    = ite (v = v₁) (multiset.countp (eq v₂) {v'}) 0 :=
  begin
    intros v v',
    by_cases h₄ : v = v₁,
    simp [h₄],
    simp [h₄],
  end,
  simp_rw [h₄], clear h₄,
  change multiset.count p univ.val = _,
  simp,

  have h₁ : ∀ x, (multiset.map (λ (x_1 : fin n), ite (x = v₁) (multiset.countp (eq v₂) {x_1}) 0) univ.val).sum
    = ite (x = v₁) 1 0 :=
  begin
    intro x,
    split_ifs with h₂,
    change (multiset.map (λ (x_1 : fin n), multiset.count v₂ (x_1 ::ₘ {})) univ.val).sum = 1,
    simp_rw [←multiset.count_bind],
    simp, simp,
  end,

  simp_rw [h₁], clear h₁,
  have h₁ : ∀ x, (x = v₁) = (v₁ = x) := by { intro, ext, cc},
  simp_rw [h₁], clear h₁,
  simp_rw [←multiset.count_singleton],
  simp_rw [←multiset.count_bind],
  simp,

  have h₁ : ∀ (a : {p : fin n × fin n // p.fst ≤ p.snd}), (v₁, v₂) = a ↔ false := by {
    intro p, cases p, simp, intro h', cc,
  },

  simp_rw [h₁], clear h₁,
  simp,

  have h₁ : ∀ (x a : fin n), ((v₁ = x ∧ v₂ = a) ∧ x ≤ a) ↔ false := by {
    intros x a,
    simp, intros h₁ h₂,
    rw [←h₁, ←h₂], exact not_le.mp h,
  },

  simp_rw [h₁], clear h₁,
  simp,
end

lemma finsum_aux₂ {X n} [add_comm_monoid X] (f : fin n × fin n → X) (hf : ∀ x x', f (x, x') = f (x', x))
  : 2 • ∑ (v : fin n), ∑ (v' : fin n), ite (v ≤ v') (f (v, v')) 0
  = ∑ (v : fin n), ((∑ (v' : fin n), f (v, v')) + f (v, v)) :=
begin
  induction n,
  simp [finsum_zero],
  simp_rw [finsum_step],
  simp,
  specialize n_ih (λ p, f (p.1.cast_succ, p.2.cast_succ)) (by simp [hf]),
  simp at n_ih,
  simp_rw [finset.sum_add_distrib, smul_add],
  simp_rw [n_ih], clear n_ih,
  simp_rw [finset.sum_add_distrib],
  simp_rw [add_assoc],
  congr' 1, abel,
  congr' 1,
  nth_rewrite 0 [add_comm],
  nth_rewrite 0 [←add_assoc],
  congr' 1,
  have h₁ : ∀ (x : fin n_n), x.cast_succ ≤ fin.last n_n := by {
    intro,
    exact (fin.cast_succ x).le_last,
  },
  have h₂ : ∀ (x : fin n_n), ¬(fin.last n_n ≤ x.cast_succ) := by {
    intro,
    simp,
    apply fin.cast_succ_lt_last,
  },
  simp_rw [h₁, h₂],
  simp [hf],
  abel,
end

lemma finsum_aux₃ {X n} [add_comm_monoid X] (f : sym2 (fin n) → X)
 : ∑ (v : fin n), ((∑ (v' : fin n), f ⟦(v, v')⟧) + f ⟦(v, v)⟧) = 
  2 • ∑ (p : sym2 (fin n)), f p :=
begin
  let f' := λ p, f ⟦p⟧,
  have hf : ∀ x x', f' (x, x') = f' (x', x) := by {
    intros x x',
    change f ⟦(x, x')⟧ = f ⟦(x', x)⟧,
    rw [sym2.eq_swap],
  },
  rw [finsum_sym2],
  change _ = 2 • ∑ (p : {p : fin n × fin n // p.fst ≤ p.snd}), f' p,
  rw [finsum_aux₁],
  rwa [finsum_aux₂],
end

lemma handshake' (V : Type u) (E : sym2 V → Type v) [fintype V]
  [∀ p, fintype (E p)] : ∑ᶠ (x : V), degree' V E x =
  ∑ᶠ (p : sym2 V), nat.card (E p) :=
begin

end

theorem handshake (G : graph V E) [fin_V : fintype V] [fin_E : fintype E] :
  ∑ (x : V), G.degree x = 2 * (fintype.card E) :=
begin
  sorry,
end
