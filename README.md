# ConVerG — Rocq formalization of condensed SPARQL evaluation

Formalization, in Rocq 9.0 (Rocq Platform 2025.08), of Chapters 5–6 of the
thesis *Querying of Multi-Version RDF Knowledge Graphs through Condensed
Representations*: the flat and condensed models, the flat and condensed
SPARQL algebras (quad patterns with constant or variable graph position,
join, filter, union, difference, optional, bind, projection, grouping with
aggregation, enumeration of the versioned named graphs), the four variable
representations ν, ι, ζ, ψ, the translation τ with representation
promotion Υ, the evaluation equivalence theorem (Theorem 6.2) with its
corollaries, and the type system of Section 5.4 with the optimal
representation function R\* (Theorem 5.1 and its minimality).
`SPEC-extensions.md` details the four extensions added after the first
version and the corrections to the thesis they required.

Every result is fully proved: there is no `Admitted`. The only assumptions
are the modeling parameters listed below.

## Build

```
rocq makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile
```

## Files (in dependency order)

| File | Content | Thesis |
|------|---------|--------|
| `RDF.v` | terms, quads, variables | Ch. 3 |
| `ListUtil.v` | list lemmas (`filter_map`, `flat_map`, `Permutation`, `NoDup`) | — |
| `Versioning.v` | versions, versioned IRIs `VI(v, g)` (injective, `VI ⊂ I`), versioned quads, version sets, graph catalogs (the value of the marker `•`) | Def. 3.1, 5.1, 5.21 |
| `Models.v` | flat model, condensed model, condensation `C`, flattening `F`, `C∘F = id`, `F∘C = id`, bag form of model correspondence, named graphs of an archive (`flat_graphs`, `graph_catalog`) | Def. 5.4–5.6, Thm 6.1 |
| `Representations.v` | dictionary encoding (bijection), representations `ψ ≤ ζ ≤ ι ≤ ν`, meet/join | Def. 5.3, 5.18 |
| `Environments.v` | environments `Γ`, raising | Def. 5.19 |
| `SolutionMappings.v` | bindings in ν, ι, ζ and ψ (`BAll`, the marker `•` with its catalog), flat/condensed mappings, expansion `Ξ`, cardinality, compatibility and merge in both algebras (including `ζ ⋈ ψ`, `ψ ⋈ ψ`), Lemmas 6.3 (value preservation), 6.4 (compatibility preservation, both directions: `compat_flat_expand_cond`, `compat_cond_expand_flat`), 6.6 (join cardinality, as a `Permutation`: `expand_merge_perm`), 6.7 (multiplicative cardinality: `expand_length`, factor of ψ: `vals_BAll_length`) | Def. 5.7, 5.8, 5.20–5.26, 5.39 |
| `Expressions.v` | SPARQL expressions (constants, variables, `BOUND`, equality, functions), evaluation over a partial lookup, conditions, representation requirements of an expression (`expr_reqs_at`) | §5.2, Def. 5.43 |
| `Aggregation.v` | grouping, aggregate functions as functions of a bag, flat evaluation and count-views condensed evaluation of `GROUP BY` with aggregates, `groupagg_perm` (Group / Aggregation / AggregateJoin cases of Thm 6.2), `count_values_c` (`COUNT_C = Σ card(m)`) | Def. 5.37–5.39 |
| `Promotion.v` | promotion `Υ` per binding / variable / mapping (`ψ ⇝ ζ ⇝ ι ⇝ ν`); Lemmas 6.1 and 6.2 (expansion preserved) | Def. 5.32–5.36 |
| `Difference.v` | product-set difference as disjoint slices (Lemma 5.1), residual over several blockers, condensed `DIFF` and its equivalence with the flat `DIFF` | Def. 5.29, 5.30 |
| `Typing.v` | environments as invariants (`env_ok`), pointwise meet, requirements `needs_reqs` / `env_meets` | Def. 5.44, §5.5 |
| `FlatAlgebra.v`, `CondensedAlgebra.v` | syntax of both algebras (`TransformReprC` is `Υ`, `GroupAggF/C` is `AggJ ∘ Agg ∘ Gr`, `GraphsF/C` is `GRAPH ?x { }`) | Def. 5.9–5.17, 5.24–5.38 |
| `FlatEvaluation.v`, `CondensedEvaluation.v` | evaluation `⟦e⟧_F(d_F)` and `⟦e⟧_C(d_C)` | §5.2, §5.3 |
| `Translation.v` | translation `τ` with result environment `R(e)` | Def. 5.47 |
| `TypeSystem.v` | typing judgement `typed E_C Γ` of condensed expressions, erasure of promotions, `translate_typed` (τ produces well-typed expressions) | Def. 5.44 |
| `Equivalence.v` | per-operator lemmas, `typed_correct` (type soundness + equivalence for every well-typed condensed expression), **`evaluation_equivalence`** (Thm 6.2 for τ), `count_preservation`, `multiplicity_preservation` | Thm 6.2 |
| `Optimality.v` | the checking judgement `Γ ⊢ e` of the thesis (`expr_ty`, `tc`), its constraints, the lower environment `env_glb`, Lemmas 5.2 (`expr_ty_glb`) and 5.3 (`tc_glb`), the computable `rstar`, Theorem 5.1 (`rstar_well_typed`), minimality (`rstar_least`, `rstar_glb`), the environment rule of JOIN (`rstar_join`), lazy promotion of τ (`translate_lazy`) | Def. 5.43–5.46, Lem. 5.2–5.3, Thm 5.1 |

## Main statements

For every well-typed condensed expression `E_C` (judgement `typed E_C Γ`,
Definition 5.38), with `erase E_C` the flat expression obtained by forgetting
the promotions `Υ`:

```coq
Theorem typed_evaluation_equivalence : forall ec env dF dC,
  typed ec env -> wf_condensed_model dC ->
  NoDup dF -> models_correspond dF dC ->
  Permutation (eval_flat (erase ec) dF) (flat_map expand (eval_cond ec dC)).

Theorem type_soundness : forall ec env dC,
  typed ec env -> wf_condensed_model dC ->
  Forall (fun m => wf_cmap m /\ env_ok env m) (eval_cond ec dC).
```

For the translation `τ` (`translate_typed` shows that `τ(e)` is well-typed
and erases to `e`):

```coq
Theorem evaluation_equivalence : forall e dF dC,
  wf_flat_expr e -> wf_condensed_model dC ->
  NoDup dF -> models_correspond dF dC ->
  Permutation (eval_flat e dF)
              (flat_map expand (eval_cond (translate_expr e) dC)).
```

Bag semantics: solution sequences are lists and `≅` is `Permutation`.
`expand` is `Ξ`. `wf_flat_expr` is the thesis's unique-naming assumption
(no repeated variable in a quad pattern, fresh variable in `BIND`,
pairwise distinct grouping and aggregate variables);
`wf_condensed_model` says that the condensed model is a function with
non-empty, duplicate-free version sets. The typing judgement carries the
same conditions and requires, for the expressions of `FILTER`, `BIND`,
`DIFF`, `OPTIONAL` and of the aggregates, the representations of
Definition 5.43 (`env_meets`: ν under a function, ι under an equality,
ι at the top of a `BIND`), ι for the grouping variables and for the
variables dropped by `PROJECTION`.

For the optimal representation function (Section 5.4), with `tc Γ e` the
checking judgement `Γ ⊢ e` of Definition 5.44 and `rstar e` the pointwise
least upper bound of the constraints of `e`:

```coq
Theorem rstar_well_typed : forall e, tc (rstar e) e.                    (* Thm 5.1 *)
Theorem rstar_least : forall e env, tc env e -> rstar e <=_env env.
Theorem rstar_glb : forall e env0, tc env0 e ->
  (forall env, tc env e -> env0 <=_env env) -> env_equiv env0 (rstar e).  (* Def. 5.46 *)
Theorem rstar_join : forall e1 e2,
  env_equiv (rstar (JoinF e1 e2)) (env_join (rstar e1) (rstar e2)).
Theorem translate_lazy : forall e, lazy (translate_expr e).
```

Assumptions (checked with `Print Assumptions`): the abstract types
`IRI`, `Literal`, `Version` with decidable equality; `VI` injective;
the dictionary bijection `id_to_val`/`val_to_id`; the abstract semantics
of built-in functions and effective boolean values (`interp_func`, `ebv`,
`term_of_bool`), identical in both algebras; the abstract aggregate
functions `agg_apply`, functions of the bag of values (`agg_apply_perm`);
`term_of_nat` for the literal produced by `COUNT`.

## Corrections and choices with respect to the thesis

1. **Projection.** `Π_C` as stated is not equivalent to `Π_F` under bag
   semantics: projecting away a `ζ` variable bound to *n* versions turns
   *n* flat solutions into one condensed mapping of cardinality 1.
   The translation now promotes the projected-away variables to `ι`
   (`dropped_vars`) before `Π_C` (`projection_perm` has this hypothesis).
2. **Versioned IRIs are IRIs** (`vi : Version -> IRI -> IRI`), so that the
   graph variable of a flat mapping is bound to an RDF term; the inverse
   functions of Eq. (5.1) follow from injectivity.
3. **Merging of bindings** (`merge_binding`) is total and semantic:
   it represents `vals(b1) ∩ vals(b2)`. On two bindings of the same
   representation it coincides with Definitions 5.25–5.26; on mixed
   representations it keeps the point-valued binding.
4. **Environment of JOIN / UNION / OPTIONAL.** The result environment uses
   the pointwise *meet* on shared variables (`env_meet`), not the join:
   `translate` does not promote the operands before `⋈_C` (its merge is
   semantic), so a variable that is `ι` on one side but may be unbound
   there (after `UNION` or `OPTIONAL`) and `ζ` on the other side can
   still carry a `ζ` binding in the result. The thesis's rule (both
   operands typed under the same Γ, Definition 5.44) gives the pointwise
   *join* (`rstar_join`, Optimality.v) and is sound because τ promotes
   both operands to R\*(⋈) before `⋈_C` (Definition 5.47). Both rules are
   instances of `typed` and both are covered by `typed_correct`.
   Environments are lower bounds on representations (`env_ok`); any extra
   promotion is harmless for correctness.
5. **Difference** needs non-empty version sets in the results (otherwise a
   condensed mapping with an empty `ζ` binding has no expansion but is
   still a mapping); this is the `wf_cmap` invariant, maintained by all
   operators and established by `wf_condensed_model`.
6. **Constant in the graph position** (Def. 5.9, 5.24). The constant is a
   versioned IRI, compared with `VI(v, g)` (Example 5.14), not with the
   named graph `g`: with a plain named graph the flat evaluation yields one
   solution per version and the condensed evaluation one solution, so
   Theorem 6.2 would fail under bag semantics.
7. **ψ representation** (Def. 5.21, 5.32, 5.39). The marker `•` denotes the
   catalog of the archive (the (graph, version) pairs present); its
   cardinality factor is the number of such pairs, not `|VA|·|G_N|`. It is
   produced by `GRAPH ?x { }` (`GraphsF`), the only operator whose result
   is exactly the set of versioned named graphs.
8. **Grouping and aggregation.** `Gr`, `Agg` and `AggJ` are fused into one
   operator `GroupAggF ks aggs e`; an aggregate is any function of the bag
   of values; the condensed evaluation weights each mapping by `card(m)`
   (count-views). The grouping variables keep the bindings of a
   representative member of the group, hence their representation (Table
   5.8: ι stays ι); the aggregate variables are bound in ν.
9. **Type system** (Def. 5.43, 5.44). Equality requires both operands at
   least at ι (the rule as written requires the same representation);
   Extend requires its expression at ι (rule) rather than ν (text); the
   constraints of an operator bear on its sub-tree (a single global Γ with
   `var ∉ D(Γ)` in Extend cannot type a BIND read by an enclosing FILTER).
   See `SPEC-extensions.md`.
