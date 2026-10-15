# Spécification des extensions : agrégation, ψ, graphe constant, optimalité de R*

Ce document fixe ce qui est formalisé pour les quatre points laissés hors
périmètre par la première version du développement, les décisions de
modélisation prises, et les énoncés prouvés (tous sans `Admitted` ; les
seules hypothèses sont les paramètres de modélisation listés dans le
README). Les sections « Écart avec la thèse » signalent les points où la
thèse (chapitres 5 et 6) doit être corrigée ou précisée ; chacun est à
valider par l'auteur.

Convention : sémantique de sacs (les séquences de solutions sont des listes,
`≅` est `Permutation`), expansion `Ξ` = `expand`, environnements = bornes
inférieures sur les représentations des liaisons (`env_ok`).

---

## 1. Terme constant en position graphe (Déf. 5.9 / 5.24)

### Spécification

La position graphe d'un motif de quadruplet est un `PatTerm` comme les trois
autres positions : `QuadPatternF s p o g` avec `g : PatTerm`
(`FlatAlgebra.v`).

* **Plat (Déf. 5.9 corrigée).** La composante graphe d'un quadruplet versionné
  `(s, p, o, g, v)` est l'IRI versionnée `VI(v, g)` : une variable y est liée,
  une constante `c` filtre les quadruplets tels que `c = VI(v, g)`.
  Formellement `match_flat` applique `match_term g (TermIRI (vi v g))`
  (`FlatEvaluation.v`).
* **Condensé (Déf. 5.24 corrigée).** Une constante `c` sélectionne l'entrée
  `(q, V)` ssi il existe `v ∈ V` avec `c = VI(v, quad_graph q)` ; aucune
  liaison n'est produite. Une variable est liée à `(quad_graph q, V)` (ζ).
  Fonction `match_graph_c` (`CondensedEvaluation.v`).
* **Typage.** `pat_env` ne contient la variable graphe que si la position est
  une variable (`map (x, ζ) (pat_vars g)`, `Translation.v`).

### Énoncés prouvés

`match_cond_expand` (sous `NoDup V` : une constante `VI(v0, g)` sélectionne
exactement une version, par injectivité de `VI`), `qp_perm` (sous
`wf_condensed_model dC`), `qp_inv` ; donc `evaluation_equivalence`
(Théorème 6.2) pour toute position graphe.

### Écart avec la thèse

Les Définitions 5.9 et 5.24 comparent la constante `t_g` avec le nom de graphe
`g` (« `t_g = d_g` avec `d_g = g` »). Avec cette lecture, pour un nom de graphe
`ex:park`, l'évaluation plate produit une solution **par version** et
l'évaluation condensée une seule solution (sans liaison ζ, cardinalité 1) :
le Théorème 6.2 est faux en sémantique de sacs. La lecture retenue — la
constante est une IRI versionnée, comparée à `VI(v, g)` — est celle de
l'Exemple 5.14 (`GRAPH <vi:park-v1>`) et de `vi-restr` (Déf. 5.40). Les
restrictions multi-versions (`vngs-of`, `vngs-in`, Déf. 5.41–5.42) doivent
passer par une variable graphe (jointure avec les métadonnées, Exemples
5.15–5.16), jamais par une constante.

---

## 2. Représentation ψ (graphe non lié, Déf. 5.18, 5.21, 5.32, 5.39)

### Spécification

* **Catalogue.** `Catalog := list (IRI * VersionSet)` et `wf_catalog`
  (`Versioning.v`). Le catalogue d'un modèle condensé, `graph_catalog dC`
  (`Models.v`), associe à chaque graphe nommé présent l'ensemble des versions
  où il contient au moins un quadruplet : c'est `τ_{ψ⇝ζ}(•)` de la
  Déf. 5.32. Côté plat, `flat_graphs dF` est l'ensemble sans doublon des
  paires `(g, v)` présentes ; `flat_graphs_catalog_pairs` relie les deux.
* **Liaison.** Constructeur `BAll : Catalog -> Binding` (le marqueur `•`,
  Déf. 5.20) avec `binding_repr (BAll _) = ψ`,
  `vals (BAll cat) = { VI(v, g) | (g, V) ∈ cat, v ∈ V }` (Déf. 5.21, lue
  comme dans la preuve du Lemme 6.1 : seules les paires présentes dans
  l'archive) et `point_val = None` (`SolutionMappings.v`). Bonne formation :
  graphes deux à deux distincts, ensembles de versions non vides sans
  doublon, catalogue non vide.
* **Opérateur producteur.** `GraphsF x` / `GraphsC x` : le motif SPARQL
  `GRAPH ?x { }`, qui lie `?x` à chaque graphe nommé versionné de l'archive.
  Plat (`graphs_flat`) : une solution `{x ↦ VI(v, g)}` par paire présente.
  Condensé (`graphs_cond`) : une seule solution
  `{x ↦ BAll (graph_catalog dC)}` (aucune si l'archive est vide). C'est le
  seul opérateur dont le résultat est exactement « tous les graphes nommés
  versionnés », donc le seul producteur légitime de ψ ; un motif de
  quadruplet produit toujours ζ (Déf. 5.24).
* **Fusion (Déf. 5.25–5.26, cas mixtes).** `merge_binding` reste sémantique
  (`vals(b1) ∩ vals(b2)`) : `ζ ⋈ ψ` et `ψ ⋈ ζ` donnent une liaison ζ
  `(g, V ∩ V_g)` ; `ψ ⋈ ψ` donne ψ (restriction de catalogue,
  `cat_restrict`).
* **Promotion (Déf. 5.32).** `promote_binding ζ (BAll cat)` = une liaison
  `BCond g V` par entrée du catalogue (`τ_{ψ⇝ζ}`) ; vers ι et ν, composition
  `τ_{ζ⇝ι} ∘ τ_{ψ⇝ζ}` (remarque finale de la Déf. 5.47) (`Promotion.v`).
* **Différence.** `binding_filter` restreint chaque entrée du catalogue ; les
  tranches de la Déf. 5.29 s'appliquent sans changement (`Difference.v`).
* **Typage.** `TyGraphs : typed (GraphsC x) [(x, ψ)]` ; une variable typée ψ
  est promue par `Υ` comme les autres.

### Énoncés prouvés

* Lemme 6.1, cas ψ ⇝ ζ : `vals_promote_binding` ; Lemme 6.2 inchangé
  (`promote_perm`).
* Lemmes 6.4–6.6 : via `merge_binding_vals` / `merge_binding_None` /
  `merge_binding_wf` étendus aux cas ψ.
* Lemme 6.7 : `expand_length` inchangé ; `vals_BAll_length` donne le facteur
  d'une variable ψ dans `card(m)` : `Σ_{(g,V) ∈ cat} |V|`.
* Cas `GraphsF` du Théorème 6.2 : `graphs_perm`, `graphs_inv`.

### Écart avec la thèse

La Déf. 5.39 et le Lemme 6.7 donnent `|VA|·|G_N|` comme facteur d'une variable
ψ, alors que la Déf. 5.21 (lue avec la preuve du Lemme 6.1) ne représente que
les paires `(g, v)` présentes dans `D(d_C)`. Le facteur correct est le nombre
de paires présentes, `Σ_g |V_g|` ; le produit `|VA|·|G_N|` n'est juste que si
chaque graphe nommé est présent dans chaque version. Par ailleurs la thèse ne
dit pas quel opérateur produit ψ ; la formalisation retient `GRAPH ?x { }`.
La règle de fusion de la Déf. 5.26 pour ψ (« `m1(var)` ») n'est correcte que
si les deux côtés sont ψ ; les cas mixtes exigent l'intersection.

---

## 3. Regroupement et agrégation (Déf. 5.37–5.39, §5.3.6, cas Group / Aggregation / AggregateJoin du Th. 6.2)

### Spécification (`Aggregation.v`)

* **Opérateur fusionné.** `GroupAggF ks aggs e` = `AggJ(Agg_1, …, Agg_n)` sur
  `Gr(ks, e)` : `ks : list Var` (variables de `GROUP BY`),
  `aggs : list (Var * AggFun * SparqlExpr)` (variable résultat, fonction
  d'agrégat, expression). C'est la traduction SPARQL 1.1 de
  `SELECT ks (f_i(e_i) AS ?a_i) … GROUP BY ks` ; la thèse ne donne pas de
  sémantique à `AggJ` et définit `Agg_C` en prose.
* **Clé de groupe.** `key_of lk ks = map lk ks : list (option Term)`
  (`None` = variable non liée) ; les groupes sont les clés distinctes
  (`group_by`). Cas SPARQL : `ks = []` et entrée vide donnent un unique
  groupe vide (`groups`).
* **Fonctions d'agrégat.** `AggFun` est abstrait ; `agg_apply : AggFun ->
  list (option Term) -> option Term` est une fonction du **sac** des valeurs
  (axiome `agg_apply_perm`). COUNT, SUM, AVG, MIN, MAX en sont des instances ;
  `count_values` est donnée explicitement. `None` est l'erreur SPARQL
  (variable résultat non liée).
* **Évaluation plate (`groupagg_flat`).** Pour chaque groupe `(k, membres)` :
  la solution `key_mapping ks k ++ agg_bindings`, où la valeur de
  l'agrégat `i` est `agg_apply f_i (map (eval e_i) membres)`.
* **Évaluation condensée (`groupagg_cond`, count-views, Déf. 5.38–5.39).**
  Même forme, mais chaque mapping condensé `m` du groupe contribue
  `eval e_i m` répété `card(m)` fois (`values_c`) ; les liaisons produites
  sont ν (`to_vals`). `COUNT_C = Σ card(m)` (Déf. 5.39) est le lemme
  `count_values_c`.
* **Typage (Déf. 5.44, règles Group / Aggregation).** `TyGroupAgg` :
  variables de `ks` au moins ι ; variables des `e_i` aux représentations de
  `cond_reqs` (ν sous une fonction) ; `ks` sans doublon, variables résultat
  deux à deux distinctes et hors de `ks`. Environnement résultat
  `groupagg_env` : `ks ∩ D(Γ)` et les variables résultat en ν.
* **Traduction.** `τ(GroupAggF ks aggs e) = GroupAggC ks aggs (Υ_reqs τ(e))`
  avec `reqs = needs_reqs R(e) (groupagg_reqs ks aggs)`.

### Énoncés prouvés

`key_expand` (Lemme 6.3 sur les clés), `values_perm` (Lemme 6.7 : le sac
pondéré est une permutation du sac plat), `group_members_perm`,
`group_keys_perm`, **`groupagg_perm`** : si `L ≅ Ξ(M)`, `M` bien formé,
`ks` point-valuées et les variables des `e_i` point-valuées dans `M`, alors
`groupagg_flat ks aggs L ≅ Ξ(groupagg_cond ks aggs M)`. Cas GroupAgg de
`typed_correct` (`groupagg_inv` pour l'invariant), extension de `translate`,
`translate_typed`, `erase_translate`.

### Écart avec la thèse

* La preuve du cas Aggregation (Ch. 6) traite COUNT, SUM, AVG, MIN, MAX un par
  un ; le résultat général est que **toute** fonction du sac des valeurs est
  préservée, parce que le sac pondéré par `card` est une permutation du sac
  plat (Lemme 6.7 + Lemme 6.3). Les formules `SUM_C = Σ card(m)·x_m` et
  `AVG_C` en découlent dès que l'arithmétique est un monoïde commutatif.
* Les variables de regroupement n'ont besoin que de ι (comparaison
  d'identifiants, décodés ici par `lk_c`) ; la formalisation lie les clés du
  résultat en ν, ce qui ne perd rien (ν est la représentation la plus
  informative) et évite de paramétrer l'opérateur par Γ. Le Tableau 5.8 les
  laisse en ι : à arbitrer.

---

## 4. Optimalité de R* (Déf. 5.43–5.46, Lemmes 5.2–5.3, Th. 5.1)

### Spécification (`Optimality.v`, `Expressions.v`, `Typing.v`)

Ce qui est prouvable sans modèle de coût est exactement ce que la thèse
appelle optimalité : R*(e) est **le plus petit** environnement (pour `≤_r`
point à point) satisfaisant les contraintes de représentation de tous les
opérateurs de `e`.

* **Expressions (Déf. 5.43).** Constructeur `ExprEq e1 e2` (égalité,
  sémantique `Term_eq_dec` sur les valeurs décodées, ce qui équivaut à
  comparer les identifiants par bijectivité du dictionnaire).
  `expr_reqs_at r e` liste les contraintes `(x, r')` : variable directement
  sous `=` ⇒ ι, sous une fonction ⇒ ν, `BOUND(?x)` ⇒ ι, en position de
  condition ⇒ `r` (`cond_reqs` = ν pour FILTER, DIFF, OPTIONAL, agrégats ;
  `bind_reqs` = ι pour BIND, règle Extend de la Déf. 5.44). Le jugement
  `typed` et la traduction `τ` utilisent désormais ces contraintes par
  variable (`env_meets`, `needs_reqs`) au lieu de « toutes les variables en
  ν ». Jugement `expr_ty Γ e r` (Déf. 5.43) et correspondance
  `expr_ty_reqs`.
* **Contraintes d'un opérateur (Déf. 5.44).** `constraints e` et jugement de
  vérification `tc Γ e` (Γ global, règles de la thesis) avec `tc_iff :
  tc Γ e <-> satisfies Γ (constraints e)`.
* **Environnement inférieur (Déf. 5.45).** `env_glb Γ1 Γ2` : meet sur le
  domaine commun (`env_glb_lookup`).
* **R\*.** `rstar e := env_raise [] (constraints e)` (borne supérieure point à
  point des contraintes), calculable.

### Énoncés prouvés

* Lemme 5.2 : `expr_ty_glb` (`Γ1 ⊢ e : r1`, `Γ2 ⊢ e : r2` ⇒
  `Γ1 ⊓ Γ2 ⊢ e : r1 ⊓ r2`).
* Lemme 5.3 : `tc_glb` (`tc Γ1 e -> tc Γ2 e -> tc (env_glb Γ1 Γ2) e`).
* Théorème 5.1 : `rstar_well_typed : tc (rstar e) e`.
* Minimalité : `rstar_least : tc Γ e -> rstar e <=_env Γ` ; donc
  `rstar_glb` : tout environnement valide et minimal est équivalent à
  `rstar e` — `rstar e` est le plus grand minorant de `{Γ | tc Γ e}`
  (Déf. 5.46), et il est unique à équivalence près.
* Règle d'environnement de JOIN : `tc_join : tc Γ (Join e1 e2) <-> tc Γ e1
  /\ tc Γ e2`, d'où `rstar_join : rstar (Join e1 e2) ≡ env_join (rstar e1)
  (rstar e2)` (le join point à point, comme dans l'Exemple 5.17). Dans la
  thèse les deux opérandes sont promus à cet environnement **avant** `⋈_C`
  (Déf. 5.47), ce qui rend la règle correcte ; `translate` ne promeut pas
  avant la jointure (fusion sémantique) et garantit donc seulement le meet.
  Les deux variantes sont des instances de `typed`, couvertes par
  `typed_correct`. Verdict sur le point du README : les deux règles sont
  correctes dans leur système respectif ; celle de la thèse décrit une
  exigence (après promotion), celle du développement une garantie (sans
  promotion).
* Promotion paresseuse (principe central de la §5.3.4) :
  `translate_lazy : lazy (translate_expr e)` — toute promotion `Υ_reqs`
  insérée par τ est immédiatement sous un opérateur dont les contraintes
  contiennent `reqs` ; aucune promotion n'est insérée sous JOIN ni UNION.

### Écart avec la thèse

* Déf. 5.43, règle Equality : « `Γ ⊢ e1 : r, Γ ⊢ e2 : r` » impose la même
  représentation aux deux opérandes, donc ν dès qu'un opérande est une
  constante ; le texte dit « au moins ι ». La formalisation retient « chaque
  opérande ≥ ι ».
* Déf. 5.44, règle Extend : la règle écrit `Γ ⊢ e_c : ι`, le texte dit ν. La
  formalisation retient ι (il suffit de pouvoir décoder).
* Déf. 5.44 : un seul Γ pour toute l'expression, et la règle Extend exige
  `var ∉ D(Γ)` : une variable introduite par BIND et lue par un FILTER
  englobant est alors intypable. La formalisation fait porter les
  contraintes sur les sous-arbres ; la variable introduite est produite en ν
  (Déf. 5.31) et n'est pas contrainte.
* Projection : contrainte ι sur les variables projetées (correction déjà
  consignée dans le README) ; `GRAPH ?x { }` : contrainte ψ.
* `R(e)` (garantie calculée par τ) et `R*(e)` (exigence) ne sont pas
  comparables point à point en général : un opérateur peut produire plus
  que ce que l'aval exige (BIND produit ν alors qu'un `=` en aval n'exige
  que ι). La bonne propriété de τ est `translate_lazy`, pas
  `R(e) ≤ R*(e)`.
* La thèse ne prouve pas que R* est optimal au sens d'un coût ; cette
  propriété relève de la validation empirique (Ch. 7) et n'est pas
  formalisable sans modèle de coût.

---

## Questions à l'auteur

1. ψ : confirmer que `GRAPH ?x { }` (ou un équivalent dans QuaQue) est bien
   la source de la représentation ψ, et accepter le facteur `Σ_g |V_g|` à
   la place de `|VA|·|G_N|` (Déf. 5.39, Lemme 6.7).
2. Graphe constant : accepter la lecture « IRI versionnée » des Déf. 5.9 et
   5.24, ou préciser que la constante doit être une IRI versionnée.
3. Egalité (Déf. 5.43) : « même représentation » ou « au moins ι » ?
4. Clés de regroupement en ν dans le résultat (Tableau 5.8 : ι) — à arbitrer.
