#!/usr/bin/env python3
"""Build segments.json: the nested segmentation of the Seymour paper.

A node is just: id, label, text, src=[file,start,end], children. No categories,
no roles — structure is only depth (level 1 = sections, level 2 = their parts,
and so on).

COVERAGE INVARIANT. Every node's children *tile* its source line range:
contiguous, non-overlapping, covering it exactly. Enforced by construction — a
child is declared with only its START line; the builder sets each child's END to
(next sibling's start - 1), the last to the parent's END. A post-build checker
re-verifies and aborts on any gap/overlap. So at every level, the children cover
every character of the parent.

Edit here, re-run, never hand-edit segments.json. See DATA_MODEL.md.
"""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
SRC_DIR = ("/u/taddmao/code/autoform/math/preprints/"
           "A-proof-of-Seymours-second-neighborhood-conjecture-"
           "September-23-2026/build/source")

# line count of each source file (used to tile each section fully)
NLINES = {
    "00-introduction.tex": 140,
    "01-reduction.tex": 242,
    "02-pruning.tex": 356,
    "03-incompatibility.tex": 148,
    "04-weighted-consequences.tex": 70,
    "05-directed-cycle-consequences.tex": 72,
    "main.tex": 47,
}


def k(start, id, label, text="", children=None):
    """A node: a span of source with a name and its NL text.

    Declared by its START line only; the END is auto-computed so children tile
    their parent exactly. No categories — a node's only structure is its depth.
    """
    return {"_start": start, "id": id, "label": label,
            "text": text, "children": children or []}


# ===========================================================================
# 1. INTRODUCTION  (00-introduction.tex, 1..140)
# ===========================================================================
SEC_INTRO = k(1, "sec:intro", "1. Introduction", children=[
    k(1, "intro:head", "§1 heading",
      text="Section 1 — Introduction."),
    k(3, "def:oriented", "Definition: oriented graph",
      text="An *oriented graph* is a finite directed graph with no loops, no "
           "multiple arcs, and no pair of opposite arcs. Its underlying "
           "undirected graph need not be complete or connected."),
    k(6, "def:neighborhoods",
      "Definition: $N_1^+(v)$, $N_2^+(v)$ + the conjecture",
      text="$$N_1^+(v)=\\{u:v\\to u\\},\\quad N_2^+(v)=\\{w\\notin\\{v\\}\\cup "
           "N_1^+(v):\\exists u,\\,v\\to u\\to w\\}.$$ $N_2^+(v)$ = vertices at "
           "directed distance exactly two, counted once. Seymour's conjecture: "
           "some vertex has $|N_1^+(v)|\\le|N_2^+(v)|$."),
    k(16, "thm:main", "Theorem 1.1 (main result)",
      text="Every nonempty finite oriented graph has a vertex $v$ such that "
           "$$|N_1^+(v)|\\le|N_2^+(v)|.$$"),
    k(23, "rmk:sinks", "Remark: sinks, essential content",
      text="Resolves the conjecture with no connectivity or degree hypothesis; "
           "a sink already satisfies it. Removing vertices reached in one step "
           "is essential to the assertion."),
    k(29, "rmk:preview", "Preview of §5 (weighted) and §6 (cycles)",
      text="The theorem yields the vertex- and arc-weighted forms via Seacrest's "
           "equivalences (two quantifier orders), stated in §5, and "
           "short-directed-cycle consequences in §6 (e.g. min in/outdegree "
           "$\\ge n/3$ forces a directed triangle)."),
    k(39, "bg:priorwork", "Background: tournament case & history",
      text="Conjecture recorded by Dean & Latka; tournament case (Dean's "
           "conjecture) proved by Fisher via Farkas, combinatorially by Havet & "
           "Thomassé; extensions by Fidler–Yuster, Ghazal, and others."),
    k(52, "bg:priorwork2", "Background: degree/ratio & random results",
      text="Degree-condition and ratio results (Kaneko–Locke, Chen–Shen–Yuster, "
           "Huang–Peng), random-orientation results, and dense-case preprints."),
    k(68, "bg:builds-on", "What this proof builds on",
      text="Builds on the minimal-counterexample and graph-product methods of "
           "Brantner–Brockman–Kay–Snively and Seacrest's subset perspective; "
           "adapts Seacrest's Lemma 4 edge-deletion idea. Main new ingredient: a "
           "pruning bound for finite binary relations whose deletion cost depends "
           "on points left uncovered."),
    k(79, "intro:strategy", "Proof strategy", children=[
        k(79, "intro:strat:head", "“Proof strategy.”",
          text="Paragraph heading: Proof strategy."),
        k(80, "intro:strat:F", "Image operator $F_D$",
          text="$F_D(S)=\\{y:\\exists x\\in S,\\,x\\to y\\}$, $F_D^2=F_D\\circ "
               "F_D$; $F_D$ does not subtract $S$. In an oriented graph "
               "$N_2^+(v)=F_D^2(\\{v\\})\\setminus F_D(\\{v\\})$."),
        k(89, "intro:strat:reduce",
          "Step A — counterexample ⟶ strict subset inequality",
          text="Minimum-order then minimum-arc counterexample; arc deletion gives "
               "$|F_D^2(S)\\setminus F_D(S)|<|F_D(S)\\setminus S|$ for nonempty "
               "proper $S$; a transitive-tournament blowup turns this into "
               "$|U|+|F_G^2(U)|<2|F_G(U)|$, all indegrees positive. (§2.)"),
        k(106, "intro:strat:extremal",
          "Step B — the extremal obstruction",
          text="Two diagonal-containing families of pairs in $V(G)\\times V(G)$ "
               "maximizing $M+d$; complementing second iterated images yields "
               "prospective families of combined size $>M+2d$."),
        k(120, "intro:strat:prune",
          "Step C — pruning restores compatibility",
          text="The pruning lemma (§3) restores compatibility, keeps the "
               "diagonal, deletes $\\le d+d'$ members, making the objective "
               "$>M+d$ — the contradiction (§4)."),
        k(135, "intro:strat:prune-proof",
          "How the pruning lemma is proved",
          text="Bounds a matching in an augmented bipartite graph; opposite-order "
               "coordinate changes factor one matrix through two index sets, and "
               "a maximum-rank choice makes kernels control matching size. "
               "Independent of orientation."),
    ]),
])

# ===========================================================================
# 2. REDUCTION  (01-reduction.tex, 1..242)
# ===========================================================================
SEC_REDUCTION = k(1, "sec:reduction",
                  "2. Counterexample → strict subset inequality",
                  children=[
    k(1, "red:head", "§2 heading",
      text="Section 2 — From a counterexample to a strict subset inequality."),
    k(3, "red:intro", "Section intro: the operator $F=F_D$",
      text="Convert a counterexample into a graph whose first image exceeds the "
           "average of a set and its second image. Here $F=F_D$ is the union of "
           "out-neighborhoods in base graph $D$; $F(S)$ need not be disjoint "
           "from $S$."),
    k(10, "prop:reduction",
      "Prop 2.1 (Counterexample reduction)",
      text="If Theorem 1.1 has a counterexample, there is a finite nonempty "
           "oriented graph $G$ with every vertex of positive indegree and "
           "$$|U|+|F_G^2(U)|<2|F_G(U)|\\quad(\\varnothing\\ne U\\subsetneq "
           "V(G)).$$"),
    k(21, "red:plan", "Two-step plan",
      text="Two steps: minimality gives a strict deficit for subsets of a "
           "counterexample; a transitive-tournament blowup turns that deficit "
           "into the required inequality."),
    k(27, "red:seacrest", "Relation to Seacrest's Lemma 4",
      text="The arc-deletion argument adapts Seacrest's Lemma 4 (his $\\lambda=1$ "
           "gives $|F^2(S)\\setminus F(S)|<|F(S)|$ in an edge-minimal "
           "counterexample). Lemma 2.2 strengthens the right side to "
           "$|F(S)\\setminus S|$ under minimum order then minimum arcs."),
    k(36, "lem:subset-deficit", "Lemma 2.2 (Subset deficit)",
      text="Let $D$ be finite nonempty oriented with $|N_1^+(v)|>|N_2^+(v)|$ for "
           "all $v$; pick $D$ of minimum order then minimum arcs. Then $D$ is "
           "strongly connected, all indegrees positive, and "
           "$$|F^2(S)\\setminus F(S)|<|F(S)\\setminus S|\\quad(\\varnothing\\ne "
           "S\\subsetneq V(D)).$$"),
    k(49, "pf:subset-deficit", "Proof of Lemma 2.2", children=[
        k(49, "pf:sd:connected", "Strongly connected, no sink",
          text="A sink satisfies the inequality, so $D$ has no sink and $>1$ "
               "vertex. A terminal strong component would be a smaller "
               "counterexample; so $D$ is strongly connected and every vertex "
               "has an in-neighbor."),
        k(59, "pf:sd:setup", "Fix $S$; define $I$, $E$, $g$",
          text="$I=F(S)\\cap S$, $E=F(S)\\setminus S$, "
               "$g(T)=|F(T)\\setminus(I\\cup T)|$. Strong connectivity gives "
               "$E\\ne\\varnothing$. Grow $T$ from $\\varnothing$ to $E$ so each "
               "step raises $g$ by less than the vertices added."),
        k(68, "pf:sd:delete",
          "Delete arcs $S\\to E\\setminus T$; find $v\\in S$",
          text="$D_T$ deletes all arcs $S\\to E\\setminus T$. Arc-minimality "
               "gives $v$ with $|N^+_{1,D_T}(v)|\\le|N^+_{2,D_T}(v)|$; it must "
               "have lost a first out-neighbor, so $v\\in S$ and "
               "$Q=F(\\{v\\})\\cap(E\\setminus T)\\ne\\varnothing$."),
        k(83, "pf:sd:endpoints", "Where surviving 2-paths land",
          text="In $D_T$, $F^2_{D_T}(\\{v\\})\\subseteq I\\cup T\\cup F(T)$; any "
               "newly counted second out-neighbor lies in $Q\\cap F(T)$."),
        k(97, "pf:sd:gained", "The lost second out-neighbors $C$",
          text="$C=F(Q)\\setminus(I\\cup T\\cup Q\\cup F(T))\\subseteq "
               "N^+_{2,D}(v)$ (using $v\\notin F(Q)$ by orientation), and no "
               "vertex of $C$ survives in $D_T$."),
        k(108, "pf:sd:increment", "Deficit increment is $<|Q|$",
          text="With $d_2<d_1$: $g(T\\cup Q)-g(T)=|C|-|Q\\cap F(T)|\\le "
               "|Q|+d_2-d_1<|Q|.$"),
        k(126, "pf:sd:terminate", "Sum over the growth to $T=E$",
          text="Summing gives $g(E)<|E|$; since $F^2(S)\\setminus "
               "F(S)=F(E)\\setminus(I\\cup E)$ has size $g(E)$, the deficit "
               "follows."),
    ]),
    k(140, "red:amplify", "Bridge: amplifying the integer deficit",
      text="Each unit of base deficit contributes a full block; internal "
           "contribution costs $\\le1$ per base vertex. Construction: the "
           "lexicographic product $D[T_m]$ (as in Brantner–Brockman–Kay–Snively "
           "Thm 4.3), but estimated for every nonempty proper subset."),
    k(150, "lem:blowup", "Lemma 2.3 (Transitive-tournament blowup)",
      text="Replace each vertex of $D$ (positive indegrees, satisfying the "
           "subset deficit) by a transitive tournament on $m>n$ vertices, with "
           "all arcs between blocks of an arc. The result $G$ is oriented, has "
           "positive indegrees, and satisfies $|U|+|F_G^2(U)|<2|F_G(U)|$."),
    k(161, "pf:blowup", "Proof of Lemma 2.3", children=[
        k(161, "pf:bl:internal", "Internal block estimates",
          text="Label blocks $1..m$ (small→large). For least element $a$, "
               "$f(T)=\\{a+1,..,m\\}$, so $|T|-|f(T)|\\le1$, "
               "$f^2(T)\\subseteq f(T)$, $|T|-2|f(T)|+|f^2(T)|\\le1$. $G$ is "
               "oriented with positive indegrees."),
        k(177, "pf:bl:firstimage", "Support $S$, $H_0$, and $|F_G(U)|$",
          text="$T_v$ = labels of $U$ in block $v$, $S=\\{v:T_v\\ne\\varnothing"
               "\\}$, $H_0=F(S)\\cup F^2(S)$. Every $F(S)$-block is filled: "
               "$|F_G(U)|=m|F(S)|+\\sum_{v\\in S\\setminus F(S)}|f(T_v)|$."),
        k(190, "pf:bl:secondimage", "Bounding $|F_G^2(U)|$",
          text="2-paths with two external arcs land in $F^2(S)$-blocks; one "
               "external arc in $F(S)$-blocks; internal-only give $f^2(T_v)$. So "
               "$|F_G^2(U)|\\le m|H_0|+\\sum_{v\\in S\\setminus H_0}|f^2(T_v)|$."),
        k(198, "pf:bl:combine", "Combine: $\\le -m+n<0$ for proper $S$",
          text="$|U|-2|F_G(U)|+|F_G^2(U)|\\le m(|F^2(S)\\setminus F(S)|-"
               "|F(S)\\setminus S|)+n$. For $S\\subsetneq V(D)$ the deficit makes "
               "the bracket $<0$, so the bound is $\\le -m+n<0$."),
        k(225, "pf:bl:full", "The case $S=V(D)$",
          text="Positive indegrees give $F_G(U)=F_G^2(U)=V(G)$, so "
               "$|U|-2|F_G(U)|+|F_G^2(U)|=|U|-|V(G)|<0$ since $U$ is proper."),
    ]),
    k(236, "pf:reduction", "Proof of Prop 2.1 (combines 2.2 & 2.3)",
      text="Choose a counterexample of minimum order then minimum arcs; Lemma "
           "2.2 supplies positive indegrees and the subset deficit, and Lemma "
           "2.3 (any $m>|V(D)|$) supplies $G$."),
])

# ===========================================================================
# 3. PRUNING  (02-pruning.tex, 1..356)
# ===========================================================================
SEC_PRUNING = k(1, "sec:pruning",
                "3. Pruning two families of pairs", children=[
    k(1, "pru:head", "§3 heading",
      text="Section 3 — Pruning two families of pairs."),
    k(3, "pru:intro", "Section intro: the deletion bound",
      text="A deletion bound for two families of ordered pairs, charging deleted "
           "members to original conflicts plus post-deletion uncovered points. "
           "Holds for every finite binary relation; no orientation needed."),
    k(10, "lem:pruning", "Lemma 3.1 (Pruning)",
      text="For finite $X$ with relation $\\to$ and $\\mathcal R,\\mathcal "
           "C\\subseteq X\\times X$: $(p,j),(i,s)$ *conflict* if $p\\to i$, "
           "$s\\to j$. With $Z=\\{(i,j)\\}$, $H=\\{(p,s)\\}$ over conflicts, "
           "there are conflict-free $\\mathcal R'\\subseteq\\mathcal R$, $\\mathcal "
           "C'\\subseteq\\mathcal C$ keeping every conflict-free member with "
           "$$|\\mathcal R\\setminus\\mathcal R'|+|\\mathcal C\\setminus\\mathcal "
           "C'|\\le|H|+|\\{z\\in Z\\text{ uncovered}\\}|.$$"),
    k(41, "pru:gap1", "Toward the proof: a rank fact",
      text="The proof bounds a matching in an augmented bipartite graph via "
           "matrix ranks; first the elementary rank fact (Lemma 3.2). A matrix "
           "supported on $T$ has zero entries outside $T$."),
    k(48, "lem:kernel-support",
      "Lemma 3.2 (Kernels at maximum support rank)",
      text="For finite $I,J$, $T\\subseteq I\\times J$: if $D:\\mathbb "
           "R^J\\to\\mathbb R^I$ has maximum rank among matrices supported on "
           "$T$, then for $x\\in\\ker D$, $y\\in\\ker D^{\\mathsf T}$, "
           "$(s,j)\\in T$, $x_jy_s=0$."),
    k(54, "pf:kernel-support", "Proof of Lemma 3.2",
      text="If $x_jy_s\\ne0$, perturb $D_\\tau=D+\\tau e_se_j^{\\mathsf T}$ "
           "(still supported on $T$): $e_s\\in\\im D_\\tau$ and $\\im "
           "D\\subseteq\\im D_\\tau$, but $y$ annihilates $\\im D$ with "
           "$y_s\\ne0$ so $e_s\\notin\\im D$ — hence $\\rank D_\\tau>\\rank D$, "
           "contradiction."),
    k(69, "pf:pruning", "Proof of Lemma 3.1 (four parts)",
      children=[
        k(69, "pf:pr:intro", "Trivial case & conventions",
          text="No conflicts ⟹ retain everything, $Z=H=\\varnothing$. Coordinate "
               "bases throughout; empty minors have determinant 1."),
        k(76, "pf:pr:graph",
          "Part 1 — augmented graph & the matching bound", children=[
            k(76, "pf:pr:graph:build", "Build $\\Gamma$",
              text="Bipartite $\\Gamma$: parts $\\mathcal R\\sqcup Z_L$, $\\mathcal "
                   "C\\sqcup Z_R$. Join conflicting members; join each member to "
                   "the opposite $Z$-copy it covers. Conflict-free members are "
                   "isolated."),
            k(90, "fig:pruning", "Figure: one conflict ⟶ 3-edge path",
              text="A conflict between $r=(p,j)$, $c=(i,s)$ forces path "
                   "$z_L-c-r-z_R$, $z=(i,j)\\in Z$; copies $z_L,z_R$ distinct. "
                   "Conflicts can share vertices/edges."),
            k(100, "pf:pr:graph:charge",
              "A small cover gives the charge $|H|+q$",
              text="A vertex cover $K$ of size $\\le|Z|+|H|$ omitting isolated "
                   "vertices: deleting its original members leaves no conflict, "
                   "and $|K\\cap(\\mathcal R\\sqcup\\mathcal C)|\\le|H|+q$ with $q$ "
                   "post-deletion uncovered $Z$-points."),
        ]),
        k(120, "pf:pr:submatch",
          "Part 2 — decompose a maximum matching",
          text="Maximum matching $\\mathcal M$ with fewest original–original "
               "edges ($k$); $\\alpha$ ($\\mathcal R$–$Z_R$), $\\beta$ "
               "($Z_L$–$\\mathcal C$), $\\ell=|\\alpha|$, $t=|\\beta|$, "
               "$|\\mathcal M|=k+\\ell+t$. Augmenting paths show $\\alpha,\\beta$ "
               "are each maximum in their subgraph."),
        k(148, "pf:pr:maps",
          "Part 3 — four maps, one commuting square",
          text="Variables $a_{xy},b_{xy}$ give $L,N,B,A$ with $NL=AB$. Goal: an "
               "assignment with $\\rank L=\\ell$, $\\rank N=t$, $\\dim\\ker A\\ge "
               "k$, forcing $|\\mathcal M|\\le|Z|+|H|$ via rank–nullity."),
        k(211, "pf:pr:choice",
          "Part 4a — simultaneous generic choice",
          text="Via Edmonds' generic-rank/matching correspondence: pick "
               "coefficients so $\\alpha$'s columns base $\\im L$, $\\beta$'s base "
               "$\\im N^{\\mathsf T}$, and each $D^{p,i}$ has maximum support "
               "rank — one product of nonzero polynomials, nonzero at some real "
               "assignment."),
        k(275, "pf:pr:kernel",
          "Part 4b — kernel restriction gives $\\dim\\ker A\\ge k$",
          text="Lift matched endpoints to $u^r\\in\\ker L$, $v^c\\in\\ker "
               "N^{\\mathsf T}$; Lemma 3.2 gives $u_{pj}v_{is}=0$ per conflict, so "
               "$Bu^r$ are independent and $A(Bu^r)=NLu^r=0$; thus $|\\mathcal "
               "M|=k+\\ell+t\\le|Z|+|H|$."),
        k(334, "pf:pr:cover",
          "Part 4c — matching bound ⟶ cover (König)",
          text="Alternating-path cover $K=(\\mathcal V_L\\setminus W_L)\\cup "
               "W_R$ covers every edge, $|K|=|\\mathcal M|\\le|Z|+|H|$, omits "
               "isolated vertices; the charge inequality proves the lemma."),
    ]),
])

# ===========================================================================
# 4. CONTRADICTION  (03-incompatibility.tex, 1..148)
# ===========================================================================
SEC_INCOMPAT = k(1, "sec:incompat", "4. The extremal contradiction", children=[
    k(1, "inc:head", "§4 heading",
      text="Section 4 — The extremal contradiction."),
    k(3, "inc:intro", "Section intro",
      text="Use the pruning lemma to rule out the graph from Prop 2.1, converting "
           "the strict subset inequalities into a strict increase of an extremal "
           "quantity on two families of pairs."),
    k(8, "prop:no-concavity", "Prop 4.1 (no such graph)",
      text="There is no nonempty finite oriented graph $G$ with every vertex "
           "having an in-neighbor and $$|U|+|F^2(U)|<2|F(U)|\\quad(\\varnothing"
           "\\ne U\\subsetneq V(G)).$$"),
    k(21, "pf:no-concavity", "Proof of Prop 4.1", children=[
        k(21, "pf:nc:ops", "Coordinate operators & compatibility",
          text="$F_1S$ advances the first coordinate along an arc, $F_2S$ the "
               "second. $P,Q$ *compatible* if $F_1P\\cap F_2Q=\\varnothing$ (= no "
               "conflict). $P=Q=\\Delta$ is compatible by orientation."),
        k(39, "pf:nc:maxobj", "The maximized objective $M+d$",
          text="Among compatible pairs with $\\Delta\\subseteq P\\cap Q$, "
               "maximize $M+d$ where $M=|P|+|Q|$, $d=|X|^2-|F_1P|-|F_2Q|$ = "
               "uncovered points. A maximum exists since $X$ is finite."),
        k(52, "pf:nc:fibers",
          "Columns/rows proper ⟶ sum the hypothesis",
          text="Each column $P_j\\ni j$ and row $Q_i\\ni i$ is proper (else "
               "compatibility breaks). Summing the concavity inequality: "
               "$|P|+|F_1^2P|<2|F_1P|$ and $|Q|+|F_2^2Q|<2|F_2Q|$."),
        k(66, "pf:nc:complement", "Complement families gain $>M+2d$",
          text="$\\mathcal R=(X\\times X)\\setminus F_2^2Q$, $\\mathcal "
               "C=(X\\times X)\\setminus F_1^2P$ give $|\\mathcal R|+|\\mathcal "
               "C|=2|X|^2-|F_2^2Q|-|F_1^2P|>M+2d$. They may conflict."),
        k(84, "pf:nc:diag",
          "The diagonal survives and is conflict-free",
          text="$\\Delta\\subseteq\\mathcal R\\cap\\mathcal C$, and each diagonal "
               "member is conflict-free (a conflict would force $(i,s)\\in F_1^2P$ "
               "or $(p,j)\\in F_2^2Q$). So pruning's preservation clause applies."),
        k(101, "pf:nc:Hbound", "The conflict set $H$: $|H|\\le d$",
          text="For a conflict, $(p,s)\\in F_1P$ or $F_2Q$ would force membership "
               "contradictions; so $H\\subseteq(X\\times X)\\setminus(F_1P\\cup "
               "F_2Q)$ and $|H|\\le d$."),
        k(120, "pf:nc:finish", "Apply pruning; the $M+d$ contradiction",
          text="Pruning gives conflict-free $P'\\subseteq\\mathcal R$, "
               "$Q'\\subseteq\\mathcal C\\supseteq\\Delta$, so $\\le d+d'$ "
               "deletions and $|P'|+|Q'|+d'>M+2d-(d+d')+d'=M+d$ — contradicting "
               "maximality of $(P,Q)$."),
    ]),
    k(143, "pf:main", "Proof of Theorem 1.1",
      text="If the theorem were false, Prop 2.1 produces a nonempty finite "
           "oriented graph with positive indegrees satisfying the concavity "
           "inequality; Prop 4.1 rules it out."),
])

# ===========================================================================
# 5. WEIGHTED CONSEQUENCES  (04-weighted-consequences.tex, 1..70)
# ===========================================================================
SEC_WEIGHTED = k(1, "sec:weighted", "5. Weighted consequences", children=[
    k(1, "wt:head", "§5 heading",
      text="Section 5 — Weighted consequences."),
    k(3, "wt:intro", "Section intro",
      text="Applies Theorem 1.1 through Seacrest's established equivalences; the "
           "equivalences are not new here."),
    k(8, "cor:weighted", "Corollary 5.1 (weighted forms)",
      text="For a nonempty finite oriented graph $D$: (i) for every $\\eta\\ge0$ "
           "some $v$ has $\\eta(N_1^+(v))\\le\\eta(N_2^+(v))$; (ii) a total-mass-one "
           "weighting (not all positive) works for every $v$; (iii) for every arc "
           "weighting $w\\ge0$ some $v$ has $\\sum_s\\beta_v^w(s)\\ge\\sum_{u\\in "
           "N_1^+(v)}w(vu)$."),
    k(42, "pf:weighted", "Proof of Corollary 5.1", children=[
        k(42, "pf:wt:iii", "(iii) = Seacrest's arc-weighted form",
          text="Seacrest's Prop 2: his arc-weighted conjecture is equivalent to "
               "the unweighted one, so Theorem 1.1 gives (iii)."),
        k(48, "pf:wt:i", "(i) by specializing $w(us)=\\eta(s)$",
          text="Setting $w(us)=\\eta(s)$ makes $\\beta_v^w(s)=\\eta(s)$ on "
               "$N_2^+(v)$ and $0$ elsewhere, so (iii)'s two sides become "
               "$\\eta(N_2^+(v))$ and $\\eta(N_1^+(v))$."),
        k(62, "pf:wt:ii", "(ii) via Farkas on $M_D$",
          text="$M_D$ has $\\pm1$ on second/first out-neighbors; reversing arcs "
               "transposes it. Seacrest's Farkas-lemma Theorem 1 gives a nonzero "
               "$\\eta\\ge0$ with $M_D\\eta\\ge0$ (the alternative contradicts (i) "
               "on $\\overleftarrow D$); normalize."),
    ]),
])

# ===========================================================================
# 6. DIRECTED-CYCLE CONSEQUENCES  (05-directed-cycle-consequences.tex, 1..72)
# ===========================================================================
SEC_CYCLES = k(1, "sec:cycles", "6. Directed-cycle consequences", children=[
    k(1, "cy:head", "§6 heading",
      text="Section 6 — Directed-cycle consequences."),
    k(3, "cy:intro", "Section intro",
      text="In a triangle-free oriented graph every exact second out-neighbor is "
           "a non-neighbor; combined with Theorem 1.1 this gives degree and order "
           "bounds (Thomassé/Sullivan, Behzad–Chartrand–Wall)."),
    k(15, "cor:cycles", "Corollary 6.1 (non-neighbors & cycles)",
      text="For order-$n$ oriented $D$ with $Z(v)=V\\setminus(\\{v\\}\\cup "
           "N_1^+(v)\\cup N_1^-(v))$: (i) no directed 3-cycle ⟹ some $v$ has "
           "$d^+(v)\\le|Z(v)|$, $n-1\\ge2d^+(v)+d^-(v)$; (ii) "
           "$\\delta^+,\\delta^-\\ge n/3$ ⟹ a directed 3-cycle; (iii) $r$-regular "
           "with girth exactly four ⟹ $n\\ge3r+1$."),
    k(42, "pf:cycles", "Proof of Corollary 6.1", children=[
        k(42, "pf:cy:setup", "$N_2^+(v)\\subseteq Z(v)$ & part (i)",
          text="No directed 3-cycle ⟹ a second out-neighbor is not $v$, a first "
               "out-neighbor, or an in-neighbor, so $N_2^+(v)\\subseteq Z(v)$. "
               "Theorem 1.1: $d^+(v)\\le|Z(v)|$; with $n-1=d^++d^-+|Z|$ gives (i)."),
        k(61, "pf:cy:finish", "Parts (ii) and (iii)",
          text="(ii): triangle-freeness would give $n-1\\ge2\\delta^++\\delta^-"
               "\\ge n$. (iii): girth four excludes 3-cycles and the regular "
               "count gives $n-1\\ge3r$."),
    ]),
])

# ===========================================================================
# Assemble the ROOT. title/abstract/references are fixed ranges in main.tex;
# each section tiles its own file. Root spans files, so it is not line-tiled.
# ===========================================================================
def leaf_src(node, src):
    node["_src"] = src
    return node


def section(node, file):
    """Tag a section subtree with its source file; it spans 1..NLINES[file]."""
    node["_file"] = file
    return node


ROOT = k(0, "paper",
         "A proof of Seymour's second-neighborhood conjecture",
         text="OpenAI — September 23, 2026.")
ROOT["_notile"] = True
ROOT["_src"] = ["main.tex", 29, 47]
ROOT["children"] = [
    leaf_src(k(29, "title", "Title",
               text="A proof of Seymour's second-neighborhood conjecture — "
                    "OpenAI."),
             ["main.tex", 29, 33]),
    leaf_src(k(34, "abstract", "Abstract",
               text="We prove that every nonempty finite oriented graph has a "
                    "vertex with at least as many vertices at directed distance "
                    "two as at directed distance one, resolving Seymour's second "
                    "neighborhood conjecture positively."),
             ["main.tex", 34, 38]),
    section(SEC_INTRO, "00-introduction.tex"),
    section(SEC_REDUCTION, "01-reduction.tex"),
    section(SEC_PRUNING, "02-pruning.tex"),
    section(SEC_INCOMPAT, "03-incompatibility.tex"),
    section(SEC_WEIGHTED, "04-weighted-consequences.tex"),
    section(SEC_CYCLES, "05-directed-cycle-consequences.tex"),
    leaf_src(k(45, "references", "References",
               text="Bibliography (plain style); see references.bib."),
             ["main.tex", 45, 47]),
]


# ===========================================================================
# Finalize: compute every node's `src` so that children TILE their parent.
# ===========================================================================
def finalize(node, file, start, end):
    """Assign node['src']=[file,start,end]; tile children across [start,end]."""
    if "_src" in node:
        file, start, end = node["_src"]
    elif "_file" in node:                       # a section: owns a whole file
        file = node["_file"]
        start, end = 1, NLINES[file]
    node["src"] = [file, start, end]

    kids = node["children"]
    if not kids:
        return
    starts = [c["_src"][1] if "_src" in c else c["_start"] for c in kids]
    for i, c in enumerate(kids):
        c_start = starts[i]
        c_end = (starts[i + 1] - 1) if i + 1 < len(kids) else end
        finalize(c, file, c_start, c_end)


def strip_build_keys(node):
    for key in ("_start", "_src", "_file", "_notile"):
        node.pop(key, None)
    for c in node["children"]:
        strip_build_keys(c)


# ===========================================================================
# Coverage check: within every container, children tile the parent's range
# exactly — contiguous, no gaps, no overlaps. Root is exempt (spans files).
# ===========================================================================
def check_coverage(node, errors, notile=False):
    kids = node["children"]
    if kids and not notile:
        f, s, e = node["src"]
        cursor = s
        for c in kids:
            cf, cs, ce = c["src"]
            if cf != f:
                errors.append(f"{node['id']}: child {c['id']} in {cf} ≠ {f}")
            if cs != cursor:
                errors.append(
                    f"{node['id']}: gap/overlap before {c['id']} "
                    f"(expected start {cursor}, got {cs})")
            if ce < cs:
                errors.append(f"{c['id']}: empty/negative range {cs}..{ce}")
            cursor = ce + 1
        if cursor - 1 != e:
            errors.append(
                f"{node['id']}: children end at {cursor-1}, parent ends at {e}")
    for c in kids:
        check_coverage(c, errors, notile=False)


def main():
    finalize(ROOT, None, None, None)

    errors = []
    # root's direct children span different files; check each child subtree.
    for c in ROOT["children"]:
        check_coverage(c, errors)

    strip_build_keys(ROOT)

    ids = []

    def collect(n):
        ids.append(n["id"])
        for c in n["children"]:
            collect(c)
    collect(ROOT)
    dups = {i for i in ids if ids.count(i) > 1}

    out = {"paper": ROOT["label"], "source_dir": SRC_DIR, "tree": ROOT}
    path = os.path.join(HERE, "segments.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=2, ensure_ascii=False)

    print(f"wrote {path}: {len(ids)} nodes")
    if dups:
        print("DUPLICATE ids:", dups)
    if errors:
        print(f"COVERAGE ERRORS ({len(errors)}):")
        for e in errors:
            print("  ", e)
        raise SystemExit(1)
    print("coverage OK: every container is exactly tiled by its children.")


if __name__ == "__main__":
    main()
