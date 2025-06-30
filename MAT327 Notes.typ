#import "@preview/noteworthy:0.2.0": *
#import "@preview/ctheorems:1.1.3": *

#show: noteworthy.with(
  paper-size: "a4",
  font: "New Computer Modern",
  language: "EN",
  title: "MAT327 Notes",
  author: "Sanchit Manchanda",
  toc-title: "Table of Contents",
)

#show: thmrules.with(qed-symbol: $square$)

#let theorem = thmbox("theorem", "Theorem", fill: rgb("#ff9999"), stroke: rgb("#ff6666"))
#let proposition = thmbox("proposition", "Proposition", fill: rgb("#90ee90"), stroke: rgb("#3cb371"))
#let definition = thmbox("definition", "Definition", fill: rgb("#ebb7eb"), stroke: rgb("#c68cc6"))
#let example = thmbox("example", "Example", fill: rgb("#9cd2ff"), stroke: rgb("#66baff"))
#let lemma = thmbox("lemma", "Lemma", fill: rgb("#a7f0f0"), stroke: rgb("#70c0c0"))
#let corollary = thmbox("corollary", "Corollary", fill: rgb("#add8e6"), stroke: rgb("#87ceeb"))
#let remark = thmbox("remark", "Remark", fill: rgb("#ffcda3"), stroke: rgb("#f7a057"))

#let proof = thmbox("proof", "Proof", inset: (x: 0em, top: 0em)).with(numbering: none)

#set enum(numbering: "(i) ")

#pagebreak()

= Topological Spaces

Our general motivation to construct topological spaces is to study continuity in the most abstract form.

Recall that

#definition[
  We say that $f: bb(R) -> bb(R)$ is continuous iff
  $ forall x_0 in bb(R) " " forall epsilon > 0 " " exists delta > 0 " " forall x in bb(R) " " (|x-x_0| <delta => |f(x)-f(x_0)| < epsilon) $
]

This is easily generalized to spaces where we have a notion of distance.

== Metric Spaces

#definition[
  Let $X$ be a set. A metric is a function $d: X times X -> bb(R)_(>= 0)$ such that
  
  + (Symmetry) $forall x,y in X "  " d(x,y) = d(y,x)$
  + (Definiteness) $forall x,y in X "  " d(x,y) = 0 <=> x=y$
  + (Triangle Inequality) $forall x,y,z in X "  " d(x,y) <= d(x,z) + d(z,y)$
]

We discuss some common examples previously seen in MAT257

#example[
  + (Usual Metric on $bb(R)$) $d(x,y) = |x-y|$
  
  + (Euclidean Metric on $bb(R)^n$) $d_2(x,y) = display(sqrt(sum_(i=1)^n |x_i-y_i|^2))$
  
  + (Taxicab Metric on $bb(R)^n$) $d_1(x,y) = display(sum_(i=1)^n |x_i-y_i|)$
  
  + (Square Metric on $bb(R)^n$) $d_infinity(x,y) = display(max_(1 <= i <= n) |x_i-y_i|)$
  
  + (Discrete Metric on any set $X$) $d(x,y) = cases(1 "if" x != y,
  0 "if" x = y)$
  
  + ($ell^p$-Metric on $bb(R)^n$) $d(x,y) = display((sum_(i=1)^n |x_i-y_i|^p)^(1/p))$
]

We see this naturally gives rise to a more general definition of continuity

#definition[
  We say that $f:(X,d_X) -> (Y, d_Y)$ is continuous iff
  $ forall x_0 in X " " forall epsilon > 0 " " exists delta > 0 " " forall x in X " " (d(x, x_0) < delta => d(f(x), f(x_0)) < epsilon) $
]

However this provides us with a new goal of defining continuity without the use of a metric.

#definition[
  Given a metric space $(X,d)$. Let $x_0 in X$ and $r > 0$.

  We define the open ball centered at $x_0$ with radius $r$ as

  $ B_d (x_0,r) = {x in X:d(x,x_0) < r} $
]

Now we note that it follows from the definition that continuity in a metric space is equivalent to

#proposition[
  $f:X->Y$ is continuous iff

  $ forall x_0 in X " " forall epsilon > 0 " " exists delta > 0 "s.t" B_d_X (x_0, delta) subset.eq f^(-1)(B_d_Y (f(x_0), epsilon)) $
]

#proof[
  
  We prove both directions together.

  Let $x_0 in X$ be arbitrary. Let $epsilon > 0$ then by the definition of continuity we have there exists some $delta > 0$ such that for all $x in X$ if $d_X (x,x_0) < delta$ then $d_Y (f(x),f(x_0)) < epsilon$.

  Now we see that $d_X (x,x_0) < delta$ is equivalent to $x in B_d_X (x_0, delta)$. Similarly we have that$d_Y (f(x), f(x_0)) < epsilon$ is equivalent to $f(x) in B_d_Y (f(x_0), epsilon)$. Now we see then that $x in f^(-1) (B_d_Y (f(x_0), epsilon))$.

  It follows then that continuity is equivalent to 
  $ x in B_d_X (x_0, delta) => x in f^(-1) (B_d_Y (f(x_0), epsilon)) $

  However this directly equivalent to

  $ B_d_X (x_0, delta) subset.eq f^(-1)(B_d_Y (f(x_0), epsilon)) $
]

#definition[
  Let $(X,d)$ be a metric space. We say that $U subset.eq X$ is open iff $U$ is a union of open balls.
]

#example[
  + On $bb(R)$, $(0,1)$ is open as $(0,1) = B_d (1/2, 1/2)$
  
  + All open balls are open
  
  + $X$ is open. Fix any $r>0$, then $X = display(union.big_(x in X) B_d (x,r))$
  
  + $diameter$ is open. Fix $I = diameter$, then $diameter = display(union.big_(i in I) B_d (x_i,r_i))$
] <X_and_diameter_are_open>

#proposition[
  Let $(X,d)$ be a metric space. $U subset.eq X$ is open iff
  $ forall x in U " " exists r > 0 "s.t." B_d (x,r) subset.eq U $
] <open-set-ball-equivalence>

#proof[
  
  ($=>$) Suppose $U subset.eq X$ is open. Then by definition $U = display(union.big_(i in I)) B_d (x_i, r_i)$ for some collection of open balls.
  \
  Fix $x in U$. Then $x in B_d (x_j, r_j)$ for some $j in I$.
  \
  It suffices to show that there exists $r > 0$ such that $B_d (x,r) subset.eq B_d (x_j, r_j)$.
  \
  Let $r = r_j - d(x, x_j)$. Since $x in B_d (x_j, r_j)$ we have $d(x, x_j) < r_j$ so $r > 0$.
  \
  Let $y in B_d (x, r)$. Then $d(y,x) < r$.
  By the triangle inequality
  $ d(y, x_j) &<= d(y,x) + d(x,x_j) \
  &< r + d(x,x_j) \
  &= (r_j - d(x,x_j)) + d(x,x_j) \
  &= r_j $
  So $y in B_d (x_j, r_j)$. Thus $B_d (x,r) subset.eq B_d (x_j, r_j) subset.eq U$.

  ($arrow.l.double$) Suppose for all $x in U$ there exists $r_x > 0$ s.t. $B_d (x,r_x) subset.eq U$.
  Then $U = display(union.big_(x in U)) B_d (x,r_x)$.
  This is a union of open balls, so $U$ is open.
]

We now use this to prove our most general form of continuity.

#theorem[
  Let $(X,d_X)$ and $(Y,d_Y)$ be metric spaces.

  Then $f:X -> Y$ is continuous iff $f^(-1)(U)$ is open in $X$ for all $U subset.eq Y$ open in $Y$.
]

#proof[

  ($=>$) Suppose $f$ is continuous. Let $U subset.eq Y$ be open in $Y$. \
  Let $x_0 in f^(-1)(U)$. Then there exists $epsilon > 0$ such that $B_d_Y (f(x_0),epsilon) subset.eq U$. This means that for all $y in B_d_Y (f(x_0),epsilon)$ we have that $d_Y (f(x_0),y) < epsilon$. Now by continuity there exists a $delta > 0$ such that for $x in X$ such that $d_X (x_,x_0) < delta$ then $d(f(x),f(x_0)) < epsilon$. However this means $x in B_d_X (x_0, delta) => f(x) in B_d_Y (f(x_0), epsilon) subset.eq U$ and so $x in f^(-1)(U)$ and thus we see that $B_d_X (x_0, delta) subset.eq f^(-1)(U)$. \
  Now as $x_0$ was arbitrary we have that every point in $f^(-1)(U)$ permits an open ball around it contained in $f^(-1)(U)$ and so $f^(-1)(U)$ is open.

  ($arrow.l.double$) Suppose $f^(-1)(U)$ is open for all open $U subset.eq Y$. Fix $x_0 in X$ and $epsilon > 0$. \
  Now we see since $B_d_Y (f(x_0), epsilon)$ is open in $Y$ that $f^(-1)(B_d_Y (f(x_0), epsilon))$ is open in $X$. \
  Now as $x_0 in f^(-1)(B_d_Y (f(x_0), epsilon))$ there exists a $delta > 0$ such that $B_d_X (x_0, delta) subset.eq f^(-1)(B_d_Y (f(x_0), epsilon))$. 
  This means that $x in B_d_X (x_0, delta) => f(x) in B_d_Y (f(x_0), epsilon)$ and so $f$ is continuous.
]

This leads us to our new goal of defining what open sets are without a metric.\
First we discuss some basic properties of open sets in metric spaces.

#proposition[
  Let $(X,d)$ be a metric space. \
  + $diameter, X$ are open
  + If $U_i$ is open for all $i in I$, then $display(union.big_(i in I)) U_i$ is open
  + If $U_i$ is open for all $i in {1, dots, n}$, then $display(inter.big_(i=1)^n) U_i$ is open
]
#proof[
  + See @X_and_diameter_are_open
  + Each $U_i$ is a union of open balls so $display(union.big_(i in I)) U_i$ is a union of open balls and hence is open.
  + Let $U_1, dots, U_n$ be a collection of open sets. Now for $x in display(inter.big_(i=1)^n) U_i$ we have that for each $i in {1,dots,n}$ that $x in U_i$ and as each $U_i$ is open there exists a $r_i > 0$ such that $B(x,r_i) subset.eq U_i$. Now taking $r = display(min_(1 <= i <= n)) r_i$ we have that $B(x,r) subset.eq U_i$ for all $i$ and so $B(x,r) subset.eq display(inter.big_(i in I)) U_i$ and so $display(inter.big_(i in I)) U_i$ is open.
]

#remark[
  In general the infinite intersection of open sets is not open.

  For example in $bb(R)$ take $U_n = (1/n,1/n)$. Then $display(inter.big_(i=1)^n U_n = {0})$ which is not open.
]

#pagebreak()

== Topological Spaces

#definition[
  Let $X$ be a set. A topology on $X$ is a collection $tau$ of subsets of $X$ satisfying

  + $diameter, X in tau$
  + If $U_i in tau$ for all $i in I$, then $display(union.big_(i in I)) U_i in tau$
  + If $U_i in tau$ for all $i in {1, dots, n}$, then $display(inter.big_(i=1)^n) U_i in tau$

  Elements of $tau$ are called open sets. We say that $(X, tau)$ is a topological space.
]

#example[
  #underline[*Metric Topology*]\
  Let $(X,d)$ be a metric space. $ tau_d = {U subset.eq X : forall x in U " " exists r > 0 " " B_d (x,r) subset.eq U} $ is a topology.
]

We see that $bb(R)$ with the usual metric induces the usual topology of $bb(R)$ where open sets are the union of open intervals.

#definition[
  A topological space $(X,tau)$ is metrizable iff there is a metric $d$ on $X$ such that $tau = tau_d$.
]

#remark[
  The metric that induces $tau$ may not be unique. For example the metrics induced by a norm on a finite dimensional vector space all induce the same topology. (See MAT257 for the proof)
]

We now look at some common examples of topologies.

#example[
  
  + Indiscrete Topology on any set $X$: $tau_("indiscrete") = {diameter, X}$
    - The captures the idea of a "smallest" topology
  + Discrete Topology on any set $X$: $tau_("discrete") = cal(P)(X)$
    - The captures the idea of a "largest" topology
  + Co-finite topology on any set $X$: $tau_("co-finite") = {U subset.eq X: X \\ U "is finite"} union {diameter}$
  + Co-countable topology on any set $X$: \ $tau_("co-countable") = {U subset.eq X: X \\ U "is countable"} union {diameter}$
]

#proof[
  + Obvious
  + Obvious
  + + By definition $diameter in tau_("co-finite")$.\
      Additionally $diameter$ is finite so $X = X \\ diameter$ and so $X in tau_("co-finite")$.\
    + Let $U_i in tau_("co-finite")$ for $i in I$ (WLOG $U_i != diameter$). Then we have that
      $ X \\ union.big_(i in I) U_i = inter.big_(i in I) (X \\ U_i) $
      is finite as the intersection of finite sets is finite and so $display(union.big_(i in I) U_i in tau_("co-finite"))$.
    + Let $U_i in tau_("co-finite")$ for $i in {1,dots,n}$ (WLOG $U_i != diameter$). Then we have that
      $ X \\ inter.big_(i=1)^n U_i = union.big_(i=1)^n (X \\ U_i) $
      is finite as the finite union of finite sets is finite and so $display(inter.big_(i=1)^n U_i in tau_("co-finite"))$.
  + Identical to the previous with the word finite substituted for countable.
]

#proposition[
  The discrete topology is metrizable by the discrete metric.
]

#proof[
  
  Let $tau_("discrete")$ be the discrete topology on $X$ and let $tau_d$ be the topology induced by the discrete metric on $X$.

  Now it is clear that $tau_d subset.eq tau_("discrete")$ as every collection of subsets of $X$ is a subset of the power set of $X$.

  Now to show that $tau_("discrete") subset.eq tau_d$. It suffices to show that $tau_d$ contains all the singletons.

  Let $x in X$. Then we see that $B(x,1/2) = {x}$ is open in $tau_d$ thus $tau_("discrete") subset.eq tau_d$ and so the discrete topology is metrizable.
]

#proposition[
  Generally the indiscrete topology is not metrizable.
]

#proof[
  
  In the case $|X| = 1$ then $tau_"indiscrete" = tau_"discrete"$ and so is metrizable.\
  Otherwise if $|X| >= 2$ suppose for the sake of contradiction there exists a metric $d$ such that it induces the indiscrete topology.
  Let $x,y in X$ then by picking $r = d(x,y)$ we see that $B(x,r)$ is open and $x in B(x,r)$ but $y in.not B(x,r)$. However this implies $B(x,r) != diameter$ and $B(x,r) != X$. Thus $d$ cannot induce the indiscrete metric.
]

#remark[
  We have actually shown something much stronger. Namely that metrizable topologies must be Hausdorff.
]

#definition[
  Let $tau$ and $tau'$ be two topologies on $X$. We say that $tau'$ is finer than $tau$ and that $tau$ is coarser than $tau'$ iff $tau subset.eq tau'$.

  We say that $tau$ and $tau'$ are comparable iff either $tau subset.eq tau'$ or $tau' subset.eq tau$.
]

#example[
  - $tau_"co-finite" subset.eq tau_"co-countable"$
  - For any topology $tau$, $tau_"indiscrete" subset.eq tau subset.eq tau_"discrete"$
]

#lemma[
  Let $d$ and $d'$ be two metrics on $X$.
  $ tau_d subset.eq tau_d' "iff" forall x in X " " forall epsilon > 0 " " exists delta > 0 "s.t" B_d' (x, delta) subset.eq B_d (x,epsilon) $
] <finer-topology-ball-criterion>

#proof[

  ($=>$) Suppose that $tau_d subset.eq tau_d'$. Fix $x in X$ and let $epsilon > 0$. Now as $B_d (x,epsilon) in tau_d subset.eq tau_d'$. Now by @open-set-ball-equivalence we get there exists a $delta > 0$ such that $B_d' (x, delta) subset.eq B_d (x,epsilon)$.

  ($arrow.l.double$) Suppose that for all $x in X$ and for all $epsilon > 0$ there exists $delta > 0$ such that $B_d' (x, delta) subset.eq B_d (x,epsilon)$. Let $U in tau_d$. Fix $x in U$. Then by @open-set-ball-equivalence there exists $epsilon > 0$ such that $B_d (x,epsilon) subset.eq U$. Now there exists $delta > 0$ such that $B_d' (x,delta) subset.eq B_d (x,epsilon) subset.eq U$. However this implies by @open-set-ball-equivalence that $U in tau_d'$ and so we have that $tau_d subset.eq tau_d'$.
]

#corollary[
  Let $d$ and $d'$ be two metrics on $X$. If there exists a constant $alpha > 0$ such that for all $x,y in X$
  $ d(x,y) <= alpha dot d'(x,y) $
  Then $tau_d subset.eq tau_d'$
]

#proof[

  Let $x in X$ and $epsilon > 0$. We see by fixing $delta = epsilon/alpha$ so that if $d'(x,y) < delta$ then
  $ d(x,y) &<= alpha dot d'(x,y)\
  &< alpha dot epsilon/alpha\
  &= epsilon $

  Thus we see that $y in B_d' (x, delta) => y in B_d (x, epsilon)$.
  We get by rewriting this as $B_d' (x, delta) subset.eq B_d (x,epsilon)$ that by @finer-topology-ball-criterion this implies that $tau_d subset.eq tau_d'$.
]

#pagebreak()

== Bases for a Topology

In a metric space, open sets are defined by open balls.

In a sense we can say that open balls "generate" all open sets, or in other words, that open balls are "basic open sets".

We want to generalize this for arbitrary topological spaces.

In a metric space $(X,d)$, $U subset.eq X$ is open iff $forall x in U$ $exists r > 0$ $B(x,r) subset.eq U$.

#definition[
  Let $X$ be a set. A collection $cal(B)$ of subsets of $X$ satisfying
  + $forall x in X$ $exists B in cal(B)$ $x in B$
  + $forall B_1, B_2 in cal(B)$ $forall x in X$ $(x in B_1 inter B_2 => exists B in cal(B) "s.t" x in B subset.eq B_1 inter B_2)$
  is called a basis for a topology on $X$. Elements of $cal(B)$ are called basic open sets. $tau_cal(B)$ is called the topology generated by $cal(B)$.
]

We will verify that bases in topological spaces induce topologies in the same way open balls in metric spaces induce topologies.

#proposition[
  Let $X$ be a set. Then $ tau_cal(B) = {U subset.eq X : forall x in U " " exists B in cal(B) " " x in B subset.eq U} $

  is a topology on $X$.
]

#proof[
  
  + $diameter in tau_cal(B)$ is vacuously true. 
    As every point in $x$ is contained in some basic open set we have that $X in tau_cal(B)$.
  + Let $U_i in tau_cal(B)$ for $i in I$. Now fix some $x in display(union.big_(i in I)) U_i$. Then there is some $i$ such that $x in U_i$. As such there exists a $B in cal(B)$ such that $x in B subset.eq U_i subset.eq display(union.big_(i in I)) U_i$ and so $display(union.big_(i in I)) U_i$ is open.
  + It suffices to show the intersection of 2 open sets is open. Let $U$ and $V$ be open sets in $tau_cal(B)$. Let $x in U inter V$. Then there exists $B_1 in cal(B)$ such that $x in B_1 subset.eq U$ and there exists $B_2$ such that $x in B_2 subset.eq V$. Thus we have $x in B_1 inter B_2$. Now by definition there exists some $B in cal(B)$ such that $x in B subset.eq B_1 inter B_2 subset.eq U inter V$. Thus we see that $U inter V$ is open.
]

#underline[*Why do we care about bases?*]

Oftentimes it is easier to discuss topologies in terms of the bases that induces them. Additionally many topological concepts are defined in terms of basic open sets.

#lemma[
  Let $cal(B)$ and $cal(B)'$ be two bases for topologies on $X$. Then the following are equivalent
  + $tau_cal(B)'$ is finer than $tau_cal(B)$ ($tau_cal(B) subset.eq tau_cal(B)'$)
  + $forall x in X$ $forall B in cal(B)$ ($x in B => exists B' in cal(B)' " " x in B' subset.eq B$)
]

#proof[
  
  (i) $=>$ (ii)

  Suppose that $tau_cal(B)'$ is finer than $tau_cal(B)$. Now any $B in cal(B)$ is open in $tau_cal(B)$ and as such it is open in $tau_cal(B)'$. Let $x in B$. Then by the definition of a basis we get that there exists a $B' in cal(B)'$ such that $x in B' subset.eq B$.

  (ii) $=>$ (i)

  Suppose that $forall x in X$ $forall B in cal(B)$ ($x in B => exists B' in cal(B)' " " x in B' subset.eq B$). Let $U$ be an open set in $tau_cal(B)$ and let $x in U$. Then there exists a $B in cal(B)$ such that $x in B subset.eq U$. Now by the assumption we have there exists $B' in cal(B)'$ such that $x in B' subset.eq B subset.eq U$. However this implies that $U$ is open in $tau_cal(B)'$ and so $tau_cal(B) subset.eq tau_cal(B)'$.
]

#lemma[
  If $cal(B)$ is a basis for a topology on $X$, then $tau_cal(B)$ is the collection of all unions of elements in $cal(B)$.
] <topology-is-union-of-basis-elements>

#proof[

  Let $U$ be an open set. Then for all $x in U$ there exists a $B_x in cal(B)$ such that $x in B_x subset.eq U$. Now we see that
  $display(union.big_(x in U) B_x = U)$ and so $U$ can be written as the union of elements in $cal(B)$.

  Conversely we see that every union of elements in $cal(B)$ is automatically in $tau_cal(B)$ as $cal(B) subset.eq tau_cal(B)$ and a topology is closed under arbitrary union.
]

#lemma[
  Let $(X,tau)$ be a topological space. If $cal(C)$ is a collection of open subsets of $X$ such that
  $ forall U in tau " " forall x in U " " exists c in cal(C) " " x in C subset.eq U $
  Then, $cal(C)$ is a basis for a topology on $X$ and $tau_cal(C) = tau$.
]

#proof[

  First we verify that $cal(C)$ is a basis. Since $X$ is an open set we have that for every $x in X$ there exists a $C in cal(C)$ such that $x in C$. Thus $cal(C)$ covers $X$.

  Next we see given $C_1, C_2 in cal(C)$ that $C_1 inter C_2$ is open and so $C_1 inter C_2 in cal(C)$. Thus the intersection of basic open sets is a basic open set and thus contains a basic open set.

  Now we show this induces the same topology.

  Let $U in tau$. Then we have that for every $x in U$ that there exists a $C_x in cal(C)$ such that $x in C_x subset.eq U$. As such we have that $U = display(union.big_(x in U) C_x)$ and so is the union of basic open sets and so $U$ is open in $tau_cal(C)$.

  Now take some open set $U in tau_cal(C)$. Then by @topology-is-union-of-basis-elements we see that $U$ is the union of basic open sets which are all open in $tau$ and so $U$ is open in $tau$. As such we see that $tau_cal(C) = tau$.
]

#definition[
  We say that a topological space $(X,tau)$ is second countable iff it has a countable basis.
]

#example[
  + Bases for $bb(R)_"usual":$
    - $cal(B)_1 = {(a,b): a,b in bb(R) "s.t" a<b}$ is an uncountable basis
    - $cal(B)_2 = {(p,q): p,q in bb(Q) "s.t" p<q}$ is a countable basis
  + Fix some $x in bb(R)$ then $cal(B)_x = {(x-r, x+r): r > 0}$ is a basis for a topology on $bb(R)$ but $tau_cal(B)_x != tau_"usual"$.
  + Basis for discrete topology: $cal(B) = {{x}: x in X}$. One notes that $(X,tau_"discrete")$ is second countable when $X$ is countable.
]

#pagebreak()

= Important Topologies

== Lower Limit Topology

#example[
  On $bb(R)$ consider the collection
  $ cal(B)_ell := { [a, b) : a, b in bb(R), a < b } $

  This $cal(B)_ell$ forms a basis for a topology on $bb(R)$.
  This topology, denoted $tau_ell$, is called #underline[Lower Limit topology] on $bb(R)$.
  The space $bb(R)_ell = (bb(R), tau_ell)$ is called #underline[Sorgenfrey Line].
]

#proposition[
  $tau_ell$ is strictly finer than $tau_"usual"$. That is $tau_"usual" subset.neq tau_ell$
]

#proof[

  ($subset.eq$) Consider $(a,b) in cal(B)_"usual"$. Let $x in (a,b)$ we see $x in [x,b) subset.eq (a,b)$. Thus $tau_"usual" subset.eq tau_ell$.

  ($subset.neq$) Consider $[0,1) in tau_ell$ but $[0,1) in.not tau_"usual"$.
]

#proposition[
  $bb(R)_ell$ is not second countable
] <R_ell_not_second_countable>

#proof[
  
  Fix any basis $cal(B)$ for $tau_ell$ We construct an injective map $bb(R) -> cal(B)$. Fix $x in bb(R)$ and consider $U_x = [x,x+1) in tau_ell$. Since $cal(B)$ is a basis we can pick some $B_x in cal(B)$ such that $x in B_x subset.eq U_x$.
  
  We show that $x mapsto B_x$ is injective.

  Suppose $x != y$ and WLOG suppose $x < y$. Now note that the minimal element of some $B_x$ is $x$ by construction. As such we see that $x in.not B_y$ thus $B_x != B_y$ and so the mapping is injective.
]

#pagebreak()

== Subspace Topology

#definition[
  Let $(X, tau)$ be a topological space and $Y subset.eq X$. Then
  $ tau_Y = {U inter Y : U in tau} $
  is a topology on $Y$. This topology is called the subspace topology on $Y$.
]

#proposition[
  If $cal(B)$ is a basis for $tau$. Then
  $ cal(B)_Y = {B inter Y : B in cal(B)} $
  is a basis for $tau_Y$.
]

#proof[
  
  Let $V$ open in $Y$ and $x in V$. Then $V = U inter Y$ where $U$ open in $X$. We see that there exists $B in cal(B)$ such that $x in B subset.eq U$ thus $x in B inter Y subset.eq V$.
]

#proposition[
  If $Y$ is open in $X$ then every open set in $Y$ with the subspace topology is open in $X$.
]

#proof[
  
  The open set in $Y$ is the intersection of an open set in $X$ and $Y$ which is open in $X$ and the intersection of 2 open sets in $X$ is open.
]

#pagebreak()

== Order Topology

#definition[
  Let $X$ be a set. A total order on (also known as linear order) $X$ is a binary relation $<$ satisfying:
  + (Irreflexivity) $forall x in X " " not (x < x)$
  + (Comparability) $forall x,y in X " " (x=y " or " x<y " or " y<x)$
  + (Transitivity) $forall x,y,z in X " " (x<y " and " y<z => x<z)$
  $(X, <)$ is called a totally ordered set.
]

#proposition[
  If $(X, <)$ is totally ordered with more than one point, then the collection $cal(B)_< $ consisting of sets of the form:
  + $(a,b)_< := {x in X: a<x<b}$, $a,b in X$ such that $a<b$
  + $(-infinity,b)_< := {x in X: x<b}$, $b in X$
  + $(a,infinity)_< := {x in X: a<x}$, $a in X$

  is a basis for a topology on $X$.
]

#definition[
  A totally ordered $(X, <)$ is called well ordered iff every non-empty subset $S subset.eq X$ has a minimum with respect to $<$
]

#theorem[
  There exists a (unique) uncountable well-ordered set called $omega_1$ with the following property.
  $ forall alpha in omega_1 " " "pred"(alpha) = {beta in omega_1 : beta < alpha} "is countable" $
]

#pagebreak()

== Box and Product Topology

Before we discuss topologies on the cartesian product of sets we must define the cartesian product.

We form the cartesian product of finitely many sets say $X_1, dots, X_n$ by saying the elements are $n$-tuples.
We have that $(x_1, dots, x_n) in X_1 times dots.c times X_n$ where each $x_j in X_j$. Of course we think of $n$-tuples as a point in $n$ dimensions.

#definition[
  Suppose $(X, tau_X)$ and $(Y, tau_Y)$ are two topological spaces. Then
  $ cal(B)_"prod" = {U times V : U in tau_X "and" V in tau_Y} $
  is not a topology but it is a basis for one. We denote the topology this basis induces as the finite product topology.
]

We prove that $cal(B)_"prod"$ is a basis for a topology.

#proof[
  
  $X$ and $Y$ are both open thus $X times Y in cal(B)_"prod"$ and so for all $(x,y) in X times Y$. There is some open set $U$, namely $U = X times Y$ such that $(x,y) in U$.

  Now suppose $U_1 times V_1, U_2 times V_2 in cal(B)_"prod"$ and let $(x,y) in (U_1 times V_1) inter (U_2 times V_2)$. Then $x in U_1 inter U_2$ and $y in V_1 inter V_2$. Now there exists $U$ open in $X$ such that $x in U subset.eq U_1 inter U_2$ and there exists $V$ open in $Y$ such that $y in V subset.eq V_1 inter V_2$. However then we have that $(x,y) in U times V subset.eq (U_1 times V_1) inter (U_2 times V_2)$ and $U times V$ is open in $cal(B)_"prod"$ thus $cal(B)_"prod"$ is a basis.
]

Generalizing to the case of the product of finitely many space is trivial by induction.

The countably infinite generalization of $n$-tuples are sequences $(x_1, x_2, dots)$ where each $x_j in X_j$. In other words we can say that sequences are functions
$ f:bb(N) -> display(union.big_(j in bb(N)) X_j) \ j mapsto x_j in X_j $

Now for an arbitrary collection of spaces ${X_alpha}$ where each $alpha in J$ for some index set $J$. We can define the arbitrary cartesian product of ${X_alpha}$ as the set of all functions
$ x:J -> union.big_(alpha in J) X_alpha \ alpha mapsto x_alpha $
in this case $x in display(product_(alpha in J) X_alpha)$

Now convince yourself in the case $J={1,dots,n}$ this is the same as the usual finite product.

#definition[
  For each $beta in J$ we define the $beta$'th projection map $pi_beta$ as the function
  $ pi_beta : product_(alpha in J) X_alpha -> X_beta \ x mapsto x_beta $
  where $x_beta = x(beta)$ is the $beta$'th coordinate of $x$.
]

Now how should we define a topology on the arbitrary product of sets?

First we will try the naive idea of just taking the collection of arbitrary boxes.

#definition[
  Let $X = display(product_(alpha in J) X_alpha)$. We define the box topology on $X$ as the topology generated by the following basis
  $ cal(B) = {product_(alpha in J) U_alpha : U_alpha "open in" X_alpha} $
]

The proof that this is a basis is very similar to the proof in the finite case.

#proposition[
  Let $U_beta subset.eq X_beta$ be an open set. Then $ pi_beta^(-1)(U_beta) = product_(alpha in J) U_alpha "where" U_alpha = cases(U_beta "if" alpha = beta, X_alpha "if" alpha != beta) $

  Moreover as this is a product of open sets we have $pi_beta$ is continuous in the box topology.
]

#definition[
   Let $f: X -> display(product_(alpha in J) Y_alpha)$. We define the coordinate functions of $f$ as $f_beta: X -> Y_beta$ defined by $f_beta = pi_beta compose f$. In essence $f_beta$ tells how inputs to $f$ act upon on the $beta$'th coordinate. As such we can write $ f(x) = product_(alpha in J) f_alpha (x) $
]

We see that if $f$ is continuous then all the coordinate functions are also continuous.

Is the reverse true? Unfortunately it is not.

#definition[
  We define $bb(R)^omega$ as the countable product of $bb(R)$. Note that this is the set of real valued sequences.
]

#example[
  Consider attempting to embed $bb(R)$ into $bb(R)^omega$ by the injective map $ f: bb(R) arrow.hook bb(R)^omega \ x mapsto (x,x,dots) $

  Clearly each coordinate function $f_alpha = (x mapsto x)$ is continuous.

  Now consider the preimage under $f$ of $ B = product_(n in bb(N)) (-1/n, 1/n) $

  $B$ is a basic open set in the box topology but $f^(-1)(B) = {0}$ which is not open.
]

This leads us to discuss an alternative topology.

#definition[
  The product topology on $product X_alpha$ is defined to be the coarsest topology for which the projection maps $pi_alpha$ are all continuous.
]

#proposition[
  The box topology contains the product topology.
]

#proof[
  
  The projection maps are continuous in the box topology and so by definition the product topology is coarser and hence is contained in the box topology.
]

This definition of the product topology feels very abstract. What are the basis elements that generate this?

We see that as the preimage of the projection maps is open that the sets of the form $ product_(alpha in J) U_alpha "where" U_alpha = cases(U_beta "if" alpha = beta, X_alpha "if" alpha != beta) $ for some $beta in J$ are open.

Now this set forms a subbasis of $X$ and so this generates the topology given by taking finite intersections.

That is all open sets are of the form $ product_(alpha in J) U_alpha "where" U_alpha = cases(U_beta "if" alpha in {beta_1,dots,beta_n}, X_alpha "if" alpha in.not {beta_1,dots,beta_n}) $ for some ${beta_1,dots,beta_n} subset.eq J$. In other words open sets are of the form $product U_alpha$ where $U_alpha = X_alpha$ for all but finitely many $alpha$.

#proposition[
  For finite products the box topology equals the product topology
]

#proof[
  
  Using the previous criterion of the product topology we see that for finite products it is equivalent to saying open sets are those which are the product of open sets in each coordinate and hence is exactly the box topology.
]

#theorem[
  For $f:A -> product X_alpha$ is continuous in the product topology on $product X_alpha$ if and only if the coordinate function $f_beta = pi_beta compose f$ is continuous for each $beta in J$.
]

#proof[

  The forward direction is obvious as $f$ and $pi_beta$ are continuous and the composition of continuous functions is continuous.

  Now for the reverse direction we have that for any open set $U$ in $product X_alpha$ we have that $U = product U_alpha$ where for all but finitely many $alpha$ we have that $U_alpha = X_alpha$.

  As such we have that
  $ f^(-1)(U) = f^(-1)(product_(alpha in J) U_alpha) &= f^(-1)(inter.big_(alpha in J) pi^(-1)_alpha (U_alpha)) \
  &= f^(-1)(inter.big_(i=1)^n pi^(-1)_beta_i (U_beta_i)) \
  &= inter.big_(i=1)^n underbrace((f^(-1) compose pi^(-1)_beta_i), f^(-1)_beta_i) (U_beta_i) $

  Now each $f_beta_i$ is continuous so $f^(-1)_beta_i (U_beta_i)$ is open and hence $f^(-1)(U)$ is the finite intersection of open sets and hence is open and so $f$ is continuous.
]

#pagebreak()

= Closure and Interior

== Closed Sets

#definition[
  Let $X$ be a topological space. We say $F subset.eq X$ is closed in $X$ iff $X backslash F$ is open in $X$.
]

#proposition[
  + $diameter, X$ are closed.
  + If $F_i$ is closed for all $i in I$, then $display(inter.big_(i in I)) F_i$ is closed.
  + If $F_1, ..., F_n$ are closed, then $display(union.big_(i=1)^n) F_i$ is closed.
]

#proof[
  
  By axioms of a topology and de Morgan's laws

  $ X backslash display(inter.big_(i in I)) F_i = union.big_(i in I) underbrace((X backslash F_i),"open") "is open" => display(inter.big_(i in I)) F_i "is closed" $
]

#theorem[
  Let $X$ and $Y$ be topological spaces and $f: X -> Y$. Then
  $ f "is continuous" <==> f^(-1)(E) "is closed in" X "for all" E subset.eq Y "closed in" Y $
]

#proof[

  ($=>$) Fix $E subset.eq Y$ closed in $Y$. Then $U = Y \\ E$ is open in $Y$.

  Now $X \\ f^(-1)(E) = f^(-1)(Y \\ E) = f^(-1)(U)$ is open in $X$ by continuity.
  
  Thus $f^(-1)(E)$ is closed in $X$.

  ($arrow.l.double$) Fix open $U subset.eq Y$. Then $E = Y \\ U$ is closed in $Y$.

  Now $X \\ f^(-1)(U) = f^(-1)(Y \\ U) = f^(-1)(E)$ is closed in $X$ by assumption.
  
  Thus $f^(-1)(U)$ is open in $X$ and so $f$ is continuous.
]

#example[
  + In $bb(R)_"usual"$:
    - $[a,b)$ is not open and not closed.
    - $[a,b]$ is closed since $bb(R) backslash [a,b] = (-oo, a) union (b, oo)$ is open.
    - ${a}$ is closed since $bb(R) backslash {a} = (-oo, a) union (a, oo)$ is open.
  + In $(X, tau_"co-finite")$: Closed sets are finite sets and $X$. (Complements of finite sets are open).
  + In $(X, tau_"discrete")$: Every set is closed.
  + In $(X, tau_"indiscrete")$: Only closed sets are $diameter$ and $X$.
]

#proposition[
  Let $X$ be a topological space and $Y subset.eq X$ be a subspace.

  $ E subset.eq Y "is closed in" Y <==> E = F inter Y "for some" F subset.eq X "closed in" X $
]

#corollary[
  If $Y subset.eq X$ is closed in $X$ then every closed set in $Y$ is closed in $X$.
]

#pagebreak()

== Closure

Recall that in a metric space $(X,d)$ that $U subset.eq X$ is open iff for all $x in U$ there exists $r > 0$ such that $B_d (x,r) subset.eq U$.
Now note the following chain of equivalencies

$ "A set" F subset.eq X "is closed" &<==> X \\ F "is open" \
&<==> forall x in X \\ F " " exists r > 0 " " B_d (x,r) subset.eq X \\ F \
&<==> forall x in X (x in.not F => exists r > 0 " " B_d (x,r) subset.eq X \\ F) \
&<==> forall x in X (x in.not F => exists r > 0 " " B_d(x,r) inter F = diameter) \
&<==> forall x in X \(underbrace(forall r > 0 " " B_d (x,r) inter F != diameter, x "is a closure point") => x in F\)$

We will generalize this to topological spaces.

#lemma[
  Let $X$ be a topological space.
  $ A subset.eq X "is open" <==> forall x in A " " exists U "open s.t" x in U subset.eq A $
]

#proof[
  
  ($=>$) Take $A=U$.

  ($arrow.l.double$) For all $x in A$ exists $U_x$ open such that $x in U_x subset.eq A$. Then $A = display(union.big_(x in A)) U_x$ is open.
]

#remark[
  The general strategy in translating things defined in terms of open sets in metric spaces to open sets in topological spaces is to replace "open ball centered at $x$ in the metric space" with "open neighborhood of $x$ in the topological space". 
]

#definition[
  Let $X$ be a topological space and $A subset.eq X$ we say that $x in X$ is a closure point of $A$ iff for every open $U subset.eq X$ s.t $x in U$, $U inter A != diameter$.

  The set of all closure points of $A$ is called the closure of $A$ denoted as $"cl"_X (A)$.
]

#proposition[
  Let $X$ be a topological space and $A subset.eq X$.

  + $"cl"_X (A)$ is the smallest closed set that contains $A$.
  + $A$ is closed iff $"cl"_X (A) = A$.
  + If $cal(B)$ is a basis for $X$ then
  $ "cl"_X (A) = {x in X : forall B in cal(B) (x in B => B inter A != diameter)} $
]

#example[
  
  In $bb(R)_"usual"$
  + $"cl"(a,b) = [a,b]$
  + $A = {1/n : n in bb(N)}$ then $"cl"(A) = A union {0}$
  + $"cl"(bb(Q)) = bb(R)$
]

#proposition[
  Some properties of closure
  + $"cl"("cl"(A)) = "cl"(A)$
  + $A subset.eq B => "cl"(A) subset.eq "cl"(B)$
  + $"cl"(A union B) = "cl"(A) union "cl"(B)$
]

#definition[
  Let $X$ be a topological space and $D subset.eq X$. We say that $D$ is dense in $X$ iff $"cl"_X (D) = X$.
]

#definition[
  We say that $X$ is separable iff there is a countable dense subset.
]

#proposition[
  Every second countable space is separable.
] <second_countable_implies_separable>

#proof[
  
  Let $D$ be a set containing a point picked from each element in the basis.
]

Unfortunately the converse is not true. Consider the following counterexample.

#example[
  $bb(R)_ell$ is not second countable but it is separable.

  We saw in @R_ell_not_second_countable that $bb(R)_ell$ is not second countable. We show that it is separable.

  We see that $"cl"_bb(R)_ell (bb(Q)) = bb(R)$ as for any $x in bb(R)$ and any open set $U subset.eq bb(R)$ such that $x in U$ we have that there exists some $r in bb(R)$ where $r > x$ and $[x,r) subset.eq U$. Now by the density of the rationals in the reals we have that there exists some $p in bb(Q)$ such that $x <= p < r$ and so $p in [x,r) subset.eq U$ and so $U inter bb(Q) != diameter$. Thus $bb(R) subset.eq "cl"_bb(R)_ell (bb(Q))$ and trivially $"cl"_bb(R)_ell (bb(Q)) subset.eq bb(R)$ thus we obtain $"cl"_bb(R)_ell (bb(Q)) = bb(R)$.
]

#proposition[
  If $(X,d)$ is a metric space, then $X$ is separable iff $X$ is second countable.
]

#proof[
  
  Clearly by @second_countable_implies_separable we have that if $X$ is second countable then $X$ is separable.

  Now suppose that $X$ is separable. Let $D subset.eq X$ be a dense countable set.

  Consider $cal(B) = {B(x,r) : x in D "and" r in bb(Q)^+}$. Clearly $cal(B)$ is countable.

  Now let $U$ be an arbitrary open set and $x in U$. Let $r > 0$ be such that $B(x,r) subset.eq U$. Since $D$ is dense in $X$ we can find some $x_0 in D inter B(x,r/2)$. Now let $r_0 in bb(Q)^+$ such that $d(x,x_0) < r_0 < r/2$.

  Now we show that $x in B(x_0, r_0) subset.eq B(x,r) subset.eq U$.

  Clearly $x in B(x_0, r_0)$. Now let $y in B(x_0,r_0)$ then $d(x_0,y) < r_0$. Now by triangle inequality
  $ d(x,y) &<= d(x,x_0) + d(x_0, y) \
  &< r/2 + r_0 \
  &< r/2 + r/2 \
  &= r $
  Thus $y in B(x,r) subset.eq U$ and so $cal(B)$ forms a countable basis and hence $X$ is second countable.
]

#pagebreak()

== Interior

There is a dual operator to the closure called the interior.

#definition[
  Let $X$ be a topological space and $A subset.eq X$ we say that $x in X$ is an interior point of $A$ iff there exists an open $U subset.eq X$ s.t $x in U subset.eq A$.

  The set of all interior points of $A$ is called the interior of $A$ denoted as $"int"_X (A)$.
]

#proposition[
  Let $X$ be a topological space and $A subset.eq X$.

  + $"int"_X (A)$ is the largest open set contained in $A$.
  + $A$ is open iff $"int"_X (A) = A$.
]

#pagebreak()

== Boundary

#definition[
  Let $X$ be a topological space. Given $A subset.eq X$, we define the boundary of $A$ as the set
  $ partial A = "cl"_X (A) inter "cl"_X (X \\ A) $
]

#proposition[
  Let $X$ be a topological space and $A subset.eq X$. Then the closure is the disjoint union of the interior and boundary. Namely that
  $ "int"_X (A) inter partial A = diameter "and" "cl"_X (A) = "int"_X (A) union partial A $
]

#proof[
  
  See Assignment 2 Problem 1a
]

#proposition[
  $partial A = diameter$ if and only if $A$ is both open and closed.
]

#proof[
  
  See Assignment 2 Problem 1b
]

#proposition[
  Let $U subset.eq X$. $U$ is open if and only if $partial U = "cl"_X (U) backslash U$.
]

#proof[
  
  See Assignment 2 Problem 1c
]

#pagebreak()

= Functions on Topological Spaces

== Continuous Functions

#theorem[
  Let $X,Y$ be topological spaces and $f: X -> Y$ then the following are equivalent
  + Preimage of open sets under $f$ are open. ($f$ is continuous)
  + Preimage of closed sets under $f$ are closed.
  + $forall A subset.eq X$ $f(overline(A)) subset.eq overline(f(A))$
]

#proof[
  
  We already know (i) and (ii) are equivalent

  (iii) $=>$ (ii)

  Let $E subset.eq Y$ be closed in $Y$ and fix $A = f^(-1)(E)$. Now it suffices to show that $overline(A) subset.eq A$. Now then we have $f(A) = E$. Thus $overline(f(A)) = E$ as $E$ is closed. However by (iii) we have that $f(overline(A)) subset.eq overline(f(A)) = E$ and so $f(overline(A)) subset.eq E$ or equivalently $overline(A) subset.eq f^(-1)(E) = A$.

  (i) $=>$ (iii)

  Let $A subset.eq X$. Consider $Y \\ overline(f(A))$ which is open. We see that $f^(-1)(Y \\ overline(f(A)))$ is open by (i) which means that for $x in f^(-1)(Y \\ overline(f(A)))$ there is some open set $U subset.eq f^(-1)(Y \\ overline(f(A)))$ such that $x in U$. Now consider $x in overline(A)$. By definition every open set $U$ such that $x in U$ must intersect $A$ and so $U$ cannot be contained $f^(-1)(Y \\ overline(f(A)))$. As such we have that $x in.not f^(-1)(Y \\ overline(f(A)))$. Thus $f(x) in.not Y \\ overline(f(A))$ which means that $f(x) in overline(f(A))$ and hence $f(overline(A)) subset.eq overline(f(A))$.
]

We now go over some basic properties of continuous functions.

#proposition[
  Constant functions are continuous.
]

#proof[
  
  $f^(-1)(U)$ is either $diameter$ or $X$ which are both open and hence the preimage of any open set is open.
]

#proposition[
  If $f:X -> Y$ and $g:Y -> Z$ are continuous then $g compose f$ is continuous.
] <comp_cont_is_cont>

#proof[
  
  $(g compose f)^(-1)(U) = f^(-1)(g^(-1)(U))$. If $U$ is open then $g^(-1)(U)$ is open and so $f^(-1)(g^(-1)(U))$ is open and then $(g compose f)^(-1)(U)$ is open.
]

#proposition[
  If $f:X -> Y$ is continuous and $A subset.eq X$ then $f|_A: A -> Y$ is continuous.
] <restriction_of_cont_is_cont>

#proof[
  
  $(f|_A)^(-1)(U) = f^(-1)(U) inter A$. Thus the preimage of an open set under $f|_A$ is open in $A$.
]

#corollary[
  The inclusion map $i:A -> X$ for $A subset.eq X$ where $i(x) = x$ is continuous.
]

#proof[
  
  By @restriction_of_cont_is_cont and the fact that identity map is continuous.
]

#proposition[
  If $X = display(union.big_(alpha in Lambda)) U_alpha$ where $U_alpha$ is open in $X$ for all $alpha in Lambda$ and

  $f:X -> Y$ is such that $f|_U_alpha: U_alpha -> Y$ is continuous for all $alpha in Lambda$

  Then $f:X -> Y$ is continuous.
]

#proof[
  
  $f^(-1)(U) = display(union.big_(alpha in Lambda) (f|_U_alpha)^(-1) (U))$ is open as it is the union of open sets by the continuity of $f|_U_alpha$.
]

#proposition[
  If $f:X -> bb(R)$ and $g: Y -> bb(R)$ are continuous then \ $f+g$, $f dot g$ and $f/g$ (if $g(x) != 0$ for all $x in X$) are continuous.
]

#proof[
  
  Consider $h = (f,g)$ this is continuous by % impending tag.

  Now consider $(x,y) mapsto x+y$, $(x,y) mapsto x dot y$ and $(x,y) mapsto x/y$ where $y != 0$ which are continuous functions from $bb(R)^2 -> bb(R)$ (We can use the usual $epsilon-delta$ proof for this). Now composing each of these functions with $h$ we see that as the composition of continuous functions is continuous by @comp_cont_is_cont that $f+g$, $f dot g$ and $f/g$ are all continuous.
]

#theorem[(Pasting Lemma)

  Suppose $X = A union B$ where $A, B$ are closed in $X$.

  Let $f: A -> Y$ and $g: B -> Y$ be continuous functions.

  Assume that $f(x) = g(x)$ for all $x in A inter B$.

  Then, $h: X -> Y$ defined by $h(x) = display(cases(f(x) "if" x in A, g(x) "if" x in B))$ is continuous.
]

#proof[
  
  We see that if $x in A inter B$ that $f(x) = g(x)$ so $h(x)$ is well defined.

  Let $E subset.eq Y$ be closed. We show that $h^(-1)(E)$ is closed.

  Note that $h^(-1)(E) = f^(-1)(E) union g^(-1)(E)$. Now as $f$ and $g$ are continuous we have that $f^(-1)(E)$ and $g^(-1)(E)$ are closed and as the finite union of closed sets is closed we have that $h^(-1)(E)$ is closed.
]

#pagebreak()

== Homeomorphisms

#definition[
  Let $(X, tau_X)$ and $(Y, tau_Y)$ be topological spaces. \
  A homeomorphism is a map $f:X -> Y$ such that $f$ is bijective and both $f$ and $f^(-1)$ are continuous.

  We say that $(X, tau_X) tilde.equiv (Y,tau_Y))$ and that $X$ and $Y$ are homeomorphic.
]

#definition[
  An embedding is a function $f:X -> Y$ such that it is a homeomorphism to its image. Namely that $f:X -> f(X)$ is a homeomorphism. We write that In other words $X$ is homeomorphic to a subspace of $Y$. In this case we write $X arrow.hook Y$.
]

#example[
  + $bb(R) tilde.equiv (0,1)$ by $f(x) = 1/pi arctan(x) + 1/2$
  + $bb(R) arrow.hook bb(R)^2$ by $f(x) = (x,0)$
  + $f:bb(R) -> S^1$ given by $f(x) = (cos(x), sin(x))$ is a continuous bijection but $f^(-1)$ is not continuous and hence is not a homeomorphism
  + $bb(R)$ is homeomorphic to $S^1$ minus one point. See stereographic projection and Assignment 2 Problem 2.
]

#pagebreak()

= Sequences

== First Countable Spaces

#definition[
  Let $X$ be a topological space and $x in X$. A local basis at $x$ is a collection $cal(B)_x$ of open sets containing $x$ such that
  $ "For every open" U subset.eq X "if" x in U "then" exists B in cal(B)_x "such that" x in B subset.eq U $
]

#definition[
  We say that $X$ is first countable iff every $x in X$ has a countable basis.
]

#example[
  + Metric spaces are first countable: ${B(x,1/n): n in bb(N)}$ is a countable local basis at $x$.
  + Second countable spaces are first countable: If $cal(B)$ is a countable basis for $X$ then $cal(B)_x = {B in cal(B): x in B}$ is a countable local basis at $x$.
  + Uncountable discrete spaces are first countable (But clearly not second countable): $cal(B)_x = {{x}}$ is a finite local basis.
  + $bb(R)_ell$ is first countable: $cal(B)_x = {[x,x+1/n): n in bb(N)}$ is a countable local basis
  + $omega_1$ is first countable: For $alpha in omega_1$, $cal(B)_alpha = {(beta,alpha+1):beta in "pred"(alpha)}$
]

#example[
  $(X, tau_"co-finite")$ for uncountable $X$ is not first countable
]

#proof[

  Suppose for the sake of contradiction that for $x in X$ there is some countable local basis ${B_i: i in bb(N)}$. Then as each $B_i$ is open we have that $B_i = X \\ F_i$ where $F_i$ is finite. Now define $F = display(union.big_(i=1)^infinity F_i)$ which is the countable union of finite sets so is countable. Now we can fix $y in (X \\ {x}) \\ F$ which is uncountable and so $y in.not F_i$ for all $i in bb(N)$ which means that $y in B_i$ for all $i in bb(N)$. Now consider $X \\ {y}$ which is the complement of a finite set and so is an open neighborhood of $x$. Now as $y in B_i$ for all $i in bb(N)$ we see that $B_i subset.eq.not X \\ {y}$ for all $i in bb(N)$ but this contradicts the fact that ${B_i: i in bb(N)}$ is a local basis.
]

#lemma[
  If $x in X$ has a countable local basis then there is a countable local basis ${B'_n : n in bb(N)}$ at $x$ with the property that $forall n in bb(N)$ $B'_(n+1) subset.eq B'_n$.
] <decreasing_local_basis>

#proof[

  Suppose ${B_n : n in bb(N)}$ is a countable basis then define
  $ B'_n = inter.big_(i=1)^n B_n $
]

#pagebreak()

== Convergence

Recall from analysis that for $f: bb(R) -> bb(R)$
$ f "is continuous" <==> forall x in bb(R) " " (x_n -> x => f(x_n) -> f(x)) $

#definition[
  Let $X$ be a topological space. A sequence in $X$ is a function $f:bb(N) -> X$. We usually denote a sequence by its range ${x_n}_(n=1)^infinity$ where $x_n = f(n)$. We say ${x_n}_(n=1)^oo$ converges to $x$ iff for every open $U$ s.t. $x in U$ $exists N in bb(N)$ $forall n > N$ $x_n in U$.
]

#remark[
  Using our usual tricks, one sees that if $cal(B)$ is a basis for $X$ then $x_n -> x$ iff
  $ forall B in cal(B) " " (x in B => exists N in bb(N) " " forall n > N " " x_n in B) $
]

In particular if $(X,d)$ is a metric space then
$ x_n -> x "iff" forall epsilon > 0 " " exists N in bb(N) " " forall n > N " " x_n in B_d (x,epsilon) $

#theorem[
  Let $(X,d)$ be a metric space and $Y$ a topological space. Then
  $ f "is continuous" "iff" forall x in bb(R) "if" x_n -> x "then" f(x_n) -> f(x) $
] <cont_iff_limit_brought_inside>

#proof[
  
  ($=>$) Fix $x in X$ and suppose $x_n -> x$. We show that $f(x_n) -> f(x)$. Fix $V subset.eq Y$ open such that $f(x) in V$. Now $f^(-1)(V)$ is open and $x in f^(-1)(V)$ thus as $x_n -> x$ there exists $N in bb(N)$ such that for $n > N$ that $x_n in f^(-1)(V)$. This implies that for $n > N$ that $f(x_n) in V$ and thus $f(x_n) -> f(x)$.

  ($arrow.l.double$) Suppose that $forall x in bb(R) "if" x_n -> x "then" f(x_n) -> f(x)$. We show that $forall A subset.eq X$ that $f(overline(A)) subset.eq overline(f(A))$. Let $x in overline(A)$ now for each $n$ pick $x_n in A inter B(x,1/n)$. We see that $x_n -> x$ and so $f(x_n) -> f(x)$. Now as each $x_n in A$ we have that $f(x_n) in f(A)$. Now as such we see that any open set $U$ such that $f(x) in U$ will contain infinitely many points of the sequence $f(x_n)$ and so will have non empty intersection with $f(A)$ and thus $f(x) in overline(f(A))$.
]

We note some important details about this proof.

#proposition[
  Let $X$, $Y$ be topological spaces. Then for $f: X -> Y$
  $ f "is continuous" => forall x in bb(R) "if" x_n -> x "then" f(x_n) -> f(x) $
]

#proof[

  This is just the proof of the ($=>$) direction of @cont_iff_limit_brought_inside.
]

#proposition[
  Let $X$ be a topological space and $A subset.eq X$.

  If $x_n in A$ for all $n in bb(N)$ and $x_n -> x$ then $x in overline(A)$.
] <limiting_points_in_closure>

#proof[
  
  For all open $U$ such that $x in U$ we have that as $x_n -> x$ there exists $N in bb(N)$ such that for $n > N$ that $x_n in U$. However as $x_n in A$ this implies that $U inter A != diameter$ and so $x in overline(A)$.
]

#lemma[
  Let $X,Y$ be topological spaces. Assume that for all $A subset.eq X$
  $ overline(A) = {x in X : exists " " {x_n}_(n=1)^infinity subset.eq A " s.t. " x_n -> x} $
  Then
  $ f "is continuous" "iff" forall x in bb(R) "if" x_n -> x "then" f(x_n) -> f(x) $
]

#proof[

  First notice that in the statement about $overline(A)$ that by @limiting_points_in_closure that the $(subset.eq)$ is always true. Namely that the assumption in this lemma is that every point in $overline(A)$ has a sequence in $A$ that converges to that point. This is the key fact used in the proof of the ($arrow.l.double$) direction of @cont_iff_limit_brought_inside. The proof follows similarly.
]

#lemma[
  If $X$ is first countable then for all $A subset.eq X$
  $ overline(A) = {x in X : exists " " {x_n}_(n=1)^infinity subset.eq A " s.t. " x_n -> x} $
] <first_countable_then_frechet_urysohn>

#proof[

  The ($supset.eq$) direction is always true by @limiting_points_in_closure

  ($subset.eq$) For $x in overline(A)$. Fix a countable local decreasing basis of $x$ denoted ${B_n : n in bb(N)}$ by @decreasing_local_basis. Now we construct the sequence $x_n$ by picking $x_n in A inter B_n$. As $B_k subset.eq B_n$ for $k >= n$ we have that $x_k in B_n$ for $k >= n$. Now for any open neighborhood $U$ of $x$ there exists $N in bb(N)$ such that $B_N subset.eq U$ and so for $n > N$ we have that $x_n in B_N subset.eq U$.
]

#remark[
  If $X$ is a topological space such that $ forall A subset.eq X (x in overline(A) <=> exists {x_n} subset.eq A "s.t" x_n -> x) $ we say $X$ is Fréchet-Urysohn.
]

#remark[
  If $X$ is a topological space such that for all topological spaces $Y$ $ f "is continuous" "iff" forall x in bb(R) "if" x_n -> x "then" f(x_n) -> f(x) $ we say that $X$ is sequential.
]

Summarizing we get this chain of implications:

$ "X is metrizable" => "X is first countable" => "X is Fréchet-Urysohn" => "X is sequential" $

Now looking at some strange examples of sequences

#example[
  + In $(X,tau_"indiscrete")$ every sequence converges to every point.
  + In $(bb(R), tau_"co-finite")$ the sequence $1,2,3,dots$ converges to every point. To see this for any point $x in bb(R)$ and any open neighborhood $U$ of $x$ we have that only finitely many elements of $bb(R)$ are not in $U$. Say $N$ is the largest of these then for every $n > N$ we have $n in U$ and so the sequence converges to $x$.
]

Our goal now is to identify spaces for which it is true that convergent sequences converge to a unique point.

#proposition[
  Let $(X,d)$ be a metric space. Then sequences converge to a unique point.
] <convergence_is_unique_in_metric_space>

#proof[

  Suppose that $x_n -> x$ and $x_n -> y$ for $x != y$. Fix $r = d(x,y) > 0$ and let $U = B(x,r/2)$ and $V = B(y,r/2)$. Clearly $U inter V = diameter$. However as $x_n -> x$ there exists $N_x$ such that for $n > N_x$ we have that $x_n in U$. Similarly there exists $N_x$ such that for $n > N_y$ we have that $x_n in V$. Now for $N = "max"(N_x,N_y)$ we have for $n > N$ that $x_n in U$ and $x_n in V$ but this contradicts the fact that $U inter V = diameter$.
]

#pagebreak()

== Hausdorff Spaces

#definition[
  Let $X$ be a topological space. We say that $X$ is Hausdorff iff for all $x,y in X$ with $x != y$ there are open sets $U,V subset.eq X$ such that $x in U$, $y in V$ and $U inter V = diameter$.
]

#theorem[
  If $X$ is Hausdorff, then sequences converge to a unique point.
]

#proof[
  
  The proof of this is almost identical to the proof of @convergence_is_unique_in_metric_space.
]

#example[
  + Metric spaces are Hausdorff
  + Spaces with the order topology are Hausdorff (in particular, $omega_1$ is Hausdorff)
  + Subspaces of Hausdorff are Hausdorff
]

#pagebreak()

== Limit Points

#definition[
  Let $X$ be a topological space and $A subset.eq X$.
  
  We say that $x in X$ is a limit point of $A$ (or cluster point or accumulation point) iff for every open neighborhood $U$ of $x$ we have that $U inter (A \\ {x}) != diameter$.

  The set of limit points of $A$ is denoted $A'$ and is called the derived set of $A$.
]

#remark[
  Every limit point is a closure point.
]

#proposition[
  For $A subset.eq X$ we have that
  $ overline(A) = A' union A $
]

#proof[

  ($supset.eq$) $A subset.eq overline(A)$ and $A' subset.eq overline(A)$ and so $A' union A subset.eq overline(A)$.

  ($subset.eq$) Suppose $x in overline(A)$ such that $x in.not A$ we show that $x in A'$. We see that for every open neighborhood $U$ of $x$ that $U inter A != diameter$. Now as $x in.not A$ we have that $A = A \\ {x}$ and so $U inter (A \\ {x}) != diameter$ and so $x in A'$.
]

#corollary[
  A is closed iff $A' subset.eq A$.
]

#example[
  In $bb(R)$ with the usual topology consider $A = {1/n : n in bb(N)}$.
  Then $A' = {0}$ and $overline(A) = A union {0}$.
] <limit_point_example>

#definition[
  A point in $A$ that is not a limit point of $A$ is called an isolated point of $A$.

  One sees that $x in A$ is an isolated point iff there is an open neighborhood $U$ of $x$ such that $U inter A = {x}$.
]

#example[
  + We see from @limit_point_example that $1/n$ is isolated in $A$ for all $n in bb(N)$.
  + Consider $A = {-1} union (0,1]$ then $A' = [0,1]$ and so $overline(A) = underbrace({-1}, "isolated") union underbrace([0,1],"limit point")$
]
