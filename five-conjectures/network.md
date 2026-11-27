# An obstruction to long-loop equilibria in the sum network-creation game

## Question and result

Mamageishvili, Mihalák and Müller (2015, p. 484) asked whether a pure Nash equilibrium can contain cycles while its shortest cycle has length at least six. In the sum game, a player pays a positive price \(\alpha\) for each undirected link it buys and adds its graph distances to all other players to its cost. A player may replace its entire set of purchased links. A single profitable deviation rules out a profile. An equilibrium edge has exactly one buyer: at a positive price either of two buyers would strictly benefit by withdrawing their duplicate purchase.

**Partial theorem.** An equilibrium cannot have a bipartite biconnected block of internal diameter three and girth at least six. Arbitrary private graphs may hang from individual block vertices. The proof applies to every ownership assignment and every positive link price. The corollary below also treats a class of nonbipartite blocks of arbitrary diameter. No priority claim is made.

## Reducing the geometry to an incidence structure

Call the two sides of the block points and lines, with adjacency meaning incidence. Two distinct points have even distance at most three and therefore share a line. Two shared lines would give a four-cycle, so this line is unique. Dually any two lines meet in exactly one point. All block vertices have degree at least two.

These incidence axioms give either a finite projective plane or a near-pencil. Here is an elementary account of the classification. If there are four points no three collinear, the projective-plane axioms hold. If no such four points exist, take a line of maximum size. If its size is at least three, it has at most one point outside it: given two outside points, their joining line meets the maximum line once, leaving two points on the maximum line outside that joining line. The four points would then have no collinear triple. There must be at least one outside point by the minimum-degree assumption. Every other line hence joins the unique outside point to one of the points of the maximum line. If the maximum line has just two points, every pair of points is itself a line. Four points would give disjoint lines, so there are just three points and the block is a six-cycle. This is a near-pencil as well.

An exterior component attaches at just one block vertex: an exterior path between distinct block vertices would contradict maximal biconnectivity. Give each block vertex \(v\) weight \(w_v\ge1\), the number of vertices in its attached part, counting the vertex itself. Any change to block links that preserves connectivity changes a block player's distance cost by the weighted changes to its block distances. No assumption on the topology or ownership of the attached parts is needed.

## A swap determines the orientation

Write

\[
s(v)=2w_v+\sum_{t\sim v}w_t.
\]
For a purchased link \(u\to v\) and any other neighbor \(x\) of \(v\), consider replacing \(uv\) by \(ux\). The distance from \(u\) rises by one to \(v\) and to all vertices in \(N(v)\setminus\{u,x\}\). It falls by one to \(x\) and to all vertices in \(N(x)\setminus\{v\}\). Every other distance stays the same. In particular, to reach any originally nonincident line at distance three, a point \(u\) can still follow any retained incident line to their unique intersection. The dual argument applies to a line player. Thus the new distance cost minus the old is exactly

\[
s(v)-s(x)-w_u.
\]
In equilibrium \(s(v)>s(x)\). A directed cycle is impossible by strict descent around the cycle. Every directed path can therefore be extended to a sink. Every sink has at least two incoming edges, so its score is strictly greater than that of each neighbor: apply the swap inequality using another incoming edge. A directed path of length two ending at a sink would also force its penultimate vertex to have a larger score than the sink. Consequently no directed path has length two. Every vertex is a source or a sink. Since the block is connected and bipartite, exactly one side purchases every block link. Call that side the points.

## Near-pencils

The graph consists of \(m\ge2\) internally disjoint three-link paths \(u-a_i-b_i-v\). Label the paths so that \(u,b_i\) are on the purchasing side. Applying the swap inequality to \(b_i\to a_i\) with replacement target \(u\) yields

\[
2w_{a_i}\ge w_u+\sum_j w_{a_j}.
\]
Summing over \(i\) contradicts \(m\ge2\) and \(w_u>0\).

## Projective planes

Let the order be \(q\ge2\). Each point lies on \(q+1\) lines, each line has \(q+1\) points, and each side has \(h=q^2+q+1\) vertices. The lines through a point are called its pencil. Let \(B(u)\) be the total weight of the lines through point \(u\).

**Equality of line weights.** Point \(u\) may buy the entire pencil of a different point \(x\) in place of its own. This costs the same. All other points remain at distance two. Every purchased line is at distance one and every other line is at distance three: a selected line meeting it away from \(u\) always exists. The deviation gives \(B(u)\ge B(x)\), so all pencil weights are equal. Summing the pencil weights over the points of any fixed line \(J\) counts \(J\) exactly \(q+1\) times and every other line once. It follows that all individual lines have the same weight \(b\ge1\).

**A point with a private neighbor.** Write \(a_p\) for point weights and \(A=\sum_p a_p\). If all points had weight one, the one-link swap inequality would require \(q-2\ge (q-1)b\), which is impossible. Choose a point \(u\) with \(a_u>1\), and an exterior neighbor \(z\) attached to \(u\).

**Two incompatible deviations.** Let \(z\) add a link to a uniformly chosen line \(J\) outside the pencil of \(u\). Every point on \(J\) becomes one step closer. Each point other than \(u\) is on exactly \(q\) of the \(q^2\) eligible lines. The chosen line becomes three steps closer; each of the other \(q^2-1\) eligible lines becomes at least one step closer. These savings apply throughout the respective attached parts, and adding a link cannot increase distances. Since every single addition must be unprofitable, its expected saving gives

\[
q\alpha \ge A-a_u+q(q^2+2)b. \tag{1}
\]
Now let \(u\) drop all \(q+1\) incidence links and buy one link to a different point \(x\). It saves \(q\alpha\). Point \(x\) becomes one step closer and the remaining other points one step farther. Each line is now one step farther on average, since \(x\) has just as many incident lines as \(u\), and all line weights are equal. More explicitly, the distance to a line through \(x\) is two and to each other line it is four. A path from \(x\) to a nonincident line can be chosen to avoid \(u\) by going through a point on that line other than \(u\). Equilibrium requires

\[
q\alpha \le A-a_u-2a_x+(q^2+q+1)b. \tag{2}
\]
The lower bound exceeds the upper bound by \(2a_x+(q-1)(q^2+1)b>0\). This contradiction proves the theorem.

## A test for nonbipartite blocks of any diameter

**Corollary.** A nonbipartite block of girth at least six in an equilibrium must contain a pair of vertices at distance three with a unique shortest path.

Indeed, suppose every pair at distance three has at least two shortest paths inside the block. These paths start with different edges, since two length-three paths with the same first edge would create a four-cycle. For a shortest path of any length at least three, its first three-edge segment therefore has a replacement starting with a different edge. Concatenation gives another shortest path to the original destination. Removing a single edge incident with the source cannot increase its distance to any vertex originally three or more steps away.

Consider a swap along \(u-v-x\) as in the orientation argument. Only \(v\) and the other neighbors of \(v\) distinct from \(u,x\) can incur a distance increase, of at most one each. The vertex \(x\) and all its neighbors other than \(v\) gain one step: the latter were originally at distance three by the girth assumption. Additional vertices may also gain. Hence the earlier expression \(s(v)-s(x)-w_u\) is an upper bound on the change. The same strict descent argument forces the sources and sinks to form a bipartition, contradicting the hypothesis. For example, the odd graph \(O_4\), whose vertices are the three-element subsets of a seven-element set and whose edges join disjoint subsets, passes this exclusion test. The checker verifies the distance and multiplicity hypotheses directly.

## Status and sources

The theorem excludes a structural class at every network size. It does not settle the existence of a network with girth at least six, or the stronger tree conjecture at edge prices above the number of players. Lenzner's prior result already excludes unicyclic examples with a cycle longer than five in the asymmetric swap model. Results in the symmetric swap model allow either endpoint to move the link and require separate interpretation.

* [Mamageishvili, Mihalák and Müller, *Tree Nash Equilibria in the Network Creation Game*, especially p. 484 (2015)](https://www.internetmathematicsjournal.com/article/1588-tree-nash-equilibria-in-the-network-creation-game.pdf)
* [Pascal Lenzner, *On Selfish Network Creation*, Theorem 5.3.1](https://hpi.de/friedrich/docs/publications/2014/Lenzner.pdf)
* [Dippel and Vetta, *One n Remains to Settle the Tree Conjecture* (2024)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.STACS.2024.28)
