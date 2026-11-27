# Computing the product of all spanning-tree bipartitions

Roland Bacher asked on September 13, 2010 for an efficient way to compute the vertex partition obtained by multiplying a proper two-coloring for every spanning tree of a finite connected simple graph. Multiplying by a global sign leaves the partition unchanged, so fix a vertex r and give it color bit 0 in every tree. In this notation the desired product is the bitwise sum over the field F₂. The original post asks for an efficient algorithm and gives no tighter time or space bound. The output has one bit for each vertex.

[Original question and answers](https://mathoverflow.net/questions/38547/efficient-computation-of-a-vertex-partition-for-graphs) · [Left To Solve record mo-38547](https://lefttosolve.com/p/mo-38547)

## Result

If the number of spanning trees is even, all vertices receive the same color. If it is odd, the answer is the unique rooted coloring in which every vertex has an even number of same-colored neighbors. In either case one Gaussian elimination over F₂ computes the answer in cubic time.

### A parity proof

Write τ for the number of spanning trees. Choose a Gallai partition, a coloring g in which every vertex has even degree within its own color class. Normalize g(r)=0. For a spanning tree T, the bit c_T(v) is the parity of the length of its unique path from r to v. The parity of the number of color changes along that path is g(v). Consequently c_T(v)+g(v) counts, modulo two, the path edges whose two ends have the same g-color.

Sum over all T. Removing a marked same-color edge of that path gives a spanning forest F with precisely two components, separating r from v. Conversely, every same-color graph edge between those components extends F uniquely to a spanning tree with that edge marked. The graph of same-color edges has even degree at every vertex, hence every cut in it has an even number of edges. Each F contributes zero modulo two. Therefore

$$\sum_T c_T(v)=\tau\,g(v)\pmod 2.$$

This proof uses the same coloring g for every tree and every v. In particular, an even tree count forces complete cancellation.

### Algorithm and existence of the auxiliary coloring

Delete the row and column of r from the graph Laplacian over F₂ to form L. Let d be its diagonal, the vector of vertex degree parities. For g(r)=0, the equations Lg=d say that the parity of the number of differently colored neighbors equals the degree parity at every nonroot vertex. The root equation follows because the sum of the full Laplacian rows is zero and the sum of all degrees is even.

To see that this system always has a solution, for every z in the kernel of L compute zᵀLz=0. Off-diagonal terms cancel in pairs, and zᵢ²=zᵢ, so dᵀz=0. A symmetric matrix has image equal to the orthogonal complement of its kernel. Thus d is in the image. This also proves the needed two-color version of Gallai's theorem.

The matrix-tree theorem gives det(L)=τ mod 2. If Gaussian elimination finds a missing pivot, return the all-zero vector. Otherwise solve Lg=d and insert g(r)=0. This includes a one-vertex graph, for which the empty minor has determinant one. The implementation takes at most O(n³) field operations and uses O(n²) matrix bits on n vertices, in addition to the input graph. Constructing the Laplacian from edge endpoints takes O(n²+m) ordinary indexing operations on m edges. Gaussian elimination over F₂ uses only binary operations. The Python implementation packs each row into an integer.

[Classic reference on parity of spanning-tree counts](https://www.ics.uci.edu/~eppstein/pubs/Epp-TR-96-14.pdf) · [Gallai's even-degree partitions](https://onlinelibrary.wiley.com/doi/full/10.1002/rsa.21115)

### Independent determinant proof

Let B be the (n−1)-by-m unsigned incidence matrix over F₂ with the row of r deleted, so L=BBᵀ and d=B1. For nonroot v replace column v of Bᵀ by the all-ones vector to form Dᵥ. The answer bit at v equals det(BDᵥ).

Indeed, expand that determinant by Cauchy–Binet. A set S of n−1 graph edges contributes the product of the determinants of the corresponding square minors of B and Dᵥ. If S is disconnected, a component missing r gives a nonzero left-kernel vector for the B minor. If S is a tree, its B minor is invertible: the kernel of its transpose amounts to vertex labels constant along every tree edge, with value 0 at r. Exactly the spanning trees survive. For a tree S, its rooted coloring solves B_Sᵀc=1, which enforces opposite colors across every tree edge. Its minor determinant is one, and Cramer's rule identifies the Dᵥ determinant as c(v).

Replacing a column before left multiplication replaces the same column of L by d. Thus the entire product coloring is adj(L)d. With A=adj(L), which is symmetric, the i-th diagonal entry of ALA is the i-th component of Ad: off-diagonal summands cancel in pairs and squares equal themselves. But ALA=det(L)A. Hence the product is det(L) times the diagonal of adj(L), including when L is singular. This directly yields the algorithm above.

The general determinant formula is kernel-checked in [TreeResult.lean](TreeResult.lean). The characteristic-two identity is in [TreeParity.lean](TreeParity.lean), and [TreeFast.lean](TreeFast.lean) proves the spanning-tree count parity formula, the even-count collapse, and equivalence of the aggregate coloring with the single binary linear solve in the nonsingular case.

## Checks and prior work

[partition.py](partition.py) implements the stated elimination. [verify_partition.py](verify_partition.py) independently enumerates spanning trees, computes their bipartitions by traversal, and uses a subset sum to aggregate the explicit tree contributions over all simple graphs of each size. It checks each choice of root. All 27,476 connected labeled graphs with one to six vertices passed, for 164,031 graph/root pairs. [Verification output](verification.txt)

A triangle on vertices 0,1,2 with a leaf 3 attached to 0 has three spanning trees. Rooting at 0, the two other triangle vertices have path lengths 1,1,2 across the three trees, hence bit zero. The leaf has lengths 1,1,1, hence bit one. This corrects which vertex is isolated in Bill Thurston's December 2010 comment. His observation that the partition is nontrivial holds. [Original comment](https://mathoverflow.net/questions/38547/efficient-computation-of-a-vertex-partition-for-graphs#comment122582_38561)

The original thread includes analyses of trees, bipartite graphs, bridges, and cut vertices. Its comments identify the parity-of-total-distance reformulation. Searches for the original post, its author, spanning-tree parity partitions, transfer currents and the connection with Gallai partitions found the classical ingredients but did not locate an earlier general solution to this precise question. A published treatment under another name could have escaped this search. The network application is the aggregation of topology information over all spanning trees of a connected network.

## Running the Lean proof

[BacherPartition.lean](BacherPartition.lean) is the standalone development. From a checkout of google-deepmind/formal-conjectures at 9097e2f90e66 with its pinned dependencies, run `lake env lean /path/to/BacherPartition.lean`. The file checks on Lean 4.33.1. Its axiom audit uses only propext, Classical.choice and Quot.sound.

The executable Lean solver is verified on arbitrary finite edge lists. For distinct loopless edges, the theorem `Bacher.algorithm_on_graph` identifies its output with the sum of root-distance parities over precisely the Mathlib spanning trees. The verified Gaussian solve costs at most 7k³ field operations and pivot comparisons for k nonroot vertices. The explicit dense edge-list preparation is also costed in Lean. Its accounting adds 3km + 2k²m + 2km operations for m edges, counting each endpoint comparison as one operation. The Python version constructs the reduced Laplacian directly from the adjacency lists and uses one cubic-time elimination. These counts measure different implementations.

[TreeSchedule.lean](TreeSchedule.lean) and [TreeCircuitResult.lean](TreeCircuitResult.lean) give an independent Boolean circuit construction. Given the reduced incidence matrix, the circuit for all output bits uses at most 2mk³ + 3k⁵ + 2k⁴ binary gates. Correctness and this gate bound both passed Lean's axiom audit.

[Left To Solve submission #2006](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2006) requests review of the translation of the original algorithmic question. It links the Lean-checked result. The proposed target uses a polynomial-time multitape Turing machine on adjacency bitstrings. The construction, correctness and polynomial operation bounds above are checked in their matrix and circuit models. The compilation into that specific machine formalism is still open in Lean.
