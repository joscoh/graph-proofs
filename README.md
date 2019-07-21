This repo contains proofs about graph algorithms in Coq. In particular, I have done the following:
1. Provided a verified version of DFS based on the CLRS version that is provably terminating and obeys the following properties:
  * The Parentheses Theorem
  * Corollary 22.8 of CLRS (u is a descendant of v iff dv < du < fu < fv)
  * The White Path Theorem
2. Provide a DFS interface consisting mainly of the above properties which defines a specification for any DFS algorithm.
3. Prove the correctness of other algorithms and applications of DFS, including reachability, cycle detection, topological sorting, and finding strongly connected components, based on this interface.

Most of the proofs are based on the proofs of the analogous algorithm in CLRS, though there are some differences. My DFS implementation uses an explicit stack (rather than recursion) and keeps track of discovery/finish times and vertex colors in sets and maps that are passed around as state, as the variables cannot be mutated directly. 

The files in the project are as following:
* Helper.v consists of some helper tactics and lemmas shared across files.
* Graph.v is an interface for graphs. AdjacencyMap.v is a particular implementation of this interface that uses maps of vertices to sets of vertices. I used a Graph interface to keep the algorithm and proofs as general as possible.
* Forest.v is an interface for (rooted) forests. The implementation is still in progress.
* Path.v provides definitions and facilities for reasoning about paths and cycles in a Graph.
* DFSSpec.v contains a specification for DFS as a module type (DFSBase), an additional specification for a DFS algorithm with cycle detection (DFSWithCycleDetection), and a further specification for a DFS algorithm with topological sorting. There is also another specification (DFSCustomOrdering) which allows for DFS with a custom ordering on the vertices that depends on a given graph. This is put into a separate interface due to limitations in Coq's module system.
* DerivedProofs.v contains a number of results based only on the definitions in DFSSpec.v (and so does not depend on the particular implementation of DFS). It proves the correctness of using DFS for reachability, the cycle detection algorithm, and the topological sorting algorithm (DFSWithTopologicalSort).
* SCCDef.v contains the definition of strong connectivity and a strongly connected component as well as numerous lemmas and results to allow proofs about them.
* SCCAlg.v defines and proves correct Kosaraju's Algorithm for computing strongly connected cmponents. It is also parameterized by an instance of DFSBase (for the first pass) and DFSCustomOrder (for the second pass), making the proof valid for any implementation of DFS.
* DFS.v defines a DFS algorithm (both as an inductive relation and as an executable function), as well as proofs that the function satsifies the DFSBase interface.
* DFSCycle.v contains the algorithm in DFS.v modified to also return a boolean that is true iff there is a cycle. It also has proofs that the function satisfies the DFSWithCycleDetect interface.
* DFSTopoSort.v contains the algorithm in DFS.v modified to also return a list of vertices sorted in reverse order of finish time (which is proved in DFSSpec.v to be a valid topological sorting). It also contains proofs that this function satisfies the DFSWithTopologicalSort interface.
* DFSOrder.v contains the algorithm in DFS.v modified to use a custom ordering that depends on a graph. Due to restrictions in Coq's module system, this ordering is represented as a typeclass, so most of the proofs are reimplemented with the additional parameters, though the proofs are almost entirely the same.
* Proofs.tex provides an overview of the algorithm and the proofs of the DFS function and derived proofs in much less detail than the Coq files.
