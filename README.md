This repo contains proofs about graph algorithms in Coq. My goals are the following:
1. Provide a verified version of DFS based on the CLRS version that is provably terminating and obeys the following properties:
  * The Parentheses Theorem
  * Corollary 22.8 of CLRS (u is a descendant of v iff dv < du < fu < fv)
  * The White Path Theorem
2. Provide a DFS interface consisting mainly of the above properties which defines a specification for any DFS algorithm.
3. Prove the correctness of other algorithms, including topological sorting and finding strongly connected components, based on this interface.

In this way, I can both provide an algorithm that attempts to stick as closely to the CLRS DFS algorithm as possible (although it uses an explicit stack and cannot mutate variables) and prove the correctness of algorithms derived from DFS no matter what implementation is used.

The files in the project are as following:
* Helper.v consists of some helper tactics and lemmas shared across files.
* Graph.v is an interface for graphs. AdjacencyMap.v is a particular implementation of this interface that uses maps of vertices to sets of vertices. I used a Graph interface to keep the algorithm and proofs as general as possible.
* Forest.v is an interface for (rooted) forests. The implementation is still in progress.
* Path.v provides definitions and facilities for reasoning about paths and cycles in a Graph.
* DFS.v defines a DFS algorithm (both as an inductive relation and as an executable function), as well as proofs that the function satsifies the 3 results above (as well as others).
* Proofs.tex provides an overview of the algorithm and the proofs of the DFS function in much less detail than the Coq files.
